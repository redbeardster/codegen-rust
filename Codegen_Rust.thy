theory Codegen_Rust
  imports Main
begin

text \<open>
  Code target \<open>Rust\<close> for Isabelle2025.

  The serializer walks the code generator's intermediate language
  (Code_Thingol) and emits a single Rust module: algebraic datatypes become
  enums, code equations become functions, and the HOL equal class is passed
  as an explicit dictionary, in the same style as the SML target.
\<close>

ML \<open>
structure Rust_Serializer =
struct

open Basic_Code_Thingol;
open Code_Thingol;
open Code_Symbol;

datatype mode = AsRef | AsVal;

val keywords = [
  "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else",
  "enum", "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop",
  "match", "mod", "move", "mut", "pub", "ref", "return", "self", "Self",
  "static", "struct", "super", "trait", "true", "type", "unsafe", "use",
  "where", "while", "abstract", "become", "box", "do", "final", "macro",
  "override", "priv", "typeof", "unsized", "virtual", "yield", "try", "gen",
  "dict_apply"
];

fun sanitize s =
  String.implode (map (fn #"'" => #"_" | c => c) (String.explode s));

fun clean_name s =
  let val s = sanitize s
  in if member (op =) keywords s orelse s = "" then s ^ "_" else s end;

fun sym_name (Constant c) = c
  | sym_name (Type_Constructor tyco) = tyco
  | sym_name (Type_Class class) = class
  | sym_name (Class_Relation (a, b)) = a ^ "_" ^ b
  | sym_name (Class_Instance (tyco, class)) = tyco ^ "_" ^ class
  | sym_name (Module m) = m;

fun base_name sym = clean_name (Long_Name.base_name (sym_name sym));

fun qualified_name sym =
  clean_name (space_implode "_" (Long_Name.explode (sym_name sym)));

fun allocate syms reserved =
  let
    val raw = map (fn sym => (sym, base_name sym)) syms;
    fun frequency base =
      length (filter (fn (_, base') => base = base') raw);
    fun choose (sym, base) =
      if frequency base = 1 andalso not (member (op =) reserved base)
      then base
      else qualified_name sym;
  in map (fn (sym, base) => (sym, choose (sym, base))) raw end;

fun lookup table sym =
  case AList.lookup (op =) table sym of
    SOME name => name
  | NONE => base_name sym;

fun tyvars (tyco `%% tys) = maps tyvars tys
  | tyvars (ITyVar v) = [v];

fun contains_tyco tyco (t `%% tys) =
      t = tyco orelse exists (contains_tyco tyco) tys
  | contains_tyco _ (ITyVar _) = false;

fun add_pat_vars (IVar (SOME v)) = cons v
  | add_pat_vars (IVar NONE) = I
  | add_pat_vars (IConst _) = I
  | add_pat_vars (t1 `$ t2) = add_pat_vars t1 #> add_pat_vars t2
  | add_pat_vars (_ `|=> (t, _)) = add_pat_vars t
  | add_pat_vars (ICase {term = t, clauses, ...}) =
      add_pat_vars t #> fold (fn (p, b) => add_pat_vars p #> add_pat_vars b) clauses;

fun linear pats =
  let
    val vs = fold add_pat_vars pats [];
    fun dup [] = false
      | dup (v :: rest) = member (op =) rest v orelse dup rest;
  in not (dup vs) end;

fun is_var (IVar _) = true
  | is_var _ = false;

fun rust_program module_name program =
  let
    val nodes = Graph.fold (fn (sym, (stmt, _)) => cons (sym, stmt)) program [];

    fun stmt_of sym = Graph.get_node program sym;

    fun constr_info sym =
      case stmt_of sym of
        Datatypecons tyco =>
          let
            val Datatype (_, cos) = stmt_of (Type_Constructor tyco);
            val tys = snd (the (find_first (fn ((c, _), _) => c = sym_name sym) cos));
          in (tyco, tys) end
      | _ => error ("Rust_Serializer: not a constructor: " ^ marker sym);

    val type_syms =
      map_filter (fn (sym, Datatype _) => SOME sym | _ => NONE) nodes;
    val fun_syms =
      map_filter (fn (sym, Fun _) => SOME sym | _ => NONE) nodes;

    fun dict_builder_base tyco = "dict_" ^ clean_name (Long_Name.base_name tyco);
    val dict_builders =
      map_filter (fn (_, Classinst {tyco, class, ...}) =>
          if class = "HOL.equal" then SOME (dict_builder_base tyco) else NONE
        | _ => NONE) nodes;

    val fun_names = allocate fun_syms ("dict_apply" :: dict_builders);
    fun fun_name sym = lookup fun_names sym;

    val type_names =
      allocate
        (filter (fn sym =>
           let val n = sym_name sym
           in n <> "fun" andalso n <> "HOL.bool" andalso n <> "Product_Type.unit" end)
         type_syms)
        [];
    fun type_name tyco =
      if tyco = "HOL.bool" then "bool"
      else if tyco = "Product_Type.unit" then "()"
      else lookup type_names (Type_Constructor tyco);

    fun tyvar v = "T" ^ clean_name v;

    fun print_ty (tyco `%% tys) =
          if tyco = "fun" then
            (case tys of
              [ty1, ty2] => "fn(" ^ print_ty ty1 ^ ") -> " ^ print_ty ty2
            | _ => error "Rust_Serializer: malformed function type")
          else if null tys then type_name tyco
          else type_name tyco ^ "<" ^ commas (map print_ty tys) ^ ">"
      | print_ty (ITyVar v) = tyvar v;

    fun builtin sym =
      case try constr_info sym of
        SOME ("HOL.bool", _) =>
          SOME (if Long_Name.base_name (sym_name sym) = "True" then "true" else "false")
      | SOME ("Product_Type.unit", _) => SOME "()"
      | _ => NONE;

    fun variant_name sym = base_name sym;

    fun print_pat (IVar NONE) = "_"
      | print_pat (IVar (SOME v)) = clean_name v
      | print_pat t =
          (case unfold_const_app t of
            SOME ({sym, ...}, args) =>
              (case builtin sym of
                SOME s => s
              | NONE =>
                  let
                    val (tyco, _) = constr_info sym;
                    val head = type_name tyco ^ "::" ^ variant_name sym;
                  in
                    if null args then head
                    else head ^ "(" ^ commas (map print_pat args) ^ ")"
                  end)
          | NONE => error "Rust_Serializer: unsupported pattern");

    fun dict_var_name {var, index, length, ...} =
      "d_" ^ clean_name var ^ (if length <= 1 then "" else string_of_int index);

    fun print_dict_val (Dict (_, Dict_Var x)) = dict_var_name x ^ ".clone()"
      | print_dict_val (Dict (_, Dict_Const ((tyco, class), dss))) =
          if class <> "HOL.equal" then
            error ("Rust_Serializer: unsupported class " ^ class)
          else
            dict_builder_base tyco ^ "(" ^
            commas (maps (fn (_, ds) => map print_dict_val ds) dss) ^ ")";

    fun print_dict_ref (Dict (_, Dict_Var x)) = dict_var_name x
      | print_dict_ref d = "&(" ^ print_dict_val d ^ ")";

    fun dict_binds vs =
      maps (fn (v, sort) =>
        map_index (fn (i, class) =>
          let
            val n = length sort;
            val name = "d_" ^ clean_name v ^ (if n <= 1 then "" else string_of_int i);
          in {name = name, class = class, var = v} end) sort) vs;

    fun adapt AsVal s = s
      | adapt AsRef s = "&(" ^ s ^ ")";

    fun print_term mode (IVar NONE) =
          error "Rust_Serializer: wildcard in an expression"
      | print_term AsRef (IVar (SOME v)) = clean_name v
      | print_term AsVal (IVar (SOME v)) = clean_name v ^ ".clone()"
      | print_term mode (IConst const) = print_app mode (const, [])
      | print_term mode (t as _ `$ _) =
          (case unfold_const_app t of
            SOME app => print_app mode app
          | NONE => error "Rust_Serializer: unsupported application")
      | print_term mode (ICase {term = t, clauses, ...}) =
          let
            val arms =
              map (fn (p, b) =>
                "        " ^ print_pat p ^ " => " ^ print_term AsVal b ^ ",") clauses;
            val expr =
              "match " ^ print_term AsRef t ^ " {\n" ^ cat_lines arms ^
              "\n        _ => panic!(\"incomplete pattern\"),\n    }";
          in adapt mode ("(" ^ expr ^ ")") end
      | print_term _ (_ `|=> _) =
          error "Rust_Serializer: lambdas are not supported"

    and print_app mode ({sym, dicts, ...}, ts) =
      let
        val dict_args = map print_dict_ref (flat dicts);
        val expr =
          (case builtin sym of
            SOME s => s
          | NONE =>
              if is_constr program sym then
                let
                  val (tyco, fields) = constr_info sym;
                  fun one i arg =
                    let
                      val owned = print_term AsVal arg;
                      val boxed =
                        i < length fields andalso contains_tyco tyco (nth fields i);
                    in if boxed then "Box::new(" ^ owned ^ ")" else owned end;
                  val args = map_index (fn (i, arg) => one i arg) ts;
                  val head = type_name tyco ^ "::" ^ variant_name sym;
                in if null args then head else head ^ "(" ^ commas args ^ ")" end
              else if (case stmt_of sym of Classparam _ => true | _ => false) then
                "dict_apply(" ^ commas (dict_args @ map (print_term AsRef) ts) ^ ")"
              else
                fun_name sym ^ "(" ^ commas (dict_args @ map (print_term AsRef) ts) ^ ")");
      in adapt mode expr end;

    fun generics (vs, ty) =
      distinct (op =) (map fst vs @ subtract (op =) (map fst vs) (tyvars ty));

    fun gen_clause vs =
      if null vs then ""
      else "<" ^ commas (map (fn v => tyvar v ^ ": Clone + 'static") vs) ^ ">";

    fun print_fun (sym, Fun ((tysm as (vs, ty), eqs), _)) =
          let
            val eqs = filter (fn ((pats, _), _) => linear pats) eqs;
            val name = fun_name sym;
            val gens = gen_clause (generics tysm);
            val dparams =
              map (fn {name, class, var} =>
                if class <> "HOL.equal" then
                  error ("Rust_Serializer: unsupported class " ^ class)
                else name ^ ": &EqualDict<" ^ tyvar var ^ ">") (dict_binds vs);
          in
            if null eqs then
              "#[inline]\npub fn " ^ name ^ gens ^ "() {\n    panic!(\"no linear code equation\");\n}\n"
            else
              let
                val ((pats, body), _) = hd eqs;
                val n = length pats;
                val (arg_tys, res_ty) = unfold_fun_n n ty;
                val trivial = length eqs = 1 andalso forall is_var pats;
                fun vparam i ty pat =
                  let
                    val pname =
                      if trivial then
                        (case pat of
                          IVar (SOME v) => clean_name v
                        | IVar NONE => "_arg" ^ string_of_int i
                        | _ => "arg" ^ string_of_int i)
                      else "arg" ^ string_of_int i;
                  in pname ^ ": &" ^ print_ty ty end;
                val vparams =
                  if trivial then map_index (fn (i, ty) => vparam i ty (nth pats i)) arg_tys
                  else map_index (fn (i, ty) => vparam i ty (IVar NONE)) arg_tys;
                val scrut =
                  if n = 0 then ""
                  else if n = 1 then "arg0"
                  else "(" ^ commas (map (fn i => "arg" ^ string_of_int i) (0 upto (n - 1))) ^ ")";
                fun arm ((pats, body), _) =
                  let
                    val pat =
                      if n = 1 then print_pat (hd pats)
                      else "(" ^ commas (map print_pat pats) ^ ")";
                  in "        " ^ pat ^ " => " ^ print_term AsVal body ^ "," end;
                val rhs =
                  if trivial then print_term AsVal body
                  else
                    "match " ^ scrut ^ " {\n" ^ cat_lines (map arm eqs) ^
                    "\n        _ => panic!(\"incomplete pattern\"),\n    }";
              in
                "#[inline]\npub fn " ^ name ^ gens ^ "(" ^ commas (dparams @ vparams) ^
                ") -> " ^ print_ty res_ty ^ " {\n    " ^ rhs ^ "\n}\n"
              end
          end
      | print_fun _ = "";

    fun skip_tyco "fun" = true
      | skip_tyco "HOL.bool" = true
      | skip_tyco "Product_Type.unit" = true
      | skip_tyco _ = false;

    fun deps_of cos =
      distinct (op =) (maps (fn (_, tys) => maps tyvars_or_tycos tys) cos)
    and tyvars_or_tycos (t `%% tys) = t :: maps tyvars_or_tycos tys
      | tyvars_or_tycos (ITyVar _) = [];

    val datatypes =
      map_filter (fn (Type_Constructor tyco, Datatype (vs, cos)) =>
            if skip_tyco tyco orelse null cos then NONE else SOME (tyco, vs, cos)
          | _ => NONE) nodes;

    fun emit_ready [] ordered _ = rev ordered
      | emit_ready pending ordered guard =
          let
            val known = map #1 ordered @ map #1 pending;
            fun ready (tyco, _, cos) =
              forall (fn d =>
                d = tyco orelse member (op =) (map #1 ordered) d orelse
                not (member (op =) known d)) (deps_of cos);
            val (now, later) = List.partition ready pending;
          in
            if null now then
              if guard then rev ordered @ pending
              else emit_ready later ordered true
            else emit_ready later (rev now @ ordered) guard
          end;

    fun print_datatype (tyco, vs, cos) =
      let
        val gens =
          if null vs then ""
          else "<" ^ commas (map tyvar vs) ^ ">";
        fun print_co ((co, _), []) = "    " ^ variant_name (Constant co) ^ ","
          | print_co ((co, _), tys) =
              "    " ^ variant_name (Constant co) ^ "(" ^
              commas (map_index (fn (i, ty) =>
                if contains_tyco tyco ty then "Box<" ^ print_ty ty ^ ">" else print_ty ty) tys) ^
              "),";
      in
        "#[derive(Clone, Debug)]\npub enum " ^ type_name tyco ^ gens ^ " {\n" ^
        cat_lines (map print_co cos) ^ "\n}\n"
      end;

    fun print_instance (Classinst {tyco, class, vs, inst_params, ...}) =
          if class <> "HOL.equal" then ""
          else
            let
              val binds = dict_binds vs;
              val gens = gen_clause (map #var binds);
              val params =
                map (fn {name, class = c, var} =>
                  if c <> "HOL.equal" then error ("Rust_Serializer: unsupported class " ^ c)
                  else name ^ ": EqualDict<" ^ tyvar var ^ ">") binds;
              val ((_, (impl, _)), _) =
                (case inst_params of
                  [p] => p
                | _ => error ("Rust_Serializer: expected one equal method for " ^ tyco));
              val impl_name = fun_name (#sym impl);
              val captures = map #name binds;
              val lets =
                map (fn n => "    let " ^ n ^ " = Rc::new(" ^ n ^ ");") captures;
              val call =
                impl_name ^ "(" ^
                commas (map (fn n => "&" ^ n) captures @ ["x", "y"]) ^ ")";
              val closure = if null captures then "|x, y| " else "move |x, y| ";
              val ret = print_ty (tyco `%% map (ITyVar o #var) binds);
            in
              "#[inline]\npub fn " ^ dict_builder_base tyco ^ gens ^ "(" ^ commas params ^
              ") -> EqualDict<" ^ ret ^ "> {\n" ^
              cat_lines lets ^ (if null lets then "" else "\n") ^
              "    EqualDict { equal: Rc::new(" ^ closure ^ call ^ ") }\n}\n"
            end
      | print_instance _ = "";

    val header =
      cat_lines [
        "// Generated by Isabelle/HOL Codegen_Rust. Module: " ^
          (if module_name = "" then "security" else module_name) ^ ".",
        "#![allow(non_camel_case_types, non_snake_case, dead_code, unused_variables,",
        "    unreachable_patterns, unused_parens, clippy::all)]",
        "",
        "use std::rc::Rc;",
        "",
        "#[derive(Clone)]",
        "pub struct EqualDict<A> {",
        "    pub equal: Rc<dyn Fn(&A, &A) -> bool>,",
        "}",
        "",
        "#[inline]",
        "fn dict_apply<A>(d: &EqualDict<A>, a: &A, b: &A) -> bool {",
        "    (d.equal)(a, b)",
        "}",
        ""
      ];

    val ty_text = cat_lines (map print_datatype (emit_ready datatypes [] false));
    val fun_text =
      cat_lines (map_filter (fn (sym, stmt) =>
        case stmt of Fun _ => SOME (print_fun (sym, stmt)) | _ => NONE) nodes);
    val inst_text =
      cat_lines (map_filter (fn (_, stmt) =>
        case stmt of Classinst _ => SOME (print_instance stmt) | _ => NONE) nodes);
  in
    header ^ "\n" ^ ty_text ^ "\n" ^ fun_text ^ "\n" ^ inst_text
  end;

fun serialize (_ : Proof.context)
    ({module_name, ...} : {
      reserved_syms: string list,
      identifiers: Code_Printer.identifiers,
      includes: (string * Pretty.T) list,
      class_syntax: string -> string option,
      tyco_syntax: string -> Code_Printer.tyco_syntax option,
      const_syntax: string -> Code_Printer.const_syntax option,
      module_name: string})
    (program : Code_Thingol.program) (_ : Code_Symbol.T list) =
  let
    val text = rust_program module_name program;
  in
    (Code_Target.Singleton ("rs", Pretty.str text), fn _ => NONE)
  end;

val literals = Code_Printer.Literals {
  literal_string = fn s => "\"" ^ s ^ "\"",
  literal_numeral = signed_string_of_int,
  literal_list = fn _ => Pretty.str "Vec::new()",
  infix_cons = (5, "cons")
};

end;
\<close>

setup \<open>
  let
    val language = {
      serializer = Code_Target.parse_args (Scan.succeed Rust_Serializer.serialize),
      literals = Rust_Serializer.literals,
      check = {
        env_var = "HOME",
        make_destination = fn p => Path.append p (Path.basic "security_monitor.rs"),
        make_command = K "rustc --edition 2021 --crate-type lib security_monitor.rs"
      },
      evaluation_args = []
    };
  in
    fn thy =>
      Code_Target.add_language ("Rust", language) thy
      handle ERROR msg =>
        if String.isSubstring "overwrite existing target" msg then thy
        else raise ERROR msg
  end
\<close>

end
