theory Security_Patterns
  imports Main
begin

section \<open>1. Базовые типы данных и структуры (Таблица 1)\<close>

datatype agentType = S | ExternalAgent
datatype actionType = req | checkRight | nullAction
datatype accessType = at
datatype dataType = PR

datatype capabilityType = C

(* Запись для абстрактного уровня (DIPM) *)
record i_action =
  agent  :: "agentType"
  access :: "accessType"
  data   :: "dataType"

(* Запись для конкретного уровня (DSPM) — расширяет i_action *)
record s_action = i_action +
  capability :: "capabilityType"

(* Структура Агента *)
record agent =
  name      :: "agentType"
  i_actions :: "i_action set"
  s_actions :: "s_action set"


section \<open>2. Абстрактный уровень (DIPM) и верификация (Таблицы 2 и 3)\<close>

definition create_i_Action :: "agentType \<Rightarrow> accessType \<Rightarrow> dataType \<Rightarrow> i_action" where
  "create_i_Action ag a d == \<lparr> agent = ag, access = a, data = d \<rparr>"

definition req_const :: "i_action" where
  "req_const == create_i_Action S at PR"

definition createAgent :: "agentType \<Rightarrow> i_action set \<Rightarrow> s_action set \<Rightarrow> agent" where
  "createAgent ag i_as s_as == \<lparr> name = ag, i_actions = i_as, s_actions = s_as \<rparr>"

(* Реализация предикатов безопасности, опущенных в статье для простоты *)
definition isAllowed :: "i_action \<Rightarrow> dataType \<Rightarrow> agent \<Rightarrow> bool" where
  "isAllowed a d ag == (a \<in> i_actions ag) \<and> (data a = d)"

definition isProtected :: "i_action \<Rightarrow> dataType \<Rightarrow> bool" where
  "isProtected a d == (data a = d)"

(* Абстрактное свойство конфиденциальности (conf_i_action) *)
definition conf_i_action :: "i_action \<Rightarrow> dataType \<Rightarrow> agent \<Rightarrow> bool" where
  "conf_i_action a d ag == isAllowed a d ag \<and> isProtected a d"

(* Субъект на абстрактном уровне *)
definition subject :: "agent" where
  "subject == createAgent S {req_const} {}"

(* Лемма confReq: Доказательство конфиденциальности абстрактного запроса *)
lemma confReq : "conf_i_action req_const PR subject"
  apply (simp only: conf_i_action_def)
  apply (simp only: isAllowed_def isProtected_def)
  apply (simp only: req_const_def)
  apply (simp only: create_i_Action_def)
  apply (simp only: subject_def)
  apply (simp only: createAgent_def)
  apply (simp add: req_const_def)
  apply (simp only: create_i_Action_def)
  done


section \<open>3. Доменный уровень (DSPM) и Гомоморфизм (Таблица 3 и Рис. 4)\<close>

definition create_s_Action :: "agentType \<Rightarrow> accessType \<Rightarrow> dataType \<Rightarrow> capabilityType \<Rightarrow> s_action" where
  "create_s_Action ag a d c == \<lparr> agent = ag, access = a, data = d, capability = c \<rparr>"

definition checkRight_const :: "s_action" where
  "checkRight_const == create_s_Action S at PR C"

(* Уточненный субъект с доменными действиями *)
definition subject_dspm :: "agent" where
  "subject_dspm == createAgent S {req_const} {checkRight_const}"

(* Доменное свойство конфиденциальности (conf_s_action) *)
definition conf_s_action :: "s_action \<Rightarrow> dataType \<Rightarrow> agent \<Rightarrow> bool" where
  "conf_s_action a d ag == (a \<in> s_actions ag) \<and> (data (i_action.truncate a) = d)"

(* Лемма confCheckRight: Доказательство для уровня мандатов *)
lemma confCheckRight : "conf_s_action checkRight_const PR subject_dspm"
   apply (simp only: conf_s_action_def)
  apply (simp only: checkRight_const_def)
  apply (simp only: subject_dspm_def)
  apply (simp only: createAgent_def)
  apply (simp only: create_s_Action_def)
  apply (simp only: i_action.defs)
  by (simp add: checkRight_const_def create_s_Action_def)


(* Гомоморфизм h: отображает доменные действия на абстрактные *)
(* definition h :: "s_action \<Rightarrow> i_action" where
  "h a == (if (actionType.fields (access a) = checkRight) then req_const 
           else \<lparr> agent = agent a, access = access a, data = data a \<rparr>)" *)

definition h :: "s_action \<Rightarrow> i_action" where
  "h a == (if a = checkRight_const then req_const 
           else \<lparr> agent = agent a, access = access a, data = data a \<rparr>)"

(* Теорема соответствия уровней (Correspondence) *)
theorem confReqH : "conf_i_action (h checkRight_const) PR subject"
  by (simp add: confReq h_def)


section \<open>4. Принципиально недоказуемый / непроверяемый случай\<close>

(* Сценарий уязвимости: Внешний злоумышленник (ExternalAgent) 
   пытается вызвать абстрактный запрос к защищенным данным PR *)
definition malicious_req :: "i_action" where
  "malicious_req == create_i_Action ExternalAgent at PR"

(* Теорема взлома: Мы пытаемся доказать, что запрос злоумышленника 
   удовлетворяет политике конфиденциальности легитимного Субъекта.
   Isabelle ЗАБЛОКИРУЕТ это доказательство. *)
theorem confReq_AttackFailed : "conf_i_action malicious_req PR subject"
  apply (simp only: conf_i_action_def)
  apply (simp only: isAllowed_def isProtected_def)
  apply (simp only: malicious_req_def)
  apply (simp only: create_i_Action_def)
  apply (simp only: subject_def)
  apply (simp only: createAgent_def)
  apply (simp only: req_const_def)
  (* На этом этапе Isabelle оставляет неразрешимую подцель (subgoal):
     1. \<lparr>agent = ExternalAgent, access = at, data = PR\<rparr> = \<lparr>agent = S, access = at, data = PR\<rparr>
     Поскольку ExternalAgent \<noteq> S, доказательство невозможно завершить. 
     Команда 'done' здесь вызовет ошибку компиляции теории. *)
  oops (* oops используется в Isabelle для отказа от недоказуемого утверждения *)

export_code conf_i_action h req_const checkRight_const in Haskell module_name Security file_prefix "codegen_haskell"

end
