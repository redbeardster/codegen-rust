use security_monitor::{
    accessType, agentType, agent_ext, checkRight_const, conf_i_action, create_i_Action, dataType,
    dict_unit, equal_i_action_ext, h, list, req_const, set,
};

fn subject() -> agent_ext<()> {
    let req = req_const();
    let i_actions = set::set(list::Cons(req, Box::new(list::Nil)));
    let s_actions = set::set(list::Nil);
    agent_ext::agent_ext(agentType::S, i_actions, s_actions, ())
}

fn verdict(ok: bool) -> &'static str {
    if ok { "allow" } else { "deny" }
}

fn main() {
    let subject = subject();
    let req = req_const();
    let malicious = create_i_Action(
        &agentType::ExternalAgent,
        &accessType::at,
        &dataType::PR,
    );
    let mapped = h(&checkRight_const());

    let legitimate = conf_i_action(&req, &dataType::PR, &subject);
    let attack = conf_i_action(&malicious, &dataType::PR, &subject);
    let via_homomorphism = conf_i_action(&mapped, &dataType::PR, &subject);

    println!("security monitor");
    println!("  subject request {req:?} -> {}", verdict(legitimate));
    println!("  external agent  {malicious:?} -> {}", verdict(attack));
    println!(
        "  h(checkRight)   {mapped:?} -> {}",
        verdict(via_homomorphism)
    );

    let same_as_req = equal_i_action_ext(&dict_unit(), &mapped, &req_const());
    println!(
        "  h(checkRight) = req_const -> {}",
        if same_as_req { "yes" } else { "no" }
    );

    let policy_holds = legitimate && !attack && via_homomorphism && same_as_req;
    if !policy_holds {
        eprintln!("policy check failed");
        std::process::exit(1);
    }
}
