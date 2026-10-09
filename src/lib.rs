#[allow(non_camel_case_types, non_snake_case, dead_code, unused_imports)]
mod security_monitor;

pub use security_monitor::*;

#[cfg(test)]
mod tests {
    use super::*;

    fn subject() -> agent_ext<()> {
        let req = req_const();
        let i_actions = set::set(list::Cons(req, Box::new(list::Nil)));
        let s_actions = set::set(list::Nil);
        agent_ext::agent_ext(agentType::S, i_actions, s_actions, ())
    }

    #[test]
    fn legitimate_request_is_confidential() {
        let subject = subject();
        let req = req_const();
        assert!(conf_i_action(&req, &dataType::PR, &subject));
    }

    #[test]
    fn external_agent_is_rejected() {
        let subject = subject();
        let malicious = create_i_Action(
            &agentType::ExternalAgent,
            &accessType::at,
            &dataType::PR,
        );
        assert!(!conf_i_action(&malicious, &dataType::PR, &subject));
    }

    #[test]
    fn homomorphism_preserves_policy() {
        let subject = subject();
        let mapped = h(&checkRight_const());
        assert!(conf_i_action(&mapped, &dataType::PR, &subject));
    }
}
