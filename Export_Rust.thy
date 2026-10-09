theory Export_Rust
  imports Codegen_Rust Security_Patterns
begin

export_code conf_i_action h req_const checkRight_const
  in Rust module_name security_monitor file "src/security_monitor.rs"

end
