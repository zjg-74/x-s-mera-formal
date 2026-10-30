-- lakefile.lean
require "plausible" from "https://github.com/leanprover-community/plausible" @ "main"

lean_lib XSMERA where
  srcDir := "LeanSrc"
  roots := #[
    `XS_MERA_Core,
    `XS_MERA_InterfaceGap,
    `XS_MERA_InterfaceGap_ModelClass,
    `XS_MERA_InterfaceGap_TemporalBridge,
    `XS_MERA_InterfaceGap_PlausibleTest,
    `XS_MERA_InterfaceGap_GreyCase,
    `XS_MERA_InterfaceGap_A3Star,
    `XS_MERA_Appendix_AxiomRisk
  ]

lean_exe xsmera_test where
  srcDir := "LeanSrc"
  root := `XS_MERA_InterfaceGap_PlausibleTest
