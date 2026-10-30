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

-- 注意：`lean_exe` 没有 `srcDir` 字段（只有 `lean_lib` 有），所以 exe 的根模块必须放在
-- 包根目录，不能指向 `LeanSrc/` 里的模块。要跑 Plausible 的属性测试，两条路：
--
--   1. 不建 exe，直接用 `lake env lean LeanSrc/XS_MERA_InterfaceGap_PlausibleTest.lean`
--      执行文件里的 `#eval`（当前做法，见 README）；
--   2. 在包根新建 `Main.lean`（`import XS_MERA_InterfaceGap_PlausibleTest` + `def main`），
--      然后启用下面这段：
--
-- lean_exe xsmera_test where
--   root := `Main
