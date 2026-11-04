-- lakefile.lean
-- 说明：Plausible 依赖已暂时移除（源码未 import Plausible，穷举扫描用纯 IO 实现；
-- 且当前网络无法访问 GitHub）。接入点见 PlausibleTest 文末 NOTE，恢复时加回：
-- require plausible from git "https://github.com/leanprover-community/plausible" @ "main"
import Lake
open Lake DSL

package «x-s-mera-formal»

@[default_target] lean_lib XSMERA where
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
-- 包根目录，不能指向 `LeanSrc/` 里的模块。要跑穷举扫描，两条路：
--
--   1. 不建 exe，直接用 `lake env lean LeanSrc/XS_MERA_InterfaceGap_PlausibleTest.lean`
--      执行文件里的 `#eval`（当前做法，见 README）；
--   2. 在包根新建 `Main.lean`（`import XS_MERA_InterfaceGap_PlausibleTest` + `def main`），
--      然后启用下面这段：
--
-- lean_exe xsmera_test where
--   root := `Main
