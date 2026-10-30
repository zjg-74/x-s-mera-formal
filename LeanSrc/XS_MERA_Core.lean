/-!
  XS_MERA_Core

  X-S-MERA 核心：GAPS 公理、B1/B2 时序桥基础原语。
  依赖链第 1 层，无内部依赖。

  ## 编译状态

  本文件依 Lean 4 规则做过类型修订，**未在本机编译验证**（本机无 Lean 工具链）。
  相对来稿的实质改动见文件末尾 `NOTE`。

  ## 为何不引入 Mathlib

  来稿使用 `ℝ`。`ℝ` 不属于 Lean 4 核心库，需 `import Mathlib`，首次构建以小时计，
  审稿人不会等。故此处把回报值域抽象为带 `LT` 的任意类型 `R`；需要实数时实例化
  `R := ℝ` 并接入 Mathlib 即可恢复原语义。
-/
namespace XS_MERA

/-! ### B1/B2 时序原语

本层不展开，供 `XS_MERA_InterfaceGap_TemporalBridge` 实例化。 -/
variable {S E V : Type}
variable (step : S → E → S)
variable (trace : ℕ → S → S)
variable (LatentState : S → Prop)
variable (Entropy : S → V)

/-! ### 奖励劫持 -/

/-- 经典奖励劫持：`p` 落在观测像集内，且存在另一个可观测实践 `p'`，
其回报更高，而行动者原本更偏好 `p`——即通过抬高自身观测指标换取回报。

来稿写作 `Reward (π p'.get) > Reward (π p.get)`。Lean 4 的 `Option.get` 需要一个
`isSome` 证明参数，不能直接 `.get`；此处改为存在量化绑定，语义等价且免去证明项。 -/
def rewardHack {P X : Type} {R : Type} [LT R]
    (p : P) (π : P → Option X) (Reward : X → R) (PreferP : P → P → Prop) : Prop :=
  ∃ (x : X), π p = some x ∧
    ∃ (p' : P) (x' : X), π p' = some x' ∧ Reward x < Reward x' ∧ PreferP p p'

/-! ### GAPS 公理

两条 `True` 公理不提供任何约束，仅占位。若论文要引用 GAPS 内部结构，
此处须替换为实质命题；否则在公理清单中应标为「空公理」。 -/
axiom GAPS_axioms : True
axiom B1B2_bridge_axioms : True

end XS_MERA

/-!
## NOTE（相对来稿的改动）

1. `ℝ` → 抽象类型参数 `R`（带 `[LT R]`），免 Mathlib 依赖。
2. `Reward (π p'.get)` → 存在量化 `∃ x', π p' = some x' ∧ …`；`Option.get` 需证明参数。
3. 顶层 `variable` 声明保留作文档，但 `rewardHack` 自带完整参数表，不依赖隐式注入，
   避免参数顺序随使用位置漂移。
-/
