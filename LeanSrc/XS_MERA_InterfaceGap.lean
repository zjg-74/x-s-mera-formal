/-!
  XS_MERA_InterfaceGap

  接口缺口基础模块：`π`、`InImage`、三重缺口、两层裁剪、`DemandPreformatted`、
  `ReactiveAction`、三重脆弱，以及 AX1–AX4（AX3 取弱式）。
  对应论文《完整的界面，残缺的接口》第四节核心概念。依赖 `XS_MERA_Core`。

  ## 编译状态

  依 Lean 4 规则做过类型修订，**未在本机编译验证**。改动见文件末尾 `NOTE`。

  ## 两处须先知道的模型问题

  1. `AX1`、`AX2`、`AX4` 三条按现定义即真，若一并以 `axiom` 声明，则公理系统实际只
     约束了 `AX3` 一条。此处 `AX4` 已证明为 `theorem`（`fun h => h.1`），`AX1` 保留
     `axiom` 形式但在注释中标明其为 definitional，`AX2` 保留 `axiom` 并注明它空转——
     真正的约束需要另行表述（见 `NOTE` 第 9 条）。
  2. `ReactiveAction` 与 `InterfaceCut` 按现定义外延相同，且都蕴含 `π p = none`；
     而 `rewardHack` 要求 `π p ≠ none`。两条在可见性上直接互斥，于是 `AX3` 恒真，
     弱版与 `AX3*` 的区分在模型中落空。这是需要决策的模型缺陷，不是笔误（见 `NOTE` 第 7、8 条）。
-/
import XS_MERA_Core

open XS_MERA

namespace XS_MERA
namespace InterfaceGap

/-! ### 基础域

`P` 原初实践空间（论文 D）；`X` 可结算信号域（论文 d）；
`π` 接口投影本身，`none` 表示投影失败、落入余量；
`Hazard` 高利害标记，区分纯观测与问责结算环路；
`D_inst` 制度明文划定的考核集合（制度裁剪）。 -/
variable {P X : Type}
variable (π : P → Option X)
variable (Hazard : Prop)
variable (D_inst : P → Prop)
variable (SlowValue : P → Prop)
variable (le_X : X → X → Prop)
variable (PreferP : P → P → Prop)
variable (AgentPref : P → Prop)
variable {R : Type} [LT R]
variable (Reward : X → R)
variable (canAttribute : X → Prop)
variable (accumulate : List P → P → Prop)
variable (transfer : P → P → Prop)

/-! ### 基础谓词 -/

/-- 已接入像集：`p` 被接口成功投影。 -/
def InImage (π : P → Option X) (p : P) : Prop := π p ≠ none

/-- `π` 的值域，作为 `X` 上的谓词（免 Mathlib 的 `Set`）。 -/
def Ranπ (π : P → Option X) (s : X) : Prop := ∃ p : P, π p = some s

/-! ### 三重接口缺口 -/

/-- 表征缺口：存在完全无法被接入的实践。 -/
def RepresentationalGap (π : P → Option X) : Prop := ∃ p : P, π p = none

/-- 时间缺口：存在具延迟涌现价值的实践，且它当前不可被接入。 -/
def TemporalGap (π : P → Option X) (SlowValue : P → Prop) : Prop :=
  ∃ p : P, SlowValue p ∧ π p = none

/-- 关系 `r` 是 `α` 上的全序（自反、传递、完全）。不用 Mathlib 的 `IsTotalOrder`：
后者是 `Type` 层 class，不能出现在 `Prop` 的合取式中。 -/
def IsTotalOrderOn {α : Type} (r : α → α → Prop) : Prop :=
  (∀ a, r a a) ∧ (∀ a b c, r a b → r b c → r a c) ∧ (∀ a b, r a b ∨ r b a)

/-- 判断缺口：`X` 上已有全序，但它无法沿 `π` 提升为 `P` 上的全序——
即面向指标的可比较性，不能升格为面向实践的可比较性。 -/
def JudgementGap (π : P → Option X) (le_X : X → X → Prop) (PreferP : P → P → Prop) : Prop :=
  IsTotalOrderOn le_X ∧
    ¬ ∃ le_P : P → P → Prop,
        IsTotalOrderOn le_P ∧
          ∀ p₁ p₂ : P, π p₁ ≠ none → π p₂ ≠ none →
            (le_P p₁ p₂ ↔ ∃ (x₁ x₂ : X), π p₁ = some x₁ ∧ π p₂ = some x₂ ∧ le_X x₁ x₂)

/-! ### 两层裁剪 -/

/-- 制度裁剪：`p` 落在制度明文划定的考核范围内。 -/
def InstitutionalCut (D_inst : P → Prop) (p : P) : Prop := D_inst p

/-- 接口裁剪：落在考核范围内，却没被接口接入。 -/
def InterfaceCut (D_inst : P → Prop) (π : P → Option X) (p : P) : Prop :=
  D_inst p ∧ π p = none

/-! ### 反应性行动与三重脆弱 -/

/-- 反应性行动：既未被接口接入，又落在考核范围内——必须在考核要求与系统不可见
之间的缝隙里维持存在。 -/
def ReactiveAction (π : P → Option X) (D_inst : P → Prop) (p : P) : Prop :=
  ¬ InImage π p ∧ InstitutionalCut D_inst p

/-- 不可归因：不存在可归因的观测信号。 -/
def NonAttributable (π : P → Option X) (canAttribute : X → Prop) (p : P) : Prop :=
  ¬ ∃ s : X, π p = some s ∧ canAttribute s

/-- 不可累积：不能被并入任何历史序列。 -/
def NonCumulable (accumulate : List P → P → Prop) (p : P) : Prop :=
  ¬ ∃ hist : List P, accumulate hist p

/-- 不可传递：不能作为先例传给其他实践。 -/
def NonTransmissible (transfer : P → P → Prop) (p : P) : Prop :=
  ¬ ∃ q : P, transfer p q

/-- 三重脆弱：反应性行动的三个缺陷同时成立，因而只能临时存续。

来稿把三个子谓词写成 `where` 子句内的辅助定义。`where` 中的声明不能可靠捕获
文件级变量，故此处提升为顶层定义。 -/
def FragileReactive (π : P → Option X) (D_inst : P → Prop)
    (canAttribute : X → Prop) (accumulate : List P → P → Prop)
    (transfer : P → P → Prop) (p : P) : Prop :=
  ReactiveAction π D_inst p ∧
    NonAttributable π canAttribute p ∧
    NonCumulable accumulate p ∧
    NonTransmissible transfer p

/-! ### 需求预格式化 -/

/-- 需求预格式化：在高利害条件下，表征缺口存在，而行动者的偏好已全部收缩进接口像集。
三者合起来正是「需求风干」的形式表述——不是实践消失，而是偏好不再指向它。

`D_inst` 未进入本定义：预格式化只涉及 `Hazard`、缺口与偏好三者。 -/
def DemandPreformatted (π : P → Option X) (Hazard : Prop) (AgentPref : P → Prop) : Prop :=
  Hazard ∧ RepresentationalGap π ∧ (∀ p : P, AgentPref p → InImage π p)

/-! ### 桥接公理 A1–A4（弱 AX3） -/
namespace Axioms

/-- AX1：`π p = none` 等价于不在像集。

这**不是实质假设**，只是 `InImage` 定义的改写（`¬(π p ≠ none)` 与 `π p = none`
在经典逻辑下等价）。保留 `axiom` 形式是原稿写法：改成 `theorem` 需要一个经典逻辑
引理，而本仓库不引入 Mathlib，无法确认该引理在核心库中可用。列在公理清单里时，
应注明它是 definitional，不是模型承诺。 -/
axiom AX1_InterfaceIsProjection (π : P → Option X) (p : P) :
    (π p = none ↔ ¬ InImage π p)

/-- AX2：预格式化必以 `Hazard` 为前提。

**这条现无信息量**：`DemandPreformatted` 的定义里已含 `Hazard` 合取项，故前件真则
后件真，属 `fun h => h.1`。要成为实质约束，应改为「无 `Hazard` 时偏好不向像集收缩」
这类独立断言，并去掉定义中的 `Hazard` 合取项。 -/
axiom AX2_PreformattedNeedsHazard (π : P → Option X) (Hazard : Prop) (AgentPref : P → Prop) :
    DemandPreformatted π Hazard AgentPref → Hazard

/-- AX3（弱版，正文默认）：反应性行动与直接奖励劫持互斥。

**注意**：按现定义，`ReactiveAction p` 蕴含 `π p = none`，而 `rewardHack` 要求
`π p ≠ none`，故本条在模型中恒真，不能作为区分弱/强版本的支点。 -/
axiom AX3_ReactiveNotHack (π : P → Option X) (D_inst : P → Prop)
    (Reward : X → R) (PreferP : P → P → Prop) (p : P) :
    ReactiveAction π D_inst p → ¬ rewardHack p π Reward PreferP

/-- AX4：接口裁剪蕴含制度裁剪。按定义即真（`InterfaceCut` 的合取首项就是 `D_inst p`），
现改为 `theorem`。若要让 AX4 成为实质断言，`InterfaceCut` 不应把 `D_inst` 写进定义。 -/
theorem AX4_CutIsSuperposition (D_inst : P → Prop) (π : P → Option X) (p : P) :
    InterfaceCut D_inst π p → InstitutionalCut D_inst p :=
  fun h => h.1

end Axioms

/-! ### 压力测试目标命题（已移出）

此处原有 `Thm_ExpandingImageDoesNotEliminateCommensurationPressure`，含 `sorry`，且
结论 `∃ p, JudgementGap π' le_X PreferP` 不含 `π'`——「拓宽像集」对结论没有任何影响，
命题既不成立也不可证。

该命题已删除，替代物见 `XS_MERA_InterfaceGap_PlausibleTest`：`Conflict`（配对上的
序与判断相悖）+ `Thm_ExpansionPreservesConflict`（只扩像集、不改序，冲突存续）。
不在此处保留一个带 `sorry` 的旧命题，是因为公开仓库里的 `sorry` 等于宣称已证。 -/

end InterfaceGap
end XS_MERA

/-!
## NOTE（相对来稿的改动与遗留问题）

### 类型层（不改变主张）

1. `Set P` → `P → Prop`，`p ∈ D_inst` → `D_inst p`，`Ranπ` 改为 `X` 上的谓词：
   `Set` 属 Mathlib，核心库没有，为免构建依赖过重一并去掉。
2. `IsTotalOrder le_X` → 自定义 `IsTotalOrderOn`：Mathlib 的 `IsTotalOrder` 是
   `Type` 层 class，不能出现在 `Prop` 的合取式中。
3. `π p₁ < π p₂` → `∃ x₁ x₂, π p₁ = some x₁ ∧ π p₂ = some x₂ ∧ le_X x₁ x₂`：
   `Option X` 上没有 `<`，不可能原样比较。
4. `DemandPreformatted` 去掉 `D_inst` 形参：其定义体不涉及 `D_inst`，原调用多处
   实参个数与定义不符，是硬错误。
5. `FragileReactive` 的 `where` 子谓词提升为顶层定义。
6. 各 `def` 给出完整显式参数表，避免文件级 `variable` 的参数顺序随使用位置漂移
   （原稿 `ReactiveAction π D_inst p` 一类调用即受此影响）。

### 语义层（需要你决策，我没有自行改）

7. **`ReactiveAction` 与 `InterfaceCut` 外延重合**：前者 = `¬InImage ∧ D_inst`，
   后者 = `D_inst ∧ π p = none`，两者等价。且都蕴含 `π p = none`，与 `rewardHack`
   要求的 `π p ≠ none` 直接矛盾，`AX3` 因而恒真。
8. **弱 AX3 与 `AX3*` 的区分在模型中落空**：`pGrey`（间接劫持）若要成为弱 AX3 的
   见证，必须满足 `ReactiveAction` 且被接入；按现定义不可能。两条出路：
   (a) 放宽 `ReactiveAction`，允许「被接入但被降格表征」（`π p = some x` 而 `x`
       丢失了该实践的关键维度）——这与论文「余量」的直觉一致；
   (b) 另立 `rewardHackIndirect`，作用于潜在状态而非观测域，并让 `ReactiveAction`
       不预设不可见。
9. **`AX1`–`AX4` 实际只约束了一条**：`AX1`、`AX4` 已是 definitional truth，`AX2`
   因定义含 `Hazard` 而空转。想让公理系统有内容，`AX2` 需独立表述，且 `InterfaceCut`
   不应把制度条件写进自身定义。
10. **`Thm_…` 的前件与结论不相关**（该定理已删除）：`JudgementGap` 不含 `π'`，故「拓宽像集」对结论
    无影响。合理重述应把缺口锚定在 `π'` 上，例如断言「存在 `p`，`PreferP` 与
    `π'` 排序不一致，且该 `p` 在 `π` 下亦不可见」——这才检验「拓宽不能消除」。
    重述版已落到 `XS_MERA_InterfaceGap_PlausibleTest` 的 `Conflict` / `LiftExists` /
    `Thm_ExpansionPreservesConflict`，本文件不再保留旧式。
-/
