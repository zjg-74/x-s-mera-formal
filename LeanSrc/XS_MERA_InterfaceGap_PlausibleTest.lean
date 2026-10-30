/-!
  XS_MERA_InterfaceGap_PlausibleTest

  A3：基线搜索。检验「拓宽接口像集能否消除通约压力」这一命题在模型中的确切形式。

  对应《完整的界面，残缺的接口》第五节（三）「优化算法」：
  「Model 再准也只是提高已接入维度的估计精度；多模态扩宽的是接口的宽度，不是方向。」
  形式版本要回答的是一个更窄的问题——**把更多实践接入像集，能否消解判断上的冲突**。

  ## 为什么换命题

  `InterfaceGap` 原来的 `Thm_ExpandingImageDoesNotEliminateCommensurationPressure`
  写作：

  ```
  (π' : P → Option X) → (∀ s, Ranπ π s → Ranπ π' s) → Hazard →
    ∃ p : P, JudgementGap π' le_X PreferP
  ```

  结论里的 `JudgementGap` 不含 `π'`，故「拓宽像集」对它没有任何影响：命题既不成立
  （`JudgementGap` 并非对任意 `π'` 都真），也不可证（前件用不上）。这类命题不能靠
  补证明救活，只能换。

  ## 换成什么

  把「通约压力」落在一个**配对**上，而不是落在一个全局的「无提升」断言上：

  - `Conflict`：存在两个都被接入的实践 `p₁ p₂`，专业判断认为 `p₁` 更值得，而结算序
    在它们的指标上恰好相反。这就是第一节那节课的抽象形式。
  - `LiftExists`：存在 `P` 上的全序，既在像集上与 `le_X` 逐点一致，又尊重 `PreferP`。
  - `conflict_blocks_lift`：有冲突 ⇒ 不存在这样的提升。
  - `Thm_ExpansionPreservesConflict`：若 `π'` 只是**扩大像集**而在既有配对上的序不变，
    冲突原样存续。
  - `agreement_blocks_conflict`：若结算序在配对上与专业判断一致，则无冲突。

  三条合起来给出正文那句话的形式对应：**冲突的存亡取决于序，不取决于像集大小**。
  「拓宽」若同时改了序，冲突当然可能消失——这既不是反驳，也正是本文该说清的边界。

  ## 关于 Plausible

  原计划用 Plausible 做随机属性测试。改用穷举基线搜索，理由有二：

  1. 定义域只有两个实践、两个指标位，九种投影 × 两种序 = 十八大类，穷举是**完备**的，
     随机搜索在这个规模上只会更弱（可能漏掉反例）；
  2. 本机无 Lean 工具链，Plausible 的 `Testable` API 未能验证；把未验证的 `#eval`
     写进 `lake build` 的必经路径，等于给审稿人送一个构建失败。

  `import Plausible` 与 `lakefile.lean` 的依赖保留，接入点见文末 `NOTE`。

  ## 编译状态

  依 Lean 4 规则书写，**未在本机编译验证**。可能报错处与替代写法见文末 `NOTE`。
-/
import XS_MERA_InterfaceGap

open XS_MERA
open XS_MERA.InterfaceGap

namespace XS_MERA
namespace ExpansionTest

variable {P X : Type}

/-! ### 冲突与提升 -/

/-- 结算序在配对上与专业判断相反：两实践都被接入，专业判断认为 `p₁` 更值得，
而结算序把 `p₂` 排在 `p₁` 之前（即 `le_X x₂ x₁` 不成立）。 -/
def Conflict (π : P → Option X) (le_X : X → X → Prop) (PreferP : P → P → Prop) : Prop :=
  ∃ (p₁ p₂ : P) (x₁ x₂ : X),
    π p₁ = some x₁ ∧ π p₂ = some x₂ ∧ PreferP p₁ p₂ ∧ ¬ le_X x₂ x₁

/-- 结算序在配对上与专业判断一致：凡专业判断认为 `p₁` 更值得，结算序都同意。 -/
def OrderAgrees (π : P → Option X) (le_X : X → X → Prop) (PreferP : P → P → Prop) : Prop :=
  ∀ (p₁ p₂ : P) (x₁ x₂ : X), π p₁ = some x₁ → π p₂ = some x₂ → PreferP p₁ p₂ → le_X x₂ x₁

/-- 存在一个 `P` 上的全序，它在像集上与 `le_X` 逐点一致，并尊重专业判断。

第三条即「提升」的实质要求：若专业判断认为 `p₁` 更值得，全序必须把 `p₂` 排在
`p₁` 之前（`le_P p₂ p₁`）。缺了这一条，`le_P := fun _ _ => True` 就能满足前两条，
提升永远存在，缺口永远不成立——`InterfaceGap` 的 `JudgementGap` 正是在这一点上
过宽（详见 `NOTE` 第 2 条）。 -/
def LiftExists (π : P → Option X) (le_X : X → X → Prop) (PreferP : P → P → Prop) : Prop :=
  ∃ le_P : P → P → Prop,
    IsTotalOrderOn le_P ∧
      (∀ (p₁ p₂ : P) (x₁ x₂ : X),
        π p₁ = some x₁ → π p₂ = some x₂ → (le_P p₁ p₂ ↔ le_X x₁ x₂)) ∧
      (∀ p₁ p₂ : P, PreferP p₁ p₂ → le_P p₂ p₁)

/-- 冲突阻断提升：只要存在一个序与判断相悖的配对，任何兼容全序都不存在。

证明只用第三条与第一条：兼容性把 `le_P p₂ p₁` 折算成 `le_X x₂ x₁`，尊重判断给出
`le_P p₂ p₁`，两者与 `Conflict` 的 `¬ le_X x₂ x₁` 直撞。不需要经典逻辑。 -/
theorem conflict_blocks_lift (π : P → Option X) (le_X : X → X → Prop)
    (PreferP : P → P → Prop) (h : Conflict π le_X PreferP) :
    ¬ LiftExists π le_X PreferP := by
  intro ⟨le_P, _hord, hagree, hrespect⟩
  obtain ⟨p₁, p₂, x₁, x₂, h₁, h₂, hpref, hnot⟩ := h
  exact hnot ((hagree p₂ p₁ x₂ x₁ h₂ h₁).mp (hrespect p₁ p₂ hpref))

/-- 序一致则无冲突。这是 `conflict_blocks_lift` 的另一面，也是「消除只可能来自改序」
的正面表述。 -/
theorem agreement_blocks_conflict (π : P → Option X) (le_X : X → X → Prop)
    (PreferP : P → P → Prop) (h : OrderAgrees π le_X PreferP) :
    ¬ Conflict π le_X PreferP := by
  intro ⟨p₁, p₂, x₁, x₂, h₁, h₂, hpref, hnot⟩
  exact hnot (h p₁ p₂ x₁ x₂ h₁ h₂ hpref)

/-! ### 拓宽像集 -/

/-- `π'` 是 `π` 的扩张：`π` 接得进来的，`π'` 都接得进来，且落在同一个指标值上。 -/
def ImageExtends (π π' : P → Option X) : Prop :=
  ∀ (p : P) (x : X), π p = some x → π' p = some x

/-- 主命题：只扩大像集、不改动既有配对上的序，冲突原样存续。

这是「拓宽的是接口的宽度，不是接口的方向」的形式版本。注意它的条件是**宽容的**：
允许 `π'` 在旧像集上任意一致，只要求它把旧配对仍映到同一对指标值、且这一对上的
序没被改动。命题不涉及 `Hazard`：高利害与否影响的是冲突的后果，不是冲突的存亡。 -/
theorem Thm_ExpansionPreservesConflict (π π' : P → Option X)
    (le_X le_X' : X → X → Prop) (PreferP : P → P → Prop)
    (hext : ImageExtends π π')
    (hord : ∀ x y : X, (∃ p₁ p₂ : P, π p₁ = some x ∧ π p₂ = some y) → (le_X x y ↔ le_X' x y))
    (h : Conflict π le_X PreferP) :
    Conflict π' le_X' PreferP := by
  obtain ⟨p₁, p₂, x₁, x₂, h₁, h₂, hpref, hnot⟩ := h
  refine ⟨p₁, p₂, x₁, x₂, hext p₁ x₁ h₁, hext p₂ x₂ h₂, hpref, ?_⟩
  intro hcontra
  exact hnot ((hord x₂ x₁ ⟨p₂, p₁, h₂, h₁⟩).mpr hcontra)

/-! ### 三实践的玩具模型

`Practice` 三门课：一节强概念课、一节讨论课、一节根本不在系统视野里的课。
`Signal` 两个指标位：低、高；`leSignal` 是「不高于」，即 `false ≤ true`。 -/

inductive Practice where
  | concept
  | discuss
  | silent

/-- 投影 `π₀`：强概念课落在低指标位，讨论课落在高指标位，第三节课接不进来。 -/
def π₀ : Practice → Option Bool
  | .concept => some false
  | .discuss => some true
  | .silent => none

/-- 投影 `π₁`：扩宽后的接口，第三节课也被接进来了——落在高指标位。 -/
def π₁ : Practice → Option Bool
  | .concept => some false
  | .discuss => some true
  | .silent => some true

/-- 结算序：`false` 不高于任何值，`true` 不高于 `true`。即低指标 < 高指标。 -/
def leSignal : Bool → Bool → Prop
  | false, _ => True
  | true, true => True
  | true, false => False

/-- 专业判断：强概念课比讨论课更值得。 -/
def prefer : Practice → Practice → Prop
  | .concept, .discuss => True
  | _, _ => False

/-- 第一节那节课的抽象形式：强概念课被判在低指标位，讨论课被判在高指标位，
而专业判断认为前者更值得。两者相悖，冲突成立。 -/
theorem toy_conflict : Conflict π₀ leSignal prefer :=
  ⟨.concept, .discuss, false, true, rfl, rfl, trivial, fun h => h⟩

/-- 同一个冲突在扩宽后的接口下原样存续：把第三节课接进来，并不改变前两门课
落在哪个指标位，也不改变这两个指标位之间的序。 -/
theorem toy_conflict_expanded : Conflict π₁ leSignal prefer :=
  ⟨.concept, .discuss, false, true, rfl, rfl, trivial, fun h => h⟩

/-- 因此不存在兼容全序：冲突在，提升就不在。 -/
theorem toy_no_lift : ¬ LiftExists π₀ leSignal prefer :=
  conflict_blocks_lift π₀ leSignal prefer toy_conflict

/-- 扩宽之后仍然不存在兼容全序。 -/
theorem toy_no_lift_expanded : ¬ LiftExists π₁ leSignal prefer :=
  conflict_blocks_lift π₁ leSignal prefer toy_conflict_expanded

/-! ### 穷举基线搜索

两个实践、两个指标位，每门课有三种可能（不可见 / 低 / 高），共九种投影；
两种序（原序、反向序）。穷举全部十八大类，打印冲突取值。

要看的不是「有没有冲突」，而是两件事：其一，冲突只在两门课**都被接入**且**序相反**时
才为真；其二，把 `silent` 一类实践接进来（像集从两个值扩到两个值+一个已存在的值），
冲突取值不变——扩宽像集不改变既有配对上的判决。 -/

/-- 计算版冲突判据：`true` 表示该投影与序下存在冲突配对（concept, discuss）。 -/
def conflictB (π : Bool → Option Bool) (le : Bool → Bool → Bool) : Bool :=
  match π true, π false with
  | some x₁, some x₂ => not (le x₂ x₁)
  | _, _ => false

/-- 计算版原序：低指标不高于高指标。 -/
def leB : Bool → Bool → Bool
  | false, _ => true
  | true, true => true
  | true, false => false

/-- 计算版反向序：高指标不高于低指标（即结算把低分排在前面）。 -/
def leB' : Bool → Bool → Bool
  | true, _ => true
  | false, false => true
  | false, true => false

def options : List (Option Bool) := [none, some false, some true]

def scan : IO Unit := do
  IO.println "A3 基线搜索：两个实践 × 两个指标位，穷举九种投影 × 两种结算序"
  IO.println "concept →   discuss →   原序冲突  反向序冲突"
  for o₁ in options do
    for o₂ in options do
      let π : Bool → Option Bool := fun b => if b then o₁ else o₂
      IO.println s!"{o₁}       {o₂}        {conflictB π leB}      {conflictB π leB'}"

def main : IO Unit := scan

end ExpansionTest
end XS_MERA

/-!
## NOTE（未编译）

### 1. 相对原命题的改动

`InterfaceGap.Thm_ExpandingImageDoesNotEliminateCommensurationPressure` 已删除（它含
`sorry`，且结论不含 `π'`，属结构错误）。替代物是本文件的
`Thm_ExpansionPreservesConflict`，两者差别有三：

| | 原命题 | 现命题 |
|---|---|---|
| 结论 | `∃ p, JudgementGap π' le_X PreferP` | `Conflict π' le_X' PreferP` |
| 与 `π'` 的关系 | 无（结论不含 `π'`） | 有（冲突的见证经 `hext` 搬到 `π'`） |
| 前件 | `Hazard` | `ImageExtends` + 序在旧配对上不变 |

`Hazard` 被移出：它决定冲突的**后果**（是否进入问责），不决定冲突的**存亡**。
把 `Hazard` 写进这条定理，是原命题第二处概念错位。

### 2. `JudgementGap` 的问题（未改，留待你决定）

`JudgementGap` 要求「不存在全序 `le_P` 使 `le_P p₁ p₂ ↔ le_X x₁ x₂`」。这个要求里没有
`PreferP`，于是只要 `le_X` 是全序，`le_P := fun _ _ => True` 在很多配置下就满足它——
判断缺口的成立与否，取决于投影是否多对一这类细节，而不取决于「情境判断无位置」。
本文件的 `LiftExists` 加了第三条（尊重 `PreferP`），才使「提升不可能」与「判断相悖」
等价。是否把 `JudgementGap` 改成这个版本，需要你定：改了更准，但与第四节行文里
「判断缺口」的直觉描述要重新对一遍。

### 3. 五处可能在 `lake build` 时报错的地方

1. `conflict_blocks_lift` 的 `obtain`：若 `Conflict` 的嵌套 `∃` 展开顺序不符，
   改为逐层 `rintro ⟨p₁, p₂, x₁, x₂, h₁, h₂, hpref, hnot⟩`。
2. `IsTotalOrderOn` 是 `A ∧ B ∧ C` 的右结合形式，`intro ⟨le_P, _hord, hagree, hrespect⟩`
   若绑定数不匹配，改为 `intro ⟨le_P, hord, hagree, hrespect⟩` 并去掉下划线。
3. `toy_conflict` 的末项 `fun h => h` 依赖 `leSignal true false` 归约为 `False`；
   若 `def` 的匹配未被编译器按构造子归约，改为 `by unfold leSignal; exact id`。
4. `scan` 里 `s!"{o₁}"` 需要 `ToString (Option Bool)`；若不成立，改用 `repr`。
5. `Practice` 未 `deriving DecidableEq`，本文件也不使用其可判定性；若 `lake build`
   报缺失实例，加 `deriving DecidableEq` 即可。

### 4. Plausible 接入点

若要恢复随机属性测试，在文件末尾加（API 未验证，取消注释前先单独 `lake env lean` 试）：

```
-- import Plausible
-- open Plausible
-- #eval Testable.check (fun (n : Nat) => n + 0 = n)
```

由于本文件的性质都带函数类型参数（`π : P → Option X`），随机采样需要为函数空间写
`Sampleable` 实例，成本高于收益；穷举在九种投影上是完备的，建议保持现状。
-/
