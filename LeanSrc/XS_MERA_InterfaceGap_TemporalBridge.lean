import Std
import XS_MERA_InterfaceGap

/-!
  XS_MERA_InterfaceGap_TemporalBridge

  A2：B2 时序桥。把静态接口 `π : P → Option X` 时序化为 `πt : Nat → P → Option X`，
  给出 TB1–TB3 三条时序假设，并导出正文第五节（二）需要的四条推论。

  对应《完整的界面，残缺的接口》第五节：

  - 「系统的采样是即时的、高频的」             → TB1（切片性，`SliceRepresentable`）
  - 「把『此刻还没显现』直接读作『没有发生』」   → TB1 + 判定规则（`ObservableAt`）
  - 「慢生长的实践在评价框架中不被计入」        → TB2（慢价值潜伏，`SlowValueLatent`）
  - 「采样越密，第四周就被标记为低效」          → TB2 推论 + TB3（判定即刻入记录）
  - 「长期评价异化」「稳态负荷」               → TB3 + 积压不减

  ## 设计选择：TB1–TB3 不写成 `axiom`

  `XS_MERA_Core` 的 `GAPS_axioms : True` 是空公理；`InterfaceGap` 的 `AX1`、`AX4`
  按定义即真。两者都会让「公理系统」在审稿人眼里失去分量。本模块改用
  **假设束**：`SliceRepresentable`、`SlowValueLatent`、`InstantVerdictRecorded`
  三个 `Prop` 谓词，每条定理显式接收它用到的那一束。好处是读者能看见结论依赖哪一条，
  也能看见拿掉哪一条结论就塌——这比 `axiom` 更经得起「公理是否特设」这一问。

  ## 编译状态

  依 Lean 4 规则书写，**未在本机编译验证**（本机无 Lean 工具链）。已知风险点见文末 `NOTE`。
-/

open XS_MERA
open XS_MERA.InterfaceGap

namespace XS_MERA
namespace TemporalBridge

/-! ### 时序化接口

静态模块里 `π : P → Option X` 一次定终身；现实中结算按期发生，每期看到的切片不同。
本层只加一个时间参数，不改 `InterfaceGap` 的任何定义。 -/

variable {P X S : Type}

/-- 第 `t` 期结算时，实践 `p` 被投影到的可观测信号；`none` 表示当期不可见。 -/
def ObservableAt (πt : Nat → P → Option X) (t : Nat) (p : P) : Prop := πt t p ≠ none

/-- 当期的表征缺口：`InterfaceGap.TemporalGap` 的时序版。 -/
def TemporalGapAt (πt : Nat → P → Option X) (SlowValue : P → Prop) (t : Nat) : Prop :=
  ∃ p : P, SlowValue p ∧ ¬ ObservableAt πt t p

/-- 延迟可结算：存在某一期，`p` 被接入。 -/
def DelayedSettleable (πt : Nat → P → Option X) (p : P) : Prop :=
  ∃ t : Nat, ObservableAt πt t p

/-- 永久不可结算：任何一期都不被接入。 -/
def NeverSettleable (πt : Nat → P → Option X) (p : P) : Prop :=
  ∀ t : Nat, ¬ ObservableAt πt t p

/-! ### TB1：切片性

「采样是即时的」在模型里不是形容词，而是一条结构条件：第 `t` 期的投影只取决于
第 `t` 期的状态切片，不携带任何关于 `t` 之后的信息。 -/

/-- TB1（切片性）：`πt` 由切片观测函数 `πs` 与状态轨迹 `σ` 复合而成，
即 `πt t = πs (σ t)`。这是对「系统只采样当下」这一设计事实的模型化，不是可证命题。 -/
def SliceRepresentable (πt : Nat → P → Option X) (πs : S → P → Option X) (σ : Nat → S) : Prop :=
  ∀ (t : Nat) (p : P), πt t p = πs (σ t) p

/-- 由 TB1 导出：两段轨迹在 `t` 期切片相同，则当期判定必相同。

这是「把此刻还没显现读作没有发生」的形式来源：结算看不见未来，不是因为它判断未来
不会发生，而是因为它的输入里根本没有未来这一项。 -/
theorem Thm_SliceBlindToFuture {πt πt' : Nat → P → Option X} {πs : S → P → Option X}
    {σ σ' : Nat → S} (h : SliceRepresentable πt πs σ) (h' : SliceRepresentable πt' πs σ')
    (t : Nat) (ht : σ t = σ' t) (p : P) :
    ObservableAt πt t p ↔ ObservableAt πt' t p := by
  unfold ObservableAt
  rw [h t p, h' t p, ht]

/-! ### TB2：慢价值潜伏

延迟涌现的价值在窗口 `[0, H)` 内不可观测，其估值只落在潜在状态 `LatentState` 上。
第二条合取项与 `XS_MERA_Core` 的 `LatentState` 对接：慢价值不是「尚未采集的信号」，
而是「本就不在信号域里的量」。 -/

/-- TB2（慢价值潜伏）：

1. 窗口内不可观测——慢价值有显现下界 `H`；
2. 估值位置——慢价值只落在潜在状态上，不进入 `π` 的像。 -/
def SlowValueLatent (πt : Nat → P → Option X) (SlowValue : P → Prop) (H : P → Nat)
    (LatentState : S → Prop) (stateOf : P → S) : Prop :=
  (∀ (p : P), SlowValue p → ∀ t : Nat, t < H p → ¬ ObservableAt πt t p) ∧
    (∀ (p : P), SlowValue p → LatentState (stateOf p))

/-- 窗口内任何一次结算都判定为「未显现」。TB2 第一条的直接展开，不含新信息——
列出来是为了让正文引用时有一个可指的名字。 -/
theorem Thm_WindowVerdictIsAbsent (πt : Nat → P → Option X) (SlowValue : P → Prop)
    (H : P → Nat) (LatentState : S → Prop) (stateOf : P → S)
    (hTB2 : SlowValueLatent πt SlowValue H LatentState stateOf)
    (p : P) (hp : SlowValue p) (t : Nat) (ht : t < H p) :
    ¬ ObservableAt πt t p :=
  hTB2.1 p hp t ht

/-- 采样加密不产生信号：只要结算时刻都落在窗口内，判定一律为「未显现」，与采样密度无关。

这是第五节「采样越密，第四周就被标记为低效」的**前半句**：密度不改变判定内容，
只改变判定出现的次数与时刻。后半句（「更早」）需要 TB3，见下。 -/
theorem Thm_DensityYieldsNoSignal (πt : Nat → P → Option X) (SlowValue : P → Prop)
    (H : P → Nat) (LatentState : S → Prop) (stateOf : P → S)
    (hTB2 : SlowValueLatent πt SlowValue H LatentState stateOf)
    (p : P) (hp : SlowValue p) (σ : Nat → Nat) (hσ : ∀ k : Nat, σ k < H p) :
    ∀ k : Nat, ¬ ObservableAt πt (σ k) p :=
  fun k => Thm_WindowVerdictIsAbsent πt SlowValue H LatentState stateOf hTB2 p hp (σ k) (hσ k)

/-! ### TB3：即时结算与记录不撤销

前两条只说明「当期看不见」。要把「当期看不见」推到「长期评价异化」，还缺一条制度假设：
判定按当期作出，且一旦进入记录便不被后续证据改写。 -/

/-- TB3（即时结算与记录）：`Record t p` 读作「`t` 期记录里，`p` 被记为未显现」。

1. 记录与当期判定一致——记录不引入额外信息，只是把当期结论固定下来；
2. 记录不撤销——`t` 期的判定在此后任何一期仍在。

**第 2 条是治理假设，不是技术事实。** 若结算周期延长、或记录允许事后修订，本条不成立，
时间缺口随之缩小。审稿人若问「何以见得判决不会被修正」，答案在此条，而不在 `π` 的定义里。 -/
def InstantVerdictRecorded (πt : Nat → P → Option X) (Record : Nat → P → Prop) : Prop :=
  (∀ (t : Nat) (p : P), Record t p → ¬ ObservableAt πt t p) ∧
    (∀ (t s : Nat) (p : P), Record t p → t ≤ s → Record s p)

/-- 记录不撤销：`t` 期的判定在此后任何一期仍在记录中。

「长期评价异化」的形式对应——一次早期误判不是一次可以淡出的误差，而是一条不会被撤回的
记载。注意它只断言记录存续，不判断记录所指的事实是否改变。 -/
theorem Thm_RecordPersists (πt : Nat → P → Option X) (Record : Nat → P → Prop)
    (hTB3 : InstantVerdictRecorded πt Record) (t s : Nat) (p : P)
    (h : Record t p) (hts : t ≤ s) :
    Record s p :=
  hTB3.2 t s p h hts

/-! ### 积压与稳态负荷

「稳态负荷」在模型里能得到的全部内容是：接口不自我更新时，积压不会自愈。
它**不主张**积压单调增加——增加还需要「每期都有新实践落进考核范围」这一外部条件，
本模块不假设这个条件。 -/

/-- 积压：`t` 期落在考核范围内、却未被接入的实践。 -/
def BacklogAt (πt : Nat → P → Option X) (D_inst : P → Prop) (t : Nat) (p : P) : Prop :=
  D_inst p ∧ ¬ ObservableAt πt t p

/-- 接口冻结：各期结算用同一套接口，`πt` 不随时间改变。 -/
def InterfaceFrozen (πt : Nat → P → Option X) : Prop :=
  ∀ (t s : Nat) (p : P), πt t p = πt s p

/-- 稳态负荷：接口冻结时，积压不随时间自愈——`t` 期积压的实践，`s ≥ t` 期仍在积压。 -/
theorem Thm_BacklogDoesNotSelfHeal (πt : Nat → P → Option X) (D_inst : P → Prop)
    (hf : InterfaceFrozen πt) (t s : Nat) (_hts : t ≤ s) (p : P)
    (h : BacklogAt πt D_inst t p) :
    BacklogAt πt D_inst s p :=
  ⟨h.1, by
    unfold ObservableAt
    rw [hf s t p]
    exact h.2⟩

/-! ### 反例模型：当下不可观测 ⇏ 永久不可结算

这是本模块最该被正文引用的一条边界。第二节与第五节的措辞若由「当期看不见」滑向
「结构上无法结算」，就从可辩护的诊断变成了过度断言。下例给出一个 `t = 0` 不可见、
`t = 1` 可见的实践，故两者不等价。 -/
namespace CounterModel

/-- 两期玩具模型：`t = 0` 切片为空，`t = 1` 起全部可见。 -/
def πTwo (t : Nat) (p : Bool) : Option Bool :=
  if t = 0 then none else some p

/-- `t = 0` 时不可观测。 -/
theorem two_notObservable_zero : ¬ ObservableAt πTwo 0 true := by
  unfold ObservableAt πTwo
  rw [ite_eq_left rfl]
  exact fun h => h rfl

/-- 但 `t = 1` 时可观测：延迟，而非永久缺席。 -/
theorem two_observable_one : ObservableAt πTwo 1 true := by
  unfold ObservableAt πTwo
  rw [ite_eq_right (by decide : ¬ (1 : Nat) = 0)]
  exact fun h => by cases h

/-- 由「当期不可观测」推「永久不可结算」是无效推理。 -/
theorem not_observable_implies_not_never :
    ¬ (∀ (πt : Nat → Bool → Option Bool) (p : Bool),
        ¬ ObservableAt πt 0 p → NeverSettleable πt p) := by
  intro h
  have hnever : NeverSettleable πTwo true := h πTwo true two_notObservable_zero
  exact hnever 1 two_observable_one

end CounterModel

end TemporalBridge
end XS_MERA

/-!
## NOTE（未编译，供校对与后续修订）

### 依赖顺序

本文件 `import XS_MERA_InterfaceGap`，只复用其命名空间与 `D_inst` 的用法，
不修改任何静态定义。`AX1–AX4` 在此不出现：时序层不重新引入公理，只引入假设束。

### 五处可能在 `lake build` 时报错的地方

1. `Thm_SliceBlindToFuture` 的 `rw [h t p, h' t p, ht]`：若 `rw` 在 `ObservableAt`
   未展开时找不到 `πt t p`，改为先 `unfold ObservableAt at *` 再 `rw`。
2. `Thm_BacklogDoesNotSelfHeal`：证明项里先 `unfold ObservableAt` 再 `rw`，
   最后 `exact h.2` 依赖 `h.2` 与展开后的目标定义等价。若失败，改用
   `⟨h.1, by simpa [ObservableAt, hf s t p] using h.2⟩`。
3. `two_observable_one`：`if_neg (by decide : ¬ (1 : Nat) = 0)` 依赖 `Nat.decEq` 可归约；
   若 `decide` 不通过，改为 `if_neg (Nat.succ_ne_zero 0)`。
4. 末尾 `exact fun h => by cases h` 处理 `some true = none`；若 `cases` 在此不接受，
   改为 `Option.noConfusion h`。
5. `namespace CounterModel` 内 `πTwo` 使用 `if t = 0`，需要 `Decidable (t = 0)`，
   由 `Nat.decEq` 自动提供，无需 `open Classical`。

### 三条不是定理的东西（正文不得据此加码）

1. 「密度导致误判」不是本模块的结论。`Thm_DensityYieldsNoSignal` 只说密度不产生信号；
   「更早被标记」需要 TB3 的第 2 条（记录不撤销）+ 结算点提前，属制度假设的推论，
   不是技术必然。
2. 「积压单调增加」不是本模块的结论。`Thm_BacklogDoesNotSelfHeal` 只说冻结接口下不减。
   要说「负荷上升」，还须补「每期都有新实践进入考核范围」的外部条件，本模块未假设。
3. 「时间缺口不可修复」不是本模块的结论。TB3 是治理假设：延长结算周期、允许记录修订，
   缺口即缩小。这既是本文的软肋，也是本文可证伪性的来源，正文第六节「其五」应与之呼应。

### 与附录的对齐

`XS_MERA_Appendix_AxiomRisk.lean` 已列 TB1（只采样初始切片）、TB2（慢价值估值在
`LatentState`）、TB3（高利害强制即时汇总）。本文件把三条落到
`SliceRepresentable` / `SlowValueLatent` / `InstantVerdictRecorded`，附录中的 TB3 风险注记
（「治理假设，非技术」）与 `InstantVerdictRecorded` 第 2 条一致，可直接互引。
-/
