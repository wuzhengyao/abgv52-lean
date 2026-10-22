/-
  Procesi —— **D5：`H = C₃×C₃` 形**（把 `(C)` 层从 `S_9` 换成 `H`）

  **为什么需要本件（口径核查，第 71 轮）**：`S9 = G.Gp p = Equiv.Perm (Fin (p*p))` 是 `S_9`
  （阶 362880），而 `P.Hp p = Cp p × Cp p` 是 `H = C₃×C₃`（阶 9）——**两个不同的群**。
  `Procesi/SaltmanT.lean` §17–§37 机检的是 **`S_9` 形**（`ProcesiS9Hyp`，右端
  `invariantsField F = EM.latticeInvariantsAlg F S9 Lat`），而论文 `rem:procesi-geometric`
  与 `Procesi/Main.lean` 的 `zH_rational_of_procesi` **消费 `H` 形**
  （`ProcesiSubgroupHyp F (P.Hp 3) Lat`，右端 `EM.latticeInvariantsAlg F (P.Hp 3) Lat`）。

  **两者不等价**：`Z_H` 是 `UD(F,9,H)` 的中心、`Z_{S_9}` 是 `UD(F,9,S_9)` 的中心，
  是两个不同中心单代数的中心；且 `F(Lat)^H ⊋ F(Lat)^{S_9}`（`S_9`-固定 ⟹ `H`-固定）。
  故 **`S_9` 形不蕴含 `H` 形**；论文的「taking `H`-invariants」是**同一已发表定理
  （Procesi 对群 `H`）的另一次实例**，不是从 `S_9` 形推出的逻辑后果。

  **本件的做法**：把 `(C)` 层＋格桥＋`≃ₐ[F]`＋交付定理从 `S_9` **换成 `H` 重做**。
  可行（且几乎逐字）的原因：`SaltmanT` 的证明只用到三件，三件都与群无关或可限制——
  ① `F(M_2')^T = F(M_2)`（§22 `latticeFunctionFieldKerToK_range`，**与群无关**）；
  ② `KerToK`／`KerEquiv` 的等变方块（§31／§32，对 `S_9` 的 `σ`）——对 `H` 只需
     `σ := iotaH h`（`iotaH := G.thetaH 3 : P.Hp 3 →* G.Gp 3`，库内已有的正则嵌入）；
  ③ 成员刻画（`EM.mem_latticeInvariantsAlg_iff`，`Iff` 级）。
  关键等式：`K^{T∧H} = K^T ∩ K^H = F(M_2) ∩ K^H = F(M_2)^H`（末一等号用「`H` 在
  `F(M_2)` 上的作用是 `K` 上作用的限制」，本件由 `rfl` 级的
  `smul_Hp_eq_iotaH` 承当）。

  **射程（勿夸大）**：本件机检的是 `H` 形的 **(C) 层 ＋ 类型层 `≃ₐ[F]` ＋ 交付定理**；
  `H` 版的 `(A)(B)`（`thm:14.16`／`prop:14.19` 对群 `H`，即 Procesi 定理对 `H` 的实例）
  是**唯一具名假设** `SaltmanCenterEqHNFixed`，**研究级，未证**。
  它与 `S_9` 版的 `SaltmanCenterEqNFixed` **并列**，不是它的推论。
-/
import Procesi.SaltmanT
import Procesi.Main
import Procesi.Alg

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

/-! ## §1 `H`-侧的定义：正则嵌入、`H`-不变、`K^{N_H}` 作为子代数 -/

/-- 正则嵌入 `ι : H = C₃×C₃ ↪ S_9`（库内既有：`G.thetaH`）。

**用途**：把 `S_9`-作用**限制**到 `H`；`Mp2` 上的 `H`-作用正是沿它定义的
（`ABGV52.ProcHyp` 的 `instSMulHpMp2`：`h • x = G.thetaH p h • x`）。 -/
def iotaH : P.Hp 3 →* G.Gp 3 := G.thetaH 3

/-- `H`-不变量域（`H = C₃×C₃`）：`F((M⊕U)|_H)^H`，即 `ProcesiSubgroupHyp` 的右端。 -/
abbrev HInv (F : Type) [Field F] : Subalgebra F (EM.latticeFunctionField F (ProcLat.Mp2 3)) :=
  EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)

/-- `H`-作用就是 `S_9`-作用沿 `ι` 的拉回（`rfl` 级，实例层已如此定义）。 -/
lemma smul_Hp_eq_iotaH (F : Type) [Field F] (h : P.Hp 3)
    (β : EM.latticeFunctionField F (ProcLat.Mp2 3)) :
    h • β = iotaH h • β := rfl

/-- `H`-不变（分式域层，`H = C₃×C₃`）：与 `TFixed`／`SFixed` 平行。 -/
def HFixed (F : Type) [Field F] (α : EM.latticeFunctionField F Mprime) : Prop :=
  ∀ h : P.Hp 3, permScaleFieldEquiv F (iotaH h) α = α

/-- 纯量被 `H` 固定（由 §36 的 `SFixed_algebraMap` 直接实例化）。 -/
lemma HFixed_algebraMap (F : Type) [Field F] (r : F) :
    HFixed F (algebraMap F (EM.latticeFunctionField F Mprime) r) :=
  fun h => SFixed_algebraMap F r (iotaH h)

/-- ★ **`K^{N_H} = {α | TFixed α ∧ HFixed α}` 作为 `K` 的 `Subalgebra`**（`H` 版 §36 步骤 A）。 -/
noncomputable def NFixedAlgH (F : Type) [Field F] [CharZero F] :
    Subalgebra F (EM.latticeFunctionField F Mprime) where
  carrier := {α | TFixed F α ∧ HFixed F α}
  zero_mem' := by
    refine ⟨fun b => ?_, fun h => ?_⟩ <;> rw [map_zero]
  one_mem' := by
    refine ⟨fun b => ?_, fun h => ?_⟩ <;> rw [map_one]
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun t => by rw [map_add, ha1 t, hb1 t], fun h => by rw [map_add, ha2 h, hb2 h]⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun t => by rw [map_mul, ha1 t, hb1 t], fun h => by rw [map_mul, ha2 h, hb2 h]⟩
  algebraMap_mem' r := ⟨TFixed_algebraMap F r, HFixed_algebraMap F r⟩

lemma mem_NFixedAlgH (F : Type) [Field F] [CharZero F]
    {α : EM.latticeFunctionField F Mprime} :
    α ∈ NFixedAlgH F ↔ TFixed F α ∧ HFixed F α := Iff.rfl

/-- 类型锁：`NFixedAlgH` 的载体（一旦改动立即编译失败）。 -/
theorem NFixedAlgH_typeLock (F : Type) [Field F] [CharZero F] :
    (NFixedAlgH F : Set (EM.latticeFunctionField F Mprime))
      = {α | TFixed F α ∧ HFixed F α} := rfl
#print axioms iotaH
#print axioms smul_Hp_eq_iotaH
#print axioms HFixed
#print axioms HFixed_algebraMap
#print axioms NFixedAlgH
#print axioms mem_NFixedAlgH
#print axioms NFixedAlgH_typeLock


/-! ## §2 `H` 版的成员刻画（`H` 版 §34）

与 §34 的唯一差别：把 `σ : G.Gp 3` 换成 `h : P.Hp 3`、把 `mem_invariantsField_iff`
换成 `EM.mem_latticeInvariantsAlg_iff`，并在 `h • β` 与 `iotaH h • β` 之间用
`smul_Hp_eq_iotaH`（`rfl`）过渡。 -/

/-- ★★★ **`H` 版 D2 收口**：`K^{N_H}` 与 `↥(EM.latticeInvariantsAlg F H Lat)` 内容一致。 -/
theorem NH_fixed_iff_invariantsField (F : Type) [Field F] [CharZero F]
    (α : EM.latticeFunctionField F Mprime) :
    (TFixed F α ∧ HFixed F α) ↔
      ∃ β : EM.latticeFunctionField F (ProcLat.Mp2 3),
        β ∈ EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3) ∧
        latticeFunctionFieldKerToK F ((latticeFunctionFieldKerEquiv F).symm β) = α := by
  constructor
  · rintro ⟨hT, hH⟩
    obtain ⟨β₀, hβ₀⟩ := (latticeFunctionFieldKerToK_range F α).mpr hT
    have hfix : ∀ h : P.Hp 3, kerScaleFieldEquiv F (iotaH h) β₀ = β₀ := by
      intro h
      apply latticeFunctionFieldKerToK_injective F
      rw [latticeFunctionFieldKerToK_kerScaleFieldEquiv, hβ₀, hH h]
    refine ⟨latticeFunctionFieldKerEquiv F β₀, ?_, ?_⟩
    · rw [EM.mem_latticeInvariantsAlg_iff]
      intro h
      rw [smul_Hp_eq_iotaH, ← latticeFunctionFieldKerEquiv_kerScaleFieldEquiv, hfix h]
    · rw [RingEquiv.symm_apply_apply]
      exact hβ₀
  · rintro ⟨β, hβ, hα⟩
    have hfixed : ∀ h : P.Hp 3, h • β = β :=
      (EM.mem_latticeInvariantsAlg_iff F (P.Hp 3) (ProcLat.Mp2 3) β).mp hβ
    refine ⟨(latticeFunctionFieldKerToK_range F α).mp ⟨(latticeFunctionFieldKerEquiv F).symm β, hα⟩, ?_⟩
    intro h
    rw [← hα, ← latticeFunctionFieldKerToK_kerScaleFieldEquiv]
    congr 1
    apply (latticeFunctionFieldKerEquiv F).injective
    rw [latticeFunctionFieldKerEquiv_kerScaleFieldEquiv, RingEquiv.apply_symm_apply]
    exact (smul_Hp_eq_iotaH F h β).symm.trans (hfixed h)
#print axioms NH_fixed_iff_invariantsField


/-! ## §3 `H` 版的类型层与交付定理（`H` 版 §36–§37） -/

/-- `H` 版「不变量域 → `K`」的环同态（同 §36 的 `invFieldToK`，右端换成 `H`-不变量）。 -/
noncomputable def invFieldToKH (F : Type) [Field F] :
    ↥(HInv F) →+* EM.latticeFunctionField F Mprime :=
  (latticeFunctionFieldKerToK F).comp
    ((latticeFunctionFieldKerEquiv F).symm.toRingHom.comp
      (Subalgebra.val (HInv F)).toRingHom)

lemma invFieldToKH_apply (F : Type) [Field F] (β : ↥(HInv F)) :
    invFieldToKH F β = latticeFunctionFieldKerToK F
      ((latticeFunctionFieldKerEquiv F).symm β.val) := rfl

lemma invFieldToKH_injective (F : Type) [Field F] :
    Function.Injective (invFieldToKH F) := by
  intro x y h
  simp only [invFieldToKH_apply] at h
  have h1 : (latticeFunctionFieldKerEquiv F).symm x.val
      = (latticeFunctionFieldKerEquiv F).symm y.val :=
    latticeFunctionFieldKerToK_injective F h
  have h2 := congrArg (latticeFunctionFieldKerEquiv F) h1
  simp only [RingEquiv.apply_symm_apply] at h2
  exact Subtype.ext h2

/-- `H` 版函数层：`K^{N_H} → ↥(H-不变量)`，由 §2 的存在性取（R13）。 -/
noncomputable def nFixedToInvFunH (F : Type) [Field F] [CharZero F]
    (α : ↥(NFixedAlgH F)) : ↥(HInv F) :=
  ⟨Classical.choose ((NH_fixed_iff_invariantsField F α.val).mp α.2),
    (Classical.choose_spec ((NH_fixed_iff_invariantsField F α.val).mp α.2)).1⟩

lemma nFixedToInvFunH_spec (F : Type) [Field F] [CharZero F] (α : ↥(NFixedAlgH F)) :
    invFieldToKH F (nFixedToInvFunH F α) = α.val :=
  (Classical.choose_spec ((NH_fixed_iff_invariantsField F α.val).mp α.2)).2

/-- ★ **`H` 版环同态** `K^{N_H} →+* ↥(H-不变量)`（四条环律降回 `K` 用单射性，R21）。 -/
noncomputable def nFixedToInvH (F : Type) [Field F] [CharZero F] :
    ↥(NFixedAlgH F) →+* ↥(HInv F) where
  toFun := nFixedToInvFunH F
  map_one' := by
    apply invFieldToKH_injective F
    rw [map_one, nFixedToInvFunH_spec]
    simp
  map_zero' := by
    apply invFieldToKH_injective F
    rw [map_zero, nFixedToInvFunH_spec]
    simp
  map_add' α β := by
    apply invFieldToKH_injective F
    rw [map_add, nFixedToInvFunH_spec, nFixedToInvFunH_spec, nFixedToInvFunH_spec]
    rfl
  map_mul' α β := by
    apply invFieldToKH_injective F
    rw [map_mul, nFixedToInvFunH_spec, nFixedToInvFunH_spec, nFixedToInvFunH_spec]
    rfl

lemma nFixedToInvH_spec (F : Type) [Field F] [CharZero F] (α : ↥(NFixedAlgH F)) :
    invFieldToKH F (nFixedToInvH F α) = α.val :=
  nFixedToInvFunH_spec F α

/-- `H` 版反方向环同态（具体映射，成员性由 §2 的 `(⟸)` 给）。 -/
noncomputable def invToNFixedH (F : Type) [Field F] [CharZero F] :
    ↥(HInv F) →+* ↥(NFixedAlgH F) where
  toFun β := ⟨invFieldToKH F β,
    ((NH_fixed_iff_invariantsField F (invFieldToKH F β)).mpr ⟨β.val, β.2, rfl⟩)⟩
  map_one' := by
    apply Subtype.ext
    simp [invFieldToKH]
  map_zero' := by
    apply Subtype.ext
    simp [invFieldToKH]
  map_add' β γ := by
    apply Subtype.ext
    simp
  map_mul' β γ := by
    apply Subtype.ext
    simp

lemma nFixedToInvH_invToNFixedH (F : Type) [Field F] [CharZero F] (β : ↥(HInv F)) :
    nFixedToInvH F (invToNFixedH F β) = β := by
  apply invFieldToKH_injective F
  rw [nFixedToInvH_spec]
  rfl

/-- ★★ **`H` 版环等价**：`K^{N_H} ≃+* ↥(H-不变量)`。 -/
noncomputable def nFixedRingEquivH (F : Type) [Field F] [CharZero F] :
    ↥(NFixedAlgH F) ≃+* ↥(HInv F) :=
  RingEquiv.ofBijective (nFixedToInvH F) ⟨fun a b h => by
      have hh := congrArg (invFieldToKH F) h
      rw [nFixedToInvH_spec, nFixedToInvH_spec] at hh
      exact Subtype.ext hh,
    fun β => ⟨invToNFixedH F β, nFixedToInvH_invToNFixedH F β⟩⟩

lemma invToNFixedH_algebraMap (F : Type) [Field F] [CharZero F] (r : F) :
    invToNFixedH F (algebraMap F ↥(HInv F) r) = algebraMap F ↥(NFixedAlgH F) r := by
  apply Subtype.ext
  show invFieldToKH F (algebraMap F ↥(HInv F) r)
    = algebraMap F (EM.latticeFunctionField F Mprime) r
  rw [invFieldToKH_apply]
  have hval : ((algebraMap F ↥(HInv F) r : ↥(HInv F))
      : EM.latticeFunctionField F (ProcLat.Mp2 3))
      = algebraMap F (EM.latticeFunctionField F (ProcLat.Mp2 3)) r := rfl
  rw [hval]
  have h1 : (latticeFunctionFieldKerEquiv F).symm
      (algebraMap F (EM.latticeFunctionField F (ProcLat.Mp2 3)) r)
      = algebraMap F (EM.latticeFunctionField F ↥(LinearMap.ker fPrime)) r := by
    rw [← latticeFunctionFieldKerEquiv_algebraMap' F r, RingEquiv.symm_apply_apply]
  rw [h1, latticeFunctionFieldKerToK_algebraMap']

/-- ★★★ **`H` 版 `≃ₐ[F]` 收口**：`K^{N_H} ≃ₐ[F] ↥(EM.latticeInvariantsAlg F H Lat)`。 -/
noncomputable def nFixedAlgEquivH (F : Type) [Field F] [CharZero F] :
    ↥(NFixedAlgH F) ≃ₐ[F] ↥(HInv F) :=
  AlgEquiv.ofRingEquiv (f := nFixedRingEquivH F) (fun r => by
    show nFixedToInvH F (algebraMap F ↥(NFixedAlgH F) r) = algebraMap F ↥(HInv F) r
    rw [show algebraMap F ↥(NFixedAlgH F) r
        = invToNFixedH F (algebraMap F ↥(HInv F) r)
        from (invToNFixedH_algebraMap F r).symm]
    exact nFixedToInvH_invToNFixedH F (algebraMap F ↥(HInv F) r))


/-! ## §4 **交付定理（`H` 形 ＝ 论文 H2 的形式）**

`H` 版 `(A)+(B)`（Procesi／Saltman 对群 `H` 的实例）作为**唯一具名假设**；
本节的定理说明：**(C) 层已机检（§2–§3）＋ 该假设 ⟺ 论文 H2**
（在 `H` 形即 `ProcesiSubgroupHyp F H Lat` 的意义下，见 `Main.lean` 的消费）。 -/

/-- **`H` 版 `(A)+(B)`**：`Z_H`（`UD(F,9,H)` 的中心）就是 `K^{N_H}`。

**与 `S_9` 版的关系**：**并列**，互不推出（`Z_H` 与 `Z_{S_9}` 是不同中心单代数的中心；
`F(Lat)^H ⊋ F(Lat)^{S_9}`）。**研究级，未证**——它是 Procesi 定理对群 `H` 的实例。 -/
def SaltmanCenterEqHNFixed (F : Type) [Field F] [CharZero F] (Z : Type) [Field Z]
    [Algebra F Z] : Prop :=
  Nonempty (Z ≃ₐ[F] ↥(NFixedAlgH F))

/-- 类型锁：`SaltmanCenterEqHNFixed` 的外形（一旦改动立即编译失败）。 -/
theorem saltmanCenterEqHNFixed_typeLock (F : Type) [Field F] [CharZero F] (Z : Type)
    [Field Z] [Algebra F Z] :
    (SaltmanCenterEqHNFixed F Z) = (Nonempty (Z ≃ₐ[F] ↥(NFixedAlgH F))) := rfl

/-- ★★★ **论文 H2**：`H` 版 `(A)+(B)` ⟹ `Z ≅ F((M⊕U)|_H)^H`（`ProcesiSubgroupHyp` 形，
即 `Main.lean` 的 `zH_rational_of_procesi` 所消费的形）。 -/
theorem h2H_of_saltmanCenterEqHNFixed (F : Type) [Field F] [CharZero F] (Z : Type)
    [Field Z] [Algebra F Z] (h : SaltmanCenterEqHNFixed F Z) :
    ProcesiSubgroupHyp F (P.Hp 3) (ProcLat.Mp2 3) Z := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans (nFixedAlgEquivH F)⟩

/-- **逻辑地位（`H` 形）**：在 `(C)` 层已机检的前提下，`H` 形 ⟺ 该唯一具名假设。 -/
theorem procesiSubgroupHyp_iff_saltmanCenterEqHNFixed (F : Type) [Field F] [CharZero F]
    (Z : Type) [Field Z] [Algebra F Z] :
    ProcesiSubgroupHyp F (P.Hp 3) (ProcLat.Mp2 3) Z ↔ SaltmanCenterEqHNFixed F Z := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (nFixedAlgEquivH F).symm⟩
  · exact h2H_of_saltmanCenterEqHNFixed F Z

/-- **L1 非空洞见证（`H` 形）**：取 `Z := ` 右端即满足（恒等型，见 §3 的 `≃ₐ[F]` 反向）。

**读法**：这只说明假设类**非空**（不是空类上的空洞真），**不是**「论文 H2 为真」——
后者要求 `Z` 取真正的 `Z_H(F,9) = Z(UD(F,9,H))`（Lean 内**未构造**，构造它正是 `H` 版
`(A)(B)` 的内容）。 -/
theorem saltmanCenterEqHNFixed_nonempty (F : Type) [Field F] [CharZero F] :
    SaltmanCenterEqHNFixed F ↥(HInv F) :=
  ⟨(nFixedAlgEquivH F).symm⟩
#print axioms invFieldToKH
#print axioms invFieldToKH_apply
#print axioms invFieldToKH_injective
#print axioms nFixedToInvFunH
#print axioms nFixedToInvFunH_spec
#print axioms nFixedToInvH
#print axioms nFixedToInvH_spec
#print axioms invToNFixedH
#print axioms nFixedToInvH_invToNFixedH
#print axioms nFixedRingEquivH
#print axioms invToNFixedH_algebraMap
#print axioms nFixedAlgEquivH
#print axioms saltmanCenterEqHNFixed_typeLock
#print axioms SaltmanCenterEqHNFixed
#print axioms h2H_of_saltmanCenterEqHNFixed
#print axioms procesiSubgroupHyp_iff_saltmanCenterEqHNFixed
#print axioms saltmanCenterEqHNFixed_nonempty

/-! ## §5 **端到端接线**：`H` 版具名假设 ⟹ 论文 §6 的有理性结论

`Main.lean` 的 `zH_rational_of_procesi` 把「`Z ≅ F((M⊕U)|_H)^H`」＋第二层（`m3_procesi`，
**无条件**）接到「`Z` 于 `F(M|_H)^H` 有理」。本节把它与 §4 的交付定理复合，
得到**从唯一具名假设出发**的端到端命题——这就是论文 §6 该层的完整逻辑链。 -/

/-- ★★★ **端到端**：`H` 版 `(A)+(B)` ⟹ `Z_H` 于 `F(M|_H)^H` 有理（显式 `k` 个变元）。

**逻辑链（全部机检，除首个前提）**：
`SaltmanCenterEqHNFixed`（具名假设）→ `ProcesiSubgroupHyp`（§4 交付定理）
→ 有理性（`Main.zH_rational_of_procesi`，其第二层 `m3_procesi` **无条件**）。 -/
theorem zH_rational_of_saltmanCenterEqHNFixed (F : Type) [Field F] [CharZero F] (Z : Type)
    [Field Z] [Algebra F Z] (h : SaltmanCenterEqHNFixed F Z) :
    ∃ k : ℕ, Nonempty (Z ≃+* EM.rationalFunctionField
      ↥(EM.latticeInvariants F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) k) :=
  zH_rational_of_procesi F Z (h2H_of_saltmanCenterEqHNFixed F Z h)

#print axioms zH_rational_of_saltmanCenterEqHNFixed

/-! ## §6 **`IsRational` 收口（`≃ₐ` 形）**：消掉 `Main.lean` 的 `≃+*` 形态缺口

`Main.lean` 的 `zH_rational_of_procesi` 给的是 **`≃+*` 形**（`∃ k, Z ≃+* F(M|_H)^H(t₁,…,t_k)`），
而库消费者的形态是 `EM.IsRational`（**`≃ₐ` 形**）。本节的差别不是数学，是**基域呈现**：
`Alg.lean` 的 `isRational_procesi : EM.IsRational ↥K0 ↥(HInv F)` 已把 `F(M|_H)^H` 呈现为它在
半函数域中的像 `K0`（＝ Lenstra `prop:1.4` 的 `l^π`），故本件只需把该结论沿 H2 的
同构搬回 `Z`，并把 `Z` 上的 `↥K0`-代数结构**沿同构拉回**（这就是 `∃ inst` 的用法——
不是逃避，而是「基域结构由同构运输给出」的唯一忠实写法）。 -/

/-- `K0 = F(M|_H)^H` 在半函数域中的像（`Alg.lean` 的基域呈现）。 -/
abbrev K0H (F : Type) [Field F] : Type :=
  ↥(EM.K0 (G := P.Hp 3) (F := F) (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3))

-- `letI` 在此**必须**保留其名字（下面 `⟨instK0, ?_⟩` 要用），故关掉该风格 linter。
set_option linter.style.haveILetI false in
/-- ★★★ **`IsRational` 收口（`H` 形，`≃ₐ` 形）**：`H` 版 `(A)+(B)` ⟹ `Z` **于 `↥K0` 有理**
（`↥K0` ＝ `F(M|_H)^H` 的典范呈现，见 `Alg.lean` §3b）。

**与 `zH_rational_of_saltmanCenterEqHNFixed` 的分工**：那条给 `≃+*` 形（显式 `k` 个变元）；
本条给库消费者所需的 `EM.IsRational`（`≃ₐ` 形），并把 `Z` 上的 `↥K0`-代数结构沿同构运输
（`∃ inst`：结构由运输给出，而不是额外假设）。 -/
theorem isRational_of_saltmanCenterEqHNFixed (F : Type) [Field F] [CharZero F] (Z : Type)
    [Field Z] [Algebra F Z] (h : SaltmanCenterEqHNFixed F Z) :
    ∃ (inst : Algebra (K0H F) Z), @EM.IsRational (K0H F) _ Z _ inst := by
  obtain ⟨e₀⟩ := h
  let e : Z ≃+* ↥(HInv F) := (e₀.trans (nFixedAlgEquivH F)).toRingEquiv
  letI instK0 : Algebra (K0H F) Z :=
    (e.symm.toRingHom.comp (algebraMap (K0H F) ↥(HInv F))).toAlgebra
  refine ⟨instK0, ?_⟩
  have hcomm : ∀ r : K0H F, e (algebraMap (K0H F) Z r) = algebraMap (K0H F) ↥(HInv F) r := by
    intro r
    show e (e.symm ((algebraMap (K0H F) ↥(HInv F)) r)) = algebraMap (K0H F) ↥(HInv F) r
    rw [RingEquiv.apply_symm_apply]
  have eA : Z ≃ₐ[K0H F] ↥(HInv F) := AlgEquiv.ofRingEquiv (f := e) hcomm
  obtain ⟨n, ⟨f⟩⟩ := isRational_procesi (F := F)
  exact ⟨n, ⟨eA.trans f⟩⟩

#print axioms K0H
#print axioms isRational_of_saltmanCenterEqHNFixed

end

end Procesi
