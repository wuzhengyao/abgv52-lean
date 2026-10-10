/-
  ABGV-5.2 —— **P 档 T2 独立重写**（`thm:Cp-general` 的公开陈述库）

  口径（kakeya／DeepMind 范式，与 B 档 `Challenge_ABGV52` 同款）：
    * 本件**零 import 主链**（不 import `P1…P6`／`PThm`），自足重述对象与谓词；
      ⟹ 任何「全文件一致的替换」（如把 `ZMod (p*p)` 一律写成 `ZMod p`）在单文件内看不出来，
         只有第二份独立重写能抓。
    * 条件命题形态（3a/3b/3c/4）由本件**独立证明**（前提即假设，可直接推）；
      **无条件深内容**（置换格上的指数界）本件**只登记陈述**（`sorry`）——「公开陈述库登记陈述，
      工作只供证明」（其证明在 `PThm`／`P5b`）。
    * 检查器 `abgv52-lean-crosscheck.py` 逐条比对 `PThm` ↔ 本件 的**陈述类型**。
    * ⚠ ∝-stale（O1 修正，2026-10-10）：`pThm_not_stably_rational`／`pThm_not_rational`
      的判据参数为 **⊕-形旧读法**（一般情形已证为假）；P 档修正序列形（q-p）与其反证
      待下一波——届时与 `PThm` **同轮**改形，保持逐条比对。
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Data.ZMod.Basic

namespace ABGV52.PT2

open CategoryTheory CategoryTheory.Limits

variable (p : ℕ) [Fact p.Prime]

/-- `C_p`（乘法写法）。 -/
abbrev Cp : Type := Multiplicative (ZMod p)

/-- `Hp p = C_p × C_p`。 -/
abbrev Hp : Type := Cp p × Cp p

/-- 置换 `ℤ[Hp p]`-格（论文 `def:lattice`）。 -/
def IsPermutationLattice (P : Rep ℤ (Hp p)) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : MulAction (Hp p) X),
    Nonempty (P ≅ Rep.ofMulAction ℤ (Hp p) X)

/-- 稳定置换格（论文 `def:lattice`）。 -/
def IsStablyPermutation (L : Rep ℤ (Hp p)) : Prop :=
  ∃ (P Q : Rep ℤ (Hp p)), IsPermutationLattice p P ∧ IsPermutationLattice p Q ∧
    Nonempty (L ⊞ P ≅ Q)

/-- 「`(p : ℤ)` 消没 `coh²`」。 -/
noncomputable def Coh2ExpDvdp (A : Rep ℤ (Hp p)) : Prop :=
  ∀ x : ↥(groupCohomology A 2), (p : ℤ) • x = 0

/-- `ZMod (p*p)` 的 `1` 不被 `p` 消没。 -/
lemma p_smul_one_zmod_ne_zero : (p : ℤ) • (1 : ZMod (p * p)) ≠ 0 := by
  intro h
  have hcast : ((p : ℤ) : ZMod (p * p)) = 0 := by simpa using h
  have hdvd : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (p : ℤ) (p * p)).mp hcast
  have hpos : (0 : ℤ) < (p : ℤ) := by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    exact_mod_cast hp
  have hlt : (p : ℤ) < ((p * p : ℕ) : ℤ) := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have : p < p * p := by nlinarith
    exact_mod_cast this
  exact absurd (Int.le_of_dvd hpos hdvd) (by omega)

/-- 论文 (2)：置换格上 `exp(coh²) ∣ p`（**无条件深内容**：本件只登记陈述）。 -/
theorem pThm_perm_exp (L : Rep ℤ (Hp p)) (hL : IsPermutationLattice p L) :
    Coh2ExpDvdp p L := by
  sorry

/-- 论文 (3) 第一句：`coh² ≅ Z/p²` ＋ 转移界 ⟹ 非稳定置换。 -/
theorem pThm_not_stably_perm (M : Rep ℤ (Hp p))
    (h2 : Nonempty (↥(groupCohomology M 2) ≃ₗ[ℤ] ZMod (p * p)))
    (hexp : ∀ L : Rep ℤ (Hp p), IsPermutationLattice p L → Coh2ExpDvdp p L) :
    ¬ IsStablyPermutation p M := by
  obtain ⟨e⟩ := h2
  intro hSP
  obtain ⟨P, Q, hP, hQ, ⟨f⟩⟩ := hSP
  -- 转移：`φ = inl ≫ f.hom`，`ψ = f.inv ≫ fst`，`φ ≫ ψ = 𝟙 M`
  have hkillM : ∀ x : ↥(groupCohomology M 2), (p : ℤ) • x = 0 := by
    intro x
    set φ : M ⟶ Q := (biprod.inl : M ⟶ M ⊞ P) ≫ f.hom with hφ
    set ψ : Q ⟶ M := f.inv ≫ (biprod.fst : M ⊞ P ⟶ M) with hψ
    have hcomp : φ ≫ ψ = 𝟙 M := by
      rw [hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, biprod.inl_fst]
    have hid : x = (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom
        ((groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x) := by
      have h := congrArg (fun g => (groupCohomology.map (MonoidHom.id (Hp p)) g 2).hom x) hcomp
      simp only [groupCohomology.map_id_comp, groupCohomology.map_id, ModuleCat.id_apply] at h
      exact h.symm
    have hkill : (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x = 0 :=
      hexp Q hQ _
    calc (p : ℤ) • x
        = (p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom
            ((groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x) := by conv_lhs => rw [hid]
      _ = (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom
            ((p : ℤ) • (groupCohomology.map (MonoidHom.id (Hp p)) φ 2).hom x) :=
          (map_zsmul (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom (p : ℤ) _).symm
      _ = (groupCohomology.map (MonoidHom.id (Hp p)) ψ 2).hom 0 := by rw [hkill]
      _ = 0 := map_zero _
  have h1 : (p : ℤ) • (1 : ZMod (p * p)) = 0 := by
    have hx := hkillM (e.symm (1 : ZMod (p * p)))
    have := congrArg e hx
    simpa using this
  exact p_smul_one_zmod_ne_zero p h1

/-- 论文 (3) 有理性侧（EM 判据作假设）。 -/
theorem pThm_not_stably_rational (M : Rep ℤ (Hp p)) (K : Type) (SRat : Type → Prop)
    (criterion : SRat K ↔ IsStablyPermutation p M)
    (h2 : Nonempty (↥(groupCohomology M 2) ≃ₗ[ℤ] ZMod (p * p)))
    (hexp : ∀ L : Rep ℤ (Hp p), IsPermutationLattice p L → Coh2ExpDvdp p L) :
    ¬ SRat K :=
  fun hK => pThm_not_stably_perm p M h2 hexp (criterion.mp hK)

/-- 论文 (3) 的「从而非有理」。 -/
theorem pThm_not_rational (M : Rep ℤ (Hp p)) (K : Type) (SRat : Type → Prop)
    (criterion : SRat K ↔ IsStablyPermutation p M)
    (h2 : Nonempty (↥(groupCohomology M 2) ≃ₗ[ℤ] ZMod (p * p)))
    (hexp : ∀ L : Rep ℤ (Hp p), IsPermutationLattice p L → Coh2ExpDvdp p L)
    (Rat : Type → Prop) (hRatSRat : Rat K → SRat K) : ¬ Rat K :=
  fun hK => pThm_not_stably_rational p M K SRat criterion h2 hexp (hRatSRat hK)

/-- 论文 (4)：以 Saltman 1984 Cor 3.13 为带名假设。 -/
theorem pThm_retract (K : Type) (RRet : Type → Prop) (saltman_cor313 : RRet K) : RRet K :=
  saltman_cor313

/-! ## 公理闸门（本件含 1 处 `sorry`：无条件深内容只登记陈述） -/

#print axioms pThm_not_stably_perm
#print axioms pThm_not_stably_rational
#print axioms pThm_not_rational
#print axioms pThm_retract

end ABGV52.PT2
