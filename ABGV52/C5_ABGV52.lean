/-
  ABGV-5.2 —— C 档 (b)：`H^(n+1)(H, Z[H]) = 0`（Shapiro）

  路线
  ====
    * 记 `coindBot = coind_⊥^H(Z)`（`⊥ : Subgroup H` 上的平凡表示沿子群包含的**余诱导**）；
    * 造 `Rep ℤ H` 同构 `coindBot ≅ regZ`（余动作为**右平移** `(h·z)(x) = z(x*h)`，
      正则模为**左乘** `w ↦ h*w`；用 `x ↦ x⁻¹` 扭转：`Φ(z) = Σ_x z(x)·single x⁻¹ 1`；
      关键等变式 = `phiFun_act`）；
    * mathlib 的 Shapiro（`groupCohomology.coindIso`）给 `H^n(H, coindBot) ≅ H^n(⊥, Z)`；
    * 平凡群的高次上同调为零（`isZero_groupCohomology_succ_of_subsingleton`）；
    * 传递得 **`H^(n+1)(H, Z[H]) = 0`**。

  用途：(b).1 中增广序列 `0 → I[H] → Z[H] → Z → 0` 的长正合列需要这一项。
-/
import ABGV52.C2_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

open CategoryTheory

namespace ABGV52

/-! ## 1. `coind_⊥^H(Z)` 及其作用公式 -/

/-- `⊥ : Subgroup H` 上的平凡表示（载体 `Z`）。 -/
noncomputable abbrev trivBot : Rep ℤ ↥(⊥ : Subgroup H) := Rep.trivial ℤ ↥(⊥ : Subgroup H) ℤ

/-- `coind_⊥^H(Z)`：`H` 在函数 `H → Z` 上按**右平移**作用。 -/
noncomputable abbrev coindBot : Rep ℤ H := Rep.coind (⊥ : Subgroup H).subtype trivBot

lemma coindBot_apply (h : H) (z : coindBot.V) (x : H) :
    (coindBot.ρ h z).1 x = z.1 (x * h) := by
  change (((Representation.coind (⊥ : Subgroup H).subtype trivBot.ρ) h) z).1 x = z.1 (x * h)
  rw [Representation.coind_apply]
  rfl

/-! ## 2. 两个互逆的映射 `Φ : coindBot → Z[H]` 与 `Ψ : Z[H] → coindBot` -/

/-- `Φ(z) = Σ_x z(x) · single x⁻¹ 1`。 -/
noncomputable def phiFun (z : coindBot.V) : MonoidAlgebra ℤ H :=
  ∑ x : H, (z.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ)

/-- `Ψ(w) = (x ↦ w.coeff x⁻¹)`。 -/
noncomputable def psiFun (w : MonoidAlgebra ℤ H) : coindBot.V :=
  ⟨fun x => w.coeff x⁻¹, by
    intro g h
    have hg : (⊥ : Subgroup H).subtype g = 1 := by
      have : g = 1 := Subsingleton.elim g 1
      rw [this]
      rfl
    rw [hg, one_mul]
    rfl⟩

/-- **等变式**（核心）：右平移 ↦ 左乘。 -/
lemma phiFun_act (h : H) (z : coindBot.V) :
    phiFun (coindBot.ρ h z) = lmul h (phiFun z) := by
  have hstep : phiFun (coindBot.ρ h z)
      = ∑ x : H, (z.1 (x * h)) • MonoidAlgebra.single x⁻¹ (1 : ℤ) := by
    simp only [phiFun]
    exact Finset.sum_congr rfl fun x _ => by rw [coindBot_apply]
  have hreindex : (∑ x : H, (z.1 (x * h)) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
      = ∑ b : H, (z.1 b) • MonoidAlgebra.single (h * b⁻¹) (1 : ℤ) := by
    have h1 := Equiv.sum_comp (Equiv.mulRight h)
      (fun b : H => (z.1 b) • MonoidAlgebra.single (h * b⁻¹) (1 : ℤ))
    simpa [mul_assoc] using h1
  rw [hstep, hreindex, phiFun, lmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul_comm, ← lmul, lmul_single]

lemma phi_psi (w : MonoidAlgebra ℤ H) : phiFun (psiFun w) = w := by
  have h1 : phiFun (psiFun w)
      = ∑ y : H, (w.coeff y) • MonoidAlgebra.single y (1 : ℤ) := by
    simp only [phiFun, psiFun]
    exact Equiv.sum_comp (Equiv.inv H)
      (fun y : H => (w.coeff y) • MonoidAlgebra.single y (1 : ℤ))
  rw [h1, ← eq_sum_coeff_smul_single w]

lemma psi_phi (z : coindBot.V) : psiFun (phiFun z) = z := by
  refine Subtype.ext (funext fun x => ?_)
  show (phiFun z).coeff x⁻¹ = z.1 x
  rw [phiFun, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · intro y _ hy
    rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (fun hxy => hy (inv_injective hxy.symm)), smul_zero]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-! ## 3. 同构 `coindBot ≅ regZ` -/

noncomputable def phiEquiv : coindBot.V ≃ₗ[ℤ] MonoidAlgebra ℤ H where
  toFun := phiFun
  invFun := psiFun
  left_inv := psi_phi
  right_inv := phi_psi
  map_add' z₁ z₂ := by
    change (∑ x : H, (z₁.1 x + z₂.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
      = (∑ x : H, (z₁.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
        + ∑ x : H, (z₂.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [add_smul]
  map_smul' m z := by
    change (∑ x : H, (m • z.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
      = m • ∑ x : H, (z.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => by simp only [smul_smul, smul_eq_mul]

lemma phi_intertwining (h : H) :
    phiEquiv.toLinearMap ∘ₗ (coindBot.ρ h) = (regZ.ρ h) ∘ₗ phiEquiv.toLinearMap := by
  refine LinearMap.ext fun z => ?_
  show phiFun (coindBot.ρ h z) = lmul h (phiFun z)
  exact phiFun_act h z

noncomputable def phiRepEquiv : coindBot.ρ.Equiv regZ.ρ :=
  Representation.Equiv.mk phiEquiv phi_intertwining

/-- **`coind_⊥^H(Z) ≅ Z[H]`**（正则表示）。 -/
noncomputable def coindBotIso : coindBot ≅ regZ :=
  Rep.mkIso phiRepEquiv

/-! ## 4. 主结论：`H^(n+1)(H, Z[H]) = 0` -/

/-- 协变系数函子性的同构传递。 -/
noncomputable def cohIsoOfIso {A B : Rep ℤ H} (e : A ≅ B) (n : ℕ) :
    groupCohomology A n ≅ groupCohomology B n where
  hom := groupCohomology.map (MonoidHom.id H) e.hom n
  inv := groupCohomology.map (MonoidHom.id H) e.inv n
  hom_inv_id := by
    rw [← groupCohomology.map_id_comp e.hom e.inv n, e.hom_inv_id, groupCohomology.map_id]
  inv_hom_id := by
    rw [← groupCohomology.map_id_comp e.inv e.hom n, e.inv_hom_id, groupCohomology.map_id]

/-- **`H^(n+1)(H, Z[H]) = 0`**（Shapiro ＋ 平凡群消失 ＋ 同构传递）。 -/
theorem isZero_groupCohomology_regZ (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology regZ (n + 1)) := by
  have hbot : CategoryTheory.Limits.IsZero (groupCohomology trivBot (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton trivBot n
  have hcoind : CategoryTheory.Limits.IsZero (groupCohomology coindBot (n + 1)) :=
    hbot.of_iso (groupCohomology.coindIso (S := (⊥ : Subgroup H)) trivBot (n + 1))
  exact hcoind.of_iso (cohIsoOfIso coindBotIso (n + 1)).symm

/-! ## 5. 公理闸门 -/

#print axioms coindBot_apply
#print axioms phiFun_act
#print axioms phi_psi
#print axioms psi_phi
#print axioms coindBotIso
#print axioms isZero_groupCohomology_regZ

end ABGV52
