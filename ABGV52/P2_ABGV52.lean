/-
  ABGV-5.2 —— **P 档 P2：Shapiro 消没**（C 档 `C5`／`C7` 的 p 版）

  内容（与 C 档逐段对应）
  ====================
    ① `coind_⊥^H(Z) ≅ Z[H]`（右平移 ↦ 左乘，写子 `x ↦ x⁻¹` 扭转）；
    ② `H^{n+1}(H, Z[H]) = 0`（Shapiro ＋ 平凡群消没 ＋ 同构传递）；
    ③ 参数化 Shapiro：对**任意** `A : Rep ℤ ↥⊥`，`H^{n+1}(H, coind_⊥^H(A)) = 0`；
    ④ `Vp p ≅ coind_⊥^H(Z[H])`（写子 `Φ(f) = (x ↦ x · f(x⁻¹))`，**自逆**）；
    ⑤ `H^{n+1}(H, Vp p) = 0`。

  用途：P3 的增广序列 `0 → I[H] → Z[H] → Z → 0` 与 P4 的 Procesi 长正合列
  的两端零化（论文 `lem:H2-MH` 的「Shapiro ⟹ 两端为零」一步）。

  p-通用性：全段结构性 —— 唯一用到 `H` 的地方是**群公理**与 `⊥` 是平凡子群；
  与 `p` 无关（故本文件与 C 档对应段逐字同构，仅换类型）。
-/
import ABGV52.P1_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

open CategoryTheory

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. `coind_⊥^H(Z)` 及其作用公式 -/

/-- `⊥ : Subgroup (Hp p)` 上的平凡表示（载体 `ℤ`）。 -/
noncomputable abbrev trivBot : Rep ℤ ↥(⊥ : Subgroup (Hp p)) :=
  Rep.trivial ℤ ↥(⊥ : Subgroup (Hp p)) ℤ

/-- `coind_⊥^H(Z)`：`H` 在函数 `H → ℤ` 上按**右平移**作用。 -/
noncomputable abbrev coindBot : Rep ℤ (Hp p) :=
  Rep.coind (⊥ : Subgroup (Hp p)).subtype (trivBot p)

lemma coindBot_apply (h : Hp p) (z : (coindBot p).V) (x : Hp p) :
    ((coindBot p).ρ h z).1 x = z.1 (x * h) := by
  change (((Representation.coind (⊥ : Subgroup (Hp p)).subtype (trivBot p).ρ) h) z).1 x
      = z.1 (x * h)
  rw [Representation.coind_apply]
  rfl

/-! ## 2. 两个互逆的映射 `Φ : coindBot → Z[H]` 与 `Ψ : Z[H] → coindBot` -/

/-- `Φ(z) = Σ_x z(x) · single x⁻¹ 1`。 -/
noncomputable def phiFun (z : (coindBot p).V) : MonoidAlgebra ℤ (Hp p) :=
  ∑ x : Hp p, (z.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ)

/-- `Ψ(w) = (x ↦ w.coeff x⁻¹)`。 -/
noncomputable def psiFun (w : MonoidAlgebra ℤ (Hp p)) : (coindBot p).V :=
  ⟨fun x => w.coeff x⁻¹, by
    intro g h
    have hg : (⊥ : Subgroup (Hp p)).subtype g = 1 := by
      have : g = 1 := Subsingleton.elim g 1
      rw [this]
      rfl
    rw [hg, one_mul]
    rfl⟩

/-- **等变式**（核心）：右平移 ↦ 左乘。 -/
lemma phiFun_act (h : Hp p) (z : (coindBot p).V) :
    phiFun p ((coindBot p).ρ h z) = lmul p h (phiFun p z) := by
  have hstep : phiFun p ((coindBot p).ρ h z)
      = ∑ x : Hp p, (z.1 (x * h)) • MonoidAlgebra.single x⁻¹ (1 : ℤ) := by
    simp only [phiFun]
    exact Finset.sum_congr rfl fun x _ => by rw [coindBot_apply]
  have hreindex : (∑ x : Hp p, (z.1 (x * h)) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
      = ∑ b : Hp p, (z.1 b) • MonoidAlgebra.single (h * b⁻¹) (1 : ℤ) := by
    have h1 := Equiv.sum_comp (Equiv.mulRight h)
      (fun b : Hp p => (z.1 b) • MonoidAlgebra.single (h * b⁻¹) (1 : ℤ))
    simpa [mul_assoc] using h1
  rw [hstep, hreindex, phiFun, lmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul_comm, ← lmul, lmul_single]

lemma phi_psi (w : MonoidAlgebra ℤ (Hp p)) : phiFun p (psiFun p w) = w := by
  have h1 : phiFun p (psiFun p w)
      = ∑ y : Hp p, (w.coeff y) • MonoidAlgebra.single y (1 : ℤ) := by
    simp only [phiFun, psiFun]
    exact Equiv.sum_comp (Equiv.inv (Hp p))
      (fun y : Hp p => (w.coeff y) • MonoidAlgebra.single y (1 : ℤ))
  rw [h1, ← eq_sum_coeff_smul_single p w]

lemma psi_phi (z : (coindBot p).V) : psiFun p (phiFun p z) = z := by
  refine Subtype.ext (funext fun x => ?_)
  show (phiFun p z).coeff x⁻¹ = z.1 x
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

noncomputable def phiEquiv : (coindBot p).V ≃ₗ[ℤ] MonoidAlgebra ℤ (Hp p) where
  toFun := phiFun p
  invFun := psiFun p
  left_inv := psi_phi p
  right_inv := phi_psi p
  map_add' z₁ z₂ := by
    change (∑ x : Hp p, (z₁.1 x + z₂.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
      = (∑ x : Hp p, (z₁.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
        + ∑ x : Hp p, (z₂.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by rw [add_smul]
  map_smul' m z := by
    change (∑ x : Hp p, (m • z.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ))
      = m • ∑ x : Hp p, (z.1 x) • MonoidAlgebra.single x⁻¹ (1 : ℤ)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => by simp only [smul_smul, smul_eq_mul]

lemma phi_intertwining (h : Hp p) :
    (phiEquiv p).toLinearMap ∘ₗ ((coindBot p).ρ h)
      = ((regZ p).ρ h) ∘ₗ (phiEquiv p).toLinearMap := by
  refine LinearMap.ext fun z => ?_
  show phiFun p ((coindBot p).ρ h z) = lmul p h (phiFun p z)
  exact phiFun_act p h z

noncomputable def phiRepEquiv : (coindBot p).ρ.Equiv (regZ p).ρ :=
  Representation.Equiv.mk (phiEquiv p) (phi_intertwining p)

/-- **`coind_⊥^H(Z) ≅ Z[H]`**（正则表示）。 -/
noncomputable def coindBotIso : coindBot p ≅ regZ p :=
  Rep.mkIso (phiRepEquiv p)

/-! ## 4. 协变系数函子性的同构传递 -/

noncomputable def cohIsoOfIso {A B : Rep ℤ (Hp p)} (e : A ≅ B) (n : ℕ) :
    groupCohomology A n ≅ groupCohomology B n where
  hom := groupCohomology.map (MonoidHom.id (Hp p)) e.hom n
  inv := groupCohomology.map (MonoidHom.id (Hp p)) e.inv n
  hom_inv_id := by
    rw [← groupCohomology.map_id_comp e.hom e.inv n, e.hom_inv_id, groupCohomology.map_id]
  inv_hom_id := by
    rw [← groupCohomology.map_id_comp e.inv e.hom n, e.inv_hom_id, groupCohomology.map_id]

/-! ## 5. 主结论 ①：`H^{n+1}(H, Z[H]) = 0` -/

/-- **`H^{n+1}(H, Z[H]) = 0`**（Shapiro ＋ 平凡群消失 ＋ 同构传递）。 -/
theorem isZero_groupCohomology_regZ (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology (regZ p) (n + 1)) := by
  have hbot : CategoryTheory.Limits.IsZero (groupCohomology (trivBot p) (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton (trivBot p) n
  have hcoind : CategoryTheory.Limits.IsZero (groupCohomology (coindBot p) (n + 1)) :=
    hbot.of_iso (groupCohomology.coindIso (S := (⊥ : Subgroup (Hp p))) (trivBot p) (n + 1))
  exact hcoind.of_iso (cohIsoOfIso p (coindBotIso p) (n + 1)).symm

/-! ## 6. 参数化的 Shapiro 消失 -/

/-- 对**任意** `A : Rep ℤ ↥⊥`，`H^{n+1}(H, coind_⊥^H(A)) = 0`。 -/
theorem isZero_groupCohomology_coind (A : Rep ℤ ↥(⊥ : Subgroup (Hp p))) (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup (Hp p)).subtype A) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton A n).of_iso
    (groupCohomology.coindIso (S := (⊥ : Subgroup (Hp p))) A (n + 1))

/-! ## 7. `Vp p ≅ coind_⊥^H(Z[H])` -/

/-- `⊥` 上的平凡表示，载体 `Z[H]`。 -/
noncomputable abbrev bigTriv : Rep ℤ ↥(⊥ : Subgroup (Hp p)) :=
  Rep.trivial ℤ ↥(⊥ : Subgroup (Hp p)) (MonoidAlgebra ℤ (Hp p))

/-- `coind_⊥^H(Z[H])`：函数 `H → Z[H]`，按**右平移**作用。 -/
noncomputable abbrev coindBig : Rep ℤ (Hp p) :=
  Rep.coind (⊥ : Subgroup (Hp p)).subtype (bigTriv p)

lemma coindBig_apply (h : Hp p) (g : (coindBig p).V) (x : Hp p) :
    ((coindBig p).ρ h g).1 x = g.1 (x * h) := by
  change (((Representation.coind (⊥ : Subgroup (Hp p)).subtype (bigTriv p).ρ) h) g).1 x
      = g.1 (x * h)
  rw [Representation.coind_apply]
  rfl

/-- 同构的写子：`Φ(f) = (x ↦ x · f(x⁻¹))`。 -/
noncomputable def phiFunV (f : Vp p) : Vp p := fun x => lmul p x (f x⁻¹)

/-- `Φ` 自逆。 -/
lemma phiFunV_involutive (f : Vp p) : phiFunV p (phiFunV p f) = f := by
  funext x
  simp only [phiFunV, inv_inv]
  rw [lmul_mul, mul_inv_cancel, lmul, ← MonoidAlgebra.one_def, one_mul]

/-- `coindBig` 的隶属条件是空的（`⊥` 是平凡群）。 -/
lemma mem_coindBig (f : Vp p) :
    f ∈ Representation.coindV (⊥ : Subgroup (Hp p)).subtype (bigTriv p).ρ := by
  intro g h
  have hg : (⊥ : Subgroup (Hp p)).subtype g = 1 := by
    have : g = 1 := Subsingleton.elim g 1
    rw [this]
    rfl
  rw [hg, one_mul]
  rfl

noncomputable def phiV : Vp p →ₗ[ℤ] (coindBig p).V where
  toFun f := ⟨phiFunV p f, mem_coindBig p (phiFunV p f)⟩
  map_add' f g := by
    refine Subtype.ext ?_
    funext x
    show lmul p x ((f x⁻¹) + (g x⁻¹)) = lmul p x (f x⁻¹) + lmul p x (g x⁻¹)
    simp only [lmul, mul_add]
  map_smul' m f := by
    refine Subtype.ext ?_
    funext x
    show lmul p x (m • (f x⁻¹)) = m • lmul p x (f x⁻¹)
    rw [lmul_smul]

noncomputable def phiVEquiv : Vp p ≃ₗ[ℤ] (coindBig p).V where
  toFun := phiV p
  invFun g := phiFunV p g.1
  left_inv f := phiFunV_involutive p f
  right_inv g := Subtype.ext (phiFunV_involutive p g.1)
  map_add' := (phiV p).map_add
  map_smul' := (phiV p).map_smul

/-- 等变式（逐元素）：坐标作用 ↦ 余诱导的右平移。 -/
lemma phiV_act_apply (h : Hp p) (f : Vp p) (x : Hp p) :
    (phiV p (act p h f)).1 x = ((coindBig p).ρ h (phiV p f)).1 x := by
  rw [coindBig_apply]
  show lmul p x (lmul p h (f (h⁻¹ * x⁻¹))) = lmul p (x * h) (f (x * h)⁻¹)
  rw [lmul_mul, mul_inv_rev]

lemma phiV_intertwining (h : Hp p) :
    (phiVEquiv p).toLinearMap ∘ₗ (Vrepr p h)
      = ((coindBig p).ρ h) ∘ₗ (phiVEquiv p).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  refine Subtype.ext (funext fun x => ?_)
  exact phiV_act_apply p h f x

/-- **`Vp p ≅ coind_⊥^H(Z[H])`**。 -/
noncomputable def VRepIso : VRep p ≅ coindBig p :=
  Rep.mkIso (Representation.Equiv.mk (phiVEquiv p) (phiV_intertwining p))

/-- **`H^{n+1}(H, Z[H]^{⊕p²}) = 0`**（Shapiro ＋ 同构传递）。 -/
theorem isZero_groupCohomology_VRep (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology (VRep p) (n + 1)) :=
  (isZero_groupCohomology_coind p (bigTriv p) n).of_iso
    (cohIsoOfIso p (VRepIso p) (n + 1))

/-! ## 8. 公理闸门 -/

#print axioms isZero_groupCohomology_regZ
#print axioms isZero_groupCohomology_coind
#print axioms phiFunV_involutive
#print axioms phiV_intertwining
#print axioms VRepIso
#print axioms isZero_groupCohomology_VRep

end ABGV52.P
