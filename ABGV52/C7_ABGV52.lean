/-
  ABGV-5.2 —— C 档 (b).2 第 1 步：`V = Z[H]^9` 的高次上同调消没

  路线（= 论文 `lem:H2-MH` 的「Shapiro ⟹ 两端为零」一步）
  ====================================================
    * **参数化 Shapiro**：对**任意** `A : Rep ℤ ↥⊥`，
      `H^{n+1}(H, coind_⊥^H(A)) = 0`（把 C5 的论证从平凡表示推广到任意系数）；
    * 把 `V = H → Z[H]`（G2 的坐标作用）**包装成 `Rep ℤ H`**（G2 刻意只给显式函数 `act`）；
    * 造 `Rep ℤ H` 同构 **`V ≅ coind_⊥^H(Z[H])`**，写子为
      `Φ(f) = (x ↦ x · f(x⁻¹))`（**自逆**，且把 G2 的坐标作用换成余诱导的右平移）；
    * 传递得 **`H^{n+1}(H, V) = 0`**。
-/
import ABGV52.C6_ABGV52

open CategoryTheory

namespace ABGV52

/-! ## 1. 参数化的 Shapiro 消失 -/

/-- 对**任意** `A : Rep ℤ ↥⊥`，`H^{n+1}(H, coind_⊥^H(A)) = 0`。 -/
theorem isZero_groupCohomology_coind (A : Rep ℤ ↥(⊥ : Subgroup H)) (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup H).subtype A) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton A n).of_iso
    (groupCohomology.coindIso (S := (⊥ : Subgroup H)) A (n + 1))

/-! ## 2. 把 `V`（G2 的坐标作用）包装成 `Rep ℤ H` -/

lemma act_smul (h : H) (m : ℤ) (z : V) : act h (m • z) = m • act h z := by
  funext i
  simp only [act_apply, Pi.smul_apply, lmul_smul]

noncomputable def actLin (h : H) : V →ₗ[ℤ] V where
  toFun := act h
  map_add' := act_add h
  map_smul' := act_smul h

noncomputable def Vrepr : Representation ℤ H V where
  toFun h := actLin h
  map_one' := LinearMap.ext fun z => act_one z
  map_mul' x y := LinearMap.ext fun z => act_mul x y z

/-- `V = Z[H]^9` 作为 `Rep ℤ H`（坐标为 G2 的坐标作用）。 -/
noncomputable abbrev VRep : Rep ℤ H := Rep.of Vrepr

/-! ## 3. `V ≅ coind_⊥^H(Z[H])` -/

/-- `⊥` 上的平凡表示，载体 `Z[H]`。 -/
noncomputable abbrev bigTriv : Rep ℤ ↥(⊥ : Subgroup H) :=
  Rep.trivial ℤ ↥(⊥ : Subgroup H) (MonoidAlgebra ℤ H)

/-- `coind_⊥^H(Z[H])`：函数 `H → Z[H]`，按**右平移**作用。 -/
noncomputable abbrev coindBig : Rep ℤ H := Rep.coind (⊥ : Subgroup H).subtype bigTriv

lemma coindBig_apply (h : H) (g : coindBig.V) (x : H) :
    (coindBig.ρ h g).1 x = g.1 (x * h) := by
  change (((Representation.coind (⊥ : Subgroup H).subtype bigTriv.ρ) h) g).1 x
      = g.1 (x * h)
  rw [Representation.coind_apply]
  rfl

/-- 同构的写子：`Φ(f) = (x ↦ x · f(x⁻¹))`。 -/
noncomputable def phiFunV (f : V) : V := fun x => lmul x (f x⁻¹)

/-- `Φ` 自逆。 -/
lemma phiFunV_involutive (f : V) : phiFunV (phiFunV f) = f := by
  funext x
  simp only [phiFunV, inv_inv]
  rw [lmul_mul, mul_inv_cancel, lmul, ← MonoidAlgebra.one_def, one_mul]

/-- `coindV` 的隶属条件是空的（`⊥` 是平凡群）。 -/
lemma mem_coindBig (f : V) : f ∈ Representation.coindV (⊥ : Subgroup H).subtype bigTriv.ρ := by
  intro g h
  have hg : (⊥ : Subgroup H).subtype g = 1 := by
    have : g = 1 := Subsingleton.elim g 1
    rw [this]
    rfl
  rw [hg, one_mul]
  rfl

noncomputable def phiV : V →ₗ[ℤ] coindBig.V where
  toFun f := ⟨phiFunV f, mem_coindBig (phiFunV f)⟩
  map_add' f g := by
    refine Subtype.ext ?_
    funext x
    show lmul x ((f x⁻¹) + (g x⁻¹)) = lmul x (f x⁻¹) + lmul x (g x⁻¹)
    simp only [lmul, mul_add]
  map_smul' m f := by
    refine Subtype.ext ?_
    funext x
    show lmul x (m • (f x⁻¹)) = m • lmul x (f x⁻¹)
    rw [lmul_smul]

noncomputable def phiVEquiv : V ≃ₗ[ℤ] coindBig.V where
  toFun := phiV
  invFun g := phiFunV g.1
  left_inv f := phiFunV_involutive f
  right_inv g := Subtype.ext (phiFunV_involutive g.1)
  map_add' := phiV.map_add
  map_smul' := phiV.map_smul

/-- 等变式（逐元素）：坐标作用 ↦ 余诱导的右平移。 -/
lemma phiV_act_apply (h : H) (f : V) (x : H) :
    (phiV (act h f)).1 x = (coindBig.ρ h (phiV f)).1 x := by
  rw [coindBig_apply]
  show lmul x (lmul h (f (h⁻¹ * x⁻¹))) = lmul (x * h) (f (x * h)⁻¹)
  rw [lmul_mul, mul_inv_rev]

lemma phiV_intertwining (h : H) :
    phiVEquiv.toLinearMap ∘ₗ (Vrepr h) = (coindBig.ρ h) ∘ₗ phiVEquiv.toLinearMap := by
  refine LinearMap.ext fun f => ?_
  refine Subtype.ext (funext fun x => ?_)
  exact phiV_act_apply h f x

noncomputable def VRepIso : VRep ≅ coindBig :=
  Rep.mkIso (Representation.Equiv.mk phiVEquiv phiV_intertwining)

/-! ## 4. 主结论：`H^{n+1}(H, V) = 0` -/

/-- **`H^{n+1}(H, Z[H]^9) = 0`**（Shapiro ＋ 同构传递）。 -/
theorem isZero_groupCohomology_VRep (n : ℕ) :
    CategoryTheory.Limits.IsZero (groupCohomology VRep (n + 1)) :=
  (isZero_groupCohomology_coind bigTriv n).of_iso (cohIsoOfIso VRepIso (n + 1))

/-! ## 5. 公理闸门 -/

#print axioms isZero_groupCohomology_coind
#print axioms phiFunV_involutive
#print axioms phiV_intertwining
#print axioms VRepIso
#print axioms isZero_groupCohomology_VRep

end ABGV52
