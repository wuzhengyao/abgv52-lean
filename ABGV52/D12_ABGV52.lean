/-
  ABGV-5.2 —— C 档 · 块 1 · 子块 **1β-ix：度数收口（终环）—— `F(Y) = F(M)^A`**

  目标：**`diagSubfield F A = latticeInvariants F A (A → ℤ)`**（⊆ 由 D9；⊇ 为本件）。

  链条（探针 `Probe52`–`Probe54` 定案）：

    * ② **多项式模型的 `A`-作用**（`rename`：`X_a ↦ X_{g·a}`）＋ **与 `K` 的相容** `smul_polyToFF`
      ＋ **`ψ` 的等变性** `smul_psiPoly`（变量层 = `smul_uX`，即 `g • u_a = u_{g·a}`，由特征正交性收口）；
    * ③ 汇编用 `probe_fixed_fraction`（`R = MvPolynomial A F`，相容式 = ②第一条）
      ＋ `probe_invariant_mem_span`（丙-3：对角不变元 ∈ `Y`-张成）
      ＋ D10 的 `phiDiag_mem_diagSubfield_of_span` ＋ D11 的 `phiDiag_comp_psiPoly`；
    * ④ 收口：`z ∈ K` 不变 ⟹ `z = P̃/Q̃`（`P̃`／`Q̃` **多项式且不变**）⟹ `ψ(P̃)` 对角不变 ⟹ `Y`-张成
      ⟹ `Φ₀(ψ P̃) = polyToFF P̃ ∈ F(Y)` ⟹ 同 `Q̃` ⟹ `z ∈ F(Y)`。

  **工艺注**：②的两条相容式走**点值归纳**（`MvPolynomial.induction_on` 的 `C`／`add`／`mul_X`），
  不用环同态复合形态 —— 后者会把 `MulSemiringAction.toRingEquiv` 的取值写成
  `(…).toRingHom x` 的句法形状，`rw` 匹配失败（陷阱 45 在复合上下文中的再现）。
-/
import ABGV52.D11_ABGV52
import ABGV52.Probe52
import ABGV52.Probe53

namespace ABGV52

namespace EM

open scoped Classical

noncomputable section

section Assembly

variable (F : Type*) [Field F]
variable (A : Type*) [CommGroup A] [Fintype A]
variable [HasEnoughRootsOfUnity F (Monoid.exponent Aˣ)]

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **多项式模型上的 `A`-作用**（`X_a ↦ X_{g·a}`，`rename` 直给）。 -/
noncomputable instance instMulSemiringActionPolyRename :
    MulSemiringAction A (MvPolynomial A F) where
  smul g p := MvPolynomial.rename (fun a => g * a) p
  one_smul p := by
    show MvPolynomial.rename (fun a : A => (1 : A) * a) p = p
    rw [show (fun a : A => (1 : A) * a) = id from funext fun a => one_mul a,
      MvPolynomial.rename_id]
    rfl
  mul_smul g h p := by
    show MvPolynomial.rename (fun a => (g * h) * a) p
      = MvPolynomial.rename (fun a => g * a) (MvPolynomial.rename (fun a => h * a) p)
    rw [MvPolynomial.rename_rename,
      show ((fun a : A => g * a) ∘ (fun a => h * a)) = (fun a => g * (h * a)) from rfl,
      show (fun a : A => g * (h * a)) = (fun a => (g * h) * a) from
        funext fun a => (mul_assoc g h a).symm]
  smul_zero g := map_zero _
  smul_add g p q := map_add _ p q
  smul_one g := map_one _
  smul_mul g p q := map_mul _ p q

lemma smul_X (g a : A) :
    g • (MvPolynomial.X a : MvPolynomial A F) = MvPolynomial.X (g * a) := by
  show MvPolynomial.rename (fun b => g * b) (MvPolynomial.X a) = _
  rw [MvPolynomial.rename_X]

lemma smul_C (g : A) (c : F) :
    g • (MvPolynomial.C c : MvPolynomial A F) = MvPolynomial.C c := by
  show MvPolynomial.rename (fun b => g * b) (MvPolynomial.C c) = MvPolynomial.C c
  rw [MvPolynomial.rename_C]

/-- `K` 侧的一般相容式（D3 的 `F`-纯量版的一般化）：`g • algebraMap r = algebraMap (g • r)`。 -/
lemma smul_algebraMap_latticeGeneral (g : A) (r : latticeAlgebra F (A → ℤ)) :
    g • algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ)) r
      = algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ)) (g • r) := by
  change (IsFractionRing.ringEquivOfRingEquiv
      (MulSemiringAction.toRingEquiv A (latticeAlgebra F (A → ℤ)) g))
    (algebraMap (latticeAlgebra F (A → ℤ)) (latticeFunctionField F (A → ℤ)) r) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    MulSemiringAction.toRingEquiv_apply_apply]

lemma polyToFF_C (c : F) :
    polyToFF F A (MvPolynomial.C c) = algebraMap F (latticeFunctionField F (A → ℤ)) c :=
  AlgHom.commutes (polyToFF F A) c

lemma psiPoly_C (c : F) :
    psiPoly F A (MvPolynomial.C c) = algebraMap F (diagAlgebra F A) c :=
  AlgHom.commutes (psiPoly F A) c

/-- 对角模型上 `F`-纯量被固定（D7 的 `SMulCommClass` 实例 ＋ 幺元）。 -/
lemma smul_algebraMap_diag (g : A) (c : F) :
    g • algebraMap F (diagAlgebra F A) c = algebraMap F (diagAlgebra F A) c := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm g c 1, smul_one,
    ← Algebra.algebraMap_eq_smul_one]

/-- 相容式的**单变量版**（`mul_X` 支的次序由此引理吸收）。 -/
lemma smul_polyToFF_X (g n : A) :
    g • polyToFF F A (MvPolynomial.X n) = polyToFF F A (g • MvPolynomial.X n) := by
  rw [polyToFF_apply, polySubst_X, smul_algebraMap_latticeGeneral, smul_regMono,
    smul_X, polyToFF_apply, polySubst_X]

/-- **`ψ` 的等变性（变量层）**：`g • u_a = u_{g·a}`。 -/
lemma smul_uX (g a : A) : g • uX F A a = uX F A (g * a) := by
  rw [uX, uX, smul_comm]
  have h : g • (∑ χ : MulChar A F, (χ a) • zMono F A (Finsupp.single χ 1))
      = ∑ χ : MulChar A F, g • ((χ a) • zMono F A (Finsupp.single χ 1)) :=
    map_sum (MulSemiringAction.toRingEquiv A (diagAlgebra F A) g) _ _
  have hsum : (∑ χ : MulChar A F, g • ((χ a) • zMono F A (Finsupp.single χ 1)))
      = ∑ χ : MulChar A F, (χ (g * a)) • zMono F A (Finsupp.single χ 1) :=
    Finset.sum_congr rfl fun χ _ => by
      rw [smul_comm, smul_zMono, charOf_single, map_mul, mul_comm, smul_smul]
  rw [h, hsum]

/-- `ψ` 侧相容式的单变量版。 -/
lemma smul_psiPoly_X (g n : A) :
    g • psiPoly F A (MvPolynomial.X n) = psiPoly F A (g • MvPolynomial.X n) := by
  rw [psiPoly_X, smul_uX, smul_X, psiPoly_X]

/-- **相容式 ②**（`K` 侧，点值形）：`g • polyToFF p = polyToFF (g • p)`。 -/
lemma smul_polyToFF (g : A) (p : MvPolynomial A F) :
    g • polyToFF F A p = polyToFF F A (g • p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [smul_C, polyToFF_C, smul_algebraMap_latticeFunctionField]
  | add p q hp hq =>
      simp only [map_add, smul_add]
      rw [hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, smul_mul']
      rw [hp, smul_polyToFF_X]

/-- **相容式 ②**（`ψ` 侧，点值形）：`g • ψ p = ψ (g • p)`。 -/
lemma smul_psiPoly (g : A) (p : MvPolynomial A F) :
    g • psiPoly F A p = psiPoly F A (g • p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [smul_C, psiPoly_C, smul_algebraMap_diag]
  | add p q hp hq =>
      simp only [map_add, smul_add]
      rw [hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, smul_mul']
      rw [hp, smul_psiPoly_X]

/-! ## ② 前哨：内联自 Probe52／Probe53（逐字未改）

## ③④ 汇编：`F(M)^A ⊆ F(Y)` -/

/-- **终环**：`F(Y) = F(M)^A`。 -/
theorem diagSubfield_eq_latticeInvariants :
    diagSubfield F A = latticeInvariants F A (A → ℤ) := by
  refine le_antisymm (diagSubfield_le_invariants F A) ?_
  intro z hz
  have hcompat : ∀ (g : A) (p : MvPolynomial A F),
      g • algebraMap (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) p
        = algebraMap (MvPolynomial A F) (latticeFunctionField F (A → ℤ)) (g • p) := by
    intro g p
    rw [algebraMap_polyFF, algebraMap_polyFF]
    exact smul_polyToFF F A g p
  have := polyToFF_isFractionRing F A
  obtain ⟨P, Q, hP, hQ, hQ0, hPQ⟩ :=
    Probe53.probe_fixed_fraction A (MvPolynomial A F) (latticeFunctionField F (A → ℤ))
      hcompat hz
  have hPmem : polyToFF F A P ∈ diagSubfield F A := by
    rw [← phiDiag_comp_psiPoly F A, AlgHom.comp_apply]
    exact phiDiag_mem_diagSubfield_of_span F A
      (Probe52.probe_invariant_mem_span F A fun g => by rw [smul_psiPoly, hP g])
  have hQmem : polyToFF F A Q ∈ diagSubfield F A := by
    rw [← phiDiag_comp_psiPoly F A, AlgHom.comp_apply]
    exact phiDiag_mem_diagSubfield_of_span F A
      (Probe52.probe_invariant_mem_span F A fun g => by rw [smul_psiPoly, hQ g])
  have hQne : polyToFF F A Q ≠ 0 := fun h =>
    hQ0 (polyToFF_injective F A (by rw [h, map_zero]))
  have hz' : z = polyToFF F A P * (polyToFF F A Q)⁻¹ := by
    have h := hPQ
    rw [algebraMap_polyFF, algebraMap_polyFF] at h
    rw [← div_eq_mul_inv, eq_div_iff hQne]
    exact h
  rw [hz']
  exact Subfield.mul_mem _ hPmem (Subfield.inv_mem _ hQmem)

end Assembly

/-! ## 公理闸门 -/

#print axioms smul_polyToFF
#print axioms smul_psiPoly
#print axioms diagSubfield_eq_latticeInvariants

end

end EM

end ABGV52
