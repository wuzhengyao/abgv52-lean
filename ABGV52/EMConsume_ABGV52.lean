/-
  T2：「`IsStablyPermutation` 完整消费」（正则子情形）——ABGV-5.2 形式化战役

  目标（EMRouteS 偏差登记 7 的收口）：`EMRouteS.isStablyRational_of_regularSubcase` 的
  S3 数据形 `(B, ρ, hρ)` 此前由 `exists_permBasis_of_isPermutationLattice` 提取后
  **落在 `Rep` 载体 `↥L`** ，而抽象机器要 `[SMulCommClass G ℤ ↥L]` 与
  `[UniqueProds (Multiplicative ↥L)]`（偏差 2 的实例菱形）⟹ 主定理只能以数据形收口。
  本文件补齐这两条实例桥，并把「`M ⊕ P ≅ 正则格`」（正则子情形之 `IsStablyPermutation`）
  整体消费为 `F(M)^G` 的稳定有理性：桥 `b` 已由 `EMBridge` 消解，格等价
  `e : ↥M × ↥P ≃+ (G → ℤ)` 由双积-积等价、iso 载体等价、系数等价三段复合构造。

  **菱形处置（偏差 2）**：目标位内层 `ℤ`-smul 经 `ZSMul.toSMul`，`LinearMap.map_smul`
  侧经 `Rep.hV2` 的 module 结构，二者非 defeq；实例 `instSMulCommClassRepCarrier` 经
  `int_smul_eq_zsmul` 归约收口。文件内以 `attribute [local instance 2000] Rep.hV2`
  统一 module 结构优先级（与 `EMRouteS` 同款）。

  射程（A13）：本件只消费**正则子情形**（`Q = 单块正则格`）；一般置换 `Q` 的 M6
  不在本件射程（`D14` 反例：1γ 已被否证）。
-/
import ABGV52.EMBridge_ABGV52
import Mathlib.CategoryTheory.Preadditive.Biproducts

open CategoryTheory Limits

namespace ABGV52

namespace EM

namespace Consume

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {G : Type} [CommGroup G] [Fintype G]

attribute [local instance 2000] Rep.hV2

/-! ## 1. `Rep` 载体上的 `SMulCommClass` 菱形桥 -/

/-- `Rep` 载体 `↥L` 上：`G`-作用（`instDistribMulActionRep`）与 `ℤ`-纯量作用交换。
菱形处置：目标位内层 `ℤ`-smul 经 `ZSMul.toSMul`、`map_smul` 侧经 `Rep.hV2`，
经 `int_smul_eq_zsmul` 归约后由 `ρ`-线性性收口。 -/
instance instSMulCommClassRepCarrier (L : Rep ℤ G) : SMulCommClass G ℤ ↥L where
  smul_comm g c x := by
    show L.ρ g (c • x) = c • L.ρ g x
    rw [← int_smul_eq_zsmul L.hV2 c x, ← int_smul_eq_zsmul L.hV2 c (L.ρ g x)]
    exact (L.ρ g).map_smul c x

/-! ## 2. 置换格载体的 `UniqueSums`／`UniqueProds`（沿置换基搬运） -/

/-- 置换格载体 `↥P` 沿 `ℤ`-基搬运出 `UniqueSums`（靶 = `X →₀ ℤ`，`X` 有限）。 -/
theorem uniqueSums_carrier_of_basis (P : Rep ℤ G) {X : Type*} [Fintype X]
    (B : Module.Basis X ℤ ↥P) : UniqueSums ↥P :=
  (AddEquiv.uniqueSums_iff B.repr.toAddEquiv).mpr inferInstance

/-- 同上，`UniqueProds (Multiplicative ↥P)` 形。 -/
theorem uniqueProds_multiplicative_carrier (P : Rep ℤ G) {X : Type*} [Fintype X]
    (B : Module.Basis X ℤ ↥P) : UniqueProds (Multiplicative ↥P) := by
  haveI : UniqueSums ↥P := uniqueSums_carrier_of_basis P B
  infer_instance

/-! ## 3. 双积载体与积载体：加法等价与等变性 -/

/-- `fst ∘ inl = id`（函数层）。 -/
theorem biprod_inl_fst_apply (M P : Rep ℤ G) (m : ↥M) :
    (biprod.fst (X := M) (Y := P)).hom ((biprod.inl (X := M) (Y := P)).hom m) = m := by
  have h := congrArg (fun f : M ⟶ M => (f : ↥M → ↥M) m)
    (biprod.inl_fst (X := M) (Y := P))
  simpa only [Rep.comp_apply, Rep.id_apply] using h

/-- `fst ∘ inr = 0`（函数层）。 -/
theorem biprod_inr_fst_apply (M P : Rep ℤ G) (p : ↥P) :
    (biprod.fst (X := M) (Y := P)).hom ((biprod.inr (X := M) (Y := P)).hom p) = 0 := by
  have h : (biprod.fst (X := M) (Y := P)).hom ((biprod.inr (X := M) (Y := P)).hom p)
      = (0 : P ⟶ M) p := by
    have h' := congrArg (fun f : P ⟶ M => (f : ↥P → ↥M) p)
      (biprod.inr_fst (X := M) (Y := P))
    rw [Rep.comp_apply] at h'
    exact h'
  rw [h]
  change (0 : ↥P →ₗ[ℤ] ↥M) p = 0
  exact LinearMap.zero_apply p

/-- `snd ∘ inl = 0`（函数层）。 -/
theorem biprod_inl_snd_apply (M P : Rep ℤ G) (m : ↥M) :
    (biprod.snd (X := M) (Y := P)).hom ((biprod.inl (X := M) (Y := P)).hom m) = 0 := by
  have h : (biprod.snd (X := M) (Y := P)).hom ((biprod.inl (X := M) (Y := P)).hom m)
      = (0 : M ⟶ P) m := by
    have h' := congrArg (fun f : M ⟶ P => (f : ↥M → ↥P) m)
      (biprod.inl_snd (X := M) (Y := P))
    rw [Rep.comp_apply] at h'
    exact h'
  rw [h]
  change (0 : ↥M →ₗ[ℤ] ↥P) m = 0
  exact LinearMap.zero_apply m

/-- `snd ∘ inr = id`（函数层）。 -/
theorem biprod_inr_snd_apply (M P : Rep ℤ G) (p : ↥P) :
    (biprod.snd (X := M) (Y := P)).hom ((biprod.inr (X := M) (Y := P)).hom p) = p := by
  have h := congrArg (fun f : P ⟶ P => (f : ↥P → ↥P) p)
    (biprod.inr_snd (X := M) (Y := P))
  simpa only [Rep.comp_apply, Rep.id_apply] using h

/-- 全恒等式（函数层）：`inl ∘ fst + inr ∘ snd = id`。 -/
theorem biprod_total_apply (M P : Rep ℤ G) (x : ↥(M ⊞ P)) :
    (biprod.inl (X := M) (Y := P)).hom ((biprod.fst (X := M) (Y := P)).hom x)
      + (biprod.inr (X := M) (Y := P)).hom ((biprod.snd (X := M) (Y := P)).hom x) = x := by
  have h := congrArg (fun f : M ⊞ P ⟶ M ⊞ P => (f : ↥(M ⊞ P) → ↥(M ⊞ P)) x)
    (biprod.total (X := M) (Y := P))
  simpa only [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply,
    Rep.comp_apply, Rep.id_apply] using h

/-- 双积载体 ≃ 积载体（加法等价）：正向 `(m, p) ↦ inl m + inr p`，反向 `x ↦ (fst x, snd x)`。 -/
def biprodProdAddEquiv (M P : Rep ℤ G) : (↥M × ↥P) ≃+ ↥(M ⊞ P) :=
  { toFun := fun z =>
      (biprod.inl (X := M) (Y := P)).hom z.1 + (biprod.inr (X := M) (Y := P)).hom z.2
    invFun := fun x =>
      ((biprod.fst (X := M) (Y := P)).hom x, (biprod.snd (X := M) (Y := P)).hom x)
    left_inv := fun z => by
      obtain ⟨m, p⟩ := z
      refine Prod.ext ?_ ?_
      · show (biprod.fst (X := M) (Y := P)).hom
          ((biprod.inl (X := M) (Y := P)).hom m + (biprod.inr (X := M) (Y := P)).hom p) = m
        rw [map_add, biprod_inl_fst_apply, biprod_inr_fst_apply, add_zero]
      · show (biprod.snd (X := M) (Y := P)).hom
          ((biprod.inl (X := M) (Y := P)).hom m + (biprod.inr (X := M) (Y := P)).hom p) = p
        rw [map_add, biprod_inl_snd_apply, biprod_inr_snd_apply, zero_add]
    right_inv := fun x => biprod_total_apply M P x
    map_add' := fun z w => by
      obtain ⟨m₁, p₁⟩ := z
      obtain ⟨m₂, p₂⟩ := w
      show (biprod.inl (X := M) (Y := P)).hom (m₁ + m₂)
          + (biprod.inr (X := M) (Y := P)).hom (p₁ + p₂)
        = ((biprod.inl (X := M) (Y := P)).hom m₁
            + (biprod.inr (X := M) (Y := P)).hom p₁)
          + ((biprod.inl (X := M) (Y := P)).hom m₂
            + (biprod.inr (X := M) (Y := P)).hom p₂)
      rw [map_add, map_add]
      abel }

/-- 双积-积等价的等变性（对 `(M ⊞ P).ρ` 与积作用）。 -/
theorem biprodProdAddEquiv_equivariant (M P : Rep ℤ G) (g : G) (z : ↥M × ↥P) :
    biprodProdAddEquiv M P (g • z) = (M ⊞ P).ρ g (biprodProdAddEquiv M P z) := by
  obtain ⟨m, p⟩ := z
  show (biprod.inl (X := M) (Y := P)).hom (M.ρ g m)
      + (biprod.inr (X := M) (Y := P)).hom (P.ρ g p)
    = (M ⊞ P).ρ g ((biprod.inl (X := M) (Y := P)).hom m
      + (biprod.inr (X := M) (Y := P)).hom p)
  rw [map_add, Rep.hom_comm_apply, Rep.hom_comm_apply]

/-! ## 4. 正则载体 `ℤ[G] ≃ₗ (G → ℤ)`（系数等价 ∘ 有限支撑→函数） -/

/-- 正则载体 `↥(Rep.ofMulAction ℤ G G) = ℤ[G]` 到 `(G → ℤ)` 的 `ℤ`-线性等价。 -/
def regularCarrierLinearEquiv : ↥(Rep.ofMulAction ℤ G G) ≃ₗ[ℤ] (G → ℤ) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).trans (Finsupp.linearEquivFunOnFinite ℤ ℤ G)

/-- 其加法等价形。 -/
def regularCarrierAddEquiv : ↥(Rep.ofMulAction ℤ G G) ≃+ (G → ℤ) :=
  { toFun := regularCarrierLinearEquiv
    invFun := regularCarrierLinearEquiv.symm
    map_add' := fun x y => regularCarrierLinearEquiv.map_add x y
    left_inv := fun x => regularCarrierLinearEquiv.left_inv x
    right_inv := fun x => regularCarrierLinearEquiv.right_inv x }

/-- 单点式：`single x a ↦ Pi.single x a`。 -/
theorem regularCarrierAddEquiv_single [DecidableEq G] (x : G) (a : ℤ) :
    regularCarrierAddEquiv (MonoidAlgebra.single x a) = Pi.single x a := by
  have h : regularCarrierLinearEquiv (MonoidAlgebra.single x a) = Pi.single x a := by
    simp only [regularCarrierLinearEquiv, LinearEquiv.trans_apply]
    simp
  exact h

/-- 左乘作用（`instDistribMulActionRegularLattice`）在 `Pi.single` 上：
`g • e_x = e_{g x}`。 -/
theorem regular_smul_single [DecidableEq G] (g x : G) (a : ℤ) :
    (g • Pi.single x a : G → ℤ) = Pi.single (g * x) a := by
  funext b
  have hL : (g • Pi.single x a : G → ℤ) b = (Pi.single x a : G → ℤ) (g⁻¹ * b) := rfl
  rw [hL]
  by_cases h : b = g * x
  · subst h
    rw [Pi.single_eq_same, inv_mul_cancel_left, Pi.single_eq_same]
  · have h1 : g⁻¹ * b ≠ x := fun hh => h (by rw [← hh, mul_inv_cancel_left])
    rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h]

/-- 系数等价在 `ofMulAction` 正则作用下的等变性。 -/
theorem regularCarrierAddEquiv_equivariant (g : G) (ξ : ↥(Rep.ofMulAction ℤ G G)) :
    regularCarrierAddEquiv ((Rep.ofMulAction ℤ G G).ρ g ξ) = g • regularCarrierAddEquiv ξ := by
  classical
  induction ξ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      have hρ : ∀ a b : ↥(Rep.ofMulAction ℤ G G),
          (Rep.ofMulAction ℤ G G).ρ g (a + b)
            = (Rep.ofMulAction ℤ G G).ρ g a + (Rep.ofMulAction ℤ G G).ρ g b :=
        fun a b => map_add (f := (Rep.ofMulAction ℤ G G).ρ g) a b
      have he : ∀ a b : ↥(Rep.ofMulAction ℤ G G),
          regularCarrierAddEquiv (a + b)
            = regularCarrierAddEquiv a + regularCarrierAddEquiv b :=
        fun a b => map_add (f := regularCarrierAddEquiv) a b
      rw [hρ x y, he ((Rep.ofMulAction ℤ G G).ρ g x) ((Rep.ofMulAction ℤ G G).ρ g y),
        he x y, smul_add, hx, hy]
  | single x a =>
      rw [show (Rep.ofMulAction ℤ G G).ρ g (MonoidAlgebra.single x a)
            = MonoidAlgebra.single (g • x) a from Representation.ofMulAction_single g x a,
        regularCarrierAddEquiv_single, regularCarrierAddEquiv_single, regular_smul_single,
        smul_eq_mul]

/-! ## 5. iso 段的加法等价与等变性 -/

/-- `φ : M ⊞ P ≅ Rep.ofMulAction ℤ G G` 给出的载体加法等价。 -/
def phiAddEquiv (M P : Rep ℤ G) (φ : M ⊞ P ≅ Rep.ofMulAction ℤ G G) :
    ↥(M ⊞ P) ≃+ ↥(Rep.ofMulAction ℤ G G) :=
  { toFun := fun x => φ.hom.hom x
    invFun := fun s => φ.inv.hom s
    map_add' := fun x y => (φ.hom.hom.toLinearMap).map_add x y
    left_inv := fun x => Iso.hom_inv_id_apply φ x
    right_inv := fun s => Iso.inv_hom_id_apply φ s }

/-- 其在 `ρ` 下的等变性（即 `φ` 的交织性）。 -/
theorem phiAddEquiv_rho (M P : Rep ℤ G) (φ : M ⊞ P ≅ Rep.ofMulAction ℤ G G) (g : G)
    (x : ↥(M ⊞ P)) :
    phiAddEquiv M P φ ((M ⊞ P).ρ g x) = (Rep.ofMulAction ℤ G G).ρ g (phiAddEquiv M P φ x) :=
  Rep.hom_comm_apply φ.hom g x

/-! ## 6. 复合：`e : ↥M × ↥P ≃+ (G → ℤ)` 与等变性 -/

/-- 目标加法等价：`(m, p) ↦ (系数化 ∘ φ) (inl m + inr p) ∈ (G → ℤ)`。 -/
def eReg (M P : Rep ℤ G) (φ : M ⊞ P ≅ Rep.ofMulAction ℤ G G) : ↥M × ↥P ≃+ (G → ℤ) :=
  (biprodProdAddEquiv M P).trans ((phiAddEquiv M P φ).trans regularCarrierAddEquiv)

/-- `eReg` 的等变性（对积作用与 `instDistribMulActionRegularLattice`）。 -/
theorem eReg_equivariant (M P : Rep ℤ G) (φ : M ⊞ P ≅ Rep.ofMulAction ℤ G G) (g : G)
    (z : ↥M × ↥P) : eReg M P φ (g • z) = g • eReg M P φ z := by
  calc eReg M P φ (g • z)
      = regularCarrierAddEquiv (phiAddEquiv M P φ (biprodProdAddEquiv M P (g • z))) := rfl
    _ = regularCarrierAddEquiv
          (phiAddEquiv M P φ ((M ⊞ P).ρ g (biprodProdAddEquiv M P z))) := by
          rw [biprodProdAddEquiv_equivariant]
    _ = regularCarrierAddEquiv
          ((Rep.ofMulAction ℤ G G).ρ g (phiAddEquiv M P φ (biprodProdAddEquiv M P z))) := by
          rw [phiAddEquiv_rho]
    _ = g • regularCarrierAddEquiv (phiAddEquiv M P φ (biprodProdAddEquiv M P z)) := by
          rw [regularCarrierAddEquiv_equivariant]
    _ = g • eReg M P φ z := rfl

/-! ## 7. 正则子情形的 `IsStablyPermutation` 消费 -/

/-- 正则子情形的稳定置换谓词：`∃ P 置换格, L ⊕ P ≅ 正则格`。 -/
def IsStablyPermutationRegular (L : Rep ℤ G) : Prop :=
  ∃ P : Rep ℤ G, IsPermutationLattice G P ∧ Nonempty (L ⊞ P ≅ Rep.ofMulAction ℤ G G)

/-- 正则格是置换格（非空见证：`X = G` 左乘）。 -/
theorem isPermutationLattice_regular : IsPermutationLattice G (Rep.ofMulAction ℤ G G) :=
  ⟨G, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- 正则子情形 ⟹ `IsStablyPermutation`（取 `Q = 正则格`）。 -/
theorem IsStablyPermutationRegular.toIsStablyPermutation {L : Rep ℤ G}
    (h : IsStablyPermutationRegular L) : IsStablyPermutation G L := by
  obtain ⟨P, hP, ⟨φ⟩⟩ := h
  exact ⟨P, Rep.ofMulAction ℤ G G, hP, isPermutationLattice_regular, ⟨φ⟩⟩

/-- **主推论（正则子情形）**：`IsStablyPermutationRegular` ＋ `M` 侧忠实性、
`UniqueProds` ⟹ `F(M)^G` 稳定有理。与 `EMBridge` 主定理同结论，输入形为
`Rep` 层谓词（S3 数据与格等价 `e` 均在内部构造）。 -/
theorem isStablyRational_of_isStablyPermutationRegular
    {F : Type*} [Field F]
    (M : Rep ℤ G)
    [FaithfulSMul G ↥M] [UniqueProds (Multiplicative ↥M)]
    [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
    (h : IsStablyPermutationRegular M) :
    IsStablyRational F ↥(latticeInvariantsAlg F G ↥M) := by
  obtain ⟨P, hP, ⟨φ⟩⟩ := h
  obtain ⟨X, hX, hAct, B, ρ, hρ⟩ := RouteS.exists_permBasis_of_isPermutationLattice P hP
  letI : Fintype X := hX
  letI : MulAction G X := hAct
  haveI : UniqueProds (Multiplicative ↥P) := uniqueProds_multiplicative_carrier P B
  exact Bridge.isStablyRational_of_regularSubcase_bridged (F := F) (G := G) (M := ↥M) (P := ↥P)
    (hfaith := inferInstance) (B := B) (ρ := ρ) (hρ := hρ)
    (e := eReg M P φ) (he := eReg_equivariant M P φ)

/-! ## 8. 公理闸门 -/

#print axioms instSMulCommClassRepCarrier
#print axioms uniqueSums_carrier_of_basis
#print axioms uniqueProds_multiplicative_carrier
#print axioms biprod_inl_fst_apply
#print axioms biprod_inr_fst_apply
#print axioms biprod_inl_snd_apply
#print axioms biprod_inr_snd_apply
#print axioms biprod_total_apply
#print axioms biprodProdAddEquiv
#print axioms biprodProdAddEquiv_equivariant
#print axioms regularCarrierLinearEquiv
#print axioms regularCarrierAddEquiv
#print axioms regularCarrierAddEquiv_single
#print axioms regular_smul_single
#print axioms regularCarrierAddEquiv_equivariant
#print axioms phiAddEquiv
#print axioms phiAddEquiv_rho
#print axioms eReg
#print axioms eReg_equivariant
#print axioms isPermutationLattice_regular
#print axioms IsStablyPermutationRegular.toIsStablyPermutation
#print axioms isStablyRational_of_isStablyPermutationRegular

end

end Consume

end EM

end ABGV52
