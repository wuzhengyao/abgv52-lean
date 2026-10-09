/-
  ABGV-5.2 —— **本体形式化 A · M4c 度账链（EMDegree）**：`Esm = l(N)^G` 与 `IsRational` 收口

  目标（`wiki/proj-ABGV52-formalize-em.md` §3.4「度账最终链（定稿）」五步）：
    在 `EMFixed_ABGV52` 已有件（`K0`/`Esm`/`SlI`/`sup_eq_top`/`SlI_eq_adjoin_primitive`/
    `Esm_le_fixed`/`faithfulSMul_semiFunctionField`）之上完成：
      ① `adjoin ↥Esm {θ̃} = ⊤`（素元素 θ 的像；经 `adjoin_eq_top_of_adjoin_eq_top` 短路，
         不必逐例 Set 层 adjoin_induction）；
      ② `[l(N) : Esm] = |G|`（`adjoin.finrank` ＋ 纯整除 ≤-链，免等价搬运）；
      ③ `Esm = FixedPoints.subfield G l(N)`（Artin ＋ `finrank_dvd_of_le_left` ＋
         `eq_of_le_of_finrank_eq'`）。

  纪律：全具名参数；θ 一律 ∃-形就地 obtain；每步即刻重编译。
  **无 sorry、无自造公理**（交付时）。
-/
import ABGV52.EMFixed_ABGV52
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.AlgebraMap

namespace ABGV52
namespace EM

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]
variable {ι : Type*} [Fintype ι]

section Main
variable (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
variable (hρ : ∀ (σ : G) (i : ι),
  mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
variable (n : ℕ) (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
variable (hyfix : ∀ (i : Fin n) (σ : G),
  semiAlgEquiv (M := M) σ (y i).1 = (y i).1)
variable (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
variable [FaithfulSMul G (latticeFunctionField F M)]

/-! ## 1. adjoin 对齐与 `adjoin ↥Esm {θ̃} = ⊤` -/

/-- `adjoin ↥K₀ ↑Esm = Esm`（Esm 自身已是中间域，adjoin 幂等）。 -/
theorem adjoin_K0_coe_Esm :
    IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (Esm (G := G) (F := F) (M := M) (P := P) B n y :
        Set (semiFunctionField (F := F) (M := M) (P := P)))
      = Esm (G := G) (F := F) (M := M) (P := P) B n y := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr le_rfl) ?_
  exact IntermediateField.subset_adjoin
    (F := ↥(K0 (G := G) (F := F) (M := M) (P := P)))
    (S := (Esm (G := G) (F := F) (M := M) (P := P) B n y :
      Set (semiFunctionField (F := F) (M := M) (P := P))))

/-- **主引理**：`adjoin ↥K₀ (↑Esm ∪ {θ̃}) = ⊤`（θ̃ = `algebraMap l l(N) θ`，
由 `sup_eq_top`＋`SlI = adjoin ↥K₀ {θ̃}` 合成）。 -/
theorem adjoin_K0_Esm_union_eq_top
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (θ : latticeFunctionField F M)
    (hSlI : SlI (F := F) (M := M) (P := P)
      = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
          {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ}) :
    IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
      ((Esm (G := G) (F := F) (M := M) (P := P) B n y :
          Set (semiFunctionField (F := F) (M := M) (P := P)))
        ∪ {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ}) = ⊤ := by
  rw [IntermediateField.adjoin_union, adjoin_K0_coe_Esm, ← hSlI]
  exact sup_eq_top (B := B) (n := n) (y := y) (hy_span := hy_span)

/-- **`adjoin ↥Esm {θ̃} = ⊤`**（基变更：把 `adjoin ↥K₀ (↑Esm ∪ {θ̃}) = ⊤`
沿 `adjoin_eq_top_of_adjoin_eq_top` 降到 ↥Esm 基，再对齐集合）。 -/
theorem adjoin_Esm_singleton_eq_top
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (θ : latticeFunctionField F M)
    (hSlI : SlI (F := F) (M := M) (P := P)
      = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
          {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ}) :
    IntermediateField.adjoin ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      {algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ} = ⊤ := by
  have hprim := adjoin_K0_Esm_union_eq_top (G := G) (F := F) (M := M) (P := P)
    (B := B) (n := n) (y := y) (hy_span := hy_span) θ hSlI
  have hprim' := IntermediateField.adjoin_eq_top_of_adjoin_eq_top
    (F := ↥(K0 (G := G) (F := F) (M := M) (P := P)))
    (E := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
    (S := ((Esm (G := G) (F := F) (M := M) (P := P) B n y :
        Set (semiFunctionField (F := F) (M := M) (P := P)))
      ∪ {algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ})) hprim
  have hEq : IntermediateField.adjoin
        ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        ((Esm (G := G) (F := F) (M := M) (P := P) B n y :
            Set (semiFunctionField (F := F) (M := M) (P := P)))
          ∪ {algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)) θ})
      = IntermediateField.adjoin
        ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        {algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ} := by
    refine le_antisymm ?_ ?_
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      intro z hz
      rcases hz with hz | hz
      · exact IntermediateField.algebraMap_mem
          (IntermediateField.adjoin
            ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
            {algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)) θ})
          (⟨z, hz⟩ : ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact IntermediateField.subset_adjoin
          (F := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
          (S := {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ})
          (Set.mem_singleton _)
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      intro z hz
      exact IntermediateField.subset_adjoin
        (F := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
        (S := ((Esm (G := G) (F := F) (M := M) (P := P) B n y :
            Set (semiFunctionField (F := F) (M := M) (P := P)))
          ∪ {algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)) θ}))
        (Or.inr hz)
  rw [← hEq]
  exact hprim'

/-! ## 2. 桥 `↥l^G →+* ↥K₀` 与第二比较（K₀ ← l^G） -/

/-- 手搭环同态 `↥l^G →+* ↥K₀`（`c ↦ algebraMap l l(N) c`；落点在
`K₀ = (l^G).map (algebraMap l l(N))` 内）。 -/
noncomputable def lGToK0 :
    ↥(FixedPoints.subfield G (latticeFunctionField F M)) →+*
      ↥(K0 (G := G) (F := F) (M := M) (P := P)) where
  toFun c := ⟨algebraMap (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P)) (c : latticeFunctionField F M),
    (by
      rw [show K0 (G := G) (F := F) (M := M) (P := P)
          = (FixedPoints.subfield G (latticeFunctionField F M)).map
            (algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P))) from rfl]
      exact Subfield.mem_map.mpr ⟨(c : latticeFunctionField F M), c.2, rfl⟩)⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- 兼容性：`algebraMap ↥K₀ l(N) (lGToK0 c) = algebraMap l l(N) c`。 -/
lemma lGToK0_coe (c : ↥(FixedPoints.subfield G (latticeFunctionField F M))) :
    algebraMap ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (semiFunctionField (F := F) (M := M) (P := P))
      (lGToK0 (G := G) (F := F) (M := M) (P := P) c)
      = algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) (c : latticeFunctionField F M) :=
  rfl

set_option maxHeartbeats 400000 in
/-- **第二比较（K₀ ← l^G）**：`minpoly ↥K₀ θ̃ ∣ (minpoly ↥l^G θ).map (lGToK0 ·)`。
经 `map_aeval_eq_aeval_map`（R := ↥l^G，S := l，T := ↥K₀，U := l(N)，
φ := lGToK0，ψ := algebraMap l l(N)；交换性 = `lGToK0_coe`）。 -/
theorem minpoly_K0_dvd_minpoly_lG (θ : latticeFunctionField F M) :
    minpoly ↥(K0 (G := G) (F := F) (M := M) (P := P))
        (algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ)
      ∣ (minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ).map
          (lGToK0 (G := G) (F := F) (M := M) (P := P)) := by
  refine minpoly.dvd (A := ↥(K0 (G := G) (F := F) (M := M) (P := P)))
    (x := algebraMap (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P)) θ) ?_
  rw [← Polynomial.map_aeval_eq_aeval_map
    (R := ↥(FixedPoints.subfield G (latticeFunctionField F M)))
    (S := latticeFunctionField F M)
    (T := ↥(K0 (G := G) (F := F) (M := M) (P := P)))
    (U := semiFunctionField (F := F) (M := M) (P := P))
    (φ := lGToK0 (G := G) (F := F) (M := M) (P := P))
    (ψ := algebraMap (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P)))
    (RingHom.ext fun c => lGToK0_coe (F := F) (M := M) (P := P) c)
    (minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ) θ]
  rw [minpoly.aeval, map_zero]

/-! ## 3. 整性与度账 ≤-链 -/

/-- `θ` 在 `↥l^G` 上整（`FixedPoints.isIntegral`，任意元素）。 -/
theorem isIntegral_lG (θ : latticeFunctionField F M) :
    IsIntegral ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ :=
  FixedPoints.isIntegral (G := G) (F := latticeFunctionField F M) θ

/-- `θ̃` 在 `↥K₀` 上整（第二比较 ＋ monic）。 -/
theorem isIntegral_K0 (θ : latticeFunctionField F M) :
    IsIntegral ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ) :=
  ⟨(minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ).map
      (lGToK0 (G := G) (F := F) (M := M) (P := P)),
    Polynomial.Monic.map (lGToK0 (G := G) (F := F) (M := M) (P := P))
      (minpoly.monic (isIntegral_lG (G := G) (F := F) (M := M) θ)),
    (minpoly.dvd_iff (A := ↥(K0 (G := G) (F := F) (M := M) (P := P)))
      (x := algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ)).mp
      (minpoly_K0_dvd_minpoly_lG (F := F) (M := M) θ)⟩

/-- `θ̃` 在 `↥Esm` 上整（`IsIntegral.tower_top`）。 -/
theorem isIntegral_Esm (θ : latticeFunctionField F M) :
    IsIntegral ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      (algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ) :=
  IsIntegral.tower_top
    (A := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
    (isIntegral_K0 (G := G) (F := F) (M := M) (P := P) θ)

set_option maxHeartbeats 800000 in
/-- **`[l(N) : Esm] = (minpoly ↥Esm θ̃).natDegree`**（`adjoin.finrank` ＋
`adjoin ↥Esm {θ̃} = ⊤`）。 -/
theorem finrank_Esm_eq_natDegree_minpoly
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (θ : latticeFunctionField F M)
    (hSlI : SlI (F := F) (M := M) (P := P)
      = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
          {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ}) :
    Module.finrank ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        (semiFunctionField (F := F) (M := M) (P := P))
      = (minpoly ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
          (algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree := by
  have hTop := adjoin_Esm_singleton_eq_top (G := G) (F := F) (M := M) (P := P)
    (B := B) (n := n) (y := y) hy_span θ hSlI
  calc Module.finrank ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        (semiFunctionField (F := F) (M := M) (P := P))
      = Module.finrank ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
          ↥(IntermediateField.adjoin
            ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
            {algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)) θ}) := by
        rw [hTop]
        exact (IntermediateField.finrank_top'
          (F := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))).symm
    _ = (minpoly ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
          (algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree :=
        IntermediateField.adjoin.finrank
          (isIntegral_Esm (G := G) (F := F) (M := M) (P := P)
            (B := B) (n := n) (y := y) θ)

/-- **第一比较（Esm ← K₀）**：
`minpoly ↥Esm θ̃ ∣ (minpoly ↥K₀ θ̃).map (algebraMap ↥K₀ ↥Esm)`。 -/
theorem minpoly_Esm_dvd_minpoly_K0 (θ : latticeFunctionField F M) :
    minpoly ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        (algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ)
      ∣ (minpoly ↥(K0 (G := G) (F := F) (M := M) (P := P))
          (algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ)).map
          (algebraMap ↥(K0 (G := G) (F := F) (M := M) (P := P))
            ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)) :=
  minpoly.dvd_map_of_isScalarTower ↥(K0 (G := G) (F := F) (M := M) (P := P))
    ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
    (algebraMap (latticeFunctionField F M)
      (semiFunctionField (F := F) (M := M) (P := P)) θ)

/-- 度账 ≤-链第一段：`natDegree(minpoly ↥Esm θ̃) ≤ natDegree(minpoly ↥K₀ θ̃)`。 -/
theorem natDegree_minpoly_Esm_le_K0 (θ : latticeFunctionField F M) :
    (minpoly ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      (algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree
      ≤ (minpoly ↥(K0 (G := G) (F := F) (M := M) (P := P))
        (algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree := by
  have hne : ((minpoly ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ)).map
      (algebraMap ↥(K0 (G := G) (F := F) (M := M) (P := P))
        ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (isIntegral_K0 (F := F) (M := M) θ))
  have hle := Polynomial.natDegree_le_of_dvd
    (minpoly_Esm_dvd_minpoly_K0 (G := G) (F := F) (M := M) (P := P)
      (B := B) (n := n) (y := y) θ) hne
  simpa only [Polynomial.natDegree_map] using hle

/-- 度账 ≤-链第二段：`natDegree(minpoly ↥K₀ θ̃) ≤ natDegree(minpoly ↥l^G θ)`。 -/
theorem natDegree_minpoly_K0_le_lG (θ : latticeFunctionField F M) :
    (minpoly ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (algebraMap (latticeFunctionField F M)
        (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree
      ≤ (minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ).natDegree := by
  have hne : ((minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ).map
      (lGToK0 (G := G) (F := F) (M := M) (P := P))) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (isIntegral_lG (G := G) (F := F) (M := M) θ))
  have hle := Polynomial.natDegree_le_of_dvd
    (minpoly_K0_dvd_minpoly_lG (F := F) (M := M) θ) hne
  simpa only [Polynomial.natDegree_map] using hle

/-- `natDegree (minpoly ↥l^G θ) = |G|`（`adjoin.finrank` ＋ Artin）。 -/
theorem natDegree_minpoly_lG_eq_card (θ : latticeFunctionField F M)
    (hθ : IntermediateField.adjoin
        ↥(FixedPoints.subfield G (latticeFunctionField F M)) {θ} = ⊤) :
    (minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ).natDegree
      = Fintype.card G := by
  have h := IntermediateField.adjoin.finrank
    (isIntegral_lG (G := G) (F := F) (M := M) θ)
  rw [hθ, IntermediateField.finrank_top'] at h
  rw [← h]
  exact FixedPoints.finrank_eq_card (G := G) (F := latticeFunctionField F M)

set_option maxHeartbeats 800000 in
/-- **度账主链**：`[l(N) : Esm] ≤ |G|`。 -/
theorem finrank_Esm_le_card
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (θ : latticeFunctionField F M)
    (hSlI : SlI (F := F) (M := M) (P := P)
      = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
          {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ})
    (hθ : IntermediateField.adjoin
        ↥(FixedPoints.subfield G (latticeFunctionField F M)) {θ} = ⊤) :
    Module.finrank ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      (semiFunctionField (F := F) (M := M) (P := P)) ≤ Fintype.card G := by
  rw [finrank_Esm_eq_natDegree_minpoly (G := G) (F := F) (M := M) (P := P)
    (B := B) (n := n) (y := y) hy_span θ hSlI]
  calc (minpoly ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        (algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree
      ≤ (minpoly ↥(K0 (G := G) (F := F) (M := M) (P := P))
        (algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ)).natDegree :=
        natDegree_minpoly_Esm_le_K0 (G := G) (F := F) (M := M) (P := P)
          (B := B) (n := n) (y := y) θ
    _ ≤ (minpoly ↥(FixedPoints.subfield G (latticeFunctionField F M)) θ).natDegree :=
        natDegree_minpoly_K0_le_lG (F := F) (M := M) θ
    _ = Fintype.card G := natDegree_minpoly_lG_eq_card (F := F) (M := M) θ hθ

/-! ## 4. 收口：`Esm = l(N)^G` -/

/-- `l(N)^G` 作为 `↥K₀`-中间域（载体定义性等于 `FixedPoints.subfield G l(N)`，
故 `↥lNG` 与 `↥(l(N)^G)` 定义性同型——度账搬运用）。 -/
noncomputable def lNG : IntermediateField ↥(K0 (G := G) (F := F) (M := M) (P := P))
    (semiFunctionField (F := F) (M := M) (P := P)) where
  carrier := (FixedPoints.subfield G
    (semiFunctionField (F := F) (M := M) (P := P)) : Set _)
  mul_mem' := fun ha hb => Subring.mul_mem
    (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))).toSubring ha hb
  add_mem' := fun ha hb => Subring.add_mem
    (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))).toSubring ha hb
  algebraMap_mem' := fun x => K0_mem_fixed (F := F) (M := M) (P := P) x.2
  inv_mem' := fun _ ha => (FixedPoints.subfield G
    (semiFunctionField (F := F) (M := M) (P := P))).inv_mem ha

set_option linter.style.haveILetI false in
set_option maxHeartbeats 800000 in
/-- **度账收口（M4c 主定理）**：`Esm = l(N)^G`（集合层）。
证明：`Esm ≤ l(N)^G`（`Esm_le_fixed`）；`[l(N) : Esm] ≤ |G|`（主链）；
`|G| = [l(N) : l(N)^G] ∣ [l(N) : Esm]`（`finrank_dvd_of_le_left`）⟹ 等号；
`eq_of_le_of_finrank_eq'` 收口。 -/
theorem Esm_eq_fixedPoints
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
    (hyfix : ∀ (i : Fin n) (σ : G),
      semiAlgEquiv (M := M) σ (y i).1 = (y i).1)
    (θ : latticeFunctionField F M)
    (hSlI : SlI (F := F) (M := M) (P := P)
      = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
          {algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) θ})
    (hθ : IntermediateField.adjoin
        ↥(FixedPoints.subfield G (latticeFunctionField F M)) {θ} = ⊤) :
    (Esm (G := G) (F := F) (M := M) (P := P) B n y :
        Set (semiFunctionField (F := F) (M := M) (P := P)))
      = (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) :
        Set (semiFunctionField (F := F) (M := M) (P := P))) := by
  haveI hfaithN : FaithfulSMul G (semiFunctionField (F := F) (M := M) (P := P)) :=
    faithfulSMul_semiFunctionField (F := F) (M := M) (P := P)
      (inferInstance : FaithfulSMul G (latticeFunctionField F M))
  have hdeg := finrank_Esm_le_card (G := G) (F := F) (M := M) (P := P)
    (B := B) (n := n) (y := y) hy_span θ hSlI hθ
  have hTop := adjoin_Esm_singleton_eq_top (G := G) (F := F) (M := M) (P := P)
    (B := B) (n := n) (y := y) hy_span θ hSlI
  haveI hFD₁ : FiniteDimensional ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      ↥(IntermediateField.adjoin
        ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        {algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) θ}) :=
    IntermediateField.adjoin.finiteDimensional
      (isIntegral_Esm (G := G) (F := F) (M := M) (P := P) (B := B) (n := n) (y := y) θ)
  haveI hFD₂ : FiniteDimensional ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      ↥(⊤ : IntermediateField
        ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
        (semiFunctionField (F := F) (M := M) (P := P))) :=
    hTop ▸ hFD₁
  haveI : FiniteDimensional ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      (semiFunctionField (F := F) (M := M) (P := P)) :=
    FiniteDimensional.of_surjective
      ((IntermediateField.topEquiv
        (F := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
        (E := semiFunctionField (F := F) (M := M) (P := P))).toLinearMap)
      (IntermediateField.topEquiv
        (F := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
        (E := semiFunctionField (F := F) (M := M) (P := P))).surjective
  have hle : Esm (G := G) (F := F) (M := M) (P := P) B n y
      ≤ lNG (G := G) (F := F) (M := M) (P := P) := by
    show (Esm (G := G) (F := F) (M := M) (P := P) B n y :
        Set (semiFunctionField (F := F) (M := M) (P := P)))
      ⊆ (lNG (G := G) (F := F) (M := M) (P := P) :
        Set (semiFunctionField (F := F) (M := M) (P := P)))
    exact Esm_le_fixed (G := G) (F := F) (M := M) (P := P)
      (B := B) (n := n) (y := y) (hyfix := hyfix)
  have hfin_lNG : Module.finrank ↥(lNG (G := G) (F := F) (M := M) (P := P))
      (semiFunctionField (F := F) (M := M) (P := P)) = Fintype.card G :=
    FixedPoints.finrank_eq_card (G := G)
      (F := semiFunctionField (F := F) (M := M) (P := P))
  have hdvd : Fintype.card G ∣ Module.finrank
      ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      (semiFunctionField (F := F) (M := M) (P := P)) := by
    have h₁ : Module.finrank ↥(lNG (G := G) (F := F) (M := M) (P := P))
        (semiFunctionField (F := F) (M := M) (P := P))
        ∣ Module.finrank ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
          (semiFunctionField (F := F) (M := M) (P := P)) :=
      IntermediateField.finrank_dvd_of_le_left hle
    rwa [hfin_lNG] at h₁
  have hfe : Module.finrank ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y)
      (semiFunctionField (F := F) (M := M) (P := P)) = Fintype.card G :=
    Nat.le_antisymm hdeg (Nat.le_of_dvd
      (Module.finrank_pos (R := ↥(Esm (G := G) (F := F) (M := M) (P := P) B n y))
        (M := semiFunctionField (F := F) (M := M) (P := P))) hdvd)
  have heq : Esm (G := G) (F := F) (M := M) (P := P) B n y
      = lNG (G := G) (F := F) (M := M) (P := P) := by
    refine IntermediateField.eq_of_le_of_finrank_eq' hle ?_
    rw [hfin_lNG]
    exact hfe
  change (Esm (G := G) (F := F) (M := M) (P := P) B n y :
      Set (semiFunctionField (F := F) (M := M) (P := P)))
    = (lNG (G := G) (F := F) (M := M) (P := P) :
      Set (semiFunctionField (F := F) (M := M) (P := P)))
  rw [heq]

end Main

/-! ## 6. 公理闸门 -/

#print axioms adjoin_K0_coe_Esm
#print axioms adjoin_K0_Esm_union_eq_top
#print axioms adjoin_Esm_singleton_eq_top
#print axioms lGToK0
#print axioms lGToK0_coe
#print axioms minpoly_K0_dvd_minpoly_lG
#print axioms isIntegral_lG
#print axioms isIntegral_K0
#print axioms isIntegral_Esm
#print axioms minpoly_Esm_dvd_minpoly_K0
#print axioms natDegree_minpoly_Esm_le_K0
#print axioms natDegree_minpoly_K0_le_lG
#print axioms natDegree_minpoly_lG_eq_card
#print axioms finrank_Esm_eq_natDegree_minpoly
#print axioms finrank_Esm_le_card
#print axioms lNG
#print axioms Esm_eq_fixedPoints

end EM
end ABGV52
