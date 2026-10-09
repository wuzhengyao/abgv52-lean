/-
  ABGV-5.2 —— C 档 · M6-B（1β-general 单项式格层）

  内容（设计件 wiki/proj-ABGV52-M6-1beta-general-design.md §4.2 步 3–4 / §6 M6-B 行）：

    * §1 单项式代入 `monoSubst`（`MvPolynomial ι F →ₐ[F] F(Q)`，`X_i ↦ x^{e_i}`）
         及其单射性 ⟹ mono 族代数无关（`algIndep_mono`）；
    * §2 生成引理：被置换基的单项式族生成 `F(Q)`（`adjoin_range_mono_eq_top`）；
         Y-族（M6-A 的特征基）经基变换展开亦生成 `F(Q)`（`adjoin_range_Y_eq_top`）；
    * §3 trdeg 三明治：`#ι ≤ trdeg ≤ #ι`（`card_le_trdeg`／`trdeg_le_card`）
         ⟹ Y-族代数无关（`algebraicIndependent_Y`）与超越基性（`isTranscendenceBasis_Y`）；
    * §4 φ-层：字数特征 `yCharOf` 与 kernel 格 `yKernel`（有限指数 ≤ |G|：
         `yKernel_index_le_card`）；
    * §5 不变量域等式：`latticeInvariants F G Q = adjoin F (yPow '' yKernel)`
         （`latticeInvariants_eq_adjoin_yPow`）。

  关键机制（免逆 DFT）：W 的任何 F-基都生成整域（基变换 ⟹ `F(y's) ⊇ F(x^{e_x}) = F(Q)`），
  配合 `trdeg = #ι` 直接得代数无关；上界 `trdeg ≤ #ι` 经直接构造
  `Algebra.IsAlgebraic ↥(Algebra.adjoin F (range mono)) (F(Q))` 实例（`mem_adjoin_iff_div`
  ＋ 显式多项式见证 `C s · X - C r`）后由 `trdeg_le_cardinalMk` 得出。

  纪律：无 sorry／无自造公理；不改任何既有文件（含 M6-A 件）；每节过后编译。
-/
import ABGV52.EM1betaGen_basis_ABGV52
import ABGV52.EMFixed_ABGV52
import ABGV52.EMIndep_ABGV52
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

open scoped Classical Cardinal

namespace ABGV52

namespace EM

set_option maxHeartbeats 800000

universe u

variable (F : Type u) [Field F]
variable (G : Type u) [CommGroup G] [Fintype G]
variable (Q : Type u) [AddCommGroup Q] [Module ℤ Q] [DistribMulAction G Q]
  [SMulCommClass G ℤ Q] [UniqueProds (Multiplicative Q)]
variable (ι : Type u) [Fintype ι]
variable (B : Module.Basis ι ℤ Q)

/-! ## 1. 单项式代入与代数无关性 -/

/-- 指数 → 幂积（乘法群层提升）：`d ↦ monoPow B d`。 -/
noncomputable def monoPowHom : Multiplicative (ι →₀ ℕ) →* Multiplicative Q where
  toFun d := monoPow (P := Q) B d.toAdd
  map_one' := by
    show monoPow (P := Q) B (0 : ι →₀ ℕ) = 1
    rw [monoPow, Finsupp.prod_zero_index]
  map_mul' d₁ d₂ := by
    show monoPow (P := Q) B (d₁.toAdd + d₂.toAdd)
      = monoPow (P := Q) B d₁.toAdd * monoPow (P := Q) B d₂.toAdd
    rw [monoPow_add]

/-- `monoPowHom` 单射（指数无关性在幂积层的形态）。 -/
theorem monoPowHom_injective : Function.Injective (monoPowHom Q ι B) := by
  intro d₁ d₂ h
  have h' : monoPow (P := Q) B d₁.toAdd = monoPow (P := Q) B d₂.toAdd := h
  have h2 : d₁.toAdd = d₂.toAdd := monoPow_injective (P := Q) B h'
  have h3 : Multiplicative.ofAdd d₁.toAdd = Multiplicative.ofAdd d₂.toAdd :=
    congrArg Multiplicative.ofAdd h2
  simpa [ofAdd_toAdd] using h3

/-- **单项式代入（代数层）**：`X_i ↦ x^{e_i}`（`MvPolynomial ι F →ₐ[F] F[Q]`）。 -/
noncomputable def monoSubstAlg : MvPolynomial ι F →ₐ[F] latticeAlgebra F Q :=
  (MonoidAlgebra.mapDomainAlgHom F F (monoPowHom Q ι B)).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (ι →₀ ℕ)).toAlgHom

lemma monoSubstAlg_apply (p : MvPolynomial ι F) :
    monoSubstAlg F Q ι B p
      = MonoidAlgebra.mapDomain (⇑(monoPowHom Q ι B))
          (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (ι →₀ ℕ) p) := rfl

/-- 单项式的像：`monomial s c ↦ c · x^s`。 -/
theorem monoSubstAlg_monomial (s : ι →₀ ℕ) (c : F) :
    monoSubstAlg F Q ι B (MvPolynomial.monomial s c)
      = MonoidAlgebra.single (monoPow (P := Q) B s) c := by
  rw [monoSubstAlg_apply, (MvPolynomial.single_eq_monomial s c).symm,
    AddMonoidAlgebra.toMultiplicativeAlgEquiv_single, MonoidAlgebra.mapDomain_single]
  rfl

/-- 变量像：`X_i ↦ x^{e_i} = mono i`（代数层）。 -/
theorem monoSubstAlg_X (i : ι) :
    monoSubstAlg F Q ι B (MvPolynomial.X i)
      = MonoidAlgebra.single (permMono (P := Q) B i) (1 : F) := by
  rw [show MvPolynomial.X i = MvPolynomial.monomial (Finsupp.single i 1) (1 : F) from rfl,
    monoSubstAlg_monomial, monoPow_single, pow_one]

/-- `monoSubstAlg` 单射（`mapDomain` 保单项式单射 ＋ 指数嵌入单射）。 -/
theorem monoSubstAlg_injective : Function.Injective (monoSubstAlg F Q ι B) := by
  have h1 : Function.Injective (fun p : MvPolynomial ι F =>
      MonoidAlgebra.mapDomain (⇑(monoPowHom Q ι B))
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (ι →₀ ℕ) p)) :=
    (MonoidAlgebra.mapDomain_injective (monoPowHom_injective Q ι B)).comp
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv F F (ι →₀ ℕ)).injective
  intro x y h
  exact h1 h

/-- **单项式代入（分式域层）**：`F[X_i] →ₐ[F] F(Q)`。 -/
noncomputable def monoSubst : MvPolynomial ι F →ₐ[F] latticeFunctionField F Q :=
  (IsScalarTower.toAlgHom F (latticeAlgebra F Q) (latticeFunctionField F Q)).comp
    (monoSubstAlg F Q ι B)

lemma monoSubst_apply (p : MvPolynomial ι F) :
    monoSubst F Q ι B p
      = algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q)
          (monoSubstAlg F Q ι B p) := rfl

theorem monoSubst_X (i : ι) :
    monoSubst F Q ι B (MvPolynomial.X i) = mono F Q ι B i := by
  rw [monoSubst_apply, monoSubstAlg_X]
  rfl

/-- `monoSubst` 单射（`IsFractionRing.injective` 复合 `monoSubstAlg_injective`）。 -/
theorem monoSubst_injective : Function.Injective (monoSubst F Q ι B) := by
  intro x y h
  apply monoSubstAlg_injective F Q ι B
  apply IsFractionRing.injective (latticeAlgebra F Q) (latticeFunctionField F Q)
  exact h

/-- **代数无关性（mono 族）**：`{x^{e_i}}` 在 `F(Q)` 上代数无关（代入单射 ⟺ 代数无关）。 -/
theorem algIndep_mono : AlgebraicIndependent F (mono F Q ι B) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have haev : MvPolynomial.aeval (mono F Q ι B) = monoSubst F Q ι B := by
    rw [MvPolynomial.aeval_unique (monoSubst F Q ι B)]
    congr 1
    funext i
    exact (monoSubst_X F Q ι B i).symm
  rw [haev]
  exact monoSubst_injective F Q ι B

/-! ## 2. 生成引理 -/

/-- 单项式生成元（乘法群层）：`m ↦ algebraMap (single m 1)`。 -/
noncomputable def hmonoGen : Multiplicative Q →* latticeFunctionField F Q where
  toFun m := algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q)
    (MonoidAlgebra.single m (1 : F))
  map_one' := by
    rw [← MonoidAlgebra.one_def, map_one]
  map_mul' m₁ m₂ := by
    rw [← map_mul, MonoidAlgebra.single_mul_single, mul_one]

/-- `hmonoGen` 在基元上的取值回归 `mono`。 -/
theorem hmonoGen_permMono (i : ι) :
    hmonoGen F Q (permMono (P := Q) B i) = mono F Q ι B i := rfl

/-- **生成引理（mono 族）**：任意被置换基的单项式族生成整域 `F(Q)`。

  证明链：单基因元 `hmonoGen m` 经 `permMono_prod_expansion` 展开为幂积；
  经 `MonoidAlgebra.induction_on` 抬到整个 `F[Q]`；经 `div_surjective` 抬到分式域。 -/
theorem adjoin_range_mono_eq_top :
    IntermediateField.adjoin F (Set.range (mono F Q ι B)) = ⊤ := by
  have hmem : ∀ a : latticeAlgebra F Q,
      (algebraMap (latticeAlgebra F Q) (latticeFunctionField F Q) a)
        ∈ (IntermediateField.adjoin F (Set.range (mono F Q ι B))) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.of_apply]
        change hmonoGen F Q m
          ∈ (IntermediateField.adjoin F (Set.range (mono F Q ι B)))
        have hexp := permMono_prod_expansion (P := Q) B ((B.repr) m.toAdd)
        rw [LinearEquiv.symm_apply_apply, ofAdd_toAdd] at hexp
        rw [hexp, show ((B.repr) m.toAdd).prod (fun j n => (permMono (P := Q) B j) ^ n)
            = ((B.repr) m.toAdd).support.prod
                (fun j => (permMono (P := Q) B j) ^ (((B.repr) m.toAdd) j)) from rfl,
          map_prod]
        refine IntermediateField.prod_mem
          (S := IntermediateField.adjoin F (Set.range (mono F Q ι B))) ?_
        intro j _
        rw [MonoidHom.map_zpow, hmonoGen_permMono]
        exact IntermediateField.pow_mem
          (S := IntermediateField.adjoin F (Set.range (mono F Q ι B)))
          (IntermediateField.subset_adjoin F (Set.range (mono F Q ι B)) ⟨j, rfl⟩)
          (((B.repr) m.toAdd) j)
    | add x ys hx hy =>
        rw [map_add]
        exact add_mem hx hy
    | smul r x hx =>
        rw [Algebra.smul_def, map_mul]
        refine mul_mem ?_ hx
        rw [← IsScalarTower.algebraMap_apply F (latticeAlgebra F Q) (latticeFunctionField F Q)]
        exact IntermediateField.algebraMap_mem
          (IntermediateField.adjoin F (Set.range (mono F Q ι B))) r
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, hzab⟩ := IsFractionRing.div_surjective (A := latticeAlgebra F Q) z
  rw [← hzab]
  exact div_mem (hmem a) (hmem b)

section Chars

variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
variable (κ : G →* Equiv.Perm ι)

/-- **生成引理（Y-族）**：M6-A 的特征基生成整域 `F(Q)`（`mono i` 经 `YBasis` 展开为 Y-组合）。 -/
theorem adjoin_range_Y_eq_top
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    IntermediateField.adjoin F (Set.range (Y F G Q ι B κ)) = ⊤ := by
  rw [eq_top_iff, ← adjoin_range_mono_eq_top F Q ι B]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x ⟨i, rfl⟩
  have hmono_expand : mono F Q ι B i
      = ∑ p : Idx F G ι κ, ((YBasis F G Q ι B κ).repr (monoSub F Q ι B i)) p
          • Y F G Q ι B κ p := by
    have hrepr := congrArg (fun w : ↥(Wb F Q ι B) => (w : latticeFunctionField F Q))
      (Module.Basis.sum_repr (YBasis F G Q ι B κ) (monoSub F Q ι B i))
    have hcoe : ((∑ p : Idx F G ι κ,
        ((YBasis F G Q ι B κ).repr (monoSub F Q ι B i)) p
          • YBasis F G Q ι B κ p : ↥(Wb F Q ι B)) : latticeFunctionField F Q)
        = ∑ p : Idx F G ι κ, ((YBasis F G Q ι B κ).repr (monoSub F Q ι B i)) p
            • Y F G Q ι B κ p := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Submodule.coe_smul, YBasis_apply, ← Y_coe]
    exact hrepr.symm.trans hcoe
  rw [hmono_expand]
  refine IntermediateField.sum_mem
    (S := IntermediateField.adjoin F (Set.range (Y F G Q ι B κ))) ?_
  intro p _
  rw [Algebra.smul_def]
  exact mul_mem (IntermediateField.algebraMap_mem
      (IntermediateField.adjoin F (Set.range (Y F G Q ι B κ)))
      (((YBasis F G Q ι B κ).repr (monoSub F Q ι B i)) p))
    (IntermediateField.subset_adjoin F (Set.range (Y F G Q ι B κ)) ⟨p, rfl⟩)

end Chars

/-! ## 3. trdeg 三明治与 Y-族的代数无关性 -/

/-- 直接构造 `Algebra.IsAlgebraic ↥(Algebra.adjoin F S) F(Q)` 实例：
  任意 `z ∈ adjoin F S` 写成 `r / s`（`mem_adjoin_iff_div`），
  取多项式见证 `s·X - r`（`s ≠ 0`）或 `X`（`s = 0` ⟹ `z = 0`）。 -/
theorem isAlgebraic_of_adjoin_eq_top (S : Set (latticeFunctionField F Q))
    (hS : IntermediateField.adjoin F S = ⊤) :
    Algebra.IsAlgebraic ↥(Algebra.adjoin F S) (latticeFunctionField F Q) := by
  haveI : Nontrivial ↥(Algebra.adjoin F S) :=
    ⟨⟨1, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  refine ⟨fun z => ?_⟩
  have hz : z ∈ IntermediateField.adjoin F S := by
    rw [hS]
    trivial
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    (IntermediateField.mem_adjoin_iff_div (F := F) (S := S)).mp hz
  by_cases hs0 : s = 0
  · refine ⟨Polynomial.X, Polynomial.X_ne_zero, ?_⟩
    rw [Polynomial.aeval_X]
    rw [hs0, div_zero] at hrs
    exact hrs
  · refine ⟨Polynomial.C ⟨s, hs⟩ * Polynomial.X - Polynomial.C ⟨r, hr⟩, ?_, ?_⟩
    · intro hp
      have hc := congrArg (fun q : Polynomial ↥(Algebra.adjoin F S) => q.coeff 1) hp
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X] at hc
      simp at hc
      exact hs0 (congrArg Subtype.val hc)
    · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
      have h1 : algebraMap ↥(Algebra.adjoin F S) (latticeFunctionField F Q)
          ⟨s, hs⟩ = s := rfl
      have h2 : algebraMap ↥(Algebra.adjoin F S) (latticeFunctionField F Q)
          ⟨r, hr⟩ = r := rfl
      rw [h1, h2, hrs, mul_div_cancel₀ r hs0, sub_self]

/-- `Algebra.IsAlgebraic` 实例（mono 族）：经生成引理 `adjoin_range_mono_eq_top`。 -/
theorem isAlgebraic_algebraAdjoin_mono :
    Algebra.IsAlgebraic ↥(Algebra.adjoin F (Set.range (mono F Q ι B)))
      (latticeFunctionField F Q) :=
  isAlgebraic_of_adjoin_eq_top F Q (Set.range (mono F Q ι B))
    (adjoin_range_mono_eq_top F Q ι B)

include B in
/-- **trdeg 上界**：`trdeg F(Q) ≤ #ι`（`trdeg_le_cardinalMk` ＋ `#(range mono) ≤ #ι`）。 -/
theorem trdeg_le_card :
    Algebra.trdeg F (latticeFunctionField F Q) ≤ (Fintype.card ι : Cardinal) := by
  haveI := isAlgebraic_algebraAdjoin_mono F Q ι B
  calc Algebra.trdeg F (latticeFunctionField F Q)
      ≤ Cardinal.mk (Set.range (mono F Q ι B)) :=
        Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := F) (s := Set.range (mono F Q ι B))
    _ ≤ Cardinal.mk ι := Cardinal.mk_range_le
    _ = (Fintype.card ι : Cardinal) := Cardinal.mk_fintype ι

include B in
/-- **trdeg 下界**：`#ι ≤ trdeg F(Q)`（mono 族代数无关）。 -/
theorem card_le_trdeg :
    (Fintype.card ι : Cardinal) ≤ Algebra.trdeg F (latticeFunctionField F Q) := by
  have h := AlgebraicIndependent.cardinalMk_le_trdeg (algIndep_mono F Q ι B)
  simpa [Cardinal.mk_fintype] using h

include ι B in
/-- trdeg 有限（`trdeg ≤ #ι < ℵ₀`）。 -/
theorem trdeg_lt_aleph0 :
    Algebra.trdeg F (latticeFunctionField F Q) < ℵ₀ :=
  lt_of_le_of_lt (trdeg_le_card F Q ι B) Cardinal.natCast_lt_aleph0

include B in
/-- **trdeg 定值**：`trdeg F(Q) = #ι`（三明治收口）。 -/
theorem trdeg_eq_card :
    Algebra.trdeg F (latticeFunctionField F Q) = (Fintype.card ι : Cardinal) :=
  le_antisymm (trdeg_le_card F Q ι B) (card_le_trdeg F Q ι B)

section Chars2

variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
variable (κ : G →* Equiv.Perm ι)

/-- `Algebra.IsAlgebraic` 实例（Y-族）：经生成引理 `adjoin_range_Y_eq_top`。 -/
theorem isAlgebraic_algebraAdjoin_Y
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    Algebra.IsAlgebraic ↥(Algebra.adjoin F (Set.range (Y F G Q ι B κ)))
      (latticeFunctionField F Q) :=
  isAlgebraic_of_adjoin_eq_top F Q (Set.range (Y F G Q ι B κ))
    (adjoin_range_Y_eq_top F G Q ι B κ hκ)

/-- **Y-族的超越基性**：`#(Idx) = #ι ≤ trdeg` ＋ 有限性 ⟹ `Y` 是超越基
（`isTranscendenceBasis_of_le_trdeg`）。 -/
theorem isTranscendenceBasis_Y
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    IsTranscendenceBasis F (Y F G Q ι B κ) := by
  haveI := isAlgebraic_algebraAdjoin_Y F G Q ι B κ hκ
  refine Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg (R := F)
    (x := Y F G Q ι B κ) (fin := trdeg_lt_aleph0 F Q ι B) (le := ?_)
  calc Cardinal.mk (Idx F G ι κ) = (Fintype.card (Idx F G ι κ) : Cardinal) :=
        Cardinal.mk_fintype _
    _ = (Fintype.card ι : Cardinal) := by rw [card_Idx F G ι κ]
    _ ≤ Algebra.trdeg F (latticeFunctionField F Q) := card_le_trdeg F Q ι B

/-- **代数无关性（Y-族）**（超越基的第一分量）。 -/
theorem algebraicIndependent_Y
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    AlgebraicIndependent F (Y F G Q ι B κ) :=
  (isTranscendenceBasis_Y F G Q ι B κ hκ).1

end Chars2

/-! ## 4. φ-层：字数特征 `yCharOf` 与 kernel 格 `yKernel`（1β-iii）

与 D5 的 `charOf`／`kernelLattice` 同式（Fischer 证明第二步的格论骨架）：指数向量
`n : Idx F G ι κ →₀ ℤ` 记录 Y-单项式的指数，`yCharOf n := ∏ p, (p.2) ^ n_p` 记录其
特征值；`yKernel := ker(yCharOf)` 给出「单项式 `∏ p, Y p ^ n_p` 不变」的指数条件
（1β-iv 的不变量域等式用）。本节末给指数上界 `[yExp : yKernel] ≤ |G|`（1β-v 用）。 -/

section YExp

variable (κ : G →* Equiv.Perm ι)

-- ⚠ `MulChar` 的群结构是 noncomputable 实例，须显式提升为局部实例才参与综合
--   （否则 `χ ^ k`（`k : ℤ`）、`1`、`χ⁻¹` 全部报「找不到实例」；与 D5 同式）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **指数向量**：`Idx F G ι κ →₀ ℤ`。 -/
abbrev yExp : Type u := Idx F G ι κ →₀ ℤ

/-- **字数特征** `yCharOf n = ∏ p, (p.2) ^ n_p`。
**注**：**不**写成 `→+ Multiplicative _` —— `Multiplicative (MulChar G F)` 的加法群
实例不可导出（D5 `charOf` 同注）；乘法性单独证成 `yCharOf_add`，商提升按 `Quotient`
手工搭建。 -/
noncomputable def yCharOf (n : yExp F G ι κ) : MulChar G F :=
  n.prod fun p k => (p.2 : MulChar G F) ^ k

/-- 单位向量上的取值：`yCharOf (single p 1) = p.2`。 -/
@[simp] lemma yCharOf_single (p : Idx F G ι κ) :
    yCharOf F G ι κ (Finsupp.single p 1) = (p.2 : MulChar G F) := by
  rw [yCharOf, Finsupp.prod_single_index]
  · exact zpow_one _
  · exact zpow_zero _

/-- `yCharOf 0 = 1`。 -/
lemma yCharOf_zero : yCharOf F G ι κ (0 : yExp F G ι κ) = 1 := by
  rw [yCharOf, Finsupp.prod_zero_index]

/-- **乘法性**：`yCharOf (n + m) = yCharOf n * yCharOf m`。 -/
lemma yCharOf_add (n m : yExp F G ι κ) :
    yCharOf F G ι κ (n + m) = yCharOf F G ι κ n * yCharOf F G ι κ m := by
  rw [yCharOf, yCharOf, yCharOf, Finsupp.prod_add_index']
  · intro p
    exact zpow_zero _
  · intro p b₁ b₂
    exact zpow_add _ b₁ b₂

/-- **取逆**：`yCharOf (-n) = (yCharOf n)⁻¹`。 -/
lemma yCharOf_neg (n : yExp F G ι κ) :
    yCharOf F G ι κ (-n) = (yCharOf F G ι κ n)⁻¹ := by
  have h : yCharOf F G ι κ (-n) * yCharOf F G ι κ n = 1 := by
    rw [← yCharOf_add, neg_add_cancel, yCharOf_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- **kernel 格** `yKernel = ker(yCharOf)`（Fischer 意义的 kernel lattice）。 -/
noncomputable def yKernel : AddSubgroup (yExp F G ι κ) where
  carrier := {n | yCharOf F G ι κ n = 1}
  zero_mem' := yCharOf_zero F G ι κ
  add_mem' := by
    intro n m hn hm
    rw [Set.mem_setOf_eq] at *
    rw [yCharOf_add, hn, hm, one_mul]
  neg_mem' := by
    intro n hn
    rw [Set.mem_setOf_eq] at *
    rw [yCharOf_neg, hn, inv_one]

/-- **`yKernel` 的形态**：`n ∈ yKernel ↔ yCharOf n = 1`。 -/
@[simp] theorem mem_yKernel_iff {n : yExp F G ι κ} :
    n ∈ yKernel F G ι κ ↔ yCharOf F G ι κ n = 1 := Iff.rfl

/-- **非空见证**：`single p (Monoid.exponent G)` 属于 `yKernel`
（特征值处取 `Monoid.exponent G` 次幂为 `1`：`(p.2) ^ e = (p.2) (· ^ e) = 1`）。 -/
theorem single_exponent_mem_yKernel (p : Idx F G ι κ) :
    Finsupp.single p (Monoid.exponent G : ℤ) ∈ yKernel F G ι κ := by
  rw [mem_yKernel_iff, yCharOf, Finsupp.prod_single_index]
  · rw [zpow_natCast]
    refine MulChar.ext' fun τ => ?_
    rw [MulChar.pow_apply_coe (p.2 : MulChar G F) (Monoid.exponent G)
        ⟨τ, τ⁻¹, mul_inv_cancel τ, inv_mul_cancel τ⟩,
      MulChar.one_apply_coe ⟨τ, τ⁻¹, mul_inv_cancel τ, inv_mul_cancel τ⟩]
    change (p.2 : MulChar G F).toMonoidHom τ ^ Monoid.exponent G = 1
    rw [← map_pow, Monoid.pow_exponent_eq_one τ, map_one]
  · exact zpow_zero _

section YExpIndex

variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]

/-- 单位群与群的自然同构（显式 `Equiv`，供 `Nat.card` 计数）。 -/
noncomputable def unitsSelfEquiv : Gˣ ≃ G where
  toFun u := (u : G)
  invFun a := Units.mkOfMulEqOne a a⁻¹ (mul_inv_cancel a)
  left_inv u := Units.ext rfl
  right_inv a := rfl

/-- 商上的良定义提升（`yKernel` 恰为 `yCharOf` 的核）。 -/
noncomputable def yQuotLift :
    (yExp F G ι κ ⧸ yKernel F G ι κ) → MulChar G F :=
  fun q => Quotient.liftOn q (yCharOf F G ι κ) (by
    intro a b hab
    have h' : -a + b ∈ yKernel F G ι κ := QuotientAddGroup.leftRel_apply.mp hab
    rw [mem_yKernel_iff, yCharOf_add, yCharOf_neg] at h'
    exact inv_mul_eq_one.mp h')

/-- `yQuotLift` 在等价类上的取值。 -/
@[simp] lemma yQuotLift_mk (n : yExp F G ι κ) :
    yQuotLift F G ι κ (Quotient.mk'' n) = yCharOf F G ι κ n := rfl

/-- `yQuotLift` 单射（`yKernel` 恰是 `yCharOf` 的核）。 -/
theorem yQuotLift_injective : Function.Injective (yQuotLift F G ι κ) := by
  intro a b
  induction a, b using Quotient.inductionOn₂
  intro hxy
  change yCharOf F G ι κ _ = yCharOf F G ι κ _ at hxy
  apply Quotient.sound'
  rw [QuotientAddGroup.leftRel_apply, mem_yKernel_iff, yCharOf_add, yCharOf_neg, hxy,
    inv_mul_cancel]

/-- **指数上界**：`[yExp : yKernel] ≤ |G|`（度数输入：指数不超过字符群的基数）。 -/
theorem yKernel_index_le_card :
    (yKernel F G ι κ).index ≤ Fintype.card G := by
  rw [AddSubgroup.index_eq_card]
  calc Nat.card (yExp F G ι κ ⧸ yKernel F G ι κ)
      ≤ Nat.card (MulChar G F) :=
        Finite.card_le_of_embedding ⟨yQuotLift F G ι κ, yQuotLift_injective F G ι κ⟩
    _ = Nat.card Gˣ := MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G F
    _ = Nat.card G := Nat.card_congr (unitsSelfEquiv G)
    _ = Fintype.card G := Nat.card_eq_fintype_card

end YExpIndex

end YExp

/-! ## 5. 不变量域等式（1β-iv）：`latticeInvariants F G Q = adjoin F (yPow '' yKernel)`

主定理 `latticeInvariants_eq_adjoin_yPow`。两方向：
* ⊇（`adjoin_yPow_le_latticeInvariants`）：生成元经特征性 `τ • yPow a = yCharEval τ a • yPow a`
  与 `mem_yKernel_iff` 落于 `latticeInvariants`。
* ⊆（`latticeInvariants_le_adjoin_yPow`，主体）：不变量 `z = r / s`（`mem_adjoin_iff_div`
  ＋ `adjoin_range_Y_eq_top`）经重正规化 `u = Pr·∏_{τ≠1} yTwist τ Ps`、`w = ∏_τ yTwist τ Ps`
  （两者皆 yTwist-固定，由 `ŷ` 单射从 aeval 层转移），再由「扭转固定 ⟹ 支撑指数 ∈ `yKernel`」
  （`mem_yKernel_yCast_of_yTwist_fixed`，系数点值比较）得 `u = ŷ(Pu) = z·ŷ(Dw)`、`w = ŷ(Dw)`，
  展开为 `yPow` 生成元的 F-组合（`IntermediateField.sum_mem` ＋ `subset_adjoin`）。

机理注：**不做**平均／特征正交（全程不出现 `|G|⁻¹`）——支撑系数的点值比较即足够。 -/

section InvEq

variable (κ : G →* Equiv.Perm ι)

-- ⚠ 与 §4 同理：`MulChar` 的群结构是 noncomputable 实例，须局部提升（`map_zpow` 的源群）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-- **字符求值**（F-值）：`yCharEval τ n = ∏ p, ((p.2) τ) ^ n_p`。 -/
noncomputable def yCharEval (τ : G) (n : yExp F G ι κ) : F :=
  n.prod fun p k => ((p.2 : MulChar G F) τ) ^ k

/-- 单点求值同态 `χ ↦ χ τ`（`MulChar G F →* F`）。 -/
noncomputable def mulCharEval (τ : G) : MulChar G F →* F where
  toFun χ := χ τ
  map_one' := MulChar.one_apply ⟨⟨τ, τ⁻¹, mul_inv_cancel τ, inv_mul_cancel τ⟩, rfl⟩
  map_mul' χ ψ := MulChar.mul_apply χ ψ τ

/-- **桥**：`(yCharOf n) τ = yCharEval τ n`（逐因子 `map_zpow`）。 -/
theorem yCharOf_apply (n : yExp F G ι κ) (τ : G) :
    yCharOf F G ι κ n τ = yCharEval F G ι κ τ n := by
  rw [yCharOf, yCharEval]
  simp only [Finsupp.prod]
  change mulCharEval F G τ (Finset.prod n.support fun p => (p.2 : MulChar G F) ^ n p)
      = Finset.prod n.support fun p => ((p.2 : MulChar G F) τ) ^ n p
  rw [map_prod]
  exact Finset.prod_congr rfl fun p _ => map_zpow (mulCharEval F G τ) _ _

/-- **ℕ → ℤ 指数提升**：`yCast d = Finsupp.mapRange Nat.cast d`。 -/
noncomputable def yCast (d : Idx F G ι κ →₀ ℕ) : yExp F G ι κ :=
  Finsupp.mapRange Nat.cast (by simp) d

@[simp] lemma yCast_apply (d : Idx F G ι κ →₀ ℕ) (p : Idx F G ι κ) :
    yCast F G ι κ d p = (d p : ℤ) := by
  rw [yCast, Finsupp.mapRange_apply]

lemma yCast_support (d : Idx F G ι κ →₀ ℕ) :
    (yCast F G ι κ d).support = d.support := by
  ext p
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, yCast_apply]
  exact ⟨fun h hc => h (by rw [hc]; simp), fun h hc => h (by exact_mod_cast hc)⟩

section InvEqRoots

variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]

/-- **Y-单项式**（ℤ-指数）：`yPow n = ∏ p, Y p ^ n_p`。 -/
noncomputable def yPow (n : yExp F G ι κ) : latticeFunctionField F Q :=
  n.prod fun p k => (Y F G Q ι B κ p) ^ k

/-- Y-求值同态 `ŷ = MvPolynomial.aeval (Y …)`（`F[x_p] →_F F(Q)`；`R := F` 显式）。 -/
noncomputable def yAeval : MvPolynomial (Idx F G ι κ) F →ₐ[F] latticeFunctionField F Q :=
  MvPolynomial.aeval (Y F G Q ι B κ)

/-- `yPow` 在 ℕ-提升上的形态：`yPow (yCast d) = ∏ p, Y p ^ d_p`。 -/
lemma yPow_yCast (d : Idx F G ι κ →₀ ℕ) :
    yPow F G Q ι B κ (yCast F G ι κ d) = d.prod fun p k => (Y F G Q ι B κ p) ^ k := by
  rw [yPow]
  simp only [Finsupp.prod]
  rw [yCast_support F G ι κ]
  exact Finset.prod_congr rfl fun p _ => by rw [yCast_apply F G ι κ, zpow_natCast]

/-- **特征性（1β-iv 核心）**：`τ • yPow a = yCharEval τ a • yPow a`。 -/
theorem yPow_smul
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (τ : G) (a : yExp F G ι κ) :
    τ • yPow F G Q ι B κ a = yCharEval F G ι κ τ a • yPow F G Q ι B κ a := by
  have hscalar : ∀ (c : F) (x : latticeFunctionField F Q) (n : ℤ),
      (c • x) ^ n = c ^ n • x ^ n := by
    intro c x n
    have hinv : ∀ (c' : F) (x' : latticeFunctionField F Q),
        (c' • x')⁻¹ = c'⁻¹ • x'⁻¹ := by
      intro c' x'
      rcases eq_or_ne c' 0 with rfl | hc
      · simp
      rcases eq_or_ne x' 0 with rfl | hx
      · simp
      exact inv_eq_of_mul_eq_one_left (by
        rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, inv_mul_cancel₀ hx,
          one_smul])
    cases n with
    | ofNat m => simpa using smul_pow c x m
    | negSucc m =>
        calc (c • x) ^ Int.negSucc m
            = ((c • x) ^ (m + 1))⁻¹ := zpow_negSucc _ _
          _ = ((c ^ (m + 1)) • (x ^ (m + 1)))⁻¹ := by rw [smul_pow]
          _ = (c ^ (m + 1))⁻¹ • (x ^ (m + 1))⁻¹ := hinv _ _
          _ = c ^ Int.negSucc m • x ^ Int.negSucc m := by
              simp only [zpow_negSucc]
  rw [yPow]
  simp only [Finsupp.prod]
  rw [Finset.smul_prod']
  calc Finset.prod a.support (fun p => τ • (Y F G Q ι B κ p) ^ (a p))
      = Finset.prod a.support
          (fun p => ((p.2 : MulChar G F) τ) ^ (a p)
            • (Y F G Q ι B κ p) ^ (a p)) :=
        Finset.prod_congr rfl fun p _ => by
          rw [smul_zpow₀', Y_smul F G Q ι B κ hκ τ p]
          exact hscalar _ _ _
    _ = Finset.prod a.support (fun p => ((p.2 : MulChar G F) τ) ^ (a p))
          • Finset.prod a.support (fun p => (Y F G Q ι B κ p) ^ (a p)) :=
        Finset.prod_smul a.support _ _

/-- **坐标扭转**：`yTwist τ P = ∑_{d ∈ P.support} monomial d (P.coeff d · ŷ_τ(yCast d))`。 -/
noncomputable def yTwist (τ : G) (P : MvPolynomial (Idx F G ι κ) F) :
    MvPolynomial (Idx F G ι κ) F :=
  ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d * yCharEval F G ι κ τ (yCast F G ι κ d))

/-- **扭转系数**：`coeff d (yTwist τ P) = P.coeff d · ŷ_τ(yCast d)`。 -/
lemma coeff_yTwist (τ : G) (P : MvPolynomial (Idx F G ι κ) F)
    (d : Idx F G ι κ →₀ ℕ) :
    (yTwist F G ι κ τ P).coeff d = P.coeff d * yCharEval F G ι κ τ (yCast F G ι κ d) := by
  rw [yTwist, MvPolynomial.coeff_sum]
  have hsingle : (∑ e ∈ P.support,
        (MvPolynomial.monomial e (P.coeff e * yCharEval F G ι κ τ (yCast F G ι κ e))).coeff d)
      = (MvPolynomial.monomial d
          (P.coeff d * yCharEval F G ι κ τ (yCast F G ι κ d))).coeff d := by
    refine Finset.sum_eq_single d ?_ ?_
    · intro e _ hne
      rw [MvPolynomial.coeff_monomial, if_neg hne]
    · intro hd
      have h0 : P.coeff d = 0 := by
        by_contra h
        exact hd (MvPolynomial.mem_support_iff.mpr h)
      rw [MvPolynomial.coeff_monomial, if_pos rfl, h0, zero_mul]
  rw [hsingle, MvPolynomial.coeff_monomial, if_pos rfl]

/-- **单项式求值**：`ŷ (monomial d c) = c · yPow (yCast d)`。 -/
lemma yAeval_monomial (d : Idx F G ι κ →₀ ℕ) (c : F) :
    yAeval F G Q ι B κ (MvPolynomial.monomial d c)
      = c • yPow F G Q ι B κ (yCast F G ι κ d) := by
  rw [yAeval, MvPolynomial.aeval_monomial, yPow_yCast F G Q ι B κ d, Algebra.smul_def]

/-- **扭转性**：`yTwist τ` 在 `ŷ` 下的像是 `τ`-平移。 -/
theorem yAeval_yTwist
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (τ : G) (P : MvPolynomial (Idx F G ι κ) F) :
    yAeval F G Q ι B κ (yTwist F G ι κ τ P) = τ • yAeval F G Q ι B κ P := by
  rw [yTwist, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum P, map_sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [yAeval_monomial F G Q ι B κ d
      (P.coeff d * yCharEval F G ι κ τ (yCast F G ι κ d)),
    yAeval_monomial F G Q ι B κ d (P.coeff d), mul_smul,
    smul_comm τ (P.coeff d) (yPow F G Q ι B κ (yCast F G ι κ d)),
    yPow_smul F G Q ι B κ hκ τ (yCast F G ι κ d)]

/-- **扭转不动 ⟹ 核成员**：若 `yTwist τ P = P`（∀τ）则支撑上的 `yCast d ∈ yKernel`。 -/
theorem mem_yKernel_yCast_of_yTwist_fixed (P : MvPolynomial (Idx F G ι κ) F)
    (hfix : ∀ τ : G, yTwist F G ι κ τ P = P) {d : Idx F G ι κ →₀ ℕ}
    (hd : d ∈ P.support) : yCast F G ι κ d ∈ yKernel F G ι κ := by
  rw [mem_yKernel_iff]
  refine MulChar.ext' fun τ => ?_
  rw [yCharOf_apply F G ι κ (yCast F G ι κ d) τ,
    MulChar.one_apply_coe ⟨τ, τ⁻¹, mul_inv_cancel τ, inv_mul_cancel τ⟩]
  have h := congrArg (fun p : MvPolynomial (Idx F G ι κ) F => p.coeff d) (hfix τ)
  rw [coeff_yTwist F G ι κ τ P d] at h
  exact mul_left_cancel₀ (MvPolynomial.mem_support_iff.mp hd) (by simpa using h)

/-- **核元素幂在不变子环中**（M6-A 特征性的重述）。 -/
theorem yPow_mem_latticeInvariants
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    {a : yExp F G ι κ} (ha : a ∈ yKernel F G ι κ) :
    yPow F G Q ι B κ a ∈ latticeInvariants F G Q := by
  rw [mem_latticeInvariants_iff]
  intro τ
  rw [yPow_smul F G Q ι B κ hκ τ a, ← yCharOf_apply F G ι κ a τ,
    (mem_yKernel_iff (n := a)).mp ha,
    MulChar.one_apply_coe ⟨τ, τ⁻¹, mul_inv_cancel τ, inv_mul_cancel τ⟩, one_smul]

/-- **`ŷ` 的像在扭核生成域中**（支撑核条件的多项式）。 -/
theorem yAeval_mem_adjoin_yPow (P : MvPolynomial (Idx F G ι κ) F)
    (hker : ∀ d ∈ P.support, yCast F G ι κ d ∈ yKernel F G ι κ) :
    yAeval F G Q ι B κ P ∈ IntermediateField.adjoin F
      (Set.range fun m : ↥(yKernel F G ι κ) => yPow F G Q ι B κ (m : yExp F G ι κ)) := by
  rw [MvPolynomial.as_sum P, map_sum]
  refine IntermediateField.sum_mem
    (S := IntermediateField.adjoin F (Set.range fun m : ↥(yKernel F G ι κ) =>
      yPow F G Q ι B κ (m : yExp F G ι κ))) ?_
  intro d hd
  rw [yAeval_monomial F G Q ι B κ d (P.coeff d), Algebra.smul_def]
  exact mul_mem
    (IntermediateField.algebraMap_mem
      (IntermediateField.adjoin F (Set.range fun m : ↥(yKernel F G ι κ) =>
        yPow F G Q ι B κ (m : yExp F G ι κ))) (P.coeff d))
    (IntermediateField.subset_adjoin F _ ⟨⟨yCast F G ι κ d, hker d hd⟩, rfl⟩)

/-- **方向 1**：扭核 `yPow` 生成的中间域 ⊆ 不变量域。 -/
theorem adjoin_yPow_le_latticeInvariants
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    (IntermediateField.adjoin F (Set.range fun m : ↥(yKernel F G ι κ) =>
        yPow F G Q ι B κ (m : yExp F G ι κ)) : Set (latticeFunctionField F Q))
      ⊆ (latticeInvariants F G Q : Set (latticeFunctionField F Q)) := by
  have hgen : Set.range (algebraMap F (latticeFunctionField F Q)) ∪
      Set.range (fun m : ↥(yKernel F G ι κ) => yPow F G Q ι B κ (m : yExp F G ι κ))
      ⊆ (latticeInvariants F G Q : Set (latticeFunctionField F Q)) := by
    rw [Set.union_subset_iff]
    refine ⟨?_, ?_⟩
    · rintro x ⟨c, rfl⟩
      exact (mem_latticeInvariants_iff (F := F) (G := G) (M := Q)
        (algebraMap F (latticeFunctionField F Q) c)).mpr fun g =>
          smul_algebraMap_latticeFunctionField F G Q g c
    · rintro x ⟨m, rfl⟩
      exact yPow_mem_latticeInvariants F G Q ι B κ hκ m.2
  intro x hx
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap F (latticeFunctionField F Q)) ∪
      Set.range (fun m : ↥(yKernel F G ι κ) => yPow F G Q ι B κ (m : yExp F G ι κ))) := hx
  exact (Subfield.closure_le.mpr hgen) hx'

/-- **方向 2**：不变量域 ⊆ 扭核 `yPow` 生成的中间域。 -/
theorem latticeInvariants_le_adjoin_yPow
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    (latticeInvariants F G Q : Set (latticeFunctionField F Q))
      ⊆ (IntermediateField.adjoin F (Set.range fun m : ↥(yKernel F G ι κ) =>
          yPow F G Q ι B κ (m : yExp F G ι κ)) : Set (latticeFunctionField F Q)) := by
  intro z hz
  have hz_adjoin : z ∈ IntermediateField.adjoin F (Set.range (Y F G Q ι B κ)) := by
    rw [adjoin_range_Y_eq_top F G Q ι B κ hκ]
    trivial
  obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := F)
    (S := Set.range (Y F G Q ι B κ))).mp hz_adjoin
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨Pr, hPr⟩ := hr
  obtain ⟨Ps, hPs⟩ := hs
  have hPr' : yAeval F G Q ι B κ Pr = r := hPr
  have hPs' : yAeval F G Q ι B κ Ps = s := hPs
  by_cases hs0 : s = 0
  · rw [hs0, div_zero] at hrs
    rw [hrs]
    exact IntermediateField.zero_mem _
  · have hz_sw : z * s = r := by
      rw [hrs]
      exact div_mul_cancel₀ r hs0
    set sg : latticeFunctionField F Q := ∏ τ : G, τ • s with hsg
    set w : MvPolynomial (Idx F G ι κ) F := ∏ τ : G, yTwist F G ι κ τ Ps with hw
    set u : MvPolynomial (Idx F G ι κ) F :=
      Pr * ∏ τ ∈ Finset.univ.erase (1 : G), yTwist F G ι κ τ Ps with hu
    have hw_eval : yAeval F G Q ι B κ w = sg := by
      rw [hw, map_prod, hsg]
      exact Finset.prod_congr rfl fun τ _ => by
        rw [yAeval_yTwist F G Q ι B κ hκ τ Ps, hPs']
    have hperm : ∀ σ : G, σ • sg = sg := by
      intro σ
      rw [hsg, Finset.smul_prod']
      trans ∏ τ : G, (σ * τ) • s
      · exact Finset.prod_congr rfl fun τ _ => by rw [mul_smul]
      · exact Fintype.prod_bijective (fun τ : G => σ * τ) (Equiv.mulLeft σ).bijective
          (fun τ : G => (σ * τ) • s) (fun ρ : G => ρ • s) (fun τ => rfl)
    have hw_erase : yAeval F G Q ι B κ w
        = s * ∏ τ ∈ Finset.univ.erase (1 : G), τ • s := by
      rw [hw_eval, hsg,
        ← Finset.mul_prod_erase Finset.univ (fun τ : G => τ • s) (a := 1)
          (Finset.mem_univ 1), one_smul]
    have hp_eval : yAeval F G Q ι B κ
          (∏ τ ∈ Finset.univ.erase (1 : G), yTwist F G ι κ τ Ps)
        = ∏ τ ∈ Finset.univ.erase (1 : G), τ • s := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun τ _ => by
        rw [yAeval_yTwist F G Q ι B κ hκ τ Ps, hPs']
    have hu_prod : yAeval F G Q ι B κ u = z * yAeval F G Q ι B κ w := by
      rw [hu, map_mul, hPr', hp_eval, hw_erase, ← hz_sw, mul_assoc]
    have hinj : Function.Injective (yAeval F G Q ι B κ) :=
      (algebraicIndependent_iff_injective_aeval).mp (algebraicIndependent_Y F G Q ι B κ hκ)
    have hu_fix : ∀ σ : G, yTwist F G ι κ σ u = u := by
      intro σ
      apply hinj
      rw [yAeval_yTwist F G Q ι B κ hκ σ u, hu_prod, smul_mul', hw_eval,
        (mem_latticeInvariants_iff (F := F) (G := G) (M := Q) z).mp hz σ, hperm σ]
    have hw_fix : ∀ σ : G, yTwist F G ι κ σ w = w := by
      intro σ
      apply hinj
      rw [yAeval_yTwist F G Q ι B κ hκ σ w, hw_eval, hperm σ]
    have hsmul_ne : ∀ τ : G, τ • s ≠ 0 := fun τ h =>
      hs0 (by simpa using congrArg (fun x : latticeFunctionField F Q => τ⁻¹ • x) h)
    have hw_ne : yAeval F G Q ι B κ w ≠ 0 := by
      rw [hw_eval, hsg]
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => hsmul_ne τ
    have hker_u : ∀ d ∈ u.support, yCast F G ι κ d ∈ yKernel F G ι κ :=
      fun d hd => mem_yKernel_yCast_of_yTwist_fixed F G ι κ u hu_fix hd
    have hker_w : ∀ d ∈ w.support, yCast F G ι κ d ∈ yKernel F G ι κ :=
      fun d hd => mem_yKernel_yCast_of_yTwist_fixed F G ι κ w hw_fix hd
    have hA_u : yAeval F G Q ι B κ u ∈ IntermediateField.adjoin F
        (Set.range fun m : ↥(yKernel F G ι κ) => yPow F G Q ι B κ (m : yExp F G ι κ)) :=
      yAeval_mem_adjoin_yPow F G Q ι B κ u hker_u
    have hA_w : yAeval F G Q ι B κ w ∈ IntermediateField.adjoin F
        (Set.range fun m : ↥(yKernel F G ι κ) => yPow F G Q ι B κ (m : yExp F G ι κ)) :=
      yAeval_mem_adjoin_yPow F G Q ι B κ w hker_w
    have hzu : z = yAeval F G Q ι B κ u / yAeval F G Q ι B κ w :=
      (eq_div_iff hw_ne).mpr hu_prod.symm
    rw [hzu]
    exact div_mem hA_u hA_w

/-- **主定理（1β-iv，格层版）**：`latticeInvariants F G Q = adjoin F {yPow m | m ∈ yKernel}`。 -/
theorem latticeInvariants_eq_adjoin_yPow
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    (latticeInvariants F G Q : Set (latticeFunctionField F Q))
      = (IntermediateField.adjoin F (Set.range fun m : ↥(yKernel F G ι κ) =>
          yPow F G Q ι B κ (m : yExp F G ι κ)) : Set (latticeFunctionField F Q)) :=
  le_antisymm (latticeInvariants_le_adjoin_yPow F G Q ι B κ hκ)
    (adjoin_yPow_le_latticeInvariants F G Q ι B κ hκ)

end InvEqRoots

end InvEq

/-! ## 公理闸门（本文件现有声明） -/

#print axioms monoPowHom
#print axioms monoPowHom_injective
#print axioms monoSubstAlg
#print axioms monoSubstAlg_apply
#print axioms monoSubstAlg_monomial
#print axioms monoSubstAlg_X
#print axioms monoSubstAlg_injective
#print axioms monoSubst
#print axioms monoSubst_apply
#print axioms monoSubst_X
#print axioms monoSubst_injective
#print axioms algIndep_mono
#print axioms hmonoGen
#print axioms hmonoGen_permMono
#print axioms adjoin_range_mono_eq_top
#print axioms adjoin_range_Y_eq_top
#print axioms isAlgebraic_of_adjoin_eq_top
#print axioms isAlgebraic_algebraAdjoin_mono
#print axioms trdeg_le_card
#print axioms card_le_trdeg
#print axioms trdeg_lt_aleph0
#print axioms trdeg_eq_card
#print axioms isAlgebraic_algebraAdjoin_Y
#print axioms isTranscendenceBasis_Y
#print axioms algebraicIndependent_Y
#print axioms yExp
#print axioms yCharOf
#print axioms yCharOf_single
#print axioms yCharOf_zero
#print axioms yCharOf_add
#print axioms yCharOf_neg
#print axioms yKernel
#print axioms mem_yKernel_iff
#print axioms single_exponent_mem_yKernel
#print axioms unitsSelfEquiv
#print axioms yQuotLift
#print axioms yQuotLift_mk
#print axioms yQuotLift_injective
#print axioms yKernel_index_le_card
#print axioms yCharEval
#print axioms mulCharEval
#print axioms yCharOf_apply
#print axioms yCast
#print axioms yCast_apply
#print axioms yCast_support
#print axioms yPow
#print axioms yAeval
#print axioms yPow_yCast
#print axioms yPow_smul
#print axioms yTwist
#print axioms coeff_yTwist
#print axioms yAeval_monomial
#print axioms yAeval_yTwist
#print axioms mem_yKernel_yCast_of_yTwist_fixed
#print axioms yPow_mem_latticeInvariants
#print axioms yAeval_mem_adjoin_yPow
#print axioms adjoin_yPow_le_latticeInvariants
#print axioms latticeInvariants_le_adjoin_yPow
#print axioms latticeInvariants_eq_adjoin_yPow

end EM

end ABGV52
