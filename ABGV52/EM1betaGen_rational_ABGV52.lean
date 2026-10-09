/-
  EM1betaGen_rational_ABGV52 —— M6-C 波（M6 收口件）：1β-一般形状有理性

  交付：
    (a) `yKernelSub`／`yKernelRank`／`yKernelBasis`／`yKernelMulEquiv`：核的自由 ℤ-基；
    (b) `yKernelFracEquiv`：分式域转运 `F(↥yKernel) ≃ₐ[F] F(ℤ^r)`；
    (c) `yKernelAlgHom`：核代数求值同态 `F[↥yKernel] →ₐ[F] F(Q)`（`single ↦ yPow`），
        单射 ＋ 像生成的子域 = `latticeInvariants`；
    (d) `yKernelFracEquivInvariantsAlg`：`F(↥yKernel) ≃ₐ[F] ↥(latticeInvariantsAlg F G Q)`；
    (e) `isRational_latticeInvariantsAlg_of_permBasis`：置换基 ⟹ 不变量代数有理性。

  设计：wiki/proj-ABGV52-M6-1beta-general-design.md §4.1；对照 D13（自由交换情形）。
  ⚠ 与 D13 的机制差异：D13 的 `phiDiag_injective` 用「复合 `Ψ ∘ Φ₀ = algebraMap`」把无关性
  化为已知同态的单射；一般格 Q 无此复合，故 (c) 的单射性改用**移位技巧**——
  把核上的 F-线性关系整体乘 `yPow (yCast N)`（`N := Σ_{a∈s}` 逐点非负截断），
  移位后的重指数族 `d a = yNat (yCast N + a)` 互异，经 `yAeval`（代数无关 ⟹ 单射）化成
  多项式系数提取。

  只读依赖：M6-A（EM1betaGen_basis）、M6-B（EM1betaGen_mono）、D1、D2、D3。
  本件不修改任何既有文件；M6-A／M6-B 中缺的引理一律在本件重述。
-/
import ABGV52.EM1betaGen_mono_ABGV52
import ABGV52.D2_ABGV52
import ABGV52.D3_ABGV52

open scoped Classical

namespace ABGV52

namespace EM

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable (F : Type u) [Field F]
variable (G : Type u) [CommGroup G] [Fintype G]
variable (Q : Type u) [AddCommGroup Q] [Module ℤ Q] [DistribMulAction G Q]
  [SMulCommClass G ℤ Q] [UniqueProds (Multiplicative Q)]
variable (ι : Type u) [Fintype ι]
variable (B : Module.Basis ι ℤ Q)
variable [HasEnoughRootsOfUnity F (Monoid.exponent Gˣ)]
variable (κ : G →* Equiv.Perm ι)

-- ⚠ `MulChar` 的群结构须显式提升（D5 陷阱 13；D10／D13 同款）。
attribute [local instance] MulChar.hasOne MulChar.hasInv MulChar.commGroup

/-! ## §1 移位机制（ℤ → ℕ 截断与移位） -/

/-- 逐点取正部：`yNat n p = (n p).toNat`（ℕ 值）。 -/
noncomputable def yNat (n : yExp F G ι κ) : Idx F G ι κ →₀ ℕ :=
  Finsupp.mapRange Int.toNat (by simp) n

@[simp] lemma yNat_apply (n : yExp F G ι κ) (p : Idx F G ι κ) :
    yNat F G ι κ n p = (n p).toNat :=
  rfl

/-- 逐点不等式 `n p ≤ (yNat n p : ℤ)`（`yNat` 是下界）。 -/
lemma le_yNat (n : yExp F G ι κ) (p : Idx F G ι κ) :
    n p ≤ ((yNat F G ι κ n p : ℕ) : ℤ) := by
  by_cases h : 0 ≤ n p
  · rw [yNat_apply, Int.toNat_of_nonneg h]
  · rw [yNat_apply, Int.toNat_of_nonpos (le_of_lt (lt_of_not_ge h))]
    exact le_of_lt (lt_of_not_ge h)

/-- 非负整向量的 `yNat` 是 ℤ-提升的左逆：`yCast (yNat n) = n`。 -/
lemma yCast_yNat_of_nonneg {n : yExp F G ι κ} (hn : ∀ p, 0 ≤ n p) :
    yCast F G ι κ (yNat F G ι κ n) = n := by
  refine Finsupp.ext fun p => ?_
  rw [yCast_apply F G ι κ, yNat_apply F G ι κ]
  exact Int.toNat_of_nonneg (hn p)

/-- 移位：`yShift N a = yNat (yCast N + a)`（把 `a` 沿 `N` 推到非负象限）。 -/
noncomputable def yShift (N : Idx F G ι κ →₀ ℕ) (a : yExp F G ι κ) : Idx F G ι κ →₀ ℕ :=
  yNat F G ι κ (yCast F G ι κ N + a)

/-- 移位的 ℤ-提升等于原和（当和逐点非负时）。 -/
lemma yCast_yShift {N : Idx F G ι κ →₀ ℕ} {a : yExp F G ι κ}
    (h : ∀ p, 0 ≤ (yCast F G ι κ N + a) p) :
    yCast F G ι κ (yShift F G ι κ N a) = yCast F G ι κ N + a :=
  yCast_yNat_of_nonneg F G ι κ h

/-! ## §2 `yPow` 的乘法性 -/

lemma yPow_zero : yPow F G Q ι B κ (0 : yExp F G ι κ) = 1 := by
  rw [yPow]
  exact Finsupp.prod_zero_index

lemma yPow_add (a b : yExp F G ι κ) :
    yPow F G Q ι B κ (a + b) = yPow F G Q ι B κ a * yPow F G Q ι B κ b := by
  rw [yPow, yPow, yPow]
  exact Finsupp.prod_add_index'
    (fun χ => zpow_zero (Y F G Q ι B κ χ))
    (fun χ b₁ b₂ => zpow_add₀ (Y_ne_zero F G Q ι B κ χ) b₁ b₂)

/-! ## §3 (a) `yKernel` 的自由 ℤ-基 -/

/-- `yKernel` 作为 ℤ-子模（载体与 `↥(yKernel F G ι κ)` 相同）。 -/
def yKernelSub : Submodule ℤ (yExp F G ι κ) :=
  AddSubgroup.toIntSubmodule (yKernel F G ι κ)

/-- (a) 核的 ℤ-秩（PID 自由基的基数，定义值）。 -/
noncomputable def yKernelRank : ℕ :=
  (Submodule.basisOfPid Finsupp.basisSingleOne (yKernelSub F G ι κ)).1

/-- (a) 核的 ℤ-基（`ℤ` 是 PID ⟹ 子模自由）。 -/
noncomputable def yKernelBasis :
    Module.Basis (Fin (yKernelRank F G ι κ)) ℤ ↥(yKernelSub F G ι κ) :=
  (Submodule.basisOfPid Finsupp.basisSingleOne (yKernelSub F G ι κ)).2

/-- (a) 核的乘法型 ≃ `ℤ^r`（加法等价转乘法）。 -/
noncomputable def yKernelMulEquiv :
    Multiplicative ↥(yKernelSub F G ι κ)
      ≃* Multiplicative (Fin (yKernelRank F G ι κ) → ℤ) :=
  AddEquiv.toMultiplicative
    (((yKernelBasis F G ι κ).repr.trans
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (yKernelRank F G ι κ)))).toAddEquiv)

/-! ## §3.5 核的 `UniqueProds`（ℚ-向量空间转运 ⟹ `IsDomain`／`Field` 自动） -/

/-- 系数 `ℤ → ℚ` 的乘法同态（核的乘法型 → `ℚ`-向量空间的乘法型）。 -/
noncomputable def yKernelToQMulHom :
    Multiplicative ↥(yKernelSub F G ι κ) →ₙ* Multiplicative (Idx F G ι κ →₀ ℚ) where
  toFun a := Multiplicative.ofAdd
    (Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp) (a.toAdd : yExp F G ι κ))
  map_mul' a b := by
    refine Multiplicative.ext ?_
    show Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp)
        ((a * b).toAdd : yExp F G ι κ)
      = Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp) (a.toAdd : yExp F G ι κ)
        + Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp) (b.toAdd : yExp F G ι κ)
    rw [show ((a * b).toAdd : yExp F G ι κ)
      = (a.toAdd : yExp F G ι κ) + (b.toAdd : yExp F G ι κ) from rfl]
    rw [Finsupp.mapRange_add]
    intro x y
    exact_mod_cast Int.cast_add x y

lemma yKernelToQMulHom_injective : Function.Injective (yKernelToQMulHom F G ι κ) := by
  intro a b hab
  have h2 : Multiplicative.ofAdd (Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp)
        (a.toAdd : yExp F G ι κ))
      = Multiplicative.ofAdd (Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp)
        (b.toAdd : yExp F G ι κ)) := hab
  have h3 : Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp) (a.toAdd : yExp F G ι κ)
      = Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp) (b.toAdd : yExp F G ι κ) :=
    congrArg Multiplicative.toAdd h2
  have h4 : (a.toAdd : yExp F G ι κ) = (b.toAdd : yExp F G ι κ) :=
    Finsupp.mapRange_injective (fun z : ℤ => (z : ℚ)) (by simp)
      (by exact_mod_cast Int.cast_injective) h3
  exact Multiplicative.ext (Subtype.ext h4)

/-- 核的 `UniqueProds`（经 ℚ-向量空间转运；`MonoidAlgebra` 的 `IsDomain`／`Field` 随之自动）。 -/
noncomputable instance instUniqueProdsY :
    UniqueProds (Multiplicative ↥(yKernelSub F G ι κ)) :=
  UniqueProds.of_injective_mulHom (yKernelToQMulHom F G ι κ)
    (yKernelToQMulHom_injective F G ι κ) inferInstance

/-! ## §4 (c) 核代数求值同态 `yKernelAlgHom` 与其基本性质 -/

/-- `yKernelSub` 与 `yKernel` 的成员关系一致（载体同一定义）。 -/
lemma yKernelSub_mem_iff (a : yExp F G ι κ) :
    a ∈ yKernelSub F G ι κ ↔ a ∈ yKernel F G ι κ :=
  Iff.rfl

/-- 乘法同态 `↥yKernel ∋ a ↦ yPow a`（目标是分式域的乘法幺半群）。 -/
noncomputable def yPowMonoidHom :
    Multiplicative ↥(yKernelSub F G ι κ) →* latticeFunctionField F Q where
  toFun m := yPow F G Q ι B κ ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
  map_one' := by
    show yPow F G Q ι B κ (((1 : Multiplicative ↥(yKernelSub F G ι κ)).toAdd :
      ↥(yKernelSub F G ι κ)) : yExp F G ι κ) = 1
    rw [show ((1 : Multiplicative ↥(yKernelSub F G ι κ)).toAdd :
      ↥(yKernelSub F G ι κ)) = 0 from rfl]
    exact yPow_zero F G Q ι B κ
  map_mul' m n := by
    show yPow F G Q ι B κ (((m * n).toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
      = yPow F G Q ι B κ ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
        * yPow F G Q ι B κ ((n.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
    rw [show (((m * n).toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
      = ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
        + ((n.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ) from rfl]
    exact yPow_add F G Q ι B κ _ _

/-- (c) 核代数求值同态 `F[↥yKernel] →ₐ[F] F(Q)`：`single m ↦ yPow m`。 -/
noncomputable def yKernelAlgHom :
    latticeAlgebra F ↥(yKernelSub F G ι κ) →ₐ[F] latticeFunctionField F Q :=
  MonoidAlgebra.lift F (latticeFunctionField F Q) (Multiplicative ↥(yKernelSub F G ι κ))
    (yPowMonoidHom F G Q ι B κ)

/-- `yKernelAlgHom` 在 `single` 上的取值。 -/
lemma yKernelAlgHom_single (m : Multiplicative ↥(yKernelSub F G ι κ)) (c : F) :
    yKernelAlgHom F G Q ι B κ (MonoidAlgebra.single m c)
      = c • yPow F G Q ι B κ ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ) := by
  change MonoidAlgebra.lift F (latticeFunctionField F Q)
      (Multiplicative ↥(yKernelSub F G ι κ)) (yPowMonoidHom F G Q ι B κ)
      (MonoidAlgebra.single m c) = c • yPow F G Q ι B κ
        ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
  rw [MonoidAlgebra.lift_single]
  rfl

/-- `yKernelAlgHom` 在 `of` 上的取值（单射证明与生成元包含都用它）。 -/
lemma yKernelAlgHom_of (m : Multiplicative ↥(yKernelSub F G ι κ)) :
    yKernelAlgHom F G Q ι B κ
        (MonoidAlgebra.of F (Multiplicative ↥(yKernelSub F G ι κ)) m)
      = yPow F G Q ι B κ ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ) := by
  rw [MonoidAlgebra.of_apply, yKernelAlgHom_single, one_smul]

/-- 生成元见证：`single (ofAdd a) 1 ↦ yPow a`（(c) 的生成元包含用）。 -/
lemma yKernelAlgHom_witness (a : ↥(yKernelSub F G ι κ)) :
    yKernelAlgHom F G Q ι B κ (MonoidAlgebra.single (Multiplicative.ofAdd a) 1)
      = yPow F G Q ι B κ (a : yExp F G ι κ) := by
  rw [yKernelAlgHom_single, one_smul]
  rfl

/-! ## §4b (c) 单射性：移位技巧 -/

/-- 核上移位向量 `N_s := Σ_{b∈s} yNat (-b)`（逐点非负，作用是把 `s` 的项整体推到非负象限）。 -/
noncomputable def yKernelShift (s : Finset (Multiplicative ↥(yKernelSub F G ι κ))) :
    Idx F G ι κ →₀ ℕ :=
  ∑ b ∈ s, yNat F G ι κ (-((b.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ))

/-- 核上移位的单项式支配读数：`m` 的负分量在 ℕ 级的读数（用不透明头名，
    使 `Finset.single_le_sum` 的同头合一得以进行，避免在含强制转换的 λ 上
    展开 `DFunLike.coe`／`EquivLike.coe` 的元变量合一爆炸）。 -/
noncomputable def yShiftCoeff (b : Multiplicative ↥(yKernelSub F G ι κ))
    (p : Idx F G ι κ) : ℕ :=
  yNat F G ι κ (-((b.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) p

/-- 支配引理（ℕ 级）：`m ∈ s` ⟹ `N_s` 的 `p` 分量不小于 `m` 的负分量读数。 -/
lemma yShiftCoeff_dom (s : Finset (Multiplicative ↥(yKernelSub F G ι κ)))
    (m : Multiplicative ↥(yKernelSub F G ι κ)) (hm : m ∈ s) (p : Idx F G ι κ) :
    yShiftCoeff F G ι κ m p ≤ (yKernelShift F G ι κ s) p := by
  rw [yKernelShift, Finsupp.finsetSum_apply]
  exact Finset.single_le_sum (f := fun b => yShiftCoeff F G ι κ b p)
    (fun b _ => Nat.zero_le _) hm

/-- `-m` 的分量被核上移位吸收：`(-m) p ≤ (N_s) p`（ℤ 级读数）。 -/
lemma yKernelShift_neg_le (s : Finset (Multiplicative ↥(yKernelSub F G ι κ)))
    (m : Multiplicative ↥(yKernelSub F G ι κ)) (hm : m ∈ s) (p : Idx F G ι κ) :
    (-((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) p
      ≤ ((yKernelShift F G ι κ s) p : ℤ) :=
  le_trans (le_yNat F G ι κ _ p)
    (Int.ofNat_le.mpr (yShiftCoeff_dom F G ι κ s m hm p))

/-- 对 `m ∈ s`，`yCast N_s + m` 逐点非负（负分量被 `yNat` 吸收）。 -/
lemma yKernelShift_add_nonneg (s : Finset (Multiplicative ↥(yKernelSub F G ι κ)))
    (m : Multiplicative ↥(yKernelSub F G ι κ)) (hm : m ∈ s) (p : Idx F G ι κ) :
    0 ≤ (yCast F G ι κ (yKernelShift F G ι κ s)
      + ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) p := by
  have key : (-((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) p
      ≤ ((yKernelShift F G ι κ s) p : ℤ) :=
    yKernelShift_neg_le F G ι κ s m hm p
  rw [Finsupp.neg_apply] at key
  have h2 := add_le_add_right key
    (((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ) p)
  rw [add_neg_cancel] at h2
  rw [add_comm] at h2
  rw [Finsupp.add_apply, yCast_apply F G ι κ]
  exact h2

/-- 移位在 `s` 上单射（系数提取用）。 -/
lemma yShift_injOn (s : Finset (Multiplicative ↥(yKernelSub F G ι κ))) :
    ∀ {m i : Multiplicative ↥(yKernelSub F G ι κ)}, m ∈ s → i ∈ s →
      yShift F G ι κ (yKernelShift F G ι κ s)
          ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
        = yShift F G ι κ (yKernelShift F G ι κ s)
          ((i.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ) →
      m = i := by
  intro m i hm hi hEq
  have h1 := yCast_yShift F G ι κ (yKernelShift_add_nonneg F G ι κ s m hm)
  have h2 := yCast_yShift F G ι κ (yKernelShift_add_nonneg F G ι κ s i hi)
  have h3 : yCast F G ι κ (yKernelShift F G ι κ s)
        + ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)
      = yCast F G ι κ (yKernelShift F G ι κ s)
        + ((i.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ) := by
    rw [← h1, ← h2, hEq]
  exact Multiplicative.ext (Subtype.ext (add_left_cancel h3))

/-- `yAeval` 单射（代数无关 ⟹ aeval 单射）。 -/
lemma yAeval_injective
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    Function.Injective (yAeval F G Q ι B κ) :=
  (algebraicIndependent_iff_injective_aeval).mp (algebraicIndependent_Y F G Q ι B κ hκ)

/-- (c) 核心：核上的重指数族 `m ↦ yPow m` 是 `F`-线性无关的（移位技巧）。 -/
lemma yPow_linearIndependent
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    LinearIndependent F (fun m : Multiplicative ↥(yKernelSub F G ι κ) =>
      yPow F G Q ι B κ ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) := by
  rw [linearIndependent_iff'']
  intro s g hg hsum i
  by_cases hi : i ∈ s
  · -- 整体乘 `yPow (yCast N_s)`，把每项推到非负象限
    have hmul : yPow F G Q ι B κ (yCast F G ι κ (yKernelShift F G ι κ s))
        * (∑ m ∈ s, g m • yPow F G Q ι B κ
            ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) = 0 := by
      rw [hsum, mul_zero]
    have hshift : (∑ m ∈ s, g m • yPow F G Q ι B κ
        (yCast F G ι κ (yKernelShift F G ι κ s)
          + ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ))) = 0 := by
      rw [← hmul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Algebra.mul_smul_comm, ← yPow_add]
    -- 把移位后的和识别为 `yAeval (Σ monomial)`
    have hterm : ∀ m ∈ s, yAeval F G Q ι B κ
        (MvPolynomial.monomial (yShift F G ι κ (yKernelShift F G ι κ s)
          ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) (g m))
        = g m • yPow F G Q ι B κ (yCast F G ι κ (yKernelShift F G ι κ s)
          + ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) := fun m hm => by
      rw [yAeval_monomial,
        ← yCast_yShift F G ι κ (yKernelShift_add_nonneg F G ι κ s m hm)]
    have hconv : (∑ m ∈ s, yAeval F G Q ι B κ
        (MvPolynomial.monomial (yShift F G ι κ (yKernelShift F G ι κ s)
          ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) (g m)))
        = ∑ m ∈ s, g m • yPow F G Q ι B κ (yCast F G ι κ (yKernelShift F G ι κ s)
          + ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) :=
      Finset.sum_congr rfl hterm
    have hpoly : yAeval F G Q ι B κ (∑ m ∈ s,
        MvPolynomial.monomial (yShift F G ι κ (yKernelShift F G ι κ s)
          ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) (g m)) = 0 := by
      rw [map_sum]
      exact hconv.trans hshift
    have hP : (∑ m ∈ s, MvPolynomial.monomial (yShift F G ι κ (yKernelShift F G ι κ s)
        ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) (g m)) = 0 :=
      yAeval_injective F G Q ι B κ hκ (by rw [hpoly, map_zero])
    -- 系数提取：移位后的重指数族互异
    have hcoeff := congrArg (fun P : MvPolynomial (Idx F G ι κ) F =>
      P.coeff (yShift F G ι κ (yKernelShift F G ι κ s)
        ((i.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ))) hP
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
    have hsingle : (∑ m ∈ s, (MvPolynomial.monomial (yShift F G ι κ (yKernelShift F G ι κ s)
          ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) (g m)).coeff
            (yShift F G ι κ (yKernelShift F G ι κ s)
              ((i.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)))
        = (MvPolynomial.monomial (yShift F G ι κ (yKernelShift F G ι κ s)
            ((i.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) (g i)).coeff
              (yShift F G ι κ (yKernelShift F G ι κ s)
                ((i.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro b hb hne
        rw [MvPolynomial.coeff_monomial,
          if_neg (fun hcontra => hne (yShift_injOn F G ι κ s hb hi hcontra))]
      · intro hi_notin
        exact absurd hi hi_notin
    rw [hsingle, MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact hcoeff
  · exact hg i hi

/-- (c) `yKernelAlgHom` 单射（系数展开 ＋ 线性无关）。 -/
lemma yKernelAlgHom_injective
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    Function.Injective (yKernelAlgHom F G Q ι B κ) := by
  intro x y hxy
  have hzero : yKernelAlgHom F G Q ι B κ (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hdecomp : (∑ m ∈ (x - y).coeff.support,
      MonoidAlgebra.single m ((x - y).coeff m)) = x - y :=
    MonoidAlgebra.sum_coeff_single (x - y)
  have hlin : (∑ m ∈ (x - y).coeff.support, (x - y).coeff m • yPow F G Q ι B κ
      ((m.toAdd : ↥(yKernelSub F G ι κ)) : yExp F G ι κ)) = 0 := by
    rw [← hdecomp, map_sum] at hzero
    refine Eq.trans ?_ hzero
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [yKernelAlgHom_single]
  have hall : ∀ m : Multiplicative ↥(yKernelSub F G ι κ), (x - y).coeff m = 0 :=
    (linearIndependent_iff''.mp (yPow_linearIndependent F G Q ι B κ hκ))
      (x - y).coeff.support (fun m => (x - y).coeff m)
      (fun m hm => Finsupp.notMem_support_iff.mp hm) hlin
  have hcoeff0 : (x - y).coeff = 0 := Finsupp.ext hall
  exact sub_eq_zero.mp (MonoidAlgebra.coeff_injective (by
    rw [hcoeff0, MonoidAlgebra.coeff_zero]))

/-- (c) `yKernelAlgHom` 的像落在不变量域中。 -/
lemma yKernelAlgHom_mem_latticeInvariants
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (x : latticeAlgebra F ↥(yKernelSub F G ι κ)) :
    yKernelAlgHom F G Q ι B κ x ∈ latticeInvariants F G Q := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      rw [yKernelAlgHom_of]
      exact yPow_mem_latticeInvariants F G Q ι B κ hκ
        ((yKernelSub_mem_iff F G ι κ (m.toAdd : yExp F G ι κ)).mp m.toAdd.2)
  | add x y hx hy =>
      rw [map_add]
      exact Subfield.add_mem _ hx hy
  | smul r x hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
      exact Subfield.mul_mem _ ((mem_latticeInvariants_iff (F := F) (G := G) (M := Q)
        (algebraMap F (latticeFunctionField F Q) r)).mpr fun g =>
          smul_algebraMap_latticeFunctionField F G Q g r) hx

/-! ## §5 (b) 分式域转运：`F(↥yKernel) ≃ₐ[F] F(ℤ^r)`（移位机制的收尾） -/

/-- (b) 核函数域 ≃ 自由格函数域（`MonoidAlgebra.domCongr` 经 `IsFractionRing` 上延）。 -/
noncomputable def yKernelFracEquiv :
    latticeFunctionField F ↥(yKernelSub F G ι κ)
      ≃ₐ[F] latticeFunctionField F (Fin (yKernelRank F G ι κ) → ℤ) :=
  IsFractionRing.algEquivOfAlgEquiv
    (MonoidAlgebra.domCongr F F (yKernelMulEquiv F G ι κ))

/-! ## §6 (d) 不变量代数有理性：`F(↥yKernel) ≃ₐ[F] ↥(latticeInvariantsAlg F G Q)` -/

/-- 不变量代数的 `Field` 结构（载体与 `latticeInvariants` 相同 ⟹ `inferInstanceAs`）。 -/
noncomputable instance instFieldInvariantsAlgM6C : Field ↥(latticeInvariantsAlg F G Q) :=
  inferInstanceAs (Field ↥(latticeInvariants F G Q))

/-- (d) 前置：`lift` 的像域 = 不变量域。

方向 1 用 (c) 的 `yKernelAlgHom_mem_latticeInvariants`（像 ⊆ 不变量）；
方向 2 用 M6-B 的闭包等式 `latticeInvariants_eq_adjoin_yPow` ＋ `adjoin_toSubfield`，
把 `adjoin F (range yPow)` 的生成元（含 `algebraMap` 与 `yPow m`）都送进
`Subfield.closure (range yKernelAlgHom)`（后者用 `yKernelAlgHom_witness` 见证）。 -/
theorem lift_fieldRange_eq_latticeInvariants
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    (IsFractionRing.lift (yKernelAlgHom_injective F G Q ι B κ hκ)
      : latticeFunctionField F ↥(yKernelSub F G ι κ) →+*
        latticeFunctionField F Q).fieldRange = latticeInvariants F G Q := by
  rw [IsFractionRing.lift_fieldRange]
  refine le_antisymm ?_ ?_
  · refine Subfield.closure_le.mpr fun y hy => ?_
    rw [SetLike.mem_coe] at hy
    obtain ⟨x, rfl⟩ := (AlgHom.mem_range (yKernelAlgHom F G Q ι B κ)).mp hy
    exact yKernelAlgHom_mem_latticeInvariants F G Q ι B κ hκ x
  · intro y hy
    have hy1 : y ∈ (latticeInvariants F G Q : Set (latticeFunctionField F Q)) := hy
    rw [latticeInvariants_eq_adjoin_yPow F G Q ι B κ hκ] at hy1
    have hy2 : y ∈ ((IntermediateField.adjoin F (Set.range fun m : ↥(yKernel F G ι κ) =>
        yPow F G Q ι B κ (m : yExp F G ι κ))).toSubfield :
        Set (latticeFunctionField F Q)) := hy1
    rw [IntermediateField.adjoin_toSubfield] at hy2
    have h1 : Set.range (algebraMap F (latticeFunctionField F Q)) ⊆
        ↑(Subfield.closure (↑(yKernelAlgHom F G Q ι B κ).range :
          Set (latticeFunctionField F Q))) := by
      rintro _ ⟨c, rfl⟩
      exact Subfield.subset_closure ((AlgHom.mem_range (yKernelAlgHom F G Q ι B κ)).mpr
        ⟨algebraMap F (latticeAlgebra F ↥(yKernelSub F G ι κ)) c,
          AlgHom.commutes (yKernelAlgHom F G Q ι B κ) c⟩)
    have h2 : Set.range (fun m : ↥(yKernel F G ι κ) =>
        yPow F G Q ι B κ (m : yExp F G ι κ)) ⊆
        ↑(Subfield.closure (↑(yKernelAlgHom F G Q ι B κ).range :
          Set (latticeFunctionField F Q))) := by
      rintro _ ⟨m, rfl⟩
      exact Subfield.subset_closure ((AlgHom.mem_range (yKernelAlgHom F G Q ι B κ)).mpr
        ⟨MonoidAlgebra.single (Multiplicative.ofAdd (⟨m.1, m.2⟩ : ↥(yKernelSub F G ι κ))) 1,
          yKernelAlgHom_witness F G Q ι B κ ⟨m.1, m.2⟩⟩)
    have hle : Subfield.closure (Set.range (algebraMap F (latticeFunctionField F Q))
        ∪ Set.range (fun m : ↥(yKernel F G ι κ) => yPow F G Q ι B κ (m : yExp F G ι κ)))
        ≤ Subfield.closure (↑(yKernelAlgHom F G Q ι B κ).range :
          Set (latticeFunctionField F Q)) :=
      Subfield.closure_le.mpr (Set.union_subset h1 h2)
    exact hle hy2

/-- (d) 前置：`lift` 的像落在不变量代数中（`IsLocalization.surj` 分解 ＋ (c) 的成员性）。 -/
lemma yKernel_lift_mem
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i))
    (x : latticeFunctionField F ↥(yKernelSub F G ι κ)) :
    IsFractionRing.liftAlgHom (yKernelAlgHom_injective F G Q ι B κ hκ) x
      ∈ latticeInvariantsAlg F G Q := by
  change IsFractionRing.liftAlgHom (yKernelAlgHom_injective F G Q ι B κ hκ) x
    ∈ (latticeInvariantsAlg F G Q : Set (latticeFunctionField F Q))
  rw [← latticeInvariants_carrier_eq F G Q]
  show IsFractionRing.lift (yKernelAlgHom_injective F G Q ι B κ hκ) x
    ∈ latticeInvariants F G Q
  obtain ⟨⟨a, b⟩, hb⟩ := IsLocalization.surj
    (nonZeroDivisors (latticeAlgebra F ↥(yKernelSub F G ι κ))) x
  have hb0 : (b : latticeAlgebra F ↥(yKernelSub F G ι κ)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hbne : yKernelAlgHom F G Q ι B κ (b : latticeAlgebra F ↥(yKernelSub F G ι κ)) ≠ 0 :=
    fun h => hb0 (yKernelAlgHom_injective F G Q ι B κ hκ (by rw [h, map_zero]))
  have hx : IsFractionRing.lift (yKernelAlgHom_injective F G Q ι B κ hκ) x
      = yKernelAlgHom F G Q ι B κ a
        * (yKernelAlgHom F G Q ι B κ (b : latticeAlgebra F ↥(yKernelSub F G ι κ)))⁻¹ := by
    have h := congrArg (IsFractionRing.lift (yKernelAlgHom_injective F G Q ι B κ hκ)) hb
    rw [map_mul, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at h
    rw [← div_eq_mul_inv]
    exact (eq_div_iff hbne).mpr h
  rw [hx]
  exact Subfield.mul_mem _ (yKernelAlgHom_mem_latticeInvariants F G Q ι B κ hκ a)
    (Subfield.inv_mem _ (yKernelAlgHom_mem_latticeInvariants F G Q ι B κ hκ _))

/-- 域 ⟶ 非平凡环的环同态单射（(d) 的单射性用）。 -/
lemma injective_of_field_y {K' L : Type*} [Field K'] [Ring L] [Nontrivial L]
    (f : K' →+* L) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  have h0 : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h1 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hmul : (x - y) * (x - y)⁻¹ = 1 := mul_inv_cancel₀ h0
  have h2 : (1 : L) = 0 := by rw [← map_one f, ← hmul, map_mul, h1, zero_mul]
  exact one_ne_zero h2

/-- (d) `F(↥yKernel) ≃ₐ[F] ↥(latticeInvariantsAlg F G Q)`（限制 `lift` 到不变量代数上）。 -/
noncomputable def yKernelFracEquivInvariantsAlg
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    latticeFunctionField F ↥(yKernelSub F G ι κ) ≃ₐ[F] ↥(latticeInvariantsAlg F G Q) :=
  AlgEquiv.ofBijective
    ((IsFractionRing.liftAlgHom (yKernelAlgHom_injective F G Q ι B κ hκ)).codRestrict
      (latticeInvariantsAlg F G Q) (yKernel_lift_mem F G Q ι B κ hκ))
    ⟨fun _ _ hxy => injective_of_field_y _ (Subtype.ext_iff.mp hxy), fun z => by
      have hz : (z : latticeFunctionField F Q)
          ∈ (IsFractionRing.lift (yKernelAlgHom_injective F G Q ι B κ hκ)
              : latticeFunctionField F ↥(yKernelSub F G ι κ) →+*
                latticeFunctionField F Q).fieldRange := by
        rw [lift_fieldRange_eq_latticeInvariants F G Q ι B κ hκ]
        exact z.2
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hz
      exact ⟨x, Subtype.ext hx⟩⟩

/-! ## §7 (e) 主定理：置换基 ⟹ 不变量代数有理性 -/

/-- 核代数侧收口：`F(↥yKernel)` 有理 ⟹ 不变量代数有理（(b) 转接到自由格 ＋ 1α）。 -/
theorem isRational_latticeInvariantsAlg_yKernel
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    IsRational F ↥(latticeInvariantsAlg F G Q) := by
  obtain ⟨n, ⟨e⟩⟩ := isRational_latticeFunctionField_free F (yKernelRank F G ι κ)
  exact ⟨n, ⟨(yKernelFracEquivInvariantsAlg F G Q ι B κ hκ).symm.trans
    ((yKernelFracEquiv F G ι κ).trans e)⟩⟩

/-- 置换基条件（§4.1 假设外形）。 -/
def PermBasisHyp (G : Type u) [CommGroup G] [Fintype G]
    (Q : Type u) [AddCommGroup Q] [Module ℤ Q] [DistribMulAction G Q]
    (ι : Type u) [Fintype ι]
    (B : Module.Basis ι ℤ Q) (κ : G →* Equiv.Perm ι) : Prop :=
  ∀ (σ : G) (i : ι),
    mulEquivOfSMul G Q σ (permMono (P := Q) B i) = permMono (P := Q) B (κ σ i)

/-- 类型锁定：外形一旦被改动，本 `rfl` 立即编译失败。 -/
theorem permBasisHyp_typeLock :
    (PermBasisHyp G Q ι B κ)
      = (∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
          = permMono (P := Q) B (κ σ i)) := rfl

/-- (e) 主定理：`(B, κ, hκ)` 为置换基 ⟹ `F(Q)^G` 有理。 -/
theorem isRational_latticeInvariantsAlg_of_permBasis
    (hκ : ∀ (σ : G) (i : ι), mulEquivOfSMul G Q σ (permMono (P := Q) B i)
      = permMono (P := Q) B (κ σ i)) :
    IsRational F ↥(latticeInvariantsAlg F G Q) :=
  isRational_latticeInvariantsAlg_yKernel F G Q ι B κ hκ

/-- 类型锁定（接线）：`PermBasisHyp` 直接可调主定理 ⟹ 假设外形与主定理一致。 -/
theorem permBasisHyp_apply_typeLock
    (h : PermBasisHyp G Q ι B κ) :
    IsRational F ↥(latticeInvariantsAlg F G Q) :=
  isRational_latticeInvariantsAlg_of_permBasis F G Q ι B κ h

/-! ## §8 公理闸门（本文件全部新声明） -/

#print axioms yNat
#print axioms yNat_apply
#print axioms le_yNat
#print axioms yCast_yNat_of_nonneg
#print axioms yShift
#print axioms yCast_yShift
#print axioms yPow_zero
#print axioms yPow_add
#print axioms yKernelSub
#print axioms yKernelRank
#print axioms yKernelBasis
#print axioms yKernelMulEquiv
#print axioms yKernelToQMulHom
#print axioms yKernelToQMulHom_injective
#print axioms instUniqueProdsY
#print axioms yKernelSub_mem_iff
#print axioms yPowMonoidHom
#print axioms yKernelAlgHom
#print axioms yKernelAlgHom_single
#print axioms yKernelAlgHom_of
#print axioms yKernelAlgHom_witness
#print axioms yKernelShift
#print axioms yShiftCoeff
#print axioms yShiftCoeff_dom
#print axioms yKernelShift_neg_le
#print axioms yKernelShift_add_nonneg
#print axioms yShift_injOn
#print axioms yAeval_injective
#print axioms yPow_linearIndependent
#print axioms yKernelAlgHom_injective
#print axioms yKernelAlgHom_mem_latticeInvariants
#print axioms yKernelFracEquiv
#print axioms instFieldInvariantsAlgM6C
#print axioms lift_fieldRange_eq_latticeInvariants
#print axioms yKernel_lift_mem
#print axioms injective_of_field_y
#print axioms yKernelFracEquivInvariantsAlg
#print axioms isRational_latticeInvariantsAlg_yKernel
#print axioms PermBasisHyp
#print axioms permBasisHyp_typeLock
#print axioms isRational_latticeInvariantsAlg_of_permBasis
#print axioms permBasisHyp_apply_typeLock

end

end EM

end ABGV52
