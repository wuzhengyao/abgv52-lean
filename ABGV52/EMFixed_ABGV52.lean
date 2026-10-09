/-
  ABGV-5.2 —— **本体形式化 A · M4c（EMFixed）**：Lenstra (1.4) 的分式域固定域层

  目标（`wiki/proj-ABGV52-formalize-em.md` §3.4 M4c 设计）：
    `IsRational ↥(l^G) ↥(l(N)^G)`——其中 l := `latticeFunctionField F M`、
    l(N) := `semiFunctionField F M P`（= M4a 的 `FractionRing l[P]`）、
    基域用 l^G 在 l(N) 中的像（`FixedPoints.subfield G l` 经 `algebraMap` 的 `.map`）。

  证明结构（三段）：
    ① 分式域桥：`σ • algebraMap a = algebraMap (semiAlgEquiv σ a)`＋ `FaithfulSMul`
       从 l 传到 l(N)；
    ② 生成性（不用单项式展开）：提取的 y（M4b `W_fixed_extraction`）的像 Y 与
       l^G-像生成 l(N)——x_j := single (x j) 1 ∈ W = span(y) ⟹ algebraMap x_j ∈ l·E；
       l·E 为域 ⟹ 含 x_j^{±1} ⟹ 含 Frac(l[x_j]) = l(N)；
    ③ 度账：`[l(N):E] = |G|·X`（Artin）且 `[l(N):E] ≤ |G|`（素元素＋minpoly 度比较）
       ⟹ X = 1 ⟹ E = l(N)^G；再经 `AlgebraicIndependent.aevalEquivField` 出 IsRational。

  **无 sorry、无自造公理**（交付时）。
-/
import ABGV52.EMRational_ABGV52
import ABGV52.EMArtin_ABGV52
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

namespace ABGV52
namespace EM

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]
variable {ι : Type*} [Fintype ι]

/-! ## 1. 分式域层桥与忠实性 -/

/-- **分式域层作用的桥**：`σ • x = ringEquivOfRingEquiv (semiAlgEquiv σ) x`
（`compHom` 构造，`rfl` 级）。 -/
lemma semiFunctionField_smul (σ : G)
    (x : semiFunctionField (F := F) (M := M) (P := P)) :
    σ • x = IsFractionRing.ringEquivOfRingEquiv
      (A := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (K := semiFunctionField (F := F) (M := M) (P := P))
      (B := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (L := semiFunctionField (F := F) (M := M) (P := P))
      (semiAlgEquiv (M := M) σ) x := rfl

/-- **`algebraMap` 与作用交换**（l[P] 层）：`σ • algebraMap a =
algebraMap (semiAlgEquiv σ a)`。 -/
lemma smul_algebraMap_semiAlg (σ : G)
    (a : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) :
    σ • algebraMap _ (semiFunctionField (F := F) (M := M) (P := P)) a
      = algebraMap _ _ (semiAlgEquiv (M := M) σ a) := by
  have h := IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (A := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (K := semiFunctionField (F := F) (M := M) (P := P))
    (B := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (L := semiFunctionField (F := F) (M := M) (P := P))
    (semiAlgEquiv (M := M) σ) a
  rw [semiFunctionField_smul]
  exact h

/-- **常元层的半线性公式**：`semiAlgEquiv σ (algebraMap c) =
algebraMap (coeffRingEquiv σ c)`（l[P] 层，`single 1 c` 形态）。 -/
lemma semiAlgEquiv_algebraMap_lattice (σ : G) (c : latticeFunctionField F M) :
    semiAlgEquiv (M := M) σ
        ((algebraMap (latticeFunctionField F M)
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))) c)
      = (algebraMap (latticeFunctionField F M)
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)))
          (coeffRingEquiv (M := M) σ c) := by
  rw [show (algebraMap (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))) c
      = MonoidAlgebra.single (1 : Multiplicative P) c from rfl]
  rw [semiAlgEquiv_single]
  have hm : mulEquivOfSMul G P σ (1 : Multiplicative P) = 1 := by
    rw [mulEquivOfSMul_apply]
    show Multiplicative.ofAdd (σ • (0 : P)) = (1 : Multiplicative P)
    rw [smul_zero]
    rfl
  rw [hm]
  rfl

/-- **忠实性传递**：`FaithfulSMul G l ⟹ FaithfulSMul G l(N)`。 -/
theorem faithfulSMul_semiFunctionField
    (hfaith : FaithfulSMul G (latticeFunctionField F M)) :
    FaithfulSMul G (semiFunctionField (F := F) (M := M) (P := P)) := by
  refine ⟨fun {σ τ} h => ?_⟩
  have h' : ∀ c : latticeFunctionField F M, σ • c = τ • c := by
    intro c
    have hx := h ((algebraMap _ (semiFunctionField (F := F) (M := M) (P := P)))
      ((algebraMap (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))) c))
    rw [smul_algebraMap_semiAlg, smul_algebraMap_semiAlg] at hx
    rw [semiAlgEquiv_algebraMap_lattice, semiAlgEquiv_algebraMap_lattice] at hx
    have h1 : (algebraMap (latticeFunctionField F M)
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)))
          (coeffRingEquiv (M := M) σ c)
        = (algebraMap (latticeFunctionField F M)
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)))
          (coeffRingEquiv (M := M) τ c) :=
      (IsFractionRing.injective
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))) hx
    have h2 : coeffRingEquiv (M := M) σ c = coeffRingEquiv (M := M) τ c := by
      have hc := congrArg (fun z : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) =>
        z.coeff (1 : Multiplicative P)) h1
      simpa [Finsupp.single_apply] using hc
    rwa [coeffRingEquiv_apply, coeffRingEquiv_apply] at h2
  exact hfaith.eq_of_smul_eq_smul h'

/-\! ## 2. 像域 K₀ 与手搭代数实例 -/

/-- **K₀**：`l^G` 在 `l(N)` 中的像（作为 `Subfield`）。 -/
noncomputable def K0 : Subfield (semiFunctionField (F := F) (M := M) (P := P)) :=
  (FixedPoints.subfield G (latticeFunctionField F M)).map
    (algebraMap (latticeFunctionField F M) (semiFunctionField (F := F) (M := M) (P := P)))

/-- 不动点隶属的 iff（`rw` 友好版；`.copy` 型防 `rw` 失配）。 -/
lemma mem_fixed_iff (x : semiFunctionField (F := F) (M := M) (P := P)) :
    x ∈ FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))
      ↔ ∀ σ : G, σ • x = x := by
  rw [FixedPoints.subfield]
  exact MulAction.mem_fixedPoints

/-- **K₀ 的元素在 `l(N)` 中不动**（`l^G` 的不动性经等价变性传递）。 -/
lemma K0_mem_fixed {x : semiFunctionField (F := F) (M := M) (P := P)}
    (hx : x ∈ K0 (G := G) (F := F) (M := M) (P := P)) :
    x ∈ FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) := by
  rw [show K0 (G := G) (F := F) (M := M) (P := P)
      = (FixedPoints.subfield G (latticeFunctionField F M)).map
        (algebraMap (latticeFunctionField F M) (semiFunctionField (F := F) (M := M) (P := P)))
      from rfl] at hx
  rw [Subfield.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [mem_fixed_iff]
  intro σ
  change σ • (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P))
      (algebraMap (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) c))
    = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P))
      (algebraMap (latticeFunctionField F M)
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) c)
  rw [smul_algebraMap_semiAlg, semiAlgEquiv_algebraMap_lattice]
  rw [show coeffRingEquiv (M := M) σ c = σ • c from rfl]
  have hc' := (mem_latticeInvariants_iff (F := F) (G := G) (M := M) c).mp hc
  rw [hc' σ]

/-- 提升环同态 `↥K₀ →+* ↥(l(N)^G)`（值落在不动元内）。 -/
noncomputable def K0ToFixed : ↥(K0 (G := G) (F := F) (M := M) (P := P)) →+*
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) where
  toFun x := ⟨(x : semiFunctionField (F := F) (M := M) (P := P)),
    K0_mem_fixed (F := F) (M := M) (P := P) x.2⟩
  map_one' := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

/-- **`l(N)^G` 作为 `K₀`-代数**（手搭实例；中间域塔无现成实例）。 -/
noncomputable instance instAlgebraFixedK0 : Algebra ↥(K0 (G := G) (F := F) (M := M) (P := P))
    ↥(FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P))) :=
  (K0ToFixed (F := F) (M := M) (P := P)).toAlgebra

/-\! ## 3. 生成性机器（B-坐标乘积展开 ⟹ l(N) ⊆ l·E） -/

/-- **B-坐标乘积展开**（乘法群层）：`ofAdd ((B.repr).symm c) = ∏ j, (x_j)^{c_j}`
（`Finsupp` 归纳；这是"单项式＝幂积"的精确形态）。 -/
lemma permMono_prod_expansion (B : Module.Basis ι ℤ P) (c : ι →₀ ℤ) :
    Multiplicative.ofAdd ((B.repr).symm c)
      = c.prod (fun j n => (permMono (P := P) B j) ^ n) := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      rw [map_zero, Finsupp.prod_zero_index]
      rfl
  | single_add j n c hc hn ih =>
      rw [map_add, ofAdd_add,
        Finsupp.prod_add_index (fun k _ => zpow_zero _)
          (fun k _ b₁ b₂ => zpow_add _ _ _), ih]
      rw [Module.Basis.repr_symm_single B j n, Finsupp.prod_single_index]
      congr 1
      -- 目标：ofAdd (n • B j) = ofAdd (B j) ^ n（两侧 ℤ-smul 实例路径不同：
      -- `Module` 公理路径 vs `ZSMul` 规范路径 ⟹ `convert` 剥层后经
      -- `int_smul_eq_zsmul` 统一实例）
      convert ofAdd_zsmul n (B j) using 2
      · exact int_smul_eq_zsmul (inferInstance) n (B j)
      · rfl
      · exact zpow_zero _

/-\! ## 3b. 生成性：l(N) ⊆ E ⊔ S_l ⟹ E ⊔ S_l = ⊤ -/

section Generation

variable (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
variable (hρ : ∀ (σ : G) (i : ι),
  mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
variable (n : ℕ) (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))

/-- 提取族的像（在 l(N) 中）。 -/
noncomputable def Yf (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B)) :
    Fin n → semiFunctionField (F := F) (M := M) (P := P) :=
  fun i => algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (semiFunctionField (F := F) (M := M) (P := P)) (y i).1

/-- **E**：`Yf` 与 `l`-像（同一个 adjoin；`⊔` 经 `sup_def` 即此形）。 -/
noncomputable def Egen (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B)) :
    IntermediateField ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (semiFunctionField (F := F) (M := M) (P := P)) :=
  IntermediateField.adjoin _ (Set.range (Yf (F := F) (M := M) (P := P) B n y) ∪
    Set.range fun c : latticeFunctionField F M =>
      algebraMap (latticeFunctionField F M) (semiFunctionField (F := F) (M := M) (P := P)) c)

/-- 分式域层的单项式像（辅助）。 -/
noncomputable def hmono : Multiplicative P →* semiFunctionField (F := F) (M := M) (P := P) where
  toFun m := algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (semiFunctionField (F := F) (M := M) (P := P))
    (MonoidAlgebra.single m (1 : latticeFunctionField F M))
  map_one' := by
    rw [show (1 : Multiplicative P) = Multiplicative.ofAdd (0 : P) from rfl]
    rw [show MonoidAlgebra.single (Multiplicative.ofAdd (0 : P))
        (1 : latticeFunctionField F M)
      = (algebraMap (latticeFunctionField F M)
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))) 1 from rfl]
    rw [map_one, map_one]
  map_mul' a b := by
    rw [show MonoidAlgebra.single (a * b) (1 : latticeFunctionField F M)
        = MonoidAlgebra.single a (1 : latticeFunctionField F M)
          * MonoidAlgebra.single b (1 : latticeFunctionField F M) from by
      rw [MonoidAlgebra.single_mul_single, mul_one]]
    rw [map_mul]

/-- `hmono` 在生成元上的值：`hmono (x_j) = algebraMap (single (x_j) 1)`（rfl）。 -/
lemma hmono_permMono (j : ι) :
    hmono (F := F) (M := M) (P := P) (permMono (P := P) B j)
      = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P))
          (MonoidAlgebra.single (permMono (P := P) B j) (1 : latticeFunctionField F M)) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- **生成性主引理**：`Ead ⊔ Sl = ⊤`（即 `l(N) = l·E` 的中间域形式）。

证明链：x_j ∈ W = span(y) 给 `hmono x_j = Σ (l-系数)·Yf`；B-坐标展开
（`permMono_prod_expansion`）给任意单项式＝幂积 ⟹ `hmono`-像全在 `Ead ⊔ Sl`；
经 `MonoidAlgebra.induction_on` 抬到整个 `l[P]`；经 `div_surjective` 抬到分式域。 -/
theorem generation_sup_eq_top
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤) :
    Egen (G := G) (F := F) (M := M) (P := P) B n y = ⊤ := by
  -- 记 M' := Ead ⊔ Sl
  have hmem : ∀ a : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P),
      (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)) a)
        ∈ (Egen (G := G) (F := F) (M := M) (P := P) B n y) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of m =>
        -- hmono m ∈ M'：经 B-坐标展开为幂积
        change hmono (F := F) (M := M) (P := P) m
          ∈ (Egen (G := G) (F := F) (M := M) (P := P) B n y)
        -- 展开：m = ofAdd m.toAdd = ∏ x_j^{c_j}
        have hexp := permMono_prod_expansion (P := P) B (B.repr m.toAdd)
        rw [LinearEquiv.symm_apply_apply, ofAdd_toAdd] at hexp
        rw [hexp, show (B.repr m.toAdd).prod (fun j n => (permMono (P := P) B j) ^ n)
            = (B.repr m.toAdd).support.prod
                (fun j => (permMono (P := P) B j) ^ ((B.repr m.toAdd) j)) from rfl,
          map_prod]
        -- 诸因子：hmono (x_j ^ c_j) = (hmono x_j) ^ c_j ∈ M'
        refine IntermediateField.prod_mem
          (S := Egen (G := G) (F := F) (M := M) (P := P) B n y) ?_
        intro j _
        rw [MonoidHom.map_zpow]
        refine IntermediateField.pow_mem
          (S := Egen (G := G) (F := F) (M := M) (P := P) B n y) ?_
          ((B.repr m.toAdd) j)
        -- hmono (x_j) ∈ M'：x_j = Σ c_i • y_i（a_j ∈ W = span y）
        have hxj_W : (⟨MonoidAlgebra.single (permMono (P := P) B j)
            (1 : latticeFunctionField F M), permMono_single_mem_W B j⟩ :
            ↥(W (F := F) (M := M) (P := P) B))
            ∈ Submodule.span (latticeFunctionField F M)
              (Set.range (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))) := by
          rw [hy_span]
          exact Submodule.mem_top
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
          (R := latticeFunctionField F M)).mp hxj_W
        -- hc : ∑ i, c i • y i = ⟨single …, _⟩
        have hcv : (∑ i, c i • y i).val
            = MonoidAlgebra.single (permMono (P := P) B j)
                (1 : latticeFunctionField F M) := by
          simpa using congrArg Subtype.val hc
        -- 转代数层：hmono x_j = Σ (algebraMap 系数) * Yf i
        rw [show hmono (F := F) (M := M) (P := P) (permMono (P := P) B j) ∈
            (Egen (G := G) (F := F) (M := M) (P := P) B n y)
          ↔ (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
              (semiFunctionField (F := F) (M := M) (P := P))
              (MonoidAlgebra.single (permMono (P := P) B j)
                (1 : latticeFunctionField F M)))
              ∈ (Egen (G := G) (F := F) (M := M) (P := P) B n y) from Iff.rfl]
        rw [← hcv]
        -- 目标：algebraMap (Σ_i c_i • y_i) ∈ M'（LHS 经 hcv 换成和新形）
        rw [show (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
              (semiFunctionField (F := F) (M := M) (P := P))
              ((∑ i, c i • y i) : ↥(W (F := F) (M := M) (P := P) B)).val)
            = ∑ i, (algebraMap (latticeFunctionField F M)
                  (semiFunctionField (F := F) (M := M) (P := P)) (c i)
                * Yf (F := F) (M := M) (P := P) B n y i) from by
          have hsum : (∑ i, c i • y i).val
              = ∑ i, c i • (y i).val := by
            simpa using map_sum (Submodule.subtype
              (W (F := F) (M := M) (P := P) B)) Finset.univ
              (fun i => c i • y i)
          rw [hsum, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          show (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
              (semiFunctionField (F := F) (M := M) (P := P)) (c i • (y i).val))
            = (algebraMap (latticeFunctionField F M)
                (semiFunctionField (F := F) (M := M) (P := P)) (c i))
              * (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
                (semiFunctionField (F := F) (M := M) (P := P)) (y i).val)
          rw [Algebra.smul_def, map_mul]
          rfl]
        refine IntermediateField.sum_mem
          (S := Egen (G := G) (F := F) (M := M) (P := P) B n y) ?_
        intro i _
        have h1 : (algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) (c i))
            ∈ (Egen (G := G) (F := F) (M := M) (P := P) B n y) :=
          IntermediateField.subset_adjoin _ _ (Or.inr ⟨c i, rfl⟩)
        have h2 : Yf (F := F) (M := M) (P := P) B n y i
            ∈ (Egen (G := G) (F := F) (M := M) (P := P) B n y) :=
          IntermediateField.subset_adjoin _ _ (Or.inl ⟨i, rfl⟩)
        exact mul_mem h1 h2
    | add x ys hx hy =>
        rw [map_add]
        exact add_mem hx hy
    | smul r x hx =>
        rw [Algebra.smul_def, map_mul]
        exact mul_mem (IntermediateField.subset_adjoin _ _ (Or.inr ⟨r, rfl⟩)) hx
  -- 分式域层：z = a/b
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, hzab⟩ := IsFractionRing.div_surjective
    (A := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) z
  rw [← hzab]
  exact div_mem (hmem a) (hmem b)

end Generation


/-\! ## 4. 度账机器 -/

/-- **小 adjoin**：`l^π(y_i)`（＝ `E_small`；度账用；注意与 `Egen = E_small ⊔ S_l` 的区别）。 -/
noncomputable def Esm (B : Module.Basis ι ℤ P) (n : ℕ)
    (y : Fin n → ↥(W (F := F) (M := M) (P := P) B)) :
    IntermediateField ↥(K0 (G := G) (F := F) (M := M) (P := P))
      (semiFunctionField (F := F) (M := M) (P := P)) :=
  IntermediateField.adjoin _ (Set.range (Yf (F := F) (M := M) (P := P) B n y))

section Degree

variable (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
variable (hρ : ∀ (σ : G) (i : ι),
  mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
variable (n : ℕ) (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
variable (hy_fix : ∀ (i : Fin n) (σ : G),
  (actW (F := F) (M := M) B ρ hρ).smul σ (y i) = y i)
variable (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)

/-- **Yf 不动**（提取族的不动性经分式域桥传递）。 -/
lemma Yf_mem_fixed
    (hyfix : ∀ (i : Fin n) (σ : G),
      semiAlgEquiv (M := M) σ (y i).1 = (y i).1)
    (i : Fin n) :
    Yf (F := F) (M := M) (P := P) B n y i
      ∈ FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) := by
  rw [mem_fixed_iff]
  intro σ
  show σ • (algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
      (semiFunctionField (F := F) (M := M) (P := P)) (y i).1)
    = algebraMap (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P)) (y i).1
  rw [smul_algebraMap_semiAlg]
  rw [show semiAlgEquiv (M := M) σ (y i).1 = (y i).1 from hyfix i σ]

/-- **`Esm ≤ l(N)^G`**：小 adjoin 落在固定域内。 -/
theorem Esm_le_fixed
    (hyfix : ∀ (i : Fin n) (σ : G),
      semiAlgEquiv (M := M) σ (y i).1 = (y i).1) :
    (Esm (G := G) (F := F) (M := M) (P := P) B n y : Set (semiFunctionField (F := F) (M := M) (P := P)))
      ⊆ (FixedPoints.subfield G (semiFunctionField (F := F) (M := M) (P := P)) :
          Set (semiFunctionField (F := F) (M := M) (P := P))) := by
  intro x hx
  rw [show Esm (G := G) (F := F) (M := M) (P := P) B n y
      = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
          (Set.range (Yf (F := F) (M := M) (P := P) B n y)) from rfl] at hx
  refine IntermediateField.adjoin_induction
    (F := ↥(K0 (G := G) (F := F) (M := M) (P := P)))
    (s := Set.range (Yf (F := F) (M := M) (P := P) B n y))
    (p := fun x _ => x ∈ FixedPoints.subfield G
      (semiFunctionField (F := F) (M := M) (P := P))) ?_ ?_ ?_ ?_ ?_ hx
  · intro x' hx'
    obtain ⟨i, rfl⟩ := hx'
    exact Yf_mem_fixed (G := G) (F := F) (M := M) (B := B) (n := n) (y := y)
      (hyfix := hyfix) i
  · intro r
    exact K0_mem_fixed (F := F) (M := M) (P := P) r.2
  · intro x' x'' hx' hx'' ihx' ihx''
    exact add_mem ihx' ihx''
  · intro x' hx' ih
    exact inv_mem ih
  · intro x' x'' hx' hx'' ihx' ihx''
    exact mul_mem ihx' ihx''

end Degree

/-\! ## 5. Sl、素元素与度账 -/

section Count

variable (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
variable (hρ : ∀ (σ : G) (i : ι),
  mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
variable (n : ℕ) (y : Fin n → ↥(W (F := F) (M := M) (P := P) B))
variable (hyfix : ∀ (i : Fin n) (σ : G),
  semiAlgEquiv (M := M) σ (y i).1 = (y i).1)
variable (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤)
variable [FaithfulSMul G (latticeFunctionField F M)]

/-- **S_l**：`l` 的像生成的中间域。 -/
noncomputable def SlI : IntermediateField ↥(K0 (G := G) (F := F) (M := M) (P := P))
    (semiFunctionField (F := F) (M := M) (P := P)) :=
  IntermediateField.adjoin _ (Set.range fun c : latticeFunctionField F M =>
    algebraMap (latticeFunctionField F M) (semiFunctionField (F := F) (M := M) (P := P)) c)

/-- **`Egen = Esm ⊔ SlI`**（`adjoin_union` 对齐）。 -/
theorem Egen_eq_sup :
    Egen (G := G) (F := F) (M := M) (P := P) B n y
      = Esm (G := G) (F := F) (M := M) (P := P) B n y
        ⊔ SlI (F := F) (M := M) (P := P) := by
  rw [Egen, Esm, SlI, IntermediateField.adjoin_union]

/-- **生成性（sup 形）**：`Esm ⊔ SlI = ⊤`。 -/
theorem sup_eq_top
    (hy_span : Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤) :
    Esm (G := G) (F := F) (M := M) (P := P) B n y
      ⊔ SlI (F := F) (M := M) (P := P) = ⊤ := by
  rw [← Egen_eq_sup (G := G) (F := F) (M := M) (P := P) (B := B) (n := n) (y := y)]
  exact generation_sup_eq_top (G := G) (F := F) (M := M) (P := P)
    (B := B) (n := n) (y := y) (hy_span := hy_span)

/-- **素元素**：`l = l^π⟮θ⟯`。 -/
theorem exists_primitive_spec :
    ∃ θ : latticeFunctionField F M,
      IntermediateField.adjoin ↥(FixedPoints.subfield G (latticeFunctionField F M)) {θ} = ⊤ :=
  Field.exists_primitive_element _ _

end Count

/-- **`SlI = ↥K₀⟮θ̃⟯`**（θ 为 l/l^G 的素元素；θ̃ := algebraMap θ）。
⊆ 经 l-侧的 `adjoin_induction` 逐案例映射；⊇ 由 θ̃ 是生成元。 -/
theorem SlI_eq_adjoin_primitive :
    ∃ θ : latticeFunctionField F M,
      IntermediateField.adjoin ↥(FixedPoints.subfield G (latticeFunctionField F M)) {θ} = ⊤
      ∧ SlI (G := G) (F := F) (M := M) (P := P)
        = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
            {algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)) θ} := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element
    (F := ↥(FixedPoints.subfield G (latticeFunctionField F M)))
    (E := latticeFunctionField F M)
  refine ⟨θ, hθ, ?_⟩
  refine le_antisymm ?_ ?_
  · rw [show SlI (G := G) (F := F) (M := M) (P := P)
        = IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
            (Set.range fun c : latticeFunctionField F M =>
              algebraMap (latticeFunctionField F M)
                (semiFunctionField (F := F) (M := M) (P := P)) c) from rfl]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro x hx
    obtain ⟨c₀, rfl⟩ := hx
    have hmem : ∀ c₀' : latticeFunctionField F M, c₀' ∈ IntermediateField.adjoin
        ↥(FixedPoints.subfield G (latticeFunctionField F M)) {θ} := by
      intro c₀'
      exact hθ ▸ Subfield.mem_top c₀'
    exact IntermediateField.adjoin_induction
      (F := ↥(FixedPoints.subfield G (latticeFunctionField F M)))
      (E := latticeFunctionField F M)
      (s := ({θ} : Set (latticeFunctionField F M)))
      (p := fun c _ => algebraMap (latticeFunctionField F M)
          (semiFunctionField (F := F) (M := M) (P := P)) c
        ∈ IntermediateField.adjoin ↥(K0 (G := G) (F := F) (M := M) (P := P))
            {algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P)) θ})
      (mem := fun x hx' => by
        rw [Set.mem_singleton_iff] at hx'
        subst hx'
        exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
      (algebraMap := fun r =>
        IntermediateField.algebraMap_mem _
          (show ↥(K0 (G := G) (F := F) (M := M) (P := P)) from
            ⟨algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P))
              (r : latticeFunctionField F M),
              Subfield.mem_map.mpr ⟨r, r.2, rfl⟩⟩))
      (add := fun x x' hx hx' ihx ihx' => by
        rw [map_add]
        exact add_mem ihx ihx')
      (inv := fun x hx ih => by
        rw [show algebraMap (latticeFunctionField F M)
            (semiFunctionField (F := F) (M := M) (P := P)) x⁻¹
            = (algebraMap (latticeFunctionField F M)
                (semiFunctionField (F := F) (M := M) (P := P)) x)⁻¹
            from map_inv₀ (algebraMap (latticeFunctionField F M)
              (semiFunctionField (F := F) (M := M) (P := P))) x]
        exact inv_mem ih)
      (mul := fun x x' hx hx' ihx ihx' => by
        rw [map_mul]
        exact mul_mem ihx ihx')
      (h := hmem c₀)
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact IntermediateField.subset_adjoin _ _ ⟨θ, rfl⟩



/-\! ## 6. 公理闸门 -/

#print axioms semiFunctionField_smul
#print axioms smul_algebraMap_semiAlg
#print axioms semiAlgEquiv_algebraMap_lattice
#print axioms faithfulSMul_semiFunctionField
#print axioms K0
#print axioms mem_fixed_iff
#print axioms K0_mem_fixed
#print axioms K0ToFixed
#print axioms instAlgebraFixedK0
#print axioms permMono_prod_expansion
#print axioms Yf
#print axioms Egen
#print axioms hmono
#print axioms hmono_permMono
#print axioms generation_sup_eq_top
#print axioms Esm
#print axioms Yf_mem_fixed
#print axioms Esm_le_fixed
#print axioms SlI
#print axioms Egen_eq_sup
#print axioms sup_eq_top
#print axioms exists_primitive_spec
#print axioms SlI_eq_adjoin_primitive

end EM
end ABGV52
