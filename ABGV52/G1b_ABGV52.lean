/-
  ABGV-5.2 —— **G 档 G1b：$S_{p^2}$-侧 Procesi 格 $M = \ker\varphi$**（参数化）

  闸门读数（2026-09-30，已过闸）：lean rc=0／error=0／无 sorry；
  八条 `#print axioms` 均为 `[propext, Classical.choice, Quot.sound]`。

  论文锚（`raw/ABGV-5.2-resolution.tex`）：
    `:563` \(\varphi(e_\alpha\otimes e_\beta) = e_\alpha - e_\beta\)（\(S_9\)-等变）；
    `:572`「The Procesi \(\mathbb Z[S_9]\)-lattice is \(M = \ker(\varphi)\)」；
    `:576` 短正合列 \(0 \to M \to U\otimes_{\mathbb Z} U \xrightarrow{\varphi} I[\Omega] \to 0\).

  本件（\(p\) 参数化，\(\Omega = \mathrm{Fin}\,(p\cdot p)\)，\(G = \mathrm{Equiv.Perm}\,\Omega\)）：
    ① 置换模 \(U = \mathbb Z[\Omega]\)（`Rep.ofMulAction`，载体 = `MonoidAlgebra ℤ Ω`）；
    ② 增广 \(\varepsilon\)（系数和）与增广理想 \(I[\Omega] = \ker\varepsilon\)；
    ③ \(\varphi\) 的**闭形式**：\(\varphi(f\otimes g) = \varepsilon(g)\cdot f - \varepsilon(f)\cdot g\)
       （在基向量上即 \(e_\alpha\otimes e_\beta\mapsto e_\alpha - e_\beta\)）；
    ④ \(G\)-等变性；\(\operatorname{range}\varphi = I[\Omega]\)；\(M := \ker\varphi\) 作为 `Rep ℤ G`.

  载体说明（2026-09-30 勘测）：本版 mathlib 的 `MonoidAlgebra R M` 是**单字段包装结构**
  （字段 `coeff : M →₀ R`），与 `M →₀ R` **不 defeq**；故一切运算都在 `MonoidAlgebra` 侧写，
  经 `MonoidAlgebra.coeffLinearEquiv` 与 `Finsupp` 侧互换。`Finsupp.total` 在本版已改名
  `Finsupp.linearCombination`。\(\varphi\) 的两个半映射不写成 `∘ₗ` 复合（该写法触发
  `Module ℤ (A ⊗ A)` 的实例菱形），改以显式 `toFun` 定义，线性性各自手证（两行）。
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

open scoped TensorProduct
open CategoryTheory

namespace ABGV52.G

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 置换集 \(\Omega\)、群 \(G = S_{p^2}\)、置换模 \(U\) -/

/-- 置换集 \(\Omega = \mathrm{Fin}\,(p^2)\)。 -/
abbrev OmegaP : Type := Fin (p * p)

/-- \(G = S_{p^2}\)（\(\Omega\) 的置换群）。 -/
abbrev Gp : Type := Equiv.Perm (OmegaP p)

/-- 群环 \(\mathbb Z[\Omega]\)（`U` 的载体，本件内简称 `ZOm`）。 -/
abbrev ZOm : Type := MonoidAlgebra ℤ (OmegaP p)

/-- 置换模 \(U = \mathbb Z[\Omega]\)。 -/
noncomputable abbrev U : Rep ℤ (Gp p) := Rep.ofMulAction ℤ (Gp p) (OmegaP p)

/-- 基点 \(\omega_0 = 0 \in \Omega\)（\(\Omega\) 非空：`p ≥ 2`）。 -/
def omega0 : OmegaP p :=
  ⟨0, Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos⟩

/-! ## 2. 增广 \(\varepsilon\) 与增广理想 \(I[\Omega]\) -/

/-- 增广 \(\varepsilon : \mathbb Z[\Omega] \to \mathbb Z\)（系数和）。
写成 `Finsupp.linearCombination` 与 `coeff` 的复合，**线性性免手证**。 -/
noncomputable def augF : ZOm p →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ (fun _ : OmegaP p => (1 : ℤ))).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

/-- 增广理想 \(I[\Omega] = \ker\varepsilon\)。 -/
noncomputable def IOmega : Submodule ℤ (ZOm p) := LinearMap.ker (augF p)

lemma augF_apply (f : ZOm p) :
    augF p f = ∑ a : OmegaP p, MonoidAlgebra.coeff f a := by
  change (Finsupp.linearCombination ℤ (fun _ : OmegaP p => (1 : ℤ)))
    (MonoidAlgebra.coeff f) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  have h : ∀ a : OmegaP p, MonoidAlgebra.coeff f a • (1 : ℤ) = MonoidAlgebra.coeff f a :=
    fun a => by simp
  simp only [h]
  exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx])

lemma augF_eq_sum_support (f : ZOm p) :
    augF p f = ∑ a ∈ (MonoidAlgebra.coeff f).support, MonoidAlgebra.coeff f a := by
  rw [augF_apply]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx])).symm

lemma augF_single (a : OmegaP p) (c : ℤ) : augF p (MonoidAlgebra.single a c) = c := by
  change (Finsupp.linearCombination ℤ (fun _ : OmegaP p => (1 : ℤ)))
    (MonoidAlgebra.coeff (MonoidAlgebra.single a c)) = c
  rw [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
  simp

/-- `coeffLinearEquiv` 与 `coeff` 在单点上的一致（包装结构侧的桥）。 -/
lemma symm_single (a : OmegaP p) (c : ℤ) :
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm (Finsupp.single a c) =
      MonoidAlgebra.single a c := by
  rw [LinearEquiv.symm_apply_eq, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single]

/-! ## 3. \(\varphi\) 的闭形式 -/

/-- \(\varphi(f \otimes g) = \varepsilon(g)\cdot f - \varepsilon(f)\cdot g\)，
由 `TensorProduct.map` 配 `rid`／`lid` 组装（**不手证双线性**）。 -/
noncomputable def phiFun : (ZOm p) ⊗[ℤ] (ZOm p) →ₗ[ℤ] (ZOm p) where
  toFun x :=
    (TensorProduct.rid ℤ (ZOm p))
        (TensorProduct.map (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) (augF p) x)
      - (TensorProduct.lid ℤ (ZOm p))
        (TensorProduct.map (augF p) (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) x)
  map_add' x y := by
    simp only [map_add]
    exact (sub_add_sub_comm _ _ _ _).symm
  map_smul' m x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    simp only [map_smul, smul_sub]

lemma phiFun_tmul (f g : ZOm p) :
    phiFun p (f ⊗ₜ[ℤ] g) = (augF p g) • f - (augF p f) • g := by
  show (TensorProduct.rid ℤ (ZOm p))
        (TensorProduct.map (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) (augF p) (f ⊗ₜ[ℤ] g))
      - (TensorProduct.lid ℤ (ZOm p))
        (TensorProduct.map (augF p) (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) (f ⊗ₜ[ℤ] g))
      = (augF p g) • f - (augF p f) • g
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.rid_tmul,
    TensorProduct.lid_tmul]
  simp

/-- 在基向量上即论文 `:563` 的 \(e_\alpha \otimes e_\beta \mapsto e_\alpha - e_\beta\)。 -/
lemma phiFun_single (a b : OmegaP p) :
    phiFun p ((MonoidAlgebra.single a (1 : ℤ)) ⊗ₜ[ℤ] (MonoidAlgebra.single b (1 : ℤ)))
      = MonoidAlgebra.single a (1 : ℤ) - MonoidAlgebra.single b (1 : ℤ) := by
  rw [phiFun_tmul, augF_single, augF_single, one_smul, one_smul]

/-! ## 4. 等变性 -/

/-- 增广是 \(G\)-不变的（置换只是重指标）。 -/
lemma augF_smul (g : Gp p) (f : ZOm p) : augF p ((U p).ρ g f) = augF p f := by
  rw [augF_apply, augF_apply]
  have h : ∀ a : OmegaP p, MonoidAlgebra.coeff ((U p).ρ g f) a
      = MonoidAlgebra.coeff f (g⁻¹ • a) :=
    fun a => Representation.coeff_ofMulAction g f a
  simp only [h]
  rw [← Equiv.sum_comp (g⁻¹ : Equiv.Perm (OmegaP p))
    (fun a : OmegaP p => MonoidAlgebra.coeff f a)]
  rfl

/-- \(\varphi\) 是 \(G\)-等变的（\(U \otimes U\) 取对角作用）。 -/
lemma phiFun_equivariant (g : Gp p) (x : (ZOm p) ⊗[ℤ] (ZOm p)) :
    phiFun p (TensorProduct.map ((U p).ρ g) ((U p).ρ g) x) = (U p).ρ g (phiFun p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f h =>
      rw [TensorProduct.map_tmul, phiFun_tmul, phiFun_tmul, augF_smul, augF_smul]
      conv_rhs => rw [map_sub, map_smul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ## 5. \(\operatorname{range}\varphi = I[\Omega]\) -/

lemma range_phiFun_le : LinearMap.range (phiFun p) ≤ IOmega p := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul f h =>
      rw [phiFun_tmul, IOmega, LinearMap.mem_ker, map_sub, map_smul, map_smul]
      have h1 : (augF p h) • (augF p f) = (augF p h) * (augF p f) := by simp
      have h2 : (augF p f) • (augF p h) = (augF p f) * (augF p h) := by simp
      rw [h1, h2, mul_comm (augF p f) (augF p h), sub_self]
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- 把 `f` 展成 `coeff` 的单点组合（`Finsupp.sum_single` 沿线性等价搬运）。 -/
lemma self_eq_sum_single (f : ZOm p) :
    f = ∑ a ∈ (MonoidAlgebra.coeff f).support,
      MonoidAlgebra.single a (MonoidAlgebra.coeff f a) := by
  have h1 : MonoidAlgebra.coeff f =
      ∑ a ∈ (MonoidAlgebra.coeff f).support,
        Finsupp.single a (MonoidAlgebra.coeff f a) := by
    conv_lhs => rw [← Finsupp.sum_single (MonoidAlgebra.coeff f)]
    rfl
  have key : (MonoidAlgebra.coeffLinearEquiv ℤ).symm (MonoidAlgebra.coeff f) =
      ∑ a ∈ (MonoidAlgebra.coeff f).support,
        MonoidAlgebra.single a (MonoidAlgebra.coeff f a) := by
    conv_lhs => rw [h1]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => symm_single p a _
  have hf : f = (MonoidAlgebra.coeffLinearEquiv ℤ).symm (MonoidAlgebra.coeff f) := by
    rw [← MonoidAlgebra.ofCoeff_coeff f]
    rfl
  conv_lhs => rw [hf, key]

lemma range_phiFun_ge : IOmega p ≤ LinearMap.range (phiFun p) := by
  intro f hf
  have hsum0 : (∑ a ∈ (MonoidAlgebra.coeff f).support, MonoidAlgebra.coeff f a) = 0 := by
    rw [← augF_eq_sum_support p f, LinearMap.mem_ker.mp hf]
  have hA : (∑ a ∈ (MonoidAlgebra.coeff f).support,
        MonoidAlgebra.coeff f a •
          (MonoidAlgebra.single a (1 : ℤ) - MonoidAlgebra.single (omega0 p) (1 : ℤ)))
      = ∑ a ∈ (MonoidAlgebra.coeff f).support,
          (MonoidAlgebra.single a (MonoidAlgebra.coeff f a)
            - MonoidAlgebra.coeff f a • MonoidAlgebra.single (omega0 p) (1 : ℤ)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_sub, MonoidAlgebra.smul_single]
    rw [show MonoidAlgebra.coeff f a • (1 : ℤ) = MonoidAlgebra.coeff f a from by simp]
  have hB : (∑ a ∈ (MonoidAlgebra.coeff f).support,
          (MonoidAlgebra.single a (MonoidAlgebra.coeff f a)
            - MonoidAlgebra.coeff f a • MonoidAlgebra.single (omega0 p) (1 : ℤ)))
      = (∑ a ∈ (MonoidAlgebra.coeff f).support,
            MonoidAlgebra.single a (MonoidAlgebra.coeff f a))
          - (∑ a ∈ (MonoidAlgebra.coeff f).support, MonoidAlgebra.coeff f a)
              • MonoidAlgebra.single (omega0 p) (1 : ℤ) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hkey : (∑ a ∈ (MonoidAlgebra.coeff f).support,
        MonoidAlgebra.coeff f a •
          (MonoidAlgebra.single a (1 : ℤ) - MonoidAlgebra.single (omega0 p) (1 : ℤ))) = f := by
    rw [hA, hB, hsum0, zero_smul, sub_zero]
    exact (self_eq_sum_single p f).symm
  rw [← hkey]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  rw [← phiFun_single p a (omega0 p)]
  exact LinearMap.mem_range_self _ _

/-- **论文 `:576` 的中间满射性**：\(\operatorname{range}\varphi = I[\Omega]\)。 -/
theorem range_phiFun_eq : LinearMap.range (phiFun p) = IOmega p :=
  le_antisymm (range_phiFun_le p) (range_phiFun_ge p)

/-! ## 6. \(M = \ker\varphi\) 作为 `Rep ℤ G` -/

lemma phiFun_ker_stable (g : Gp p) {x : (ZOm p) ⊗[ℤ] (ZOm p)}
    (hx : x ∈ LinearMap.ker (phiFun p)) :
    TensorProduct.map ((U p).ρ g) ((U p).ρ g) x ∈ LinearMap.ker (phiFun p) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [phiFun_equivariant p g x, hx, map_zero]

noncomputable def MKer_act (g : Gp p) (x : ↥(LinearMap.ker (phiFun p))) :
    ↥(LinearMap.ker (phiFun p)) :=
  ⟨TensorProduct.map ((U p).ρ g) ((U p).ρ g) x.1, phiFun_ker_stable p g x.2⟩

noncomputable instance : DistribMulAction (Gp p) ↥(LinearMap.ker (phiFun p)) where
  smul g x := MKer_act p g x
  one_smul x := by
    apply Subtype.ext
    show TensorProduct.map ((U p).ρ (1 : Gp p)) ((U p).ρ (1 : Gp p)) x.1 = x.1
    rw [map_one]
    change TensorProduct.map (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p)
      (LinearMap.id : ZOm p →ₗ[ℤ] ZOm p) x.1 = x.1
    simp only [TensorProduct.map_id, LinearMap.id_apply]
  mul_smul a b x := by
    apply Subtype.ext
    show TensorProduct.map ((U p).ρ (a * b)) ((U p).ρ (a * b)) x.1
        = TensorProduct.map ((U p).ρ a) ((U p).ρ a)
            (TensorProduct.map ((U p).ρ b) ((U p).ρ b) x.1)
    rw [Rep.ρ_mul, TensorProduct.map_comp]
    rfl
  smul_zero g := by
    apply Subtype.ext
    show TensorProduct.map ((U p).ρ g) ((U p).ρ g)
      (0 : (ZOm p) ⊗[ℤ] (ZOm p)) = 0
    simp
  smul_add g x y := by
    apply Subtype.ext
    show TensorProduct.map ((U p).ρ g) ((U p).ρ g) (x.1 + y.1)
        = TensorProduct.map ((U p).ρ g) ((U p).ρ g) x.1
          + TensorProduct.map ((U p).ρ g) ((U p).ρ g) y.1
    rw [map_add]

/-- **Procesi 格 \(M = \ker\varphi\) 作为 `Rep ℤ G`**（论文 `:572`）。 -/
noncomputable def MRep : Rep ℤ (Gp p) :=
  Rep.ofDistribMulAction ℤ (Gp p) ↥(LinearMap.ker (phiFun p))

/-! ## 7. 公理闸门 -/

#print axioms augF_apply
#print axioms augF_single
#print axioms phiFun_tmul
#print axioms phiFun_single
#print axioms augF_smul
#print axioms phiFun_equivariant
#print axioms range_phiFun_eq
#print axioms phiFun_ker_stable

end ABGV52.G
