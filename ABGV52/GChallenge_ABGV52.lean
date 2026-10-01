/-
  ABGV-5.2 —— **G 档 T2 独立重写**（几何等同归约层的公开陈述库）

  口径（kakeya／DeepMind 范式，与 B 档 `Challenge_ABGV52`、P 档 `PChallenge_ABGV52` 同款）：
    * 本件**零 import 主链**（不 import `G1b`／`G1c`／`G1d`／`G2p`／`GThm` 及 `P*`／`D*`），
      自足重建对象与陈述 ⟹ 任何「全文件一致的替换」（如把 `Fin (p*p)` 写成 `Fin p`、
      把搬运写成 `ω ↦ e (h⁻¹ * e.symm ω)`）在单文件内看不出来，只有第二份独立重写能抓。
    * **构造路线与主线不同**：主线以 `TensorProduct.map`＋`rid`/`lid` 定义 `φ`、以
      `Rep.ofMulAction` 的搬运实例定义限制；本件以 **`TensorProduct.lift`＋`LinearMap.mk₂`**
      定义 `φ`、以 **`Equiv` 置换＋`MonoidAlgebra.mapDomainLinearEquiv`** 定义限制。
    * 深内容（θ-无关性／正则限制／几何等同）本件**只登记陈述**（`sorry`）——「公开陈述库登记陈述，
      工作只供证明」；**平凡实例探针**独立证明（L1 非空洞性）。
    * 检查器 `abgv52-lean-crosscheck.py` 的 `[3c]` 逐条比对 `GThm` ↔ 本件 的**陈述类型**。
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Fixed
import Mathlib.Data.ZMod.Basic

open scoped TensorProduct
open CategoryTheory

namespace ABGV52.GT2

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 对象层 -/

/-- 基集 $\Omega$，$|\Omega| = p^2$。 -/
abbrev OmegaP : Type := Fin (p * p)

/-- $C_p$（乘法写法）。 -/
abbrev Cp : Type := Multiplicative (ZMod p)

/-- $H = C_p\times C_p$。 -/
abbrev Hp : Type := Cp p × Cp p

/-- $\mathbb Z[\Omega]$。 -/
abbrev ZH : Type := MonoidAlgebra ℤ (OmegaP p)

/-- $\mathbb Z[H]$。 -/
abbrev ZHH : Type := MonoidAlgebra ℤ (Hp p)

/-! ## 2. 增广与 $\varphi$（`lift` 路线） -/

/-- 增广 $\varepsilon$（系数和）。 -/
noncomputable def aug : ZH p →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ (fun _ : OmegaP p => (1 : ℤ))).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

lemma aug_apply (f : ZH p) : aug p f = ∑ a : OmegaP p, MonoidAlgebra.coeff f a := by
  change (Finsupp.linearCombination ℤ (fun _ : OmegaP p => (1 : ℤ)))
    (MonoidAlgebra.coeff f) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  have h : ∀ a : OmegaP p, MonoidAlgebra.coeff f a • (1 : ℤ) = MonoidAlgebra.coeff f a :=
    fun a => by simp
  simp only [h]
  exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx])

/-- **$\varphi(f\otimes g) = \varepsilon(g)f - \varepsilon(f)g$**。
工程注（实测）：`TensorProduct.lift`／`LinearMap.mk₂` 在 `ℤ` 上触发
`Int.instSemiring` vs `Int.instCommSemiring.toSemiring` **实例菱形**（`lift` 的产物与
`→ₗ[ℤ]` 声明不同型，`rw` 亦匹配不上）⟹ 与主线同走
**结构字面量 ＋ `TensorProduct.map`＋`rid`/`lid`** 的 mathlib 惯用形。
本件与主线的**独立性**落在限制侧（`Equiv` 置换 ＋ `mapDomainLinearEquiv`）。 -/
noncomputable def phiFun : ZH p ⊗[ℤ] ZH p →ₗ[ℤ] ZH p where
  toFun x :=
    (TensorProduct.rid ℤ (ZH p))
        (TensorProduct.map (LinearMap.id : ZH p →ₗ[ℤ] ZH p) (aug p) x)
      - (TensorProduct.lid ℤ (ZH p))
        (TensorProduct.map (aug p) (LinearMap.id : ZH p →ₗ[ℤ] ZH p) x)
  map_add' x y := by
    simp only [map_add]
    exact (sub_add_sub_comm _ _ _ _).symm
  map_smul' m x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    simp only [map_smul, smul_sub]

lemma phiFun_tmul (f g : ZH p) :
    phiFun p (f ⊗ₜ[ℤ] g) = aug p g • f - aug p f • g := by
  show (TensorProduct.rid ℤ (ZH p))
        (TensorProduct.map (LinearMap.id : ZH p →ₗ[ℤ] ZH p) (aug p) (f ⊗ₜ[ℤ] g))
      - (TensorProduct.lid ℤ (ZH p))
        (TensorProduct.map (aug p) (LinearMap.id : ZH p →ₗ[ℤ] ZH p) (f ⊗ₜ[ℤ] g))
    = aug p g • f - aug p f • g
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.rid_tmul,
    TensorProduct.lid_tmul, LinearMap.id_apply, LinearMap.id_apply]

/-! ## 3. 搬运作用与限制 $M|_\theta$ -/

/-- 由双射 `e : H ≃ Ω` 搬运的正则置换：$\omega \mapsto e\,(h\cdot e^{-1}\omega)$。 -/
def actPerm (e : Hp p ≃ OmegaP p) (h : Hp p) : Equiv.Perm (OmegaP p) where
  toFun ω := e (h * e.symm ω)
  invFun ω := e (h⁻¹ * e.symm ω)
  left_inv ω := by
    simp only [Equiv.symm_apply_apply, inv_mul_cancel_left, Equiv.apply_symm_apply]
  right_inv ω := by
    simp only [Equiv.symm_apply_apply, mul_inv_cancel_left, Equiv.apply_symm_apply]

lemma actPerm_one (e : Hp p ≃ OmegaP p) : actPerm p e (1 : Hp p) = Equiv.refl (OmegaP p) := by
  ext ω
  simp only [actPerm, Equiv.coe_fn_mk, Equiv.refl_apply, one_mul, Equiv.apply_symm_apply]

lemma actPerm_mul (e : Hp p ≃ OmegaP p) (a b : Hp p) :
    actPerm p e (a * b) = (actPerm p e b).trans (actPerm p e a) := by
  ext ω
  simp only [actPerm, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.symm_apply_apply, mul_assoc]

/-- `ℤ[Ω]` 上由置换诱导的线性等价。 -/
noncomputable def actLin (e : Hp p ≃ OmegaP p) (h : Hp p) : ZH p ≃ₗ[ℤ] ZH p :=
  MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ (actPerm p e h)

lemma actLin_coeff (e : Hp p ≃ OmegaP p) (h : Hp p) (f : ZH p) (ω : OmegaP p) :
    MonoidAlgebra.coeff (actLin p e h f) ω
      = MonoidAlgebra.coeff f ((actPerm p e h).symm ω) := by
  rw [actLin, MonoidAlgebra.coeff_mapDomainLinearEquiv]
  exact Finsupp.equivMapDomain_apply (actPerm p e h) (MonoidAlgebra.coeff f) ω

lemma actLin_one (e : Hp p ≃ OmegaP p) :
    actLin p e (1 : Hp p) = LinearEquiv.refl ℤ (ZH p) := by
  refine LinearEquiv.ext fun f => ?_
  refine MonoidAlgebra.coeff_injective ?_
  ext ω
  rw [actLin_coeff, actPerm_one]
  rfl

lemma actLin_mul (e : Hp p ≃ OmegaP p) (a b : Hp p) :
    actLin p e (a * b) = (actLin p e b).trans (actLin p e a) := by
  rw [actLin, actLin, actLin, actPerm_mul, MonoidAlgebra.mapDomainLinearEquiv_trans]

/-- 逐元素形式的合成律（`toLinearMap` 形，供张量项 `simp` 匹配）。 -/
lemma actLin_mul_apply (e : Hp p ≃ OmegaP p) (a b : Hp p) (f : ZH p) :
    (actLin p e (a * b)).toLinearMap f
      = (actLin p e a).toLinearMap ((actLin p e b).toLinearMap f) := by
  rw [actLin_mul]
  rfl

lemma aug_actLin (e : Hp p ≃ OmegaP p) (h : Hp p) (f : ZH p) :
    aug p (actLin p e h f) = aug p f := by
  rw [aug_apply, aug_apply]
  simp only [actLin_coeff]
  exact Equiv.sum_comp (actPerm p e h).symm
    (fun a : OmegaP p => MonoidAlgebra.coeff f a)

/-- `toLinearMap` 形的同一引理（供张量项 `simp` 匹配）。 -/
lemma aug_actLin' (e : Hp p ≃ OmegaP p) (h : Hp p) (f : ZH p) :
    aug p ((actLin p e h).toLinearMap f) = aug p f :=
  aug_actLin p e h f

/-- $\varphi$ 在搬运下等变。 -/
lemma phi_equivariant (e : Hp p ≃ OmegaP p) (h : Hp p)
    (x : ZH p ⊗[ℤ] ZH p) :
    phiFun p (TensorProduct.map (actLin p e h).toLinearMap (actLin p e h).toLinearMap x)
      = actLin p e h (phiFun p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [TensorProduct.map_tmul, phiFun_tmul, phiFun_tmul]
      simp only [aug_actLin']
      conv_rhs => rw [map_sub, map_smul, map_smul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

lemma ker_stable (e : Hp p ≃ OmegaP p) (h : Hp p) {x : ZH p ⊗[ℤ] ZH p}
    (hx : x ∈ LinearMap.ker (phiFun p)) :
    TensorProduct.map (actLin p e h).toLinearMap (actLin p e h).toLinearMap x ∈ LinearMap.ker (phiFun p) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [phi_equivariant, hx, map_zero]

/-- `U` 上的 $H$-作用（`e` 搬运的正则作用）。 -/
noncomputable def UOfRep (e : Hp p ≃ OmegaP p) :
    Representation ℤ (Hp p) (ZH p) where
  toFun h := (actLin p e h).toLinearMap
  map_one' := by
    refine LinearMap.ext fun f => ?_
    show actLin p e (1 : Hp p) f = f
    rw [actLin_one]
    rfl
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_
    show (actLin p e (a * b)).toLinearMap f
      = (actLin p e a).toLinearMap ((actLin p e b).toLinearMap f)
    exact actLin_mul_apply p e a b f

lemma tensor_actLin_mul (e : Hp p ≃ OmegaP p) (a b : Hp p)
    (x : ZH p ⊗[ℤ] ZH p) :
    TensorProduct.map (actLin p e (a * b)).toLinearMap (actLin p e (a * b)).toLinearMap x
      = TensorProduct.map (actLin p e a).toLinearMap (actLin p e a).toLinearMap
          (TensorProduct.map (actLin p e b).toLinearMap (actLin p e b).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
      simp only [actLin_mul_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- $M|_\theta = \ker\varphi$ 承对角作用。 -/
noncomputable def MresRep (e : Hp p ≃ OmegaP p) :
    Representation ℤ (Hp p) ↥(LinearMap.ker (phiFun p)) where
  toFun h :=
    { toFun := fun x => ⟨TensorProduct.map (actLin p e h).toLinearMap (actLin p e h).toLinearMap x.1,
        ker_stable p e h x.2⟩
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
      map_smul' := fun m x => Subtype.ext (map_smul _ m x.1) }
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show TensorProduct.map (actLin p e 1).toLinearMap (actLin p e 1).toLinearMap x.1 = x.1
    rw [actLin_one]
    change TensorProduct.map (LinearMap.id : ZH p →ₗ[ℤ] ZH p)
      (LinearMap.id : ZH p →ₗ[ℤ] ZH p) x.1 = x.1
    simp only [TensorProduct.map_id, LinearMap.id_apply]
  map_mul' a b := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show TensorProduct.map (actLin p e (a * b)).toLinearMap (actLin p e (a * b)).toLinearMap x.1
        = TensorProduct.map (actLin p e a).toLinearMap (actLin p e a).toLinearMap
            (TensorProduct.map (actLin p e b).toLinearMap (actLin p e b).toLinearMap x.1)
    exact tensor_actLin_mul p e a b x.1

/-- **限制 $M|_\theta$**（基点 `e`）。 -/
noncomputable abbrev MresOf (e : Hp p ≃ OmegaP p) : Rep ℤ (Hp p) :=
  Rep.of (MresRep p e)

/-! ## 4. Procesi 侧：$V = \mathbb Z[H]^{\oplus p^2}$、$\pi$、$M_{\mathrm{rep}}$ -/

/-- $V = \mathbb Z[H]^{\oplus p^2}$。 -/
abbrev Vp : Type := Hp p → ZHH p

/-- 左乘 $h$。 -/
noncomputable def lmul (h : Hp p) (z : ZHH p) : ZHH p := MonoidAlgebra.single h 1 * z

lemma lmul_mul (a b : Hp p) (w : ZHH p) : lmul p (a * b) w = lmul p a (lmul p b w) := by
  rw [lmul, lmul, lmul, ← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

lemma lmul_zero (h : Hp p) : lmul p h (0 : ZHH p) = 0 := mul_zero _

lemma lmul_sub (h : Hp p) (x y : ZHH p) : lmul p h (x - y) = lmul p h x - lmul p h y :=
  mul_sub _ _ _

/-- 坐标作用 $z \mapsto (i \mapsto h\cdot z(h^{-1}i))$。 -/
noncomputable def actV (h : Hp p) (z : Vp p) : Vp p := fun i => lmul p h (z (h⁻¹ * i))

lemma actV_one (z : Vp p) : actV p 1 z = z := by
  funext i
  show lmul p 1 (z (1⁻¹ * i)) = z i
  rw [inv_one, one_mul, lmul, ← MonoidAlgebra.one_def, one_mul]

lemma actV_mul (a b : Hp p) (z : Vp p) : actV p (a * b) z = actV p a (actV p b z) := by
  funext i
  simp only [actV, mul_inv_rev, mul_assoc, lmul_mul]

lemma actV_zero (h : Hp p) : actV p h (0 : Vp p) = 0 := by
  funext i
  exact lmul_zero p h

lemma actV_add (h : Hp p) (x y : Vp p) : actV p h (x + y) = actV p h x + actV p h y := by
  funext i
  exact mul_add _ _ _

lemma actV_smul (h : Hp p) (m : ℤ) (z : Vp p) : actV p h (m • z) = m • actV p h z := by
  funext i
  simp only [actV, Pi.smul_apply, lmul, mul_smul_comm]

/-- 增广（$\mathbb Z[H]$ 上）。 -/
noncomputable def augH : ZHH p →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ (fun _ : Hp p => (1 : ℤ))).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

lemma augH_apply (w : ZHH p) : augH p w = ∑ a : Hp p, MonoidAlgebra.coeff w a := by
  change (Finsupp.linearCombination ℤ (fun _ : Hp p => (1 : ℤ)))
    (MonoidAlgebra.coeff w) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  have h : ∀ a : Hp p, MonoidAlgebra.coeff w a • (1 : ℤ) = MonoidAlgebra.coeff w a :=
    fun a => by simp
  simp only [h]
  exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx])

lemma augH_lmul (h : Hp p) (w : ZHH p) : augH p (lmul p h w) = augH p w := by
  rw [augH_apply, augH_apply]
  simp only [lmul, MonoidAlgebra.coeff_single_mul_apply, one_mul]
  exact Equiv.sum_comp (Equiv.mulLeft h⁻¹)
    (fun a : Hp p => MonoidAlgebra.coeff w a)

lemma lmul_single (h c : Hp p) :
    lmul p h (MonoidAlgebra.single c (1 : ℤ)) = MonoidAlgebra.single (h * c) (1 : ℤ) := by
  simp only [lmul, MonoidAlgebra.single_mul_single, mul_one]

lemma lmul_smul (h : Hp p) (m : ℤ) (w : ZHH p) : lmul p h (m • w) = m • lmul p h w := by
  rw [lmul, lmul, mul_smul_comm]

/-- **Procesi 映射** $\pi(z) = \sum_b \big(z_b - \varepsilon(z_b)\,e_b\big)$。 -/
noncomputable def pi : Vp p →ₗ[ℤ] ZHH p where
  toFun z := ∑ b : Hp p, (z b - augH p (z b) • MonoidAlgebra.single b (1 : ℤ))
  map_add' z w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.add_apply, map_add, add_smul]
    abel
  map_smul' m z := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]
    rw [show (m • augH p (z b)) • MonoidAlgebra.single b (1 : ℤ)
          = m • (augH p (z b) • MonoidAlgebra.single b (1 : ℤ))
        from smul_assoc m (augH p (z b)) (MonoidAlgebra.single b (1 : ℤ))]

lemma actV_apply_mul (h c : Hp p) (z : Vp p) : actV p h z (h * c) = lmul p h (z c) := by
  rw [actV, inv_mul_cancel_left]

lemma pi_apply (z : Vp p) :
    pi p z = ∑ b : Hp p, (z b - augH p (z b) • MonoidAlgebra.single b (1 : ℤ)) := rfl

lemma pi_term_eq (h c : Hp p) (z : Vp p) :
    actV p h z (h * c) - augH p (actV p h z (h * c)) • MonoidAlgebra.single (h * c) (1 : ℤ)
      = lmul p h (z c - augH p (z c) • MonoidAlgebra.single c (1 : ℤ)) := by
  rw [actV_apply_mul, augH_lmul, ← lmul_single, ← lmul_smul, ← lmul_sub]

/-- **`pi` 是 `H`-等变的**（重指标 `Equiv.mulLeft`）。 -/
lemma pi_equivariant (h : Hp p) (z : Vp p) : pi p (actV p h z) = lmul p h (pi p z) := by
  have hF : ∀ w : Vp p, pi p w
      = ∑ b : Hp p, (w b - augH p (w b) • MonoidAlgebra.single b (1 : ℤ)) := fun w => pi_apply p w
  rw [hF (actV p h z), hF z]
  simp only [lmul, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun b : Hp p =>
    (actV p h z b - augH p (actV p h z b) • MonoidAlgebra.single b (1 : ℤ)))]
  exact Finset.sum_congr rfl (fun c _ => pi_term_eq p h c z)

lemma ker_pi_stable (h : Hp p) {z : Vp p} (hz : z ∈ LinearMap.ker (pi p)) :
    actV p h z ∈ LinearMap.ker (pi p) := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [pi_equivariant, hz, lmul_zero]

/-- `M_rep = ker pi` 承 `H`-作用。 -/
noncomputable def MrepRep : Representation ℤ (Hp p) ↥(LinearMap.ker (pi p)) where
  toFun h :=
    { toFun := fun z => ⟨actV p h z.1, ker_pi_stable p h z.2⟩
      map_add' := fun x y => Subtype.ext (actV_add p h x.1 y.1)
      map_smul' := fun m x => Subtype.ext (actV_smul p h m x.1) }
  map_one' := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    exact actV_one p z.1
  map_mul' a b := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    exact actV_mul p a b z.1

/-- **`M_rep`**（论文的 `M|_H` 抽象形）。 -/
noncomputable abbrev M_rep : Rep ℤ (Hp p) := Rep.of (MrepRep p)

/-- `ker pi` 承 `H`-作用（由 `MrepRep` 读出；供不变量域 `F(M_rep)^H`）。 -/
noncomputable instance distribMulAction_kerPi :
    DistribMulAction (Hp p) ↥(LinearMap.ker (pi p)) where
  smul h z := (MrepRep p h) z
  one_smul z := by
    show (MrepRep p 1) z = z
    rw [map_one]
    rfl
  mul_smul a b z := by
    show (MrepRep p (a * b)) z = (MrepRep p a) ((MrepRep p b) z)
    rw [map_mul]
    rfl
  smul_zero h := by
    show (MrepRep p h) 0 = 0
    exact map_zero _
  smul_add h z w := by
    show (MrepRep p h) (z + w) = (MrepRep p h) z + (MrepRep p h) w
    exact map_add _ _ _

/-\! ## 5. 公开陈述登记 -/

/-- **theta-无关性（论文 `:644`）**：任意两基点给出的限制同构。 -/
theorem gThm_embedding_independence (e₁ e₂ : Hp p ≃ OmegaP p) :
    Nonempty (MresOf p e₁ ≅ MresOf p e₂) := by
  sorry

/-- **正则限制（论文 `:624`）**：**任意**基点给出的限制都与 `M_rep` 同构。 -/
theorem gThm_restrict_canonical (e : Hp p ≃ OmegaP p) :
    Nonempty (MresOf p e ≅ M_rep p) := by
  sorry

/-- **平凡实例探针**（L1 非空洞性）：同一基点时为恒等同构，陈述不空洞。 -/
theorem gThm_embedding_independence_refl (e : Hp p ≃ OmegaP p) :
    Nonempty (MresOf p e ≅ MresOf p e) :=
  ⟨Iso.refl _⟩

/-\! ## 6. 不变量域（D 档对象层的独立重写；G-3 陈述所需） -/

section Invariants

/-- `ι →₀ ℤ` 的唯一和（`Finsupp ≃ (ι → ℤ)`）。 -/
instance uniqueSums_finsupp {ι : Type*} [Fintype ι] : UniqueSums (ι →₀ ℤ) :=
  (AddEquiv.uniqueSums_iff (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).toAddEquiv).mpr inferInstance

/-- `ℤ[Ω] ⊗ ℤ[Ω] ≅ (Ω × Ω →₀ ℤ)`（包装 → Finsupp → 张积-函数 → 消 `ℤ ⊗ ℤ`）。 -/
noncomputable def zomTensorEquiv :
    (ZH p) ⊗[ℤ] (ZH p) ≃ₗ[ℤ] ((OmegaP p × OmegaP p) →₀ ℤ) :=
  (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv ℤ)
      (MonoidAlgebra.coeffLinearEquiv ℤ)).trans
    (finsuppTensorFinsupp' ℤ (OmegaP p) (OmegaP p))

instance uniqueSums_zomTensor : UniqueSums ((ZH p) ⊗[ℤ] (ZH p)) :=
  (AddEquiv.uniqueSums_iff (zomTensorEquiv p).toAddEquiv).mpr inferInstance

/-- 群环（包装结构 `MonoidAlgebra`）的唯一和（经 `coeffLinearEquiv` 搬到 `Finsupp`）。 -/
instance uniqueSums_monoidAlgebra {M : Type*} [Fintype M] :
    UniqueSums (MonoidAlgebra ℤ M) :=
  (AddEquiv.uniqueSums_iff (MonoidAlgebra.coeffLinearEquiv ℤ).toAddEquiv).mpr inferInstance

/-- `ker pi` 上的唯一和（沿子模包含拉回 `Vp`）。 -/
instance uniqueSums_kerPi : UniqueSums ↥(LinearMap.ker (pi p)) :=
  UniqueSums.of_injective_addHom
    { toFun := fun z => (z.1 : Vp p), map_add' := fun _ _ => rfl }
    Subtype.val_injective inferInstance

/-- `ker φ` 上的唯一和（沿子模包含拉回）。 -/
instance uniqueSums_kerPhi : UniqueSums ↥(LinearMap.ker (phiFun p)) :=
  UniqueSums.of_injective_addHom
    { toFun := fun x => (x.1 : (ZH p) ⊗[ℤ] (ZH p)), map_add' := fun _ _ => rfl }
    Subtype.val_injective inferInstance

/-- `|H| = p * p`（基点存在的算术）。 -/
lemma card_Hp : Fintype.card (Hp p) = p * p := by
  simp [Hp, Cp, Fintype.card_prod, ZMod.card]

/-- 基点 `H ≃ Ω`（`Classical.choice`）。
注：不变量域的作用需要一个基点；按 **G-1（θ-无关性）** 不同基点给出同构的结果，
故本件的选择不影响陈述的数学内容（主线取 G1c 的 `eHO`）。 -/
noncomputable def eHO : Hp p ≃ OmegaP p := Fintype.equivFinOfCardEq (card_Hp p)

/-- `ker φ` 承 `H`-作用（由 `MresRep` 在基点 `eHO` 上读出）。 -/
noncomputable instance distribMulAction_kerPhi :
    DistribMulAction (Hp p) ↥(LinearMap.ker (phiFun p)) where
  smul h x := (MresRep p (eHO p) h) x
  one_smul x := by
    show (MresRep p (eHO p) 1) x = x
    rw [map_one]
    rfl
  mul_smul a b x := by
    show (MresRep p (eHO p) (a * b)) x = (MresRep p (eHO p) a) ((MresRep p (eHO p) b) x)
    rw [map_mul]
    rfl
  smul_zero h := by
    show (MresRep p (eHO p) h) 0 = 0
    exact map_zero _
  smul_add h x y := by
    show (MresRep p (eHO p) h) (x + y) = (MresRep p (eHO p) h) x + (MresRep p (eHO p) h) y
    exact map_add _ _ _

/-- `g` 在 `Multiplicative L` 上诱导的乘法自同构。 -/
noncomputable def mulEquivOfSMul (G : Type*) [Group G] (L : Type*) [AddCommMonoid L]
    [DistribMulAction G L] (g : G) : Multiplicative L ≃* Multiplicative L where
  toFun x := Multiplicative.ofAdd (g • x.toAdd)
  invFun x := Multiplicative.ofAdd (g⁻¹ • x.toAdd)
  left_inv x := by
    show Multiplicative.ofAdd (g⁻¹ • (g • x.toAdd)) = x
    rw [smul_smul, inv_mul_cancel, one_smul]
    rfl
  right_inv x := by
    show Multiplicative.ofAdd (g • (g⁻¹ • x.toAdd)) = x
    rw [smul_smul, mul_inv_cancel, one_smul]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (g • (x * y).toAdd)
      = Multiplicative.ofAdd (g • x.toAdd) * Multiplicative.ofAdd (g • y.toAdd)
    rw [show (x * y).toAdd = x.toAdd + y.toAdd from rfl, smul_add]
    rfl

/-- **`F[L]`**：格的群代数（单项式环）。 -/
abbrev latticeAlgebra (F : Type*) [Semiring F] (L : Type*) [AddCommMonoid L] : Type _ :=
  MonoidAlgebra F (Multiplicative L)

noncomputable def latticeAlgebraEquiv (F : Type*) [Field F] (G : Type*) [Group G] (L : Type*)
    [AddCommMonoid L] [DistribMulAction G L] (g : G) :
    latticeAlgebra F L ≃+* latticeAlgebra F L :=
  MonoidAlgebra.mapDomainRingEquiv F (mulEquivOfSMul G L g)

noncomputable def latticeAlgebraActionHom (F : Type*) [Field F] (G : Type*) [Group G]
    (L : Type*) [AddCommMonoid L] [DistribMulAction G L] :
    G →* (latticeAlgebra F L ≃+* latticeAlgebra F L) where
  toFun g := latticeAlgebraEquiv F G L g
  map_one' := by
    have h1 : mulEquivOfSMul G L (1 : G) = MulEquiv.refl (Multiplicative L) := by
      ext x
      simp [mulEquivOfSMul]
    rw [latticeAlgebraEquiv, h1]
    refine RingEquiv.ext fun x => MonoidAlgebra.ext ?_
    simp [MonoidAlgebra.mapDomainRingEquiv]
  map_mul' g h := by
    have hcomp : mulEquivOfSMul G L (g * h)
        = (mulEquivOfSMul G L h).trans (mulEquivOfSMul G L g) := by
      ext x
      show (g * h) • x.toAdd = g • (h • x.toAdd)
      rw [mul_smul]
    simp only [latticeAlgebraEquiv, hcomp, MonoidAlgebra.mapDomainRingEquiv_trans]
    refine RingEquiv.ext fun x => MonoidAlgebra.ext ?_
    simp [MonoidAlgebra.mapDomainRingEquiv]

/-- **`F[L]` 上的 `G`-作用**（`g · x^m = x^{g·m}`，系数不动）。 -/
noncomputable instance mulSemiringAction_latticeAlgebra (F : Type*) [Field F] (G : Type*)
    [Group G] (L : Type*) [AddCommMonoid L] [DistribMulAction G L] :
    MulSemiringAction G (latticeAlgebra F L) :=
  MulSemiringAction.compHom (latticeAlgebra F L) (latticeAlgebraActionHom F G L)

/-- **`F(L)`**：格的函数域 `Frac F[L]`。 -/
abbrev latticeFunctionField (F : Type*) [Field F] (L : Type*) [AddCommMonoid L] : Type _ :=
  FractionRing (MonoidAlgebra F (Multiplicative L))

/-- **`F(L)` 上的 `G`-作用**（由 `F[L]` 上的作用经分式域延拓）。 -/
noncomputable instance mulSemiringAction_latticeFunctionField (F : Type*) [Field F] (G : Type*)
    [Group G] (L : Type*) [AddCommMonoid L] [DistribMulAction G L] :
    MulSemiringAction G (latticeFunctionField F L) :=
  MulSemiringAction.compHom (latticeFunctionField F L)
    ((IsFractionRing.ringEquivOfRingEquivHom (latticeAlgebra F L)
      (latticeFunctionField F L)).comp (latticeAlgebraActionHom F G L))

/-- **不变量域 `F(L)^G`**。 -/
noncomputable def latticeInvariants (F : Type*) [Field F] (G : Type*) [Group G] (L : Type*)
    [AddCommGroup L] [Module ℤ L] [DistribMulAction G L] [SMulCommClass G ℤ L]
    [UniqueProds (Multiplicative L)] : Subfield (latticeFunctionField F L) :=
  FixedPoints.subfield G (latticeFunctionField F L)

end Invariants

/-\! ## 7. G-3 陈述（几何等同；以 Procesi 1967 为带名假设） -/

/-- **几何等同（论文 `rem:procesi-geometric`）**：设 `Z ≅ F(M|_theta)^H`（Procesi 1967，
**带名假设**），则 `Z ≅ F(M_rep)^H`。 -/
theorem gThm_geometric_identification (F : Type*) [Field F] (Z : Type*) [Field Z]
    (hProcesi : Nonempty (Z ≃+* ↥(latticeInvariants F (Hp p)
      ↥(LinearMap.ker (phiFun p))))) :
    Nonempty (Z ≃+* ↥(latticeInvariants F (Hp p)
      ↥(LinearMap.ker (pi p)))) := by
  sorry

/-\! ## 8. 公理闸门 -/

#print axioms pi_equivariant
#print axioms ker_pi_stable
#print axioms M_rep
#print axioms gThm_embedding_independence_refl


end ABGV52.GT2
