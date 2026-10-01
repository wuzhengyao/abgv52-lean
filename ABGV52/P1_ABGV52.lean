/-
  ABGV-5.2 —— **P 档（一般奇素数 p）：`thm:Cp-general` 的形式化**
  P1：参数化骨架 —— 对象、坐标作用、增广理想、Procesi 映射 π 与短正合列

  与 C 档（p = 3）的关系
  ====================
  本档是 C 档（`G2`／`G2b`／`G4`／`C1`／`C2`／`C8` 的定义层）的**参数化孪生**：
  同样的坐标模型 `Vp = Z[Hp p]^{⊕p²}`（坐标 = `Hp p` 的元素，共 p² 个）、
  同样的 `π z = Σ_b (z b − ε(z b)·b)`、同样的 Procesi 序列
  `0 → Mp → Vp → I[Hp p] → 0`（论文 `thm:Cp-general` 的
  `0 → M|_H → Z[H]^{⊕p²} → I[H] → 0`）。

  设计（2026-09-30 用户裁定）：**平行参数化开发** —— C 档（p=3）件一字不动，
  本档独立成链；故**只 import mathlib**，不与 C 档共享实例（避免 p ↦ 3 时的实例撞车）。
  论文第 (4) 条（retract rational）按用户裁定**作显式假设**（Saltman 1984 Cor 3.13），日后接线。

  p 的范围：`[Fact p.Prime]`（`ZMod p` 成域的充要条件）；「奇」用于后续指数论证。
-/
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic

open CategoryTheory

namespace ABGV52.P

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. 群 `Hp p = C_p × C_p` -/

/-- `C_p`（乘法写法）。 -/
abbrev Cp : Type := Multiplicative (ZMod p)

/-- 论文 `thm:Cp-general` 的群 `H = C_p × C_p`。 -/
abbrev Hp : Type := Cp p × Cp p

/-- `|H| = p²`（后续 `aug(normEl) = p²`、指数论证用）。 -/
lemma card_Hp : Fintype.card (Hp p) = p * p := by
  simp [Hp, Cp, Fintype.card_prod, ZMod.card]

/-! ## 2. `Hp p` 在 `Z[Hp p]` 上的左乘 -/

/-- 左乘辅助定义（与 C 档 `lmul` 同式）。 -/
noncomputable def lmul (h : Hp p) (z : MonoidAlgebra ℤ (Hp p)) : MonoidAlgebra ℤ (Hp p) :=
  MonoidAlgebra.single h 1 * z

lemma lmul_mul (a b : Hp p) (w : MonoidAlgebra ℤ (Hp p)) :
    lmul p a (lmul p b w) = lmul p (a * b) w := by
  show MonoidAlgebra.single a 1 * (MonoidAlgebra.single b 1 * w)
      = MonoidAlgebra.single (a * b) 1 * w
  rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

noncomputable instance : DistribMulAction (Hp p) (MonoidAlgebra ℤ (Hp p)) where
  smul := lmul p
  one_smul z := one_mul z
  mul_smul a b z := (lmul_mul p a b z).symm
  smul_zero h := mul_zero _
  smul_add h z w := mul_add _ _ _

/-! ## 3. 环绕模 `Vp p = Z[Hp p]^{⊕p²}`（坐标模型：`Hp p → Z[Hp p]`） -/

/-- 环绕模（论文 `thm:Cp-general` 的 `Z[H]^{⊕p²}`）。 -/
abbrev Vp : Type := Hp p → MonoidAlgebra ℤ (Hp p)

/-- **坐标作用**：`(act h z) i = h · z (h⁻¹ * i)`（与 C 档同式）。
不声明为实例（与 Pi 逐点作用争用 `•`）。 -/
noncomputable def act (h : Hp p) (z : Vp p) : Vp p := fun i => lmul p h (z (h⁻¹ * i))

@[simp] lemma act_apply (h : Hp p) (z : Vp p) (i : Hp p) :
    act p h z i = lmul p h (z (h⁻¹ * i)) := rfl

lemma act_one (z : Vp p) : act p 1 z = z := by
  funext i; rw [act_apply, inv_one, one_mul]; exact one_mul (z i)

lemma act_mul (a b : Hp p) (z : Vp p) : act p (a * b) z = act p a (act p b z) := by
  funext i
  rw [act_apply, act_apply, act_apply, lmul_mul, mul_inv_rev, mul_assoc]

lemma act_add (h : Hp p) (z w : Vp p) : act p h (z + w) = act p h z + act p h w := by
  funext i; simp only [act_apply, Pi.add_apply, lmul, mul_add]

lemma act_zero (h : Hp p) : act p h (0 : Vp p) = 0 := by
  funext i; rw [act_apply, Pi.zero_apply, Pi.zero_apply, lmul, mul_zero]

/-! ## 4. 增广 `ε` 与增广理想 `I[Hp p]` -/

/-- 增广映射 `ε : Z[Hp p] → ℤ`（系数和）。 -/
noncomputable def aug : MonoidAlgebra ℤ (Hp p) →ₗ[ℤ] ℤ :=
  (MonoidAlgebra.liftNC (AddMonoidHom.id ℤ) ((1 : Hp p →* ℤ) : Hp p → ℤ)).toIntLinearMap

/-- 增广理想 `I[H] = ker ε`。 -/
noncomputable def I_H : Submodule ℤ (MonoidAlgebra ℤ (Hp p)) := LinearMap.ker (aug p)

lemma aug_single (h : Hp p) : aug p (MonoidAlgebra.single h (1 : ℤ)) = 1 := by
  simp [aug]

lemma aug_mul (x y : MonoidAlgebra ℤ (Hp p)) : aug p (x * y) = aug p x * aug p y := by
  have h := MonoidAlgebra.liftNC_mul (k := ℤ) (G := Hp p) (R := ℤ)
    (f := RingHom.id ℤ) (g := (1 : Hp p →* ℤ)) x y
    (by intro a b _; exact Commute.all _ _)
  simpa [aug] using h

lemma aug_one : aug p (1 : MonoidAlgebra ℤ (Hp p)) = 1 := by
  have h := MonoidAlgebra.liftNC_one (k := ℤ) (G := Hp p) (R := ℤ)
    (f := RingHom.id ℤ) (g := (1 : Hp p →* ℤ))
  simpa [aug] using h

lemma aug_lmul (h : Hp p) (w : MonoidAlgebra ℤ (Hp p)) : aug p (lmul p h w) = aug p w := by
  rw [lmul, aug_mul, aug_single, one_mul]

lemma lmul_single (h c : Hp p) :
    lmul p h (MonoidAlgebra.single c (1 : ℤ)) = MonoidAlgebra.single (h * c) (1 : ℤ) := by
  rw [lmul, MonoidAlgebra.single_mul_single, one_mul]

lemma lmul_smul (h : Hp p) (m : ℤ) (w : MonoidAlgebra ℤ (Hp p)) :
    lmul p h (m • w) = m • lmul p h w := by
  rw [lmul, lmul, mul_smul_comm]

lemma lmul_sub (h : Hp p) (x y : MonoidAlgebra ℤ (Hp p)) :
    lmul p h (x - y) = lmul p h x - lmul p h y := by
  rw [lmul, lmul, lmul, mul_sub]

lemma lmul_sum (h : Hp p) (s : Finset (Hp p)) (f : Hp p → MonoidAlgebra ℤ (Hp p)) :
    lmul p h (∑ b ∈ s, f b) = ∑ b ∈ s, lmul p h (f b) := by
  simp only [lmul, Finset.mul_sum]

lemma lmul_zero (h : Hp p) : lmul p h (0 : MonoidAlgebra ℤ (Hp p)) = 0 := mul_zero _

lemma act_apply_mul (h c : Hp p) (z : Vp p) : act p h z (h * c) = lmul p h (z c) := by
  rw [act_apply, inv_mul_cancel_left]

/-! ## 5. Procesi 映射 `π` -/

/-- 取第 `b` 个坐标。 -/
noncomputable def evalB (b : Hp p) : Vp p →ₗ[ℤ] MonoidAlgebra ℤ (Hp p) where
  toFun z := z b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma evalB_apply (b : Hp p) (z : Vp p) : evalB p b z = z b := rfl

/-- 单个坐标的贡献 `z ↦ z b − ε(z b)·b`。 -/
noncomputable def piTerm (b : Hp p) : Vp p →ₗ[ℤ] MonoidAlgebra ℤ (Hp p) :=
  evalB p b - (LinearMap.toSpanSingleton ℤ (MonoidAlgebra ℤ (Hp p))
    (MonoidAlgebra.single b (1 : ℤ))).comp ((aug p).comp (evalB p b))

lemma piTerm_apply (b : Hp p) (z : Vp p) :
    piTerm p b z = z b - aug p (z b) • MonoidAlgebra.single b (1 : ℤ) := by
  simp only [piTerm, LinearMap.sub_apply, evalB_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]

/-- **Procesi 映射** `π : Z[H]^{⊕p²} → Z[H]`。 -/
noncomputable def pi : Vp p →ₗ[ℤ] MonoidAlgebra ℤ (Hp p) :=
  ∑ b : Hp p, piTerm p b

lemma aug_smul' (m : ℤ) (w : MonoidAlgebra ℤ (Hp p)) : aug p (m • w) = m * aug p w :=
  map_smul (aug p) m w

lemma aug_piTerm (b : Hp p) (z : Vp p) : aug p (piTerm p b z) = 0 := by
  rw [piTerm_apply, map_sub, aug_smul', aug_single]
  ring

/-- 方向 ①：`range π ⊆ I[H]`。 -/
theorem range_pi_le : LinearMap.range (pi p) ≤ I_H p := by
  intro w hw
  obtain ⟨z, rfl⟩ := hw
  rw [I_H, LinearMap.mem_ker, pi, LinearMap.sum_apply, map_sum]
  exact Finset.sum_eq_zero (fun b _ => aug_piTerm p b z)

/-! ## 6. `π` 的等变性 -/

/-- **逐坐标核心**：`πTerm (h·c) (h • z) = h · πTerm c z`。 -/
lemma piTerm_act (h c : Hp p) (z : Vp p) :
    piTerm p (h * c) (act p h z) = lmul p h (piTerm p c z) := by
  rw [piTerm_apply, piTerm_apply, act_apply_mul, aug_lmul, lmul_sub, lmul_smul, lmul_single]

/-- `π` 是 `H`-等变的。 -/
theorem pi_equivariant (h : Hp p) (z : Vp p) : pi p (act p h z) = lmul p h (pi p z) := by
  have hL : pi p (act p h z) = ∑ b : Hp p, piTerm p b (act p h z) := by
    simp only [pi, LinearMap.sum_apply, Finset.sum_apply]
  have hR : lmul p h (pi p z) = ∑ c : Hp p, lmul p h (piTerm p c z) := by
    have hz : pi p z = ∑ c : Hp p, piTerm p c z := by
      simp only [pi, LinearMap.sum_apply, Finset.sum_apply]
    rw [hz]
    simp only [lmul, Finset.mul_sum]
  rw [hL, hR, ← Equiv.sum_comp (Equiv.mulLeft h) (fun b : Hp p => piTerm p b (act p h z))]
  exact Finset.sum_congr rfl (fun c _ => piTerm_act p h c z)

/-- **核稳定**：`ker π` 在坐标作用下不变（`Mp` 成为 `ℤ[H]`-模的根据）。 -/
theorem ker_pi_stable (h : Hp p) {z : Vp p} (hz : z ∈ LinearMap.ker (pi p)) :
    act p h z ∈ LinearMap.ker (pi p) := by
  rw [LinearMap.mem_ker] at hz ⊢
  rw [pi_equivariant, hz, lmul_zero]

/-! ## 7. 满射性：`range π = I[H]` -/

/-- 只在槽 `1` 放 `single h 1` 的向量。 -/
noncomputable def deltaVec (h : Hp p) : Vp p :=
  fun b => if b = 1 then MonoidAlgebra.single h 1 else 0

lemma pi_deltaVec (h : Hp p) : pi p (deltaVec p h) = MonoidAlgebra.single h 1 - 1 := by
  rw [pi, LinearMap.sum_apply, Finset.sum_eq_single (1 : Hp p)]
  · rw [piTerm_apply, deltaVec, if_pos rfl, aug_single, one_smul]
    rfl
  · intro b _ hb
    rw [piTerm_apply, deltaVec, if_neg hb, map_zero, zero_smul, sub_zero]
  · intro hnot
    exact absurd (Finset.mem_univ (1 : Hp p)) hnot

lemma smul_single_one (c : ℤ) (g : Hp p) :
    c • MonoidAlgebra.single g (1 : ℤ) = MonoidAlgebra.single g c := by
  simp

lemma eq_sum_coeff_smul_single (w : MonoidAlgebra ℤ (Hp p)) :
    w = ∑ g : Hp p, (w.coeff g) • MonoidAlgebra.single g (1 : ℤ) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single w]
  rw [Finsupp.sum_fintype w.coeff (fun g c => MonoidAlgebra.single g c)
      (by intro g; simp)]
  exact Finset.sum_congr rfl (fun g _ => (smul_single_one p (w.coeff g) g).symm)

lemma aug_eq_sum_coeff (w : MonoidAlgebra ℤ (Hp p)) :
    aug p w = ∑ g : Hp p, w.coeff g := by
  conv_lhs => rw [eq_sum_coeff_smul_single p w]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [aug_smul', aug_single, mul_one]

lemma eq_sum_coeff_smul_sub_one (w : MonoidAlgebra ℤ (Hp p)) (hw : aug p w = 0) :
    w = ∑ g : Hp p, (w.coeff g) • (MonoidAlgebra.single g (1 : ℤ) - 1) := by
  have hsplit : (∑ g : Hp p, (w.coeff g) • (MonoidAlgebra.single g (1 : ℤ) - 1))
      = (∑ g : Hp p, (w.coeff g) • MonoidAlgebra.single g (1 : ℤ))
        - (∑ g : Hp p, (w.coeff g) • (1 : MonoidAlgebra ℤ (Hp p))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun g _ => smul_sub _ _ _)
  rw [hsplit, ← eq_sum_coeff_smul_single p w]
  have hconst : (∑ g : Hp p, (w.coeff g) • (1 : MonoidAlgebra ℤ (Hp p))) = (aug p w) • 1 := by
    rw [aug_eq_sum_coeff p w, Finset.sum_smul]
  rw [hconst, hw, zero_smul, sub_zero]

theorem range_pi_ge : I_H p ≤ LinearMap.range (pi p) := by
  intro w hw
  have hw0 : aug p w = 0 := (LinearMap.mem_ker).mp hw
  rw [eq_sum_coeff_smul_sub_one p w hw0]
  refine Submodule.sum_mem _ (fun g _ => ?_)
  refine Submodule.smul_mem _ _ ?_
  have : MonoidAlgebra.single g (1 : ℤ) - 1 = pi p (deltaVec p g) := (pi_deltaVec p g).symm
  rw [this]
  exact LinearMap.mem_range_self _ _

/-- **`range π = I[H]`**（论文 `prop:procesi-H` 的满射性）。 -/
theorem range_pi_eq : LinearMap.range (pi p) = I_H p :=
  le_antisymm (range_pi_le p) (range_pi_ge p)

/-! ## 8. `Rep ℤ (Hp p)` 对象与 Procesi 短正合列 -/

/-- 自建正则模（载体 = 群环本身）。 -/
noncomputable def regZ : Rep ℤ (Hp p) :=
  Rep.ofDistribMulAction ℤ (Hp p) (MonoidAlgebra ℤ (Hp p))

/-- `I[H]` 在左乘下稳定。 -/
theorem I_H_stable (h : Hp p) {w : MonoidAlgebra ℤ (Hp p)} (hw : w ∈ I_H p) :
    lmul p h w ∈ I_H p := by
  rw [I_H, LinearMap.mem_ker] at hw ⊢
  rw [aug_lmul, hw]

noncomputable def I_H_act (h : Hp p) (w : ↥(I_H p)) : ↥(I_H p) :=
  ⟨lmul p h w.1, I_H_stable p h w.2⟩

noncomputable instance : DistribMulAction (Hp p) ↥(I_H p) where
  smul h w := I_H_act p h w
  one_smul w := by
    apply Subtype.ext
    show lmul p 1 w.1 = w.1
    exact one_mul w.1
  mul_smul a b w := by
    apply Subtype.ext
    show lmul p (a * b) w.1 = lmul p a (lmul p b w.1)
    exact (lmul_mul p a b w.1).symm
  smul_zero h := by
    apply Subtype.ext
    show lmul p h (0 : MonoidAlgebra ℤ (Hp p)) = 0
    exact lmul_zero p h
  smul_add h x y := by
    apply Subtype.ext
    show lmul p h (x.1 + y.1) = lmul p h x.1 + lmul p h y.1
    simp only [lmul, mul_add]

/-- **`I[H]` 作为 `Rep ℤ (Hp p)`**。 -/
noncomputable def I_H_rep : Rep ℤ (Hp p) :=
  Rep.ofDistribMulAction ℤ (Hp p) ↥(I_H p)

lemma act_smul (h : Hp p) (m : ℤ) (z : Vp p) : act p h (m • z) = m • act p h z := by
  funext i
  simp only [act_apply, Pi.smul_apply, lmul_smul]

noncomputable def actLin (h : Hp p) : Vp p →ₗ[ℤ] Vp p where
  toFun := act p h
  map_add' := act_add p h
  map_smul' := act_smul p h

noncomputable def Vrepr : Representation ℤ (Hp p) (Vp p) where
  toFun h := actLin p h
  map_one' := LinearMap.ext fun z => act_one p z
  map_mul' x y := LinearMap.ext fun z => act_mul p x y z

/-- `Vp p = Z[H]^{⊕p²}` 作为 `Rep ℤ (Hp p)`。 -/
noncomputable abbrev VRep : Rep ℤ (Hp p) := Rep.of (Vrepr p)

/-- **`Mp = ker π` 作为 `Rep ℤ (Hp p)`**（论文的 `M|_H`）。 -/
noncomputable def M_act (h : Hp p) (z : ↥(LinearMap.ker (pi p))) : ↥(LinearMap.ker (pi p)) :=
  ⟨act p h z.1, ker_pi_stable p h z.2⟩

noncomputable instance : DistribMulAction (Hp p) ↥(LinearMap.ker (pi p)) where
  smul h z := M_act p h z
  one_smul z := by
    apply Subtype.ext
    show act p 1 z.1 = z.1
    exact act_one p z.1
  mul_smul a b z := by
    apply Subtype.ext
    show act p (a * b) z.1 = act p a (act p b z.1)
    exact act_mul p a b z.1
  smul_zero h := by
    apply Subtype.ext
    show act p h (0 : Vp p) = 0
    exact act_zero p h
  smul_add h x y := by
    apply Subtype.ext
    show act p h (x.1 + y.1) = act p h x.1 + act p h y.1
    exact act_add p h x.1 y.1

noncomputable def M_rep : Rep ℤ (Hp p) :=
  Rep.ofDistribMulAction ℤ (Hp p) ↥(LinearMap.ker (pi p))

/-- 包含 `Mp ↪ Vp`。 -/
noncomputable def inclM : M_rep p ⟶ VRep p :=
  Rep.ofHom (Representation.IntertwiningMap.mk (LinearMap.ker (pi p)).subtype (by
    intro h
    ext z
    rfl))

@[simp] lemma inclM_apply (z : (M_rep p).V) : (inclM p).hom z = z.1 := rfl

/-- `π` 以 `I[H]` 为靶。 -/
noncomputable def piToI : Vp p →ₗ[ℤ] ↥(I_H p) :=
  (pi p).codRestrict (I_H p) fun z => range_pi_le p (LinearMap.mem_range_self (pi p) z)

/-- `π : Vp → I[H]` 作为 `Rep` 态射。 -/
noncomputable def piHom : VRep p ⟶ I_H_rep p :=
  Rep.ofHom (Representation.IntertwiningMap.mk (piToI p) (by
    intro h
    refine LinearMap.ext fun z => ?_
    exact Subtype.ext (pi_equivariant p h z)))

/-- **Procesi 短复形** `0 → Mp → Vp → I[H] → 0`。 -/
noncomputable def procesiComplex : CategoryTheory.ShortComplex (Rep ℤ (Hp p)) :=
  CategoryTheory.ShortComplex.mk (inclM p) (piHom p) (by
    ext z
    exact Subtype.ext ((LinearMap.mem_ker).mp z.2))

attribute [local instance 1500] Rep.hV2

instance : CategoryTheory.Mono (inclM p) := by
  rw [Rep.mono_iff_injective]
  intro x y h
  exact Subtype.ext h

lemma piToI_surjective : Function.Surjective (piToI p) := by
  intro w
  have hw : (w : MonoidAlgebra ℤ (Hp p)) ∈ LinearMap.range (pi p) :=
    (range_pi_eq p).symm ▸ w.2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩

instance : CategoryTheory.Epi (piHom p) :=
  (Rep.epi_iff_surjective (piHom p)).mpr (piToI_surjective p)

noncomputable abbrev procesiComplexMod : CategoryTheory.ShortComplex (ModuleCat ℤ) :=
  (procesiComplex p).map (forget₂ (Rep ℤ (Hp p)) (ModuleCat ℤ))

lemma procesiComplexMod_exact : (procesiComplexMod p).Exact := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : (piToI p x : ↥(I_H p)) = 0 := hx
  have hx'' : ((piToI p x : ↥(I_H p)) : MonoidAlgebra ℤ (Hp p)) = 0 := by rw [hx']; rfl
  exact ⟨⟨x, (LinearMap.mem_ker).mpr hx''⟩, rfl⟩

/-- **Procesi 序列正合**。 -/
theorem procesiComplex_exact : (procesiComplex p).Exact :=
  ((procesiComplex p).exact_map_iff_of_faithful (forget₂ (Rep ℤ (Hp p)) (ModuleCat ℤ))).mp
    (procesiComplexMod_exact p)

/-- **Procesi 序列短正合**（论文 `thm:Cp-general` 的 `0 → M|_H → Z[H]^{⊕p²} → I[H] → 0`）。 -/
theorem procesiComplex_shortExact : (procesiComplex p).ShortExact :=
  CategoryTheory.ShortComplex.ShortExact.mk' (procesiComplex_exact p)
    (inferInstanceAs (CategoryTheory.Mono (inclM p)))
    (inferInstanceAs (CategoryTheory.Epi (piHom p)))

/-! ## 9. 公理闸门（无 sorry、无自造公理） -/

#print axioms card_Hp
#print axioms pi_equivariant
#print axioms ker_pi_stable
#print axioms range_pi_eq
#print axioms procesiComplex_shortExact

end ABGV52.P
