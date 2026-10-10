/-
  ABGV-5.2 —— EM 判据（修正形）清零波：`EM.IsQuasiPermutation` 与
  `¬ EM.IsQuasiPermutation H M_H_rep`

  背景
  ====
    论文 `thm:endo-miyata` 的 ⊕-形陈述为假（机器核反例）；修正形按
    EM1973a :176–180 的**序列形**给出：

      M 是 quasi-permutation ⟺ ∃ 短正合列 0 → M → P → Q → 0（P、Q 置换格）。

    本件落地：
      §1 `EM.IsQuasiPermutation`（一般群 G）＋ 类型锁；
      §2 与根级（H-专用）谓词的 `Iff.rfl` 桥；
      §3 一般 G 的双积原子工具 ＋
         `IsStablyPermutation ⟹ IsQuasiPermutation`（f := inl ≫ e.hom，g := e.inv ≫ snd）；
      §4 度 1 消没工具（S3/S4 的度 2 机器的度 1 镜像）：
         `subsingleton_coh1_TZ`、`subsingleton_permHK`、`subsingleton_ofMulAction_coh1`；
      §5 Ext 侧组装：`extOneTriv_addEquiv_coh1`（ExtBridge 的度 1 镜像）＋ 加法形搬运；
      §6 主定理 `¬ EM.IsQuasiPermutation H M_H_rep`（度 1→2 LES 反证：若 M_H 是
         quasi-permutation，则 coh² 的指数整除 3，与判别对 `⟂` 矛盾）；
      §7 非空性对照（L1）：`EM.IsQuasiPermutation H I_H_rep`（增广序列）；
      §8 附带产物：`¬ EM.IsStablyPermutation H M_H_rep`（O1 重接线）。

  工艺要点（前序探针 ProbeQ1/ProbeQ2 实测）
  ====
    * Ext 上 `(3:ℤ) • −` 存在**实例菱形**（`Ext.Linear` 的 `Module ℤ` vs
      `AddGroup.toIntModule`）⟹ Ext 侧一律写**加法形** `y + y + y`，只用
      `Ext.add_comp`（加法专用）；ℤ-标量仅出现在 coh 侧，配一条转换引理
      `three_smul_coh_eq_add_three`；
    * `ShortComplex.moduleCat_exact_iff` 只对 `ModuleCat` 复形可用 ⟹ 先证
      忘记函子像的正合性，再 `exact_map_iff_of_faithful` 反射回 `Rep`；
    * `Subsingleton (Additive K →+ ℤ)` 走基数论证（`card_nsmul_eq_zero` ＋
      `Nat.cast_smul_eq_nsmul` ＋ 无零因子）。
-/
import ABGV52.C8b_ABGV52
import ABGV52.D1_ABGV52
import ABGV52.S4_ABGV52
import ABGV52.ExtBridge_ABGV52
import ABGV52.ExtLES_ABGV52
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section

namespace ABGV52

-- `ℤ` 上 `AddCommGroup.toIntModule` 与 `Rep.hV2` 争用 `Module ℤ ↥X`（同 C4 的处理）。
attribute [local instance 1500] Rep.hV2

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## §1 EM 判据（修正形）：quasi-permutation 的序列刻画 -/

namespace EM

/-- **EM 判据（修正序列形，EM1973a :176–180）**：`M` 是 quasi-permutation，若存在
短正合列 `0 → M → P → Q → 0`（`P`、`Q` 均为置换格）。

论文 `thm:endo-miyata` 的 ⊕-形陈述为假（`M_H` 即反例）；本定义是修正形。 -/
def IsQuasiPermutation (G : Type*) [Group G] (M : Rep ℤ G) : Prop :=
  ∃ (P Q : Rep ℤ G) (f : M ⟶ P) (g : P ⟶ Q),
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    EM.IsPermutationLattice G P ∧ EM.IsPermutationLattice G Q

/-- 类型锁（定义外形逐字锁定）。 -/
example (G : Type*) [Group G] (M : Rep ℤ G) :
    EM.IsQuasiPermutation G M ↔
      ∃ (P Q : Rep ℤ G) (f : M ⟶ P) (g : P ⟶ Q),
        Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
        EM.IsPermutationLattice G P ∧ EM.IsPermutationLattice G Q :=
  Iff.rfl

end EM

/-! ## §2 与根级（H-专用）谓词的桥

  注意：不放进 `namespace EM`——否则 `IsPermutationLattice` 先解析到
  `EM.IsPermutationLattice`（一般 G 版），产生 `Group ↑P` 合成失败。 -/

theorem EM.isPermutationLattice_iff (P : Rep ℤ H) :
    EM.IsPermutationLattice H P ↔ _root_.ABGV52.IsPermutationLattice P :=
  Iff.rfl

theorem EM.isStablyPermutation_iff (L : Rep ℤ H) :
    EM.IsStablyPermutation H L ↔ _root_.ABGV52.IsStablyPermutation L :=
  Iff.rfl

/-- 桥（O1 传播）：`EM.IsQuasiPermutation H`（一般 G 版在 H 的实例）与定义层
`Hyp_ABGV52.IsQuasiPermutation` 定义级同体（∃-体逐项 defeq：置换格谓词已由
`EM.isPermutationLattice_iff` 桥定）。 -/
theorem EM.isQuasiPermutation_iff (M : Rep ℤ H) :
    EM.IsQuasiPermutation H M ↔ _root_.ABGV52.IsQuasiPermutation M :=
  Iff.rfl

/-! ## §3 一般群 G：双积原子工具 ＋ `IsStablyPermutation ⟹ IsQuasiPermutation` -/

namespace EM

section GeneralG

variable {G : Type} [Group G]

/-- `Iso` 的 `inv ∘ hom = id`（函数层；避开 `Iso.*_apply` 的名字波动）。
`e : A ≅ B` 时 `e.hom_inv_id : e.hom ≫ e.inv = 𝟙 A`。 -/
theorem iso_inv_hom_apply {A B : Rep ℤ G} (e : A ≅ B) (x : ↥A) : e.inv (e.hom x) = x := by
  have h : (e.hom ≫ e.inv) x = (𝟙 A) x := congrArg (fun m => m x) e.hom_inv_id
  simpa only [Rep.comp_apply, Rep.id_apply] using h

/-- `Iso` 的 `hom ∘ inv = id`（函数层；`e.inv_hom_id : e.inv ≫ e.hom = 𝟙 B`）。 -/
theorem iso_hom_inv_apply {A B : Rep ℤ G} (e : A ≅ B) (y : ↥B) : e.hom (e.inv y) = y := by
  have h : (e.inv ≫ e.hom) y = (𝟙 B) y := congrArg (fun m => m y) e.inv_hom_id
  simpa only [Rep.comp_apply, Rep.id_apply] using h

/-- `fst ∘ inl = id`（函数层；同 EMConsume 的双积工具，此处降到 `[Group G]`）。 -/
theorem biprod_inl_fst_apply (M P : Rep ℤ G) (m : ↥M) :
    (biprod.fst (X := M) (Y := P)).hom ((biprod.inl (X := M) (Y := P)).hom m) = m := by
  have h := congrArg (fun f : M ⟶ M => (f : ↥M → ↥M) m)
    (biprod.inl_fst (X := M) (Y := P))
  simpa only [Rep.comp_apply, Rep.id_apply] using h

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

/-- **`IsStablyPermutation ⟹ IsQuasiPermutation`**（修正形的主桥，EM1973a :176–180）：
`M ⊞ P ≅ Q` ⟹ 短正合列 `0 → M →^{inl ≫ e} Q →^{e⁻¹ ≫ snd} P → 0`。

准置换见证取交换后的对 `(Q, P)`（`P`、`Q` 均为置换格）。 -/
theorem isQuasiPermutation_of_isStablyPermutation (M : Rep ℤ G)
    (h : EM.IsStablyPermutation G M) : EM.IsQuasiPermutation G M := by
  obtain ⟨P, Q, hP, hQ, ⟨e⟩⟩ := h
  refine ⟨Q, P, biprod.inl ≫ e.hom, e.inv ≫ biprod.snd, ?_, ?_, ?_, hQ, hP⟩
  · -- `inl ≫ e.hom` 单射
    intro x y hxy
    have h2 : (biprod.inl (X := M) (Y := P)).hom x
        = (biprod.inl (X := M) (Y := P)).hom y := by
      have h3 : e.hom ((biprod.inl (X := M) (Y := P)).hom x)
          = e.hom ((biprod.inl (X := M) (Y := P)).hom y) := by
        simpa only [Rep.comp_apply] using hxy
      have h4 := congrArg (fun w => e.inv w) h3
      simpa only [iso_inv_hom_apply] using h4
    calc x = (biprod.fst (X := M) (Y := P)).hom
          ((biprod.inl (X := M) (Y := P)).hom x) :=
          (biprod_inl_fst_apply M P x).symm
      _ = (biprod.fst (X := M) (Y := P)).hom
          ((biprod.inl (X := M) (Y := P)).hom y) := by rw [h2]
      _ = y := biprod_inl_fst_apply M P y
  · -- 正合性（元素层：`snd (e⁻¹ y) = 0` ⟺ `y ∈ range(inl ≫ e)`）
    intro y
    constructor
    · intro hy
      refine ⟨(biprod.fst (X := M) (Y := P)).hom (e.inv y), ?_⟩
      have htot := biprod_total_apply M P (e.inv y)
      have hsnd : (biprod.snd (X := M) (Y := P)).hom (e.inv y) = 0 := by
        have hgy : (e.inv ≫ biprod.snd) y = 0 := hy
        rwa [Rep.comp_apply] at hgy
      rw [hsnd, map_zero, add_zero] at htot
      calc (biprod.inl ≫ e.hom) ((biprod.fst (X := M) (Y := P)).hom (e.inv y))
          = e.hom ((biprod.inl (X := M) (Y := P)).hom
              ((biprod.fst (X := M) (Y := P)).hom (e.inv y))) :=
            Rep.comp_apply biprod.inl e.hom _
        _ = e.hom (e.inv y) := by rw [htot]
        _ = y := iso_hom_inv_apply e y
    · rintro ⟨x, rfl⟩
      rw [show (e.inv ≫ biprod.snd) ((biprod.inl ≫ e.hom) x)
            = (biprod.snd (X := M) (Y := P)).hom
                (e.inv (e.hom ((biprod.inl (X := M) (Y := P)).hom x))) from rfl]
      rw [iso_inv_hom_apply]
      exact biprod_inl_snd_apply M P x
  · -- `e⁻¹ ≫ snd` 满射
    intro p
    refine ⟨e.hom ((biprod.inr (X := M) (Y := P)).hom p), ?_⟩
    calc (e.inv ≫ biprod.snd) (e.hom ((biprod.inr (X := M) (Y := P)).hom p))
        = (biprod.snd (X := M) (Y := P)).hom
            (e.inv (e.hom ((biprod.inr (X := M) (Y := P)).hom p))) :=
          Rep.comp_apply e.inv biprod.snd _
      _ = (biprod.snd (X := M) (Y := P)).hom ((biprod.inr (X := M) (Y := P)).hom p) := by
          rw [iso_inv_hom_apply]
      _ = p := biprod_inr_snd_apply M P p

end GeneralG

end EM

/-! ## §4 度 1 消没工具（S3/S4 度 2 机器的镜像） -/

/-- 有限群到 `ℤ` 的加法同态逐点为零（基数论证：`card • x = 0` ＋ 无零因子）。 -/
theorem addHom_TZ_apply_zero (K : Subgroup H)
    (f : Additive ↥K →+ ↥(Rep.trivial ℤ ↥K ℤ)) (x : Additive ↥K) : f x = 0 := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  have hx : Fintype.card (Additive ↥K) • x = 0 := card_nsmul_eq_zero
  have h1 := map_nsmul f (Fintype.card (Additive ↥K)) x
  rw [hx, map_zero] at h1
  have h2 : (Fintype.card (Additive ↥K) : ℤ) * f x = 0 := by
    simpa only [Int.nsmul_eq_mul] using h1.symm
  have hc : (Fintype.card (Additive ↥K) : ℤ) ≠ 0 := by
    haveI : Nonempty (Additive ↥K) := ⟨Additive.ofMul 1⟩
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp h2).resolve_left hc

/-- `Hom(↥K, ℤ)` 上的 `Subsingleton`（逐点为零）。 -/
theorem subsingleton_addHom_TZ (K : Subgroup H) :
    Subsingleton (Additive ↥K →+ ↥(Rep.trivial ℤ ↥K ℤ)) := by
  refine ⟨fun f g => ?_⟩
  ext x
  exact (addHom_TZ_apply_zero K f x).trans (addHom_TZ_apply_zero K g x).symm

/-- **有限群上 `coh¹(K, ℤtriv)` 消没**：`coh¹(K,ℤ) ≅ Hom(K,ℤ)`（`H1IsoOfIsTrivial`），
后者被逐点零化。 -/
theorem subsingleton_coh1_TZ (K : Subgroup H) :
    Subsingleton (cohOf ↥K (Rep.trivial ℤ ↥K ℤ) 1) := by
  haveI : Subsingleton (Additive ↥K →+ ↥(Rep.trivial ℤ ↥K ℤ)) := subsingleton_addHom_TZ K
  refine ⟨fun x y => ?_⟩
  exact (groupCohomology.H1IsoOfIsTrivial (k := ℤ) (G := ↥K)
    (A := Rep.trivial ℤ ↥K ℤ)).toLinearEquiv.injective (Subsingleton.elim _ _)

/-- `Subsingleton` 沿 `AddEquiv` 拉回。 -/
theorem subsingleton_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (h : Subsingleton B) : Subsingleton A := by
  haveI := h
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- `Subsingleton` 沿 `LinearEquiv` 拉回（靶侧已知）。 -/
theorem subsingleton_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (e : V ≃ₗ[ℤ] W) (h : Subsingleton W) :
    Subsingleton V := by
  haveI := h
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- `Subsingleton` 经收缩（retract）拉回（`kills_of_retract` 的度 1 镜像）。 -/
theorem subsingleton_coh1_of_retract {A B : Rep ℤ H} (γ : A ⟶ B) (δ : B ⟶ A)
    (h : γ ≫ δ = 𝟙 A) (hB : Subsingleton (coh B 1)) : Subsingleton (coh A 1) := by
  haveI := hB
  have hid : ∀ z : coh A 1,
      (groupCohomology.map (MonoidHom.id H) δ 1).hom
        ((groupCohomology.map (MonoidHom.id H) γ 1).hom z) = z := by
    intro z
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, h, groupCohomology.map_id]
    rfl
  exact ⟨fun x y => by
    calc x = (groupCohomology.map (MonoidHom.id H) δ 1).hom
          ((groupCohomology.map (MonoidHom.id H) γ 1).hom x) := (hid x).symm
      _ = (groupCohomology.map (MonoidHom.id H) δ 1).hom
          ((groupCohomology.map (MonoidHom.id H) γ 1).hom y) := by
          rw [Subsingleton.elim ((groupCohomology.map (MonoidHom.id H) γ 1).hom x)
            ((groupCohomology.map (MonoidHom.id H) γ 1).hom y)]
      _ = y := hid y⟩

/-- **`coh¹(H, ℤ[H/K])` 消没**（Shapiro 收缩 ＋ `Subsingleton` 沿 `coindIso` 运输）。 -/
theorem subsingleton_permHK (K : Subgroup H) : Subsingleton (coh (permHK K) 1) := by
  haveI : Fintype ↥K := Fintype.ofFinite _
  exact subsingleton_coh1_of_retract (shapiroHom K) (shapiroOfCoind K) (shapiroHom_comp K)
    (subsingleton_of_linearEquiv
      (groupCohomology.coindIso (S := K) (Rep.trivial ℤ ↥K ℤ) 1).toLinearEquiv
      (subsingleton_coh1_TZ K))

/-! ## §4b 轨道分解（度 1）：有限 `H`-集 `X` 上 `coh¹(H, ℤ[X])` 消没 -/

section Orbit1

variable (X : Type) [Fintype X] [MulAction H X]

/-- `OrbitQ` 的 `Fintype`/`DecidableEq`（S4 的局部实例不导出，此处度 1 重声明）。 -/
noncomputable local instance orbitQFintype1 : Fintype (OrbitQ X) := Fintype.ofFinite _
noncomputable local instance orbitQDecEq1 : DecidableEq (OrbitQ X) := Classical.decEq _

/-- `α_ω` 在 `coh¹` 上诱导的映射。 -/
noncomputable def orbAlphaCoh1 (ω : OrbitQ X) :
    groupCohomology (Rep.ofMulAction ℤ H X) 1
      ⟶ groupCohomology (permHK (orbStab X ω)) 1 :=
  groupCohomology.map (MonoidHom.id H) (orbAlpha X ω) 1

/-- `β_ω` 在 `coh¹` 上诱导的映射。 -/
noncomputable def orbBetaCoh1 (ω : OrbitQ X) :
    groupCohomology (permHK (orbStab X ω)) 1
      ⟶ groupCohomology (Rep.ofMulAction ℤ H X) 1 :=
  groupCohomology.map (MonoidHom.id H) (orbBeta X ω) 1

/-- `E_ω` 在 `coh¹` 上诱导的映射（直接定义为复合）。 -/
noncomputable def orbCoh1 (ω : OrbitQ X) :
    groupCohomology (Rep.ofMulAction ℤ H X) 1
      ⟶ groupCohomology (Rep.ofMulAction ℤ H X) 1 :=
  orbAlphaCoh1 X ω ≫ orbBetaCoh1 X ω

lemma cohMap_sum_orbE1 :
    groupCohomology.map (MonoidHom.id H) (∑ ω : OrbitQ X, orbE X ω) 1
      = ∑ ω : OrbitQ X, orbCoh1 X ω := by
  rw [cohMap_sum Finset.univ (fun ω : OrbitQ X => orbE X ω) 1]
  exact Finset.sum_congr rfl (fun ω _ =>
    groupCohomology.map_id_comp (orbAlpha X ω) (orbBeta X ω) 1)

/-- **`coh¹(H, ℤ[X])` 消没**（轨道幂等分解：`x = Σ_ω (E_ω)_* x`，逐项经
`coh¹(H, ℤ[H/K_ω])` 分解，后者消没——`subsingleton_permHK`）。

与 S4 的 `threeKills_ofMulAction` 同型（前者杀 `3·`，本件杀整体）。 -/
theorem subsingleton_ofMulAction_coh1 :
    Subsingleton (coh (Rep.ofMulAction ℤ H X) 1) := by
  classical
  refine ⟨fun x y => ?_⟩
  have hsplit : ∀ z : coh (Rep.ofMulAction ℤ H X) 1,
      z = ∑ ω : OrbitQ X, (orbCoh1 X ω).hom z := by
    intro z
    calc z = (groupCohomology.map (MonoidHom.id H) (𝟙 (Rep.ofMulAction ℤ H X)) 1).hom z := by
          rw [groupCohomology.map_id]; rfl
      _ = (groupCohomology.map (MonoidHom.id H) (∑ ω : OrbitQ X, orbE X ω) 1).hom z := by
          rw [show (𝟙 (Rep.ofMulAction ℤ H X)) = ∑ ω : OrbitQ X, orbE X ω
                from (sum_orbE X).symm]
      _ = (∑ ω : OrbitQ X, orbCoh1 X ω).hom z := by rw [cohMap_sum_orbE1]
      _ = ∑ ω : OrbitQ X, (orbCoh1 X ω).hom z := moduleCat_sum_hom_apply Finset.univ _ z
  calc x = ∑ ω : OrbitQ X, (orbCoh1 X ω).hom x := hsplit x
    _ = ∑ ω : OrbitQ X, (orbCoh1 X ω).hom y := by
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        haveI : Subsingleton (coh (permHK (orbStab X ω)) 1) := subsingleton_permHK (orbStab X ω)
        have hω : (orbAlphaCoh1 X ω).hom x = (orbAlphaCoh1 X ω).hom y :=
          Subsingleton.elim _ _
        rw [show (orbCoh1 X ω).hom x
              = (orbBetaCoh1 X ω).hom ((orbAlphaCoh1 X ω).hom x) from by
          rw [orbCoh1, ModuleCat.comp_apply]]
        rw [hω]
        rw [show (orbBetaCoh1 X ω).hom ((orbAlphaCoh1 X ω).hom y)
              = (orbCoh1 X ω).hom y from by
          rw [orbCoh1, ModuleCat.comp_apply]]
    _ = y := (hsplit y).symm

end Orbit1

/-- **置换格 `L` 上 `coh¹` 消没**（展开 `IsPermutationLattice` 后经轨道分解）。 -/
theorem subsingleton_perm_coh1 (L : Rep ℤ H) (hL : IsPermutationLattice L) :
    Subsingleton (coh L 1) := by
  obtain ⟨X, hF, hA, ⟨e⟩⟩ := hL
  letI : Fintype X := hF
  letI : MulAction H X := hA
  exact subsingleton_of_linearEquiv (cohLinearEquivOfIso e 1)
    (subsingleton_ofMulAction_coh1 X)

/-! ## §5 Ext 侧组装（度 1） -/

/-- ExtBridge 的度 1 镜像：`Ext¹(ℤtriv, A) ≃+ coh¹(A)`。 -/
noncomputable def extOneTriv_addEquiv_coh1 (A : Rep.{0} ℤ H) :
    Ext trivRep A 1 ≃+ ↥(groupCohomology A 1) :=
  (extAddEquivLinYonedaHomology trivRep A (Rep.barResolution ℤ H) 0).trans
    ((groupCohomologyIso A 1 (Rep.barResolution ℤ H)).toLinearEquiv.toAddEquiv.symm)

/-- `Subsingleton (Ext¹(ℤtriv, A))` 从 `coh¹(A)` 运输。 -/
theorem subsingleton_ext_one_triv (A : Rep.{0} ℤ H) (h : Subsingleton (coh A 1)) :
    Subsingleton (Ext trivRep A 1) :=
  subsingleton_of_addEquiv (extOneTriv_addEquiv_coh1 A) h

/-- coh 侧 ℤ-标量的加法形转换（Ext 侧一律加法形，故此转换只在 coh 侧需要）。 -/
theorem three_smul_coh_eq_add_three (A : Rep ℤ H) (x : coh A 2) :
    (3 : ℤ) • x = x + x + x := by
  rw [show (3 : ℤ) = 1 + 1 + 1 from rfl, add_zsmul, add_zsmul, one_zsmul]

/-- `Coh2ExpDvd3` 的加法形。 -/
theorem coh_add_three_eq_zero (A : Rep ℤ H) (h : Coh2ExpDvd3 A) :
    ∀ x : coh A 2, x + x + x = 0 :=
  fun x => (three_smul_coh_eq_add_three A x).symm.trans (h x)

/-- 「三倍为零」沿 `AddEquiv` 拉回。 -/
theorem add_three_eq_zero_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (h : ∀ b : B, b + b + b = 0) : ∀ a : A, a + a + a = 0 := by
  intro a
  have h1 : e (a + a + a) = e a + e a + e a := by rw [map_add, map_add]
  have h2 : e a + e a + e a = e 0 := (h (e a)).trans (map_zero e).symm
  exact e.injective (h1.trans h2)

/-- `Ext²(ℤtriv, A)` 的加法形「三倍为零」（经 `extTwoTriv_addEquiv_coh2` 运输）。 -/
theorem extTwoTriv_add_three_eq_zero (A : Rep.{0} ℤ H) (h : Coh2ExpDvd3 A) :
    ∀ z : Ext trivRep A 2, z + z + z = 0 :=
  add_three_eq_zero_of_addEquiv (extTwoTriv_addEquiv_coh2 A) (coh_add_three_eq_zero A h)

/-! ## §6 主定理：`M_H` 不是 quasi-permutation（度 1→2 LES 反证） -/

/-- **`M_H_rep` 不是 quasi-permutation**（EM 判据修正形的否定侧）。

反证：设 `0 → M → P → Q → 0`（`P`、`Q` 置换格）。取 `x₂ : coh²(M)` 使 `3·x₂ ≠ 0`
（判别对 `⟂`），`y := x₂` 沿 `extTwoTriv_addEquiv_coh2` 搬到 `Ext²(ℤtriv, M)`。
`(3y).comp (mk₀ f) = 0` 由 `P` 置换（`perm_exp`）；度 1→2 LES 的连接同态给出
`x₃ : Ext¹(ℤtriv, Q)` 满足 `x₃.comp extClass = 3y`；`Q` 置换 ⟹ `Ext¹(ℤtriv, Q)` 消没
⟹ `x₃ = 0` ⟹ `3y = 0` ⟹ `3x₂ = 0`，矛盾。 -/
theorem not_isQuasiPermutation_M_H_rep : ¬ EM.IsQuasiPermutation H M_H_rep := by
  rintro ⟨P, Q, f, g, hf, hfg, hg, hP, hQ⟩
  -- 短复形 `0 → M → P → Q → 0`（正合性经遗忘函子反射）
  let S : CategoryTheory.ShortComplex (Rep ℤ H) :=
    CategoryTheory.ShortComplex.mk f g (by
      ext m
      show g (f m) = 0
      exact hfg.apply_apply_eq_zero m)
  have hSmap : (S.map (forget₂ (Rep ℤ H) (ModuleCat ℤ))).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := (hfg x₂).mp hx₂
    exact ⟨x₁, hx₁⟩
  have hSex : S.Exact :=
    (S.exact_map_iff_of_faithful (forget₂ (Rep ℤ H) (ModuleCat ℤ))).mp hSmap
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' hSex ((Rep.mono_iff_injective f).mpr hf)
      ((Rep.epi_iff_surjective g).mpr hg)
  -- `P` 置换 ⟹ `Ext²(ℤtriv, P)` 的三倍消没
  have hPkill : ∀ z : Ext trivRep P 2, z + z + z = 0 :=
    extTwoTriv_add_three_eq_zero P
      (perm_exp P ((EM.isPermutationLattice_iff P).mp hP))
  -- 判别对给出 `3`-不消没的 `x₂`
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : coh M_H_rep 2, (3 : ℤ) • x₂ ≠ 0 := by
    by_contra h
    exact discriminant_pair_M_H_rep.2 (fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  have hx₂' : x₂ + x₂ + x₂ ≠ 0 :=
    fun h => hx₂ ((three_smul_coh_eq_add_three M_H_rep x₂).trans h)
  -- 经桥搬到 Ext² 侧
  let e := extTwoTriv_addEquiv_coh2 M_H_rep
  let y : Ext trivRep M_H_rep 2 := e.symm x₂
  have hey : e y = x₂ := AddEquiv.apply_symm_apply e x₂
  -- `(y+y+y) ∘ f = 0`
  have hφ : (y + y + y).comp (Ext.mk₀ S.f) (add_zero 2) = 0 := by
    rw [Ext.add_comp, Ext.add_comp]
    exact hPkill (y.comp (Ext.mk₀ S.f) (add_zero 2))
  -- 度 1→2 LES：连接同态打到 `y+y+y`
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (X := trivRep) (S := S) (hS := hS)
    (x₁ := y + y + y) (hx₁ := hφ) (n₀ := 1) (hn₀ := rfl)
  -- `Q` 置换 ⟹ `Ext¹(ℤtriv, Q)` 消没
  haveI : Subsingleton (Ext trivRep Q 1) :=
    subsingleton_ext_one_triv Q (subsingleton_perm_coh1 Q
      ((EM.isPermutationLattice_iff Q).mp hQ))
  have h3y : y + y + y = 0 := by
    have hx₃0 : x₃ = 0 := Subsingleton.elim x₃ 0
    rw [← hx₃, hx₃0]
    simp
  -- `e(y+y+y) = x₂+x₂+x₂ ≠ 0` 与 `e 0 = 0` 矛盾
  have : x₂ + x₂ + x₂ = 0 := by
    have h1 : e (y + y + y) = e y + e y + e y := by rw [map_add, map_add]
    rw [hey, h3y, map_zero] at h1
    exact h1.symm
  exact hx₂' this

/-! ## §7 非空性对照（L1）：增广序列使 `I_H` 成为 quasi-permutation -/

/-- **非空性对照（L1）**：`I_H` 是 quasi-permutation——增广短正合列
`0 → I[H] → ℤ[H] → ℤ → 0`（`ℤ[H]`、`ℤ` 均为置换格）。

即：判据的假设类在当前域类中**非空**（`M_H` 的否定不是空洞真）。 -/
theorem isQuasiPermutation_IH : EM.IsQuasiPermutation H I_H_rep := by
  have hInj : Function.Injective (augComplex.f) :=
    (Rep.mono_iff_injective augComplex.f).mp
      (inferInstanceAs (Mono inclHom))
  have hSurj : Function.Surjective (augComplex.g) :=
    (Rep.epi_iff_surjective augComplex.g).mp
      (inferInstanceAs (Epi augHom))
  have hEx : Function.Exact (augComplex.f) (augComplex.g) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact augComplexMod).mp
      augComplexMod_exact
  exact ⟨regZ, trivRep, augComplex.f, augComplex.g, hInj, hEx, hSurj,
    ⟨H, inferInstance, inferInstance, ⟨regZIsoLeftRegular⟩⟩,
    ⟨PUnit, inferInstance, inferInstance,
      ⟨(Rep.ofMulActionSubsingletonIsoTrivial (k := ℤ) (G := H) PUnit).symm⟩⟩⟩

/-! ## §8 O1 重接线：`M_H` 不是稳定置换格 -/

/-- **`M_H` 不是稳定置换格**（O1 重接线：`¬quasi-permutation ⟹ ¬SRat` 的中间件）。 -/
theorem not_isStablyPermutation_M_H_rep : ¬ EM.IsStablyPermutation H M_H_rep :=
  fun h => discriminant_pair_M_H_rep.2
    (stable_exp M_H_rep ((EM.isStablyPermutation_iff M_H_rep).mp h))

/-- 同上，根级谓词形。 -/
theorem not_isStablyPermutation_M_H_rep_root : ¬ IsStablyPermutation M_H_rep :=
  fun h => discriminant_pair_M_H_rep.2 (stable_exp M_H_rep h)

/-! ## §9 公理闸门 -/

#print axioms EM.iso_inv_hom_apply
#print axioms EM.biprod_total_apply
#print axioms EM.isQuasiPermutation_of_isStablyPermutation
#print axioms addHom_TZ_apply_zero
#print axioms subsingleton_coh1_TZ
#print axioms subsingleton_permHK
#print axioms subsingleton_ofMulAction_coh1
#print axioms subsingleton_perm_coh1
#print axioms extOneTriv_addEquiv_coh1
#print axioms three_smul_coh_eq_add_three
#print axioms extTwoTriv_add_three_eq_zero
#print axioms not_isQuasiPermutation_M_H_rep
#print axioms isQuasiPermutation_IH
#print axioms not_isStablyPermutation_M_H_rep
#print axioms not_isStablyPermutation_M_H_rep_root

end ABGV52
