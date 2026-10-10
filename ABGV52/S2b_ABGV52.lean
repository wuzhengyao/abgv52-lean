/-
  ABGV-5.2 —— S2b：`lem:H2-Z` 完整同构的机验交付件

  论文 `raw/ABGV-5.2-resolution.tex:1126`（label `lem:H2-Z`，§4）：

    `lem:H2-Z`. With the trivial H-action on ℤ, coh²(H, ℤ) ≅ C₃ × C₃.

  本件交付该同构的 Lean 形式 `H2_Z_equiv`（§5，第 (4) 项），
  附四条构件：

    §2  `coh2_iso_homQZ`（第 (1) 项）—— 纯装配，零新数学：
        H²(K, ℤ) ≃ₗ Hom(K, ℚ/ℤ)
        = S2 的 `coh1QZ_iso_coh2Z`（长正合列的 δ 桥）
          与 `groupCohomology.H1IsoOfIsTrivial`（Shapiro）复合。
    §3  `torsion3_equiv`（第 (2) 项）—— 本轮唯一新数学：
        ℚ/ℤ 的 3-挠子群 ≃+ ZMod 3（1/3 ↦ 1）。
        陈述适配说明：字面载体 `{q : QZ // (3 : ℤ) • q = 0}` 在本
        mathlib 无 `Add` 实例，故以 `↥(torsion3Sub QZ)` 为载体；
        二者类型字面等（defeq），见证见 §3 末 `example ... := rfl`。
    §4  `homQZ_equiv`（第 (3) 项）——
        (Additive H →+ TQD H) ≃ₗ[ℤ] (ZMod 3 × ZMod 3)。
    §5  `H2_Z_equiv`（第 (4) 项）—— 论文 `lem:H2-Z` 的精确形。
    §6  `threeKillsH_via_equiv`（第 (5) 项）—— 由新同构重推 S2 弱化形
        `threeKills_coh2` 的同一结论。**检验力说明（2026-10-09 审查修正）**：
        §6 末的 `rfl` 例只是「同一命题的陈述恒等」见证（Lean 定义性证明
        无关性使同命题任意两证明 `rfl` 相等，**内容层零判别力**）；
        真正的取向/标定检验在 §8 的**值层锚**（1 ↦ 1/3、2 ↦ 2/3、
        非退化、端到端无串扰——均已配负对照证其判别力）。

  纪律：无 sorry（无占位）、无自造公理、不改任何既有文件；
  全部新声明过 `#print axioms`，均为标准三公理
  [propext, Classical.choice, Quot.sound] 的**子集**
  （16 条恰三／5 条 [propext, Quot.sound]／4 条 [propext]）。
-/
import ABGV52.S2_ABGV52
import ABGV52.Hyp_ABGV52

open CategoryTheory

namespace ABGV52

attribute [local instance 1500] Rep.hV2

set_option maxHeartbeats 400000

/-! ## 1. 记号契约（沿用 S2）

* `TZ K` —— 平凡 `ℤ[K]`-模（载体 `ℤ`），`coh²(K, ℤ)` 的系数；
* `QZ`  —— `ℚ ⧸ zmultiples 1`（即 `ℚ/ℤ`）；
* `TQD K` —— 平凡 `ℤ[K]`-模（载体 `QZ`）；
* `H = C₃ × C₃`（`Hyp_ABGV52.lean`）。
-/

/-! ## 2. 第 (1) 项：`H²(K, ℤ) ≃ₗ Hom(K, ℚ/ℤ)`（纯装配） -/

/-- H²(K, ℤ) ≃ₗ[ℤ] Hom(K, ℚ/ℤ)：长正合列 δ 桥取逆，接 Shapiro。 -/
noncomputable def coh2_iso_homQZ (K : Type) [Group K] [Fintype K] :
    ↥(groupCohomology (TZ K) 2) ≃ₗ[ℤ] (Additive K →+ TQD K) :=
  (coh1QZ_iso_coh2Z K).symm.toLinearEquiv.trans
    (groupCohomology.H1IsoOfIsTrivial (TQD K)).toLinearEquiv

#print axioms coh2_iso_homQZ

/-! ## 3. 第 (2) 项：`ℚ/ℤ` 的 3-挠子群 ≃ `ZMod 3`（新数学） -/

/-- `M` 的 3-挠子群 `{m | 3 • m = 0}`。 -/
def torsion3Sub (M : Type*) [AddCommGroup M] : AddSubgroup M where
  carrier := {m : M | (3 : ℤ) • m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show (3 : ℤ) • (a + b) = 0
    rw [zsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    show (3 : ℤ) • (-a) = 0
    rw [zsmul_neg, ha, neg_zero]

/-- 成员资格即挠条件（字面同一命题，供类型精确匹配）。 -/
lemma torsion3Sub_mem_iff (M : Type*) [AddCommGroup M] (m : M) :
    m ∈ torsion3Sub M ↔ (3 : ℤ) • m = 0 :=
  ⟨fun h => h, fun h => h⟩

/-- `ZMod 3` 中 `3 • k = 0`。 -/
lemma zmod3_zsmul_three (k : ZMod 3) : (3 : ℤ) • k = 0 := by
  rw [zsmul_eq_mul,
    show ((3 : ℤ) : ZMod 3) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr (dvd_refl 3),
    zero_mul]

/-- `q ↦ q/3`（作为 `ℚ →+ ℚ`）。 -/
noncomputable def divThreeHom : ℚ →+ ℚ :=
  AddMonoidHom.mk' (fun q : ℚ => q / 3) (by intro a b; rw [add_div])

/-- `ℤ → ℚ/ℤ`，`n ↦ n/3 mod 1`。 -/
noncomputable def f3 : ℤ →+ QZ :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
    (divThreeHom.comp (Int.castAddHom ℚ))

lemma f3_three : f3 3 = 0 := by
  have h : (((3 : ℤ)) : ℚ) / 3 = ((1 : ℤ) : ℚ) := by norm_num
  show (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) (((3 : ℤ) : ℚ) / 3) : QZ) = 0
  rw [show (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) (((3 : ℤ) : ℚ) / 3) : QZ)
      = QuotientAddGroup.mk ((((3 : ℤ)) : ℚ) / 3) from rfl, h]
  exact (mk_intCast_eq_zero 1).trans
    (map_zero (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))))

/-- `ZMod 3 →+ ℚ/ℤ`，`1 ↦ 1/3`（经 `ZMod.lift`）。 -/
noncomputable def iota3 : ZMod 3 →+ QZ := ZMod.lift 3 ⟨f3, f3_three⟩

lemma iota3_injective : Function.Injective iota3 := by
  show Function.Injective (ZMod.lift 3 ⟨f3, f3_three⟩)
  rw [ZMod.lift_injective]
  intro m hm
  have hm' : (QuotientAddGroup.mk ((m : ℚ) / 3) : QZ) = 0 := hm
  obtain ⟨n, hn⟩ := (mem_zmultiples_one_iff _).mp ((mk_eq_zero_iff _).mp hm')
  have hmul : (3 : ℤ) * n = m := by
    have hQ : (3 : ℚ) * (n : ℚ) = (m : ℚ) := by
      rw [hn]
      ring
    exact_mod_cast hQ
  have hdvd : (3 : ℤ) ∣ m := ⟨n, hmul.symm⟩
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma iota3_surjective : ∀ q : ↥(torsion3Sub QZ), ∃ k : ZMod 3, iota3 k = q := by
  intro q
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (q : QZ)
  have h3r : (QuotientAddGroup.mk ((3 : ℤ) • r) : QZ) = 0 := by
    rw [QuotientAddGroup.mk_zsmul]
    show (3 : ℤ) • (QuotientAddGroup.mk r : QZ) = 0
    rw [hr]
    exact q.2
  obtain ⟨n, hn⟩ := (mem_zmultiples_one_iff _).mp ((mk_eq_zero_iff _).mp h3r)
  refine ⟨(n : ZMod 3), ?_⟩
  show iota3 ((n : ℤ) : ZMod 3) = (q : QZ)
  have h1 : iota3 ((n : ℤ) : ZMod 3) = QuotientAddGroup.mk ((n : ℚ) / 3) := by
    show ZMod.lift 3 ⟨f3, f3_three⟩ ((n : ℤ) : ZMod 3) = QuotientAddGroup.mk ((n : ℚ) / 3)
    rw [ZMod.lift_coe]
    rfl
  have h2 : (q : QZ) = QuotientAddGroup.mk ((n : ℚ) / 3) := by
    rw [← hr]
    have hr' : r = (n : ℚ) / 3 := by
      have hz : (3 : ℤ) • r = (3 : ℚ) * r := by
        rw [zsmul_eq_mul]
        norm_num
      have hQ : (3 : ℚ) * r = (n : ℚ) := by rw [← hz, ← hn]
      rw [← hQ, eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
      ring
    rw [hr']
  rw [h1]
  exact h2.symm

/-- 第 (2) 项：`(ℚ/ℤ)[3] ≃+ ZMod 3`（`iota3` 的双射装成加法等价，取逆）。 -/
noncomputable def torsion3_equiv : ↥(torsion3Sub QZ) ≃+ ZMod 3 := by
  have hmem : ∀ k : ZMod 3, iota3 k ∈ torsion3Sub QZ := fun k => by
    show (3 : ℤ) • iota3 k = 0
    rw [← map_zsmul iota3 (3 : ℤ) k, zmod3_zsmul_three k, map_zero]
  let F : ZMod 3 →+ ↥(torsion3Sub QZ) :=
    AddMonoidHom.codRestrict iota3 (torsion3Sub QZ) hmem
  have hF : Function.Bijective F :=
    ⟨(AddMonoidHom.injective_codRestrict iota3 (torsion3Sub QZ) hmem).mpr iota3_injective,
      fun q => by
        obtain ⟨k, hk⟩ := iota3_surjective q
        exact ⟨k, Subtype.ext hk⟩⟩
  exact (AddEquiv.ofBijective F hF).symm

/-- 字面载体 `{q : QZ // 3 • q = 0}` 与 `↥(torsion3Sub QZ)` 类型字面等
（defeq 见证；字面形无自适应 `Add` 实例，故一律用右式）。 -/
example : ({q : QZ // (3 : ℤ) • q = 0} : Type) = ↥(torsion3Sub QZ) := rfl

#print axioms torsion3_equiv

/-! ## 4. 第 (3) 项：`Hom(H, ℚ/ℤ) ≃ₗ ZMod 3 × ZMod 3` -/

/-- `TQD H` 的载体与 `QZ` 一致（defeq 见证）。 -/
example : ↥(torsion3Sub (TQD H)) = ↥(torsion3Sub QZ) := rfl

/-- 挠等价搬到 `TQD H`（经上述 defeq）。 -/
noncomputable def torsion3_equiv_TQD : ↥(torsion3Sub (TQD H)) ≃+ ZMod 3 :=
  torsion3_equiv

#print axioms torsion3_equiv_TQD

/-- `Additive (C₃ × C₃) ≃+ ZMod 3 × ZMod 3`（逐分量 toAdd）。 -/
noncomputable def additiveH_equiv : Additive H ≃+ (ZMod 3 × ZMod 3) where
  toFun x := (x.toMul.1.toAdd, x.toMul.2.toAdd)
  invFun p := Additive.ofMul (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2)
  left_inv x := by
    apply Additive.ext
    simp
  right_inv p := by
    obtain ⟨a, b⟩ := p
    simp
  map_add' x y := rfl

/-- 沿定义域同构搬运 Hom 型：`(G' →+ M) ≃+ (G →+ M)`。 -/
noncomputable def precompAddEquiv {G G' M : Type*} [AddCommGroup G] [AddCommGroup G']
    [AddCommGroup M] (e : G ≃+ G') : (G' →+ M) ≃+ (G →+ M) where
  toFun φ := φ.comp e.toAddMonoidHom
  invFun ψ := ψ.comp e.symm.toAddMonoidHom
  left_inv φ := by ext x; simp
  right_inv ψ := by ext x; simp
  map_add' φ ψ := by ext x; simp

/-- `(M1 × M2) →+ P ≃+ (M1 →+ P) × (M2 →+ P)`（逐分量）。 -/
noncomputable def prodHomEquiv (M1 M2 P : Type*) [AddCommGroup M1] [AddCommGroup M2]
    [AddCommGroup P] : ((M1 × M2) →+ P) ≃+ ((M1 →+ P) × (M2 →+ P)) where
  toFun φ := (φ.comp (AddMonoidHom.inl M1 M2), φ.comp (AddMonoidHom.inr M1 M2))
  invFun fg := (fg.1.comp (AddMonoidHom.fst M1 M2)) + (fg.2.comp (AddMonoidHom.snd M1 M2))
  left_inv φ := by
    ext p
    obtain ⟨a, b⟩ := p
    show φ (AddMonoidHom.inl M1 M2 a) + φ (AddMonoidHom.inr M1 M2 b) = φ (a, b)
    rw [← map_add]
    congr 1
    show (a, 0) + (0, b) = (a, b)
    simp
  right_inv fg := by
    obtain ⟨f, g⟩ := fg
    apply Prod.ext
    · ext x
      simp
    · ext y
      simp
  map_add' φ ψ := by
    apply Prod.ext <;> ext x <;> simp

/-- `n ↦ n • m`，作为 `ℤ →+ M`。 -/
noncomputable def zsmulHom (M : Type*) [AddCommGroup M] (m : M) : ℤ →+ M :=
  AddMonoidHom.mk' (fun n : ℤ => n • m) (fun a b => add_zsmul m a b)

lemma zsmulHom_three (M : Type*) [AddCommGroup M] (m : M) (hm : (3 : ℤ) • m = 0) :
    zsmulHom M m 3 = 0 :=
  hm

/-- 挠元素 `m` 给出的同态 `ZMod 3 →+ M`（`k ↦ k • m`）。 -/
noncomputable def torsionToHom (M : Type*) [AddCommGroup M]
    (m : ↥(torsion3Sub M)) : ZMod 3 →+ M :=
  ZMod.lift 3 ⟨zsmulHom M m.1, zsmulHom_three M m.1 ((torsion3Sub_mem_iff M m.1).mp m.2)⟩

lemma torsionToHom_coe (M : Type*) [AddCommGroup M] (m : ↥(torsion3Sub M)) (n : ℤ) :
    torsionToHom M m ((n : ℤ) : ZMod 3) = n • m.1 := by
  show ZMod.lift 3 ⟨zsmulHom M m.1, zsmulHom_three M m.1 ((torsion3Sub_mem_iff M m.1).mp m.2)⟩
      ((n : ℤ) : ZMod 3) = n • m.1
  rw [ZMod.lift_coe]
  rfl

/-- `(ZMod 3 →+ M) ≃+ M[3]`（在 `1` 处取值）。 -/
noncomputable def zmod3HomTorsion (M : Type*) [AddCommGroup M] :
    (ZMod 3 →+ M) ≃+ ↥(torsion3Sub M) where
  toFun φ := ⟨φ 1, (torsion3Sub_mem_iff M (φ 1)).mpr (by
    show (3 : ℤ) • φ 1 = 0
    rw [← map_zsmul φ (3 : ℤ) (1 : ZMod 3), zmod3_zsmul_three 1, map_zero])⟩
  invFun := torsionToHom M
  left_inv φ := by
    ext k
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective k
    rw [torsionToHom_coe]
    show n • φ (1 : ZMod 3) = φ ((n : ℤ) : ZMod 3)
    rw [← map_zsmul φ n (1 : ZMod 3)]
    exact congrArg φ (zsmul_one n)
  right_inv m := by
    apply Subtype.ext
    change (torsionToHom M m) (1 : ZMod 3) = m.1
    rw [← (Int.cast_one : (((1 : ℤ) : ZMod 3)) = 1)]
    rw [torsionToHom_coe]
    rw [one_zsmul]
  map_add' φ ψ := by
    apply Subtype.ext
    show (φ + ψ) 1 = φ 1 + ψ 1
    rfl

/-- 第 (3) 项：Hom(H, ℚ/ℤ) ≃ₗ[ℤ] ZMod 3 × ZMod 3。 -/
noncomputable def homQZ_equiv : (Additive H →+ TQD H) ≃ₗ[ℤ] (ZMod 3 × ZMod 3) :=
  (((precompAddEquiv (M := TQD H) additiveH_equiv).symm).trans
    ((prodHomEquiv (ZMod 3) (ZMod 3) (TQD H)).trans
      (((zmod3HomTorsion (TQD H)).prodCongr (zmod3HomTorsion (TQD H))).trans
        ((torsion3_equiv_TQD).prodCongr (torsion3_equiv_TQD))))).toIntLinearEquiv

#print axioms additiveH_equiv
#print axioms precompAddEquiv
#print axioms prodHomEquiv
#print axioms zmod3HomTorsion
#print axioms homQZ_equiv

/-! ## 5. 第 (4) 项：论文 `lem:H2-Z` 精确形

论文（`raw/ABGV-5.2-resolution.tex:1126`，label `lem:H2-Z`）：

  With the trivial H-action on ℤ, coh²(H, ℤ) ≅ C₃ × C₃.

其中 `C₃ × C₃` 记作乘法群 `H`；系数模为加法 `ZMod 3 × ZMod 3`。
-/

/-- 论文 `lem:H2-Z`：H²(H, ℤ) ≃ₗ[ℤ] ZMod 3 × ZMod 3。 -/
noncomputable def H2_Z_equiv : ↥(groupCohomology (TZ H) 2) ≃ₗ[ℤ] (ZMod 3 × ZMod 3) :=
  (coh2_iso_homQZ H).trans homQZ_equiv

#print axioms H2_Z_equiv
#print H2_Z_equiv

/-! ## 6. 第 (5) 项：由新同构重推 S2 弱化形

由新同构 `H2_Z_equiv` 重推 S2 弱化形 `threeKills_coh2` 的同一
结论（"3 消没"）；`ZMod 3 × ZMod 3` 上该结论逐分量显然。
**检验力说明（2026-10-09 审查修正）**：§6 末 `rfl` 例 = 陈述恒等
见证（定义性证明无关性 ⟹ 同命题任意两证明 `rfl` 相等；实测：S2
旧路证明（早于本件 9 日、结构上不可能引用 `H2_Z_equiv`）同样 `rfl`
通过 ⟹ 该例内容层零判别力）。真正的取向/标定检验在 **§8 值层锚**。
辅助事实 `C₃^3 = 1` 与 `H^3 = 1` 一并交付。
-/

lemma C3_pow_three (a : C3) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  show (3 : ℕ) • Multiplicative.toAdd a = 0
  rw [nsmul_eq_mul,
    show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3,
    zero_mul]

lemma H_pow_three (x : H) : x ^ 3 = 1 := by
  obtain ⟨a, b⟩ := x
  exact Prod.ext (C3_pow_three a) (C3_pow_three b)

theorem threeKillsH_via_equiv : ∀ x : cohOf H (TZ H) 2, (3 : ℤ) • x = 0 :=
  smul_three_eq_zero_of_linearEquiv' H2_Z_equiv (fun y => by
    obtain ⟨a, b⟩ := y
    show ((3 : ℤ) • a, (3 : ℤ) • b) = (0, 0)
    rw [zmod3_zsmul_three a, zmod3_zsmul_three b])

-- 与 S2 弱化形同一结论（同一命题，故项级 defeq = **陈述恒等见证**；
-- 内容层零判别力——审查 2026-10-09 实测：S2 旧路证明同样 rfl 通过；
-- 实质检验在 §8 值层锚）：
example : threeKillsH_via_equiv = threeKills_coh2 H H_pow_three := rfl

#print axioms C3_pow_three
#print axioms H_pow_three
#print axioms threeKillsH_via_equiv

/-! ## 7. 全声明公理闸门（余下声明的 `#print axioms`） -/

#print axioms torsion3Sub
#print axioms torsion3Sub_mem_iff
#print axioms zmod3_zsmul_three
#print axioms divThreeHom
#print axioms f3
#print axioms f3_three
#print axioms iota3
#print axioms iota3_injective
#print axioms iota3_surjective
#print axioms zsmulHom
#print axioms zsmulHom_three
#print axioms torsionToHom
#print axioms torsionToHom_coe

/-! ## 8. 值层锚（2026-10-09 审查修正并入；判别力负对照见
`ProbeS2bR2.lean` 之 N3：错标定 2/3 时 A6/B1 型 `rfl` 失败）

以下把「新同构非退化且标定正确」变成可机验事实：
A1–A3 = `iota3` 在 1/2/3 上的取值；A5 = 非平凡配对 1/3+2/3=0；
D1 = 非退化（iota3 ≠ 0）；B1/B2 = 端到端（`homQZ_equiv.symm (1,0)`
在两个生成元上的取值：1/3 与 0，无串扰）。 -/

/-- A1：1 ↦ 1/3（值层，非仅类型层）。 -/
example : iota3 ((1 : ℤ) : ZMod 3) = QuotientAddGroup.mk ((1 : ℚ) / 3) := by
  show ZMod.lift 3 ⟨f3, f3_three⟩ ((1 : ℤ) : ZMod 3) = QuotientAddGroup.mk ((1 : ℚ) / 3)
  rw [ZMod.lift_coe]
  rfl

/-- A2：2 ↦ 2/3。 -/
example : iota3 ((2 : ℤ) : ZMod 3) = QuotientAddGroup.mk ((2 : ℚ) / 3) := by
  show ZMod.lift 3 ⟨f3, f3_three⟩ ((2 : ℤ) : ZMod 3) = QuotientAddGroup.mk ((2 : ℚ) / 3)
  rw [ZMod.lift_coe]
  rfl

/-- A3：3 ↦ 0（3 = 0 mod 3）。 -/
example : iota3 ((3 : ℤ) : ZMod 3) = 0 := by
  rw [show ((3 : ℤ) : ZMod 3) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr (dvd_refl 3)]
  exact map_zero iota3

/-- A5：1/3 + 2/3 = 0（2 ↦ −1：非平凡配对）。 -/
example : iota3 ((2 : ℤ) : ZMod 3) + iota3 ((1 : ℤ) : ZMod 3) = 0 := by
  rw [← map_add]
  have h : ((2 : ℤ) : ZMod 3) + ((1 : ℤ) : ZMod 3) = 0 := by
    rw [← Int.cast_add]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr (dvd_refl 3)
  rw [h, map_zero]

/-- D1：1 ↦ 1/3 ≠ 0（构造非退化，非零同态）。 -/
example : iota3 ((1 : ℤ) : ZMod 3) ≠ 0 := by
  intro h
  have h1 : ((1 : ℤ) : ZMod 3) = 0 := iota3_injective (by rw [h, map_zero])
  exact absurd h1 (by decide)

/-- B1：`homQZ_equiv.symm (1,0)` 把第一个生成元送到 1/3（端到端标定）。 -/
example : (homQZ_equiv.symm (1, 0))
      (Additive.ofMul (Multiplicative.ofAdd (1 : ZMod 3), 1))
    = QuotientAddGroup.mk ((1 : ℚ) / 3) := by
  show (((torsionToHom (TQD H) (torsion3_equiv_TQD.symm (1 : ZMod 3))).comp
        (AddMonoidHom.fst (ZMod 3) (ZMod 3))
      + (torsionToHom (TQD H) (torsion3_equiv_TQD.symm (0 : ZMod 3))).comp
        (AddMonoidHom.snd (ZMod 3) (ZMod 3)))
      (additiveH_equiv (Additive.ofMul (Multiplicative.ofAdd (1 : ZMod 3), 1))))
    = QuotientAddGroup.mk ((1 : ℚ) / 3)
  rw [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  show torsionToHom (TQD H) (torsion3_equiv_TQD.symm (1 : ZMod 3)) (1 : ZMod 3)
      + torsionToHom (TQD H) (torsion3_equiv_TQD.symm (0 : ZMod 3)) (0 : ZMod 3)
    = QuotientAddGroup.mk ((1 : ℚ) / 3)
  rw [map_zero, add_zero]
  rw [← (Int.cast_one : (((1 : ℤ) : ZMod 3)) = 1), torsionToHom_coe, one_zsmul]
  show (torsion3_equiv_TQD.symm (1 : ZMod 3) : QZ) = QuotientAddGroup.mk ((1 : ℚ) / 3)
  change iota3 ((1 : ℤ) : ZMod 3) = QuotientAddGroup.mk ((1 : ℚ) / 3)
  show ZMod.lift 3 ⟨f3, f3_three⟩ ((1 : ℤ) : ZMod 3) = QuotientAddGroup.mk ((1 : ℚ) / 3)
  rw [ZMod.lift_coe]
  rfl

/-- B2：同上，第二个生成元送到 0（无串扰）。 -/
example : (homQZ_equiv.symm (1, 0))
      (Additive.ofMul (1, Multiplicative.ofAdd (1 : ZMod 3)))
    = 0 := by
  show (((torsionToHom (TQD H) (torsion3_equiv_TQD.symm (1 : ZMod 3))).comp
        (AddMonoidHom.fst (ZMod 3) (ZMod 3))
      + (torsionToHom (TQD H) (torsion3_equiv_TQD.symm (0 : ZMod 3))).comp
        (AddMonoidHom.snd (ZMod 3) (ZMod 3)))
      (additiveH_equiv (Additive.ofMul (1, Multiplicative.ofAdd (1 : ZMod 3)))))
    = 0
  rw [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  show torsionToHom (TQD H) (torsion3_equiv_TQD.symm (1 : ZMod 3)) (0 : ZMod 3)
      + torsionToHom (TQD H) (torsion3_equiv_TQD.symm (0 : ZMod 3)) (1 : ZMod 3)
    = 0
  rw [map_zero, zero_add]
  rw [← (Int.cast_one : (((1 : ℤ) : ZMod 3)) = 1), torsionToHom_coe, one_zsmul]
  show (torsion3_equiv_TQD.symm (0 : ZMod 3) : QZ) = 0
  change iota3 ((0 : ℤ) : ZMod 3) = 0
  show ZMod.lift 3 ⟨f3, f3_three⟩ ((0 : ℤ) : ZMod 3) = 0
  rw [ZMod.lift_coe]
  exact map_zero f3

end ABGV52

