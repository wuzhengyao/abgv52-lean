/-
  ABGV-5.2 —— **本体形式化 B · T2（可证桥层）：rational ⟹ retract rational**

  蓝图（`wiki/proj-ABGV52-formalize-saltman.md` §3.3 T2，逐字）：
  「`lemma rational_isRetractRational`：有理扩张（\(K\cong \mathrm{RatFunc}\) 型或直接取
   \(S=F[x_1..x_n]\)、\(w=1\)、\(\phi=\psi=\mathrm{id}\)）⟹ `IsRetractRational F K`；
   ＋ `RatFunc F` 实例探针（测定义不卡死）。」

  本件内容（三层，由内到外）
  ==========================
  1. **核心见证**（蓝图原话「直接取 `S = F[x₁..xₙ]`、`w = 1`」）：
     `isRetractRational_rationalFunctionField` —— `F(t₁,…,tₙ)` retract rational。
     见证：`S := MvPolynomial (Fin n) F`（`K := FractionRing S`），`w := 1`；
     φ = 结构映射进入 `Localization.Away 1`，ψ = 沿 `AlgHom.id` 的
     `IsLocalization.Away.liftAlgHom`（`1` 是单位 ⟹ 可下降；`w = 1` 局部化不做事），
     复合为恒等（`lift_eq` 落在恒等上）。
  2. **搬运引理**：`IsRetractRational.of_algEquiv` —— retract rationality 沿
     `K ≃ₐ[F] L` 搬运（def3.1 的 `S` 本可任取；沿 `e.symm` 把 `S`-代数结构从 `L`
     借到 `K`，`IsFractionRing` 随同一同构搬运）。此引理使 `D1_ABGV52` 的
     `EM.IsRational`（定义在 `≃ₐ` 上）与具体见证对接。
  3. **桥与探针**：
     * `isRetractRational_of_isRational`（蓝图拟名 `rational_isRetractRational`）
       —— `EM.IsRational F K ⟹ IsRetractRational F K`；
     * `isRetractRational_self'` —— 端到端探针：`F/F` 由本桥 ＋ `EM.isRational_self`
       二次导出（与 M1 的直证 `isRetractRational_self` 互为对照）；
     * `isRetractRational_ratFunc` —— `RatFunc F` 实例探针：取**第三种** `S`
       （`S := Polynomial F`，不是多项式环本身），经 `MvPolynomial.uniqueAlgEquiv`
       与 `MvPolynomial (Fin 1) F` 对接，测定义不卡死。

  数学定位（诚实登记，L8① 口径）
  ==============================
  * 本件 = 蓝图 §0.3 **第 2 层（可证桥层）**的第一块真定理：把「有理 ⟹ retract
    rational」在库内变成**无条件定理**（`IsRetractRational` 的第一个非平凡实例，
    超出 M1 的 `K = F` 探针）。它是后续 S-a 线（Fischer：`F ∋ ζ_e` ⟹ 纯超越）
    在库内的落点接口。
  * **不构成** Saltman cor3.13 任何部分的证明：一般 `F` 的 cor3.13 仍须 [23]（M5），
    本件只把**结论谓词**一侧（`RRet` 槽）具体化为库内可证对象，不含 `A`-作用、
    不含忠实性、不含 Fischer 定理、不含 §1 范畴语言（M4）。

  **无 sorry、无自造公理**。
-/
import ABGV52.SaltDef_ABGV52
import ABGV52.D1_ABGV52
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.RatFunc.Basic

universe u

namespace ABGV52

/-! ## 1. 核心见证：有理函数域 retract rational（S = F[x₁,…,xₙ]，w = 1） -/

/-- **T2 核心见证**：`n` 元有理函数域 `F(t₁,…,tₙ)` 在 `F` 上 retract rational。

见证（Saltman def3.1，`S` 取多项式环本身）：`S := MvPolynomial (Fin n) F`，
`K := FractionRing S = F(t₁,…,tₙ)`（`IsFractionRing` 实例）；`w := 1`
（局部化不做事），φ := 结构映射 `S →ₐ[F] S(1/1)`，ψ := 沿 `AlgHom.id F S` 的
`IsLocalization.Away.liftAlgHom`，复合由 `IsLocalization.Away.lift_eq` 落在恒等上。 -/
theorem isRetractRational_rationalFunctionField (F : Type u) [Field F] (n : ℕ) :
    IsRetractRational F (EM.rationalFunctionField F n) := by
  have hg : IsUnit ((AlgHom.id F (MvPolynomial (Fin n) F))
      (1 : MvPolynomial (Fin n) F)) := by
    rw [map_one]
    exact isUnit_one
  refine IsRetractRational.mk' F (EM.rationalFunctionField F n) (MvPolynomial (Fin n) F)
    n 1 one_ne_zero
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
      (Localization.Away (1 : MvPolynomial (Fin n) F)))
    (IsLocalization.Away.liftAlgHom (x := (1 : MvPolynomial (Fin n) F))
      (f := AlgHom.id F (MvPolynomial (Fin n) F)) hg) ?_
  refine AlgHom.ext fun s => ?_
  show IsLocalization.Away.liftAlgHom (x := (1 : MvPolynomial (Fin n) F))
      (f := AlgHom.id F (MvPolynomial (Fin n) F)) hg
      (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
        (Localization.Away (1 : MvPolynomial (Fin n) F)) s) = s
  rw [IsLocalization.Away.liftAlgHom_apply, IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.lift_eq (x := (1 : MvPolynomial (Fin n) F)) hg s]
  rfl

/-! ## 2. 搬运引理：retract rationality 沿 `≃ₐ` 不变 -/

/-- **沿 `F`-代数同构搬运 retract rationality**：`L/F` retract rational 且
`e : K ≃ₐ[F] L` ⟹ `K/F` retract rational。

构造：取 `h` 的整环 `S`（`IsFractionRing S L`）；把 `S` 在 `K` 上的代数结构经
`e.symm` 从 `L` 借来——记 `f : S →ₐ[F] K` 为 `S → L → K` 的复合（`f` 是
唯一的新数据），置 `Algebra S K := f.toRingHom.toAlgebra`（`RingHom.toAlgebra`）。
`IsScalarTower F S K` 由 `f.commutes` 经 `IsScalarTower.of_algebraMap_eq` 得出；
`IsFractionRing S K` 经 `IsFractionRing.of_algEquiv` 沿 `L ≃ₐ[S] K` 搬运；
φ、ψ 与复合等式**原样复用**（其类型不涉及 `K`）。

用途：`EM.IsRational F K` 定义在 `K ≃ₐ[F] F(t₁,…,tₙ)` 上，本条把它与 §1 的具体
见证对接（§3 的桥即一步应用）。 -/
theorem IsRetractRational.of_algEquiv {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] (e : K ≃ₐ[F] L) (h : IsRetractRational F L) :
    IsRetractRational F K := by
  obtain ⟨S, hCR, hDom, hAFS, hASL, hTSL, hFracL, n, w, hw, φ, ψ, hcomp⟩ := h
  -- 局部实例（`let`/`have` 即可：本定理目标为命题，风格 lint 偏好
  -- 非 `letI`；本地定义同样参与实例解析与 defeq）
  let : CommRing S := hCR
  let : IsDomain S := hDom
  let : Algebra F S := hAFS
  let : Algebra S L := hASL
  let : IsScalarTower F S L := hTSL
  let : IsFractionRing S L := hFracL
  -- `K` 上的 `S`-代数结构：经 `e.symm` 从 `L` 借来
  let f : S →ₐ[F] K := (e.symm : L ≃ₐ[F] K).toAlgHom.comp (IsScalarTower.toAlgHom F S L)
  let : Algebra S K := f.toRingHom.toAlgebra
  have hTSK : IsScalarTower F S K :=
    IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hFracK : IsFractionRing S K := by
    let eS : L ≃ₐ[S] K :=
      { toFun := ⇑e.symm
        invFun := ⇑e
        left_inv := fun x => e.apply_symm_apply x
        right_inv := fun x => e.symm_apply_apply x
        map_mul' := fun x y => e.symm.map_mul' x y
        map_add' := fun x y => e.symm.map_add' x y
        commutes' := fun s => rfl }
    exact IsFractionRing.of_algEquiv eS
  exact ⟨S, hCR, hDom, hAFS, inferInstance, inferInstance, inferInstance,
    n, w, hw, φ, ψ, hcomp⟩

/-! ## 3. 桥：`EM.IsRational` ⟹ `IsRetractRational` -/

/-- **T2 桥**（蓝图拟名 `rational_isRetractRational`）：`K/F` **有理**
（`EM.IsRational`：`K ≃ₐ[F] F(t₁,…,tₙ)` 非空）⟹ `K/F` **retract rational**。
证明 = §1 核心见证 ＋ §2 搬运（一步）。 -/
theorem isRetractRational_of_isRational {F K : Type u} [Field F] [Field K] [Algebra F K]
    (h : EM.IsRational F K) : IsRetractRational F K := by
  obtain ⟨n, ⟨e⟩⟩ := h
  exact (isRetractRational_rationalFunctionField F n).of_algEquiv e

/-- **端到端探针（L1）**：`F` 自身 retract rational——由本桥（`EM.isRational_self`
＋ §2 搬运，走 `F ≃ₐ[F] F(t₁,…,t₀)`）**二次导出**，与 M1 的直证
`isRetractRational_self`（SaltDef）互为对照：两条独立路径得到同一实例。 -/
theorem isRetractRational_self' (F : Type u) [Field F] : IsRetractRational F F :=
  isRetractRational_of_isRational (EM.isRational_self F)

/-! ## 4. `RatFunc F` 实例探针（测定义不卡死） -/

/-- **`RatFunc F` 实例探针**（蓝图 T2 第二项）：`F⟮X⟯`（`F` 上一元有理函数域）
retract rational。

与 §1 的差别（本探针的着力点）：见证取**第三种** `S`——`S := Polynomial F`
（不是多项式环 `MvPolynomial (Fin n) F` 本身），故先经
`MvPolynomial.uniqueAlgEquiv (R := F) (σ := Fin 1) : MvPolynomial (Fin 1) F ≃ₐ[F] F[X]`
把两端对接（φ 侧先过该同构再进 `Localization.Away 1`，ψ 侧先下降再过其逆）；
`IsFractionRing (Polynomial F) (RatFunc F)` 为 mathlib 现成实例。
这同时检验：def3.1 的 ∃ 不对 `S` 的类型做任何限制（只要 K 是其分式域）。 -/
theorem isRetractRational_ratFunc (F : Type u) [Field F] :
    IsRetractRational F (RatFunc F) := by
  let e : Polynomial F ≃ₐ[F] MvPolynomial (Fin 1) F :=
    (MvPolynomial.uniqueAlgEquiv (R := F) (σ := Fin 1)).symm
  have hg : IsUnit ((AlgHom.id F (MvPolynomial (Fin 1) F))
      (1 : MvPolynomial (Fin 1) F)) := by
    rw [map_one]
    exact isUnit_one
  refine IsRetractRational.mk' F (RatFunc F) (Polynomial F) 1 1 one_ne_zero
    ((IsScalarTower.toAlgHom F (MvPolynomial (Fin 1) F)
      (Localization.Away (1 : MvPolynomial (Fin 1) F))).comp e.toAlgHom)
    (e.symm.toAlgHom.comp (IsLocalization.Away.liftAlgHom
      (x := (1 : MvPolynomial (Fin 1) F))
      (f := AlgHom.id F (MvPolynomial (Fin 1) F)) hg)) ?_
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply]
  show e.symm (IsLocalization.Away.liftAlgHom (x := (1 : MvPolynomial (Fin 1) F))
      (f := AlgHom.id F (MvPolynomial (Fin 1) F)) hg
      (IsScalarTower.toAlgHom F (MvPolynomial (Fin 1) F)
        (Localization.Away (1 : MvPolynomial (Fin 1) F)) (e x))) = x
  rw [IsScalarTower.toAlgHom_apply, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (x := (1 : MvPolynomial (Fin 1) F)) hg (e x)]
  exact e.symm_apply_apply x

/-! ## 5. 公理闸门 -/

#print axioms isRetractRational_rationalFunctionField
#print axioms IsRetractRational.of_algEquiv
#print axioms isRetractRational_of_isRational
#print axioms isRetractRational_self'
#print axioms isRetractRational_ratFunc

end ABGV52
