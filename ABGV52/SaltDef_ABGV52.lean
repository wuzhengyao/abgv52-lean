/-
  ABGV-5.2 —— **本体形式化 B · M1（定义层）**：Saltman 1984 def3.1／def3.2

  目标（蓝图 `wiki/proj-ABGV52-formalize-saltman.md` §3.3 T1）：把既有 `SaltmanHyp`
  接口（`Saltman_ABGV52.lean`，整条定理压成单槽）拆出**第一层**——把 `RRet` 从
  「抽象入参」变成**库内可定义的对象**。

  源（逐字，raw/Saltman1984.tex；印刷页 = PDF 页 + 164）：

    def3.1（印 180）："Let \(K\supseteq F\) be fields. \(K/F\) is called retract
      rational if and only if \(K\) is the quotient field of an \(F\) algebra
      domain \(S\subseteq K\), such that there are \(F\) algebra maps
      \(\phi: S\to F[x_1,\dots,x_n](1/w)\) and
      \(\psi: F[x_1,\dots,x_n](1/w)\to S\), where \(F[x_1,\dots,x_n](1/w)\) is a
      localized polynomial ring and \(\psi\circ\phi\) is the identity on \(S\)."

    def3.2（印 181）："Let \(S,R\) be \(F\) algebra domains and let \(\phi: S\to R\)
      be an \(F\) algebra map. We say \(\phi\) factors rationally if and only if
      there is a localized polynomial ring \(F[x_1,\dots,x_n](1/w)\), a
      \(0\neq r\in R\), and \(F\) algebra maps \(\psi: S\to F[x_1,\dots,x_n](1/w)\)
      and \(\eta: F[x_1,\dots,x_n](1/w)\to R(1/r)\) such that \(\phi = \eta\circ\psi\)."

  形式化约定（与逐字的偏差，均显式登记）
  =====================================
  * "\(S\subseteq K\) 且 K 为 S 的分式域" 形式化为**抽象 S**：
    `Algebra S K` ＋ `IsFractionRing S K`（K 为域 ⟹ 结构映射单 ⟹ 与 S ⊆ K 的
    子环表述同义，避免子环强制转换的开销）。
  * 源未明写「\(w\neq 0\)」；但局部化 \(F[x](1/w)\) 欲为**非退化环**须 \(w\neq 0\)
    （`Submonoid.powers 0` 含 0 ⟹ 零环），且源语境明言 "localized polynomial
    ring"（= 整环）。故显式加 `w ≠ 0` 并在此登记（**加性收紧，不是放宽**）。
  * def3.2 的等式 "\(\phi = \eta\circ\psi\)"：两侧落点不同（R 与 R(1/r)），形式化为
    逐点 `algebraMap R (Localization.Away r) (φ s) = η (ψ s)`。
  * **定义外形锁定**（阶段 5.5 第 5 条变体）：以**构造子** `IsRetractRational.mk'`
    锁定 ∃-链形状——定义外形一旦改动，`mk'` 的 `⟨…⟩` 立即编译失败
    （比整体重打 `rfl` 更稳，且供后续里程碑复用）。

  **无 sorry、无自造公理**。
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Hom

universe u

namespace ABGV52

/-! ## 1. 定义层（Saltman def3.1／def3.2） -/

/-- **Saltman def3.1（retract rational，逐字对应）**：
`K/F`（域扩张）retract rational ⟺ 存在 F-代数整环 `S`（`IsFractionRing S K`，
即 K 为 S 的分式域）与**局部化多项式环** `F[x₁,…,xₙ](1/w)`（`w ≠ 0`），
及 F-代数映射 `φ : S → F[x](1/w)`、`ψ : F[x](1/w) → S`，使得 `ψ ∘ φ = id_S`。 -/
def IsRetractRational (F K : Type u) [Field F] [Field K] [Algebra F K] : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra F S)
    (_ : Algebra S K) (_ : IsScalarTower F S K) (_ : IsFractionRing S K),
    ∃ (n : ℕ) (w : MvPolynomial (Fin n) F) (_ : w ≠ 0),
      ∃ (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S),
        ψ.comp φ = AlgHom.id F S

/-- **Saltman def3.2（factors rationally，逐字对应）**：
F-代数整环间的 F-代数映射 `φ : S → R` factors rationally ⟺ 存在局部化多项式环
`F[x](1/w)`（`w ≠ 0`）、`0 ≠ r ∈ R`，与 F-代数映射 `ψ : S → F[x](1/w)`、
`η : F[x](1/w) → R(1/r)`，使得 `φ`（经 `R → R(1/r)` 的典范映射）`= η ∘ ψ`。 -/
def FactorsRationally (F S R : Type u) [Field F]
    [CommRing S] [IsDomain S] [Algebra F S]
    [CommRing R] [IsDomain R] [Algebra F R] (φ : S →ₐ[F] R) : Prop :=
  ∃ (n : ℕ) (w : MvPolynomial (Fin n) F) (_ : w ≠ 0) (r : R) (_ : r ≠ 0),
    ∃ (ψ : S →ₐ[F] Localization.Away w)
      (η : Localization.Away w →ₐ[F] Localization.Away r),
      ∀ s : S, algebraMap R (Localization.Away r) (φ s) = η (ψ s)

/-! ## 2. 定义外形锁定（构造子式）与构造工具 -/

/-- **构造子（兼定义外形锁定）**：def3.1 的全部见证显式列出——定义形状若漂移，
本构造立即失败。 -/
theorem IsRetractRational.mk' (F K : Type u) [Field F] [Field K] [Algebra F K]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra F S] [Algebra S K]
    [IsScalarTower F S K] [IsFractionRing S K]
    (n : ℕ) (w : MvPolynomial (Fin n) F) (hw : w ≠ 0)
    (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S)
    (h : ψ.comp φ = AlgHom.id F S) : IsRetractRational F K :=
  ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, n, w, hw, φ, ψ, h⟩

/-! ## 3. 非空洞探针（L1：定义类非空） -/

/-- 探针：`K = F` 是 retract rational。见证：`S = F`（Field 自实例
`IsFractionRing F F`）、`n = 0`、`w = 1`；`φ = Algebra.ofId`（典范映射）；
`ψ` = 在局部化上的求值（`aeval`，空族）经 `IsLocalization.Away.liftAlgHom` 下降；
复合 = 恒等（`lift_eq` + 常数上的取值）。 -/
theorem isRetractRational_self (F : Type*) [Field F] : IsRetractRational F F := by
  let φ : F →ₐ[F] Localization.Away (1 : MvPolynomial (Fin 0) F) :=
    Algebra.ofId F (Localization.Away (1 : MvPolynomial (Fin 0) F))
  let g : MvPolynomial (Fin 0) F →ₐ[F] F := MvPolynomial.aeval fun _ => (1 : F)
  have hg : IsUnit (g (1 : MvPolynomial (Fin 0) F)) := by
    rw [map_one]; exact isUnit_one
  let ψ : Localization.Away (1 : MvPolynomial (Fin 0) F) →ₐ[F] F :=
    IsLocalization.Away.liftAlgHom (x := (1 : MvPolynomial (Fin 0) F)) (f := g) hg
  have hcomp : ψ.comp φ = AlgHom.id F F := by
    refine AlgHom.ext fun c => ?_
    have h1 : ψ (φ c) = g (algebraMap F (MvPolynomial (Fin 0) F) c) := by
      rw [show φ c = algebraMap F (Localization.Away (1 : MvPolynomial (Fin 0) F)) c
          from rfl]
      rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin 0) F)
        (Localization.Away (1 : MvPolynomial (Fin 0) F)) c]
      exact IsLocalization.Away.lift_eq (x := (1 : MvPolynomial (Fin 0) F)) hg _
    rw [AlgHom.comp_apply, AlgHom.id_apply, h1]
    simp [g, MvPolynomial.algebraMap_eq]
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 1, one_ne_zero, φ, ψ, hcomp⟩

/-! ## 4. 公理闸门 -/

#print axioms isRetractRational_self

end ABGV52
