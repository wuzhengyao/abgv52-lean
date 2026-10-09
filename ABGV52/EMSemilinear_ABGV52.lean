/-
  ABGV-5.2 —— **本体形式化 A · M4a（EMSemilinear）**：半线性（系数扭化）作用机器

  目标（蓝图 `wiki/proj-ABGV52-formalize-em.md` §3.4）：为 Masuda (1.4) 的
  「扭化基」读法造机器——基域 `l = F(M)`（带 `G` 作用）上，置换格 `P` 的
  单项式环 `l[P]` 携带**半线性**作用

    σ · single(m, c) = single(σ·m, σ·c)   （源 Lenstra1974.tex `:148–150` 逐字）

  本件 = 三层中的**单项式层**（≙ M2 的 `latticeAlgebraTransport` 之扭化版）：
    * `coeffRingEquiv`：`σ` 在系数域 `l = F(M)` 上的环等价（D1 作用的等价位）；
    * `semiAlgEquiv`：`l[P] ≃+* l[P]`（先单项式置换、再系数扭化）；
    * `semiAlgEquiv_single`：单项式公式；
    * `smul_single_one`：`c • single m 1 = single m c`；
    * `semiAlgEquiv_smul`：**一般半线性** `σ • (c • x) = (σ•c) • (σ•x)`；
    * `semiActionHom`：`G →* (l[P] ≃+* l[P])`（两条同态律）＋作用实例；
    * `smul_single`：`σ • single m c`。

  后续（M4b/M4c）：上延到分式域 `l(P)`（半线性保持）＋ 对 `W := span_l(单项式)`
  用 M3 `speiser_span` ＋ 固定域步。

  **无 sorry、无自造公理**。
-/
import ABGV52.D3_ABGV52

namespace ABGV52
namespace EM

variable {F : Type*} [Field F]
variable {G : Type*} [Group G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]

/-! ## 1. 系数与单项式两条轴 -/

/-- `σ` 在系数域 `l = F(M)` 上的环等价（= D1 作用的等价位）。 -/
noncomputable def coeffRingEquiv (σ : G) :
    latticeFunctionField F M ≃+* latticeFunctionField F M :=
  IsFractionRing.ringEquivOfRingEquiv (latticeAlgebraEquiv F G M σ)

@[simp] lemma coeffRingEquiv_apply (σ : G) (x : latticeFunctionField F M) :
    coeffRingEquiv (M := M) σ x = σ • x := rfl

/-- 单项式轴的置换（= D1 的 `latticeAlgebraEquiv` 之于 `P`）。 -/
noncomputable def monoRingEquiv (σ : G) :
    MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) ≃+*
      MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) :=
  MonoidAlgebra.mapDomainRingEquiv (latticeFunctionField F M)
    (mulEquivOfSMul G P σ)

/-- **半线性单项式等价**：`single m c ↦ single (σ•m) (σ•c)`（先单项式、再系数）。 -/
noncomputable def semiAlgEquiv (σ : G) :
    MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) ≃+*
      MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) :=
  (monoRingEquiv (M := M) σ).trans
    (MonoidAlgebra.mapRingEquiv (Multiplicative P) (coeffRingEquiv (M := M) σ))

/-- **单项式公式**（本件主公式）。 -/
lemma semiAlgEquiv_single (σ : G) (m : Multiplicative P)
    (c : latticeFunctionField F M) :
    semiAlgEquiv (M := M) σ (MonoidAlgebra.single m c)
      = MonoidAlgebra.single (mulEquivOfSMul G P σ m)
          (coeffRingEquiv (M := M) σ c) := by
  simp only [semiAlgEquiv, RingEquiv.trans_apply, monoRingEquiv,
    MonoidAlgebra.mapRingEquiv_single, MonoidAlgebra.mapDomainRingEquiv_single,
    coeffRingEquiv_apply, mulEquivOfSMul_apply]

/-- 纯量乘法的单项式形态：`c • single m 1 = single m c`。 -/
lemma smul_single_one (c : latticeFunctionField F M) (m : Multiplicative P) :
    c • MonoidAlgebra.single m (1 : latticeFunctionField F M)
      = MonoidAlgebra.single m c := by
  rw [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self_apply, MonoidAlgebra.single_mul_single, one_mul,
    mul_one]

/-! ## 2. 一般半线性（动机含 ∀c） -/

/-- **半线性**：`σ • (c • x) = (σ•c) • (σ•x)`（一切 `x`，不只单项式）。 -/
lemma semiAlgEquiv_smul (σ : G) (x :
    MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) :
    ∀ c : latticeFunctionField F M, semiAlgEquiv (M := M) σ (c • x)
      = (coeffRingEquiv (M := M) σ c) • (semiAlgEquiv (M := M) σ x) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      intro c
      rw [show (MonoidAlgebra.of (latticeFunctionField F M)
          (Multiplicative P)) m
          = MonoidAlgebra.single m (1 : latticeFunctionField F M) from rfl]
      rw [smul_single_one, semiAlgEquiv_single]
      rw [semiAlgEquiv_single, map_one, smul_single_one, coeffRingEquiv_apply]
  | add x y hx hy =>
      intro c
      rw [smul_add, map_add, map_add, smul_add, hx c, hy c]
  | smul r x hx =>
      intro c
      rw [smul_smul, hx (c * r), map_mul, hx r, mul_smul]

/-! ## 3. 作用同态 -/

/-- **单位律**：`semiAlgEquiv 1 = id`（逐点）。 -/
lemma semiAlgEquiv_one (x :
    MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) :
    semiAlgEquiv (G := G) (M := M) (1 : G) x = x := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      rw [show (MonoidAlgebra.of (latticeFunctionField F M) (Multiplicative P)) m
          = MonoidAlgebra.single m (1 : latticeFunctionField F M) from rfl]
      rw [semiAlgEquiv_single]
      congr 1
      · rw [mulEquivOfSMul_apply, one_smul, ofAdd_toAdd]
      · rw [coeffRingEquiv_apply, one_smul]
  | add x y hx hy => rw [map_add, hx, hy]
  | smul r x hx => rw [semiAlgEquiv_smul, hx, coeffRingEquiv_apply, one_smul]

/-- **乘法律**：`semiAlgEquiv (σ * τ) = semiAlgEquiv σ ∘ semiAlgEquiv τ`（逐点）。 -/
lemma semiAlgEquiv_mul (σ τ : G) (x :
    MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) :
    semiAlgEquiv (M := M) (σ * τ) x
      = semiAlgEquiv (M := M) σ (semiAlgEquiv (M := M) τ x) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
      rw [show (MonoidAlgebra.of (latticeFunctionField F M) (Multiplicative P)) m
          = MonoidAlgebra.single m (1 : latticeFunctionField F M) from rfl]
      rw [semiAlgEquiv_single, semiAlgEquiv_single, semiAlgEquiv_single]
      congr 1
      · simp only [mulEquivOfSMul_apply, toAdd_ofAdd, mul_smul]
      · rw [coeffRingEquiv_apply, coeffRingEquiv_apply, coeffRingEquiv_apply,
          mul_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul r x hx =>
      rw [semiAlgEquiv_smul, semiAlgEquiv_smul, semiAlgEquiv_smul, hx]
      simp only [coeffRingEquiv_apply, mul_smul]

/-- 半线性作用同态 `G →* (l[P] ≃+* l[P])`。 -/
noncomputable def semiActionHom :
    G →* (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P) ≃+*
      MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) where
  toFun σ := semiAlgEquiv (M := M) σ
  map_one' := RingEquiv.ext (semiAlgEquiv_one (M := M))
  map_mul' σ τ := RingEquiv.ext (semiAlgEquiv_mul (M := M) σ τ)

/-- `l(P)`：系数扭化单项式环的分式域（Masuda 的基本对象）。 -/
abbrev semiFunctionField : Type _ :=
  FractionRing (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))

/-- `l(P)` 上的半线性 `G`-作用（由 `semiActionHom` 经分式域延拓；D1 模板）。 -/
noncomputable instance : MulSemiringAction G (semiFunctionField (F := F) (M := M) (P := P)) :=
  MulSemiringAction.compHom (semiFunctionField (F := F) (M := M) (P := P))
    ((IsFractionRing.ringEquivOfRingEquivHom
        (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (semiFunctionField (F := F) (M := M) (P := P))).comp (semiActionHom (M := M)))

/-- **单项式上的作用公式（分式域层，环等价形态）**：
`ringEquivOfRingEquiv (semiAlgEquiv σ) (algebraMap (single m c)) =
algebraMap (single (σ•m) (σ•c))`。
（WIP 收口 2026-10-08：K/L 隐式推断超时 ⟹ 四处显式 pin。） -/
lemma ringEquivOfRingEquiv_semiAlgEquiv_single (σ : G) (m : Multiplicative P)
    (c : latticeFunctionField F M) :
    IsFractionRing.ringEquivOfRingEquiv
        (A := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (K := semiFunctionField (F := F) (M := M) (P := P))
        (B := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
        (L := semiFunctionField (F := F) (M := M) (P := P))
        (semiAlgEquiv (M := M) σ)
        (algebraMap
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P))
          (MonoidAlgebra.single m c))
      = algebraMap
          (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
          (semiFunctionField (F := F) (M := M) (P := P))
          (MonoidAlgebra.single (mulEquivOfSMul G P σ m)
            (coeffRingEquiv (M := M) σ c)) := by
  have h := IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (A := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (K := semiFunctionField (F := F) (M := M) (P := P))
    (B := MonoidAlgebra (latticeFunctionField F M) (Multiplicative P))
    (L := semiFunctionField (F := F) (M := M) (P := P))
    (semiAlgEquiv (M := M) σ) (MonoidAlgebra.single m c)
  rw [h, semiAlgEquiv_single]

/-! ## 4. 公理闸门 -/

#print axioms coeffRingEquiv
#print axioms monoRingEquiv
#print axioms semiAlgEquiv
#print axioms semiAlgEquiv_single
#print axioms smul_single_one
#print axioms semiAlgEquiv_smul
#print axioms semiActionHom
#print axioms semiFunctionField
#print axioms ringEquivOfRingEquiv_semiAlgEquiv_single

end EM
end ABGV52
