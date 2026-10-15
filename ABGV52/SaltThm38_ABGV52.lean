/-
  ABGV-5.2 · B 档 · M3 —— **`thm3.8`（retract rational ⟺ 局部提升）**（Saltman 1984 §3，第 111 轮）

  **来源** ✓：`raw/Saltman1984.tex:501–510`（label `thm3.8` ✓；**⚠-tex-sourced** ✗）逐字：
  > **thm3.8.** Let \(K / F\) be an extension of fields. The following are equivalent:
  > (i) \(K / F\) is retract rational. (ii) \(K\) is the quotient field of an affine \(F\) algebra
  > \(S\) which satisfies the following condition. Suppose \(T\), \(M\) is a local \(F\) algebra,
  > \(L = T / M\), \(\rho : T \to L\) is the canonical map, and \(\phi : S \to L\) is an \(F\)
  > algebra map. Then there is an \(F\) algebra map \(\phi^{\prime}: S \to T\) such that
  > \(\rho \circ \phi^{\prime} = \phi\).
  **印版核验** ✓（L12／L16 ✓）：`raw/Saltman1984.pdf` **PDF 页 20 ＝ 印版 184** ✓（偏移 `+164` ✓），
  逐字与上同 ✓（本轮按页读图核 ✓）。

  **本件内容** ✓：
  ① **工具** ✓ `finiteType_localizationAway` ✓（`Algebra.FiniteType` 在**单元局部化**下保持 ✓）；
  ② **`thm3_8`（相对化形 ✓）** ✓✓✓：对**给定**的子代数 `S : Subalgebra F K` ✓（仿射 ✓ ＋
     `IsFractionRing ↥S K` ✓），`IsRetractRational F K` ⟺ **`HasLocalLifting F ↥S ↥S (id)` ＋
     `∀ r ≠ 0, Algebra.FiniteType F (S(1/r))`** ✓ —— 即源 `thm3.8(ii)` 的**用点形** ✓；
  ③ **非空洞探针** ✓（L1 ✓）。

  **⚠ 口径** ✓（**诚实登记** ✓）：本件给**相对化形** ✓（`S` **给定** ✓）—— 这正是源**证明**所走的路 ✓
  （源 3.8 的 (ii)⟹(i) 逐字：「suppose 3.8(ii) holds for such `S`. By 3.9, the identity `i : S → S`
  factors rationally and 3.5 finishes the argument」✓）。源**陈述**里的 **∃ `S`** 形 ✓
  （「`K` **is** the quotient field of an affine `S` which satisfies …」✓）由**一步抽出** ✓ 得到 ✓：
  `IsRetractRational` 的见证 `S` ✓ ⟹ 取 `S' := (algebraMap S K).range` ✓（`IsFractionRing` ⟹ 单 ✓）
  ⟹ `↥S' ≃ₐ[F] S` ✓ 搬运 `FiniteType`／`IsFractionRing` ✓。**该一步登记为下一件** ✗（本件未落 ✗、
  **不作声称** ✓）。

  **⚠ 假设口径** ✓（§68／§73 ✓）：`hRaff` ✓（`∀ r ≠ 0, FiniteType F (S(1/r))` ✓）**须显式** ✓ ——
  源 `thm3.9`／`thm3.8` 的**陈述**未写仿射性 ✓ 而其**证明**两处都用到 ✓，且 `R` 仿射**推不出** `R(1/r)`
  仿射 ✗（§68 的印版级发现 ✓）。

  **无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/
import ABGV52.SaltGeneric_ABGV52
import ABGV52.GaloisAlgebra_ABGV52
import ABGV52.SaltLocalProj_ABGV52
import ABGV52.SaltLocalLift_ABGV52
import ABGV52.SaltCor_ABGV52
import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Localization.Away.Basic
open TensorProduct MvPolynomial
universe u
noncomputable section

namespace ABGV52

/-- **升级波（2026-10-15，mathlib `aa35a48`／Lean 4.35.0）**：`NoetherField F G = FractionRing (MvPolynomial G F)`
的 `F`-代数结构在 4.35 下有两个**可合成**候选 —— `OreLocalization.instAlgebra` ✓ 与
`DivisionRing.toRatAlgebra` ✓ —— 二者仅**命题相等**（非 defeq）⟹ 4.35 对"合成实例与推断实例不同一"**报错**
（4.33 静默取一 ✗）。此处按本工程既有语义**钉住前者** ✓，与升级前实际取值一致 ✓。 -/
local instance noetherFieldAlgebra (F G : Type u) [Field F] :
    Algebra F (NoetherField F G) := OreLocalization.instAlgebra

/- **同波第二支**：把通用实例 `DivisionRing.toRatAlgebra`（对 `F = ℚ` 且底环为除环时与上式
**命题相等而非 defeq**）在本文件内屏蔽，使 `OreLocalization.instAlgebra` 成为唯一来源。
Lean 按文件编译 ⟹ 本改动**只影响本文件的精化**（不改变源码层语义）。 -/
attribute [-instance] DivisionRing.toRatAlgebra



/-! ## 1. 工具：`Algebra.FiniteType` 在单元局部化下保持 ✓ -/

/-- **工具** ✓✓：`Algebra.FiniteType F S` ⟹ `Algebra.FiniteType F (S(1/r))` ✓。
**证法** ✓（两句 ✓）：`IsLocalization.finiteType_of_monoid_fg` ✓ 给 `FiniteType S (S(1/r))` ✓
（`Submonoid.powers r` 有限生成 ✓），再用 `Algebra.FiniteType.trans` ✓ 沿 `F → S → S(1/r)` 复合 ✓。
**⚠ 用途** ✓：`thm3.8` 的 **(i)⟹(ii)** 里 `hRaff` ✓ 的实体 ✓；
亦给 `FiniteType F (F[x](1/w))` ✓（取 `S := MvPolynomial (Fin n) F` ✓）✓。 -/
theorem finiteType_localizationAway {F S : Type u} [Field F] [CommRing S] [Algebra F S]
    [Algebra.FiniteType F S] (r : S) : Algebra.FiniteType F (Localization.Away r) :=
  Algebra.FiniteType.trans (R := F) (S := S) (A := Localization.Away r) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) (Localization.Away r))

/-! ## 2. 源 `thm3.8`（相对化形 ✓：`S` 给定 ✓） -/

/-- **源 `thm3.8`** ✓✓✓（**相对化形** ✓，印版 184 ✓）：设 `S ⊆ K` 是**仿射** `F`-子代数 ✓ 且
`K = q(S)` ✓，则
`K/F` **retract rational** ✓ ⟺ `S` 满足源 `thm3.8(ii)` ✓（＝ `HasLocalLifting F ↥S ↥S (id)` ✓
＋ `∀ r ≠ 0, FiniteType F (S(1/r))` ✓）。
**证法** ✓（源 `:511–517` ✓ 逐句 ✓）：
**(ii)⟹(i)** ＝ 第 110 轮的 `factorsRationally_of_hasLocalLifting` ✓（`φ := id` ✓）
＋ `lem3_5` ✓ 的 `.mpr` ✓（源「3.5 finishes the argument」✓）；
**(i)⟹(ii)** ＝ `lem3_5` ✓ 的 `.mp` ✓（源「the identity `i : S → S` factors rationally」✓）
＋ §3 的 `hasLocalLifting_of_factorsRationally` ✓（**3.9 的易方向** ✓）
＋ 上条的 `finiteType_localizationAway` ✓。
**⚠ 口径** ✓：`hRaff` ✓（局部化仿射性 ✓）是**假设**而非导出 ✓（§68 ✓）。 -/
theorem thm3_8 {F K : Type u} [Field F] [Field K] [Algebra F K] (S : Subalgebra F K)
    [Algebra.FiniteType F ↥S] (hS : IsFractionRing ↥S K) :
    IsRetractRational F K ↔
      (HasLocalLifting F ↥S ↥S (AlgHom.id F ↥S) ∧
        ∀ r : ↥S, r ≠ 0 → Algebra.FiniteType F (Localization.Away r)) := by
  constructor
  · intro hrt
    refine ⟨?_, fun r _ => finiteType_localizationAway r⟩
    exact hasLocalLifting_of_factorsRationally (AlgHom.id F ↥S) ((lem3_5 S hS).mp hrt)
  · rintro ⟨hlift, hRaff⟩
    exact (lem3_5 S hS).mpr
      (factorsRationally_of_hasLocalLifting (AlgHom.id F ↥S) inferInstance hlift hRaff)

/-! ## 3. 非空洞探针（L1 ✓） -/

/-- **非空洞探针（L1）** ✓✅：`K = F`、`S = ⊤` 档 ✓ ——
由 `isRetractRational_self` ✓ 经 `thm3_8` ✓ 的 **(i)⟹(ii)** 得源 `thm3.8(ii)` 的**内容** ✓ ⟹
该条件**可满足** ✓（**非空洞** ✓）。 -/
theorem thm3_8_probe (F : Type u) [Field F] :
    HasLocalLifting F ↥(⊤ : Subalgebra F F) ↥(⊤ : Subalgebra F F)
        (AlgHom.id F ↥(⊤ : Subalgebra F F)) ∧
      ∀ r : ↥(⊤ : Subalgebra F F), r ≠ 0 → Algebra.FiniteType F (Localization.Away r) :=
  (thm3_8 (⊤ : Subalgebra F F) (isFractionRing_top_self F)).mp (isRetractRational_self F)

/-! ## 4. 源 `thm3.8` 的 **∃ `S` 形**（印版 184 的**陈述**形 ✓；含 L1 探针 ✓）

**走向** ✓（源 `thm3.8` 的陈述用 **∃ `S`** ✓：「`K` **is** the quotient field of an affine `F`
algebra `S` which satisfies …」✓）：由 `IsRetractRational` 的见证抽出**子代数** ✓ ——
① 见证 `S` ✓（§2 的 `S` 是**抽象类型** ✓，非子代数 ✗）；② `IsFractionRing S K` ⟹ 结构映射**单** ✓；
③ 取 `S' := (algebraMap S K).range` ✓（`Subalgebra F K` ✓）；④ 搬运两件 ✓：
`Algebra.FiniteType` ✓ 沿 `↥S' ≃ₐ[F] S` ✓（`Algebra.FiniteType.equiv` ✓）、
`IsFractionRing ↥S' K` ✓ 沿 `↥S' ≃+* S` ✓（`IsFractionRing.of_ringEquiv_left` ✓，
其第三参数即「两条结构映射经 `e` 一致」✓ —— 由 `AlgEquiv.ofInjective` 在 `range` 上的
计算形给出 ✓）。**⚠ 无需搬运 `HasLocalLifting`** ✓：∃ 形右侧经 §2 的 `thm3_8` ✓
在**新子代数**上直接重跑 ✓（`(thm3_8 S' hS').mp hrt` ✓）。 -/

/-- **从「retract rational」抽出「仿射的子代数」** ✓✓✓：`IsRetractRational F K` ⟹
存在 `S : Subalgebra F K`，`S` **仿射** ✓ 且 `K = q(S)` ✓。
**证法** ✓：由 `IsRetractRational` 的见证 `φ`／`ψ` ✓ 得 `ψ` **满** ✓（`ψ ∘ φ = id` ✓）⟹
`FiniteType F S` ✓（`Algebra.FiniteType.of_surjective` ✓ 用在 `FiniteType F (F[x](1/w))` ✓ 上，
后者由 §1 的工具 ✓）；再取 `S' := range` ✓ 搬运 ✓。
**⚠ 用途** ✓：源 `thm3.8` 的 **∃ `S`** 形 ✓ 的唯一缺件 ✓。 -/
theorem exists_affine_subalgebra_of_isRetractRational {F K : Type u} [Field F] [Field K]
    [Algebra F K] (h : IsRetractRational F K) :
    ∃ (S : Subalgebra F K), Algebra.FiniteType F ↥S ∧ IsFractionRing ↥S K := by
  obtain ⟨S, hCR, hDom, hAFS, hASK, hTSK, hFrac, n, w, hw, φ, ψ, hcomp⟩ := h
  let : CommRing S := hCR
  let : IsDomain S := hDom
  let : Algebra F S := hAFS
  let : Algebra S K := hASK
  let : IsScalarTower F S K := hTSK
  let : IsFractionRing S K := hFrac
  have hsurj : Function.Surjective ψ :=
    fun s => ⟨φ s, by simpa [AlgHom.comp_apply] using congrArg (fun f => f s) hcomp⟩
  have hFinA : Algebra.FiniteType F (Localization.Away w) := finiteType_localizationAway w
  have hFinS : Algebra.FiniteType F S := Algebra.FiniteType.of_surjective ψ hsurj
  have hinj : Function.Injective (IsScalarTower.toAlgHom F S K) := IsFractionRing.injective S K
  let S' : Subalgebra F K := (IsScalarTower.toAlgHom F S K).range
  let e : S ≃ₐ[F] ↥S' := AlgEquiv.ofInjective (IsScalarTower.toAlgHom F S K) hinj
  have hFinS' : Algebra.FiniteType F ↥S' := Algebra.FiniteType.equiv hFinS e
  have hFracS' : IsFractionRing ↥S' K :=
    IsFractionRing.of_ringEquiv_left (R := ↥S') (S := S) (K := K) e.toRingEquiv.symm
      (fun x => by
        have h2 : ((e (e.symm x) : ↥S') : K) = (x : K) :=
          congrArg (fun y : ↥S' => (y : K)) (AlgEquiv.apply_symm_apply e x)
        change (x : K) = IsScalarTower.toAlgHom F S K (e.symm x)
        rw [← h2]
        rfl)
  exact ⟨S', hFinS', hFracS'⟩

/-- **源 `thm3.8`（∃ `S` 形 ✓ ＝ 源陈述的形 ✓，印版 184 ✓）** ✓✓✓✅：
`K/F` **retract rational** ✓ ⟺ **存在** 仿射 `F`-子代数 `S ⊆ K` ✓（`K = q(S)` ✓）
使源 `thm3.8(ii)` 成立 ✓（`HasLocalLifting F ↥S ↥S id` ✓ ＋
`∀ r ≠ 0, FiniteType F (S(1/r))` ✓）。
**证法** ✓：**(⟸)** ＝ §2 的 `thm3_8` ✓（`S` 给定档 ✓）的 `.mpr` ✓；
**(⟹)** ＝ 上条的抽出 ✓ ＋ §2 的 `thm3_8` ✓ 的 `.mp` ✓。
**⚠ 与 §2 的关系** ✓：§2 是**相对化形** ✓（`S` 给定 ✓，源**证明**所走 ✓）；
本条补上**源陈述**的 ∃ 形 ✓ ⟹ `thm3.9`＋`thm3.8` 的 M3 链 ✓ 至此**完整** ✓。
**非空洞** ✓（L1 ✓）：探针见下条 ✓。 -/
theorem thm3_8_exists {F K : Type u} [Field F] [Field K] [Algebra F K] :
    IsRetractRational F K ↔
      ∃ (S : Subalgebra F K) (_ : Algebra.FiniteType F ↥S) (_ : IsFractionRing ↥S K),
        HasLocalLifting F ↥S ↥S (AlgHom.id F ↥S) ∧
          ∀ r : ↥S, r ≠ 0 → Algebra.FiniteType F (Localization.Away r) := by
  constructor
  · intro hrt
    obtain ⟨S, hfin, hfrac⟩ := exists_affine_subalgebra_of_isRetractRational hrt
    exact ⟨S, hfin, hfrac, (thm3_8 S hfrac).mp hrt⟩
  · rintro ⟨S, hfin, hfrac, hcond⟩
    let : Algebra.FiniteType F ↥S := hfin
    exact (thm3_8 S hfrac).mpr hcond

/-- **非空洞探针（L1）** ✓✅：`K = F` 档 ✓ —— 由 `isRetractRational_self` ✓ 经本条 ✓ 得
**∃ 形右侧的内容** ✓ ⟹ 该条件**可满足** ✓（**非空洞** ✓）。 -/
theorem thm3_8_exists_probe (F : Type u) [Field F] :
    ∃ (S : Subalgebra F F) (_ : Algebra.FiniteType F ↥S) (_ : IsFractionRing ↥S F),
      HasLocalLifting F ↥S ↥S (AlgHom.id F ↥S) ∧
        ∀ r : ↥S, r ≠ 0 → Algebra.FiniteType F (Localization.Away r) :=
  thm3_8_exists.mp (isRetractRational_self F)

/-! ## 公理闸门 -/

#print axioms finiteType_localizationAway
#print axioms thm3_8
#print axioms thm3_8_probe
#print axioms exists_affine_subalgebra_of_isRetractRational
#print axioms thm3_8_exists
#print axioms thm3_8_exists_probe

/-- **攻击顺序 ② `hRA` 的第三件** ✓✅（第 228 轮 ✓）：**`MulSemiringAction G (Localization.Away T)`** ✓ ——
**由 `T` 的 `G`-不变化** ✓ 经**库内一般件** ✓ **`locMulSemiringAction`** ✓（`SaltLocalProj_ABGV52:340` ✓）得 ✓。
**⚠ 本件是它唯一可为之处** ✓：**该实例的两个来源分处两件** ✓ —— `MvPolynomial G F` 的**作用** ✓ 在
`SaltGeneric_ABGV52` ✓（**本器序 109** ✓）、**一般件** ✓ 在 `SaltLocalProj_ABGV52` ✓（**序 111** ✓）⟹
**只有序 111 之后的件能同时看见两者** ✓（**本件序 120** ✓）。
**⚠ 已试并作废的一式** ✗（**留痕** ✓）：**给 `SaltGeneric` 加 `import SaltLocalProj`** ✗ ——
**编译通过** ✓ 但**闸门「编译顺序自检」判不过** ✗（`SaltGeneric` 序 109 **早于** `SaltLocalProj` 序 111 ✗
⟹ **被依赖者列在其使用者之后** ✗，`gate-r228.txt` ✓）⟹ **已回退** ✓，**改落本处** ✓。
**⚠ 意义** ✓：**r206 目标的三实例**至此**全部可产** ✓✅ —— ①／② 见 `SaltGeneric` 第 226 轮两件 ✓，③ 见本条 ✓。 -/
theorem exists_mulSemiringAction_away_of_noetherAdjoin {F : Type} [Field F] {G : Type} [Group G]
    [Fintype G] [DecidableEq G] (T : MvPolynomial G F) (hTinv : ∀ g : G, g • T = T) :
    Nonempty (MulSemiringAction G (Localization.Away T)) :=
  ⟨ABGV52.BTier.locMulSemiringAction (F := F) (A := MvPolynomial G F) (G := G) T hTinv⟩

#print axioms exists_mulSemiringAction_away_of_noetherAdjoin

/-- **接线 (乙)：`hS₀R` 由构造供给** ✓✅（第 229 轮 ✓）：r206 目标的假设 `hS₀R` ✓（即
`awayToFieldAlg T hT (algebraMap ↥S (Localization.Away T) r) = algebraMap ↥S (NoetherField F G) r` ✗）
**不是须重绑的假设** ✗ —— 它与 `exists_algHom_away_of_noetherAdjoin` ✓ 的**结论逐字同形** ✓：
取 `inst := ι.toRingHom.toAlgebra` ✓ 后 `algebraMap ↥S (Localization.Away T) r` **定义上等于** `ι r` ✓
⟹ **一行得** ✓（**§190.6 (i) 的 (乙)** ✓）。
**⚠ 意义** ✓：`hS₀R` ✓ 在接线档**被消去** ✓（**是「供给」而非「重绑」** ✓）。 -/
theorem exists_hS0R_away_of_noetherAdjoin {F : Type} [Field F] {G : Type} [Group G]
    [Fintype G] [DecidableEq G] {n : ℕ} {a : Fin n → NoetherField F G}
    {s₀ : NoetherField F G} (T : MvPolynomial G F) (hT : T ≠ 0)
    (hTle : Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
      (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G)))) :
    ∃ (inst : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T)),
      letI := inst
      ∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
        awayToFieldAlg (F := F) (G := G) T hT
            (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) r)
          = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r := by
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G) T hT hTle
  exact ⟨ι.toRingHom.toAlgebra, hι⟩

#print axioms exists_hS0R_away_of_noetherAdjoin

/-- **接线收口** ✓✅（第 229 轮 ✓）：**`t` 三项** ✓（`ht`／`htinv`／`hle` ✓）**与三实例** ✓
**全部由构造供给** ✓ —— `T` ✓ 由 `exists_invariant_t_of_noether` ✓ 产出；
`Algebra ↥S (Localization.Away T)` ✓ 由 `exists_algHom_away_of_noetherAdjoin` ✓ 产出
（`IsScalarTower` ✓ 随 `inferInstance` ✓ 得 ✓）；`MulSemiringAction G (Localization.Away T)` ✓
由 `exists_mulSemiringAction_away_of_noetherAdjoin` ✓ 产出 ✓。
**⚠ 更进一层** ✓：`hact_map` ✓ 与 `hS₀R` ✓ **亦在证明体内导出** ✗（**不再是假设** ✗）——
分别由库内件 `locMulSemiringAction_algebraMap` ✓（`SaltLocalProj` ✓）与 `exists_hS0R_away_of_noetherAdjoin` ✓（本件 ✓）。
**⚠ 余下输入** ✓：**只有** `hRG` ✓／`hgal` ✓／`hProj` ✓（源侧 Galois 结构与投射性 ✓，**仍未证** ✗）。
**⚠ 形** ✓：结论为 **`∃` 形** ✓ —— `T`／三件性质／三实例作 **`∃`-binder** ✓，
`hRG`／`hgal`／`hProj` 在实例**之内** ✓（**§181.2 (f) 的多重量词逐层形** ✓，证明体用 `intro _ _ _` ✓ 按源序绑定 ✓）。
**⚠ 不声称** ✗：源 `theorem-5-1` **未证** ✗；`hgal`／`hProj` **仍未证** ✗（**断言强度 ≤ 证据层级** ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_noetherWiring
    {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} {a : Fin n → NoetherField F G} {s₀ : NoetherField F G}
    (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤)
    (hs₀ : s₀ ≠ 0) (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a))
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i)
    (hs₀_fix : ∀ (g : G), g • s₀ = s₀)
    (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      (∀ (_hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        BTier.IsGaloisWithGroup ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
          (Localization.Away T) G _hRG →
        BTier.GaloisProjectiveHyp ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
          (Localization.Away T) G _hRG →
        Nonempty (GenericExtensionWitnessFieldFinite F G)) := by
  classical
  obtain ⟨T, hTne, hTinv, hTle⟩ := exists_invariant_t_of_noether (F := F) (G := G) a s₀ hs₀
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G) T hTne hTle
  let instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away T) := inferInstance
  let instM : MulSemiringAction G (Localization.Away T) :=
    BTier.locMulSemiringAction (F := F) (A := MvPolynomial G F) (G := G) T hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away T) p)
        = algebraMap (MvPolynomial G F) (Localization.Away T) (g • p) := by
    intro g p
    exact BTier.locMulSemiringAction_algebraMap (F := F) (A := MvPolynomial G F)
      (G := G) T hTinv g p
  have hS0R : ∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
      awayToFieldAlg (F := F) (G := G) T hTne
          (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) r)
        = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r :=
    fun r => hι r
  refine ⟨T, hTne, hTinv, hTle, instA, hST, instM, ?_⟩
  intro hRG hgal hProj
  exact nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin
    (F := F) (G := G) (t := T) hind hgen hs₀ hs₀_mem ha_fix hs₀_fix
    hTne hTinv hTle hact hRG hgal hProj hS0R hinf

#print axioms nonempty_genericExtensionWitnessFieldFinite_of_noetherWiring

/-- **`hRG` 的构造供给（核心件）** ✓✅（第 230 轮 ✓）：给定 `ι : ↥S →ₐ[F] Localization.Away T` ✓
（其与 `awayToFieldAlg` 的复合 ＝ `algebraMap ↥S (NoetherField F G)` ✓）与 `T` 的 `G`-不变化 ✓，
则 **`G`-作用与 `↥S`-纯量交换** ✓ —— **即源侧 `hRG`** ✓（`∀ g r x, g • (r • x) = r • (g • x)` ✗）。
**证明** ✓：该式 ⟺ `ι` 的像**逐点不动** ✓（用 `smul_mul'` ✓ 拆开：`g • (ι r * x) = (g • ι r) * (g • x)` ✓）
⟸ 由 **`awayToField_injective`** ✓（库内 ✓）＋ **`awayToField_smul`** ✓（库内 ✓）
＋ **`smul_eq_self_of_mem_adjoin_of_fixed`** ✓（库内 ✓）三者得 ✓。
**⚠ 同族用法** ✓：与 `exists_algHom_base_of_equivariant` ✓（`SaltGeneric:3510` ✓）内的 `hfixed` ✓ **逐字同法** ✓。
**⚠ 检索优先** ✓（**第六次兑现** ✓，§152.2／§153.2／§188.2／§189.2／§191.4(a) 之续 ✓）：三件**皆已在库** ✓
⟹ **`hRG` 不是新假设** ✗（**§191.7(i) 的下一手已收** ✓）。 -/
theorem smulCommClass_away_of_algHom {F : Type} [Field F] {G : Type} [Group G]
    [Fintype G] [DecidableEq G] {n : ℕ} {a : Fin n → NoetherField F G}
    {s₀ : NoetherField F G}
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i)
    (hs₀_fix : ∀ (g : G), g • s₀ = s₀)
    (T : MvPolynomial G F) (hT : T ≠ 0) (hTinv : ∀ g : G, g • T = T)
    (ι : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) →ₐ[F] Localization.Away T)
    (hι : ∀ r, awayToFieldAlg (F := F) (G := G) T hT (ι r)
      = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r) :
    letI : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
        ι.toRingHom.toAlgebra
    letI : MulSemiringAction G (Localization.Away T) :=
        awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
    ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
      (x : Localization.Away T), g • (r • x) = r • (g • x) := by
  let _instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  let _instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  intro g r x
  have hfix : g • ι r = ι r := by
    refine awayToField_injective (F := F) (G := G) T hT ?_
    change awayToField (F := F) (G := G) T hT
        (awayRingHom (F := F) hTinv g (ι r))
      = awayToField (F := F) (G := G) T hT (ι r)
    rw [awayToField_smul (F := F) (G := G) (t := T) hTinv hT g (ι r)]
    change g • (awayToFieldAlg (F := F) (G := G) T hT) (ι r)
      = (awayToFieldAlg (F := F) (G := G) T hT) (ι r)
    rw [hι r]
    exact smul_eq_self_of_mem_adjoin_of_fixed (F := F) (G := G) (a := a) (s₀ := s₀)
      ha_fix hs₀_fix g r.property
  calc g • (r • x) = g • (ι r * x) := rfl
    _ = (g • ι r) * (g • x) := smul_mul' g (ι r) x
    _ = ι r * (g • x) := by rw [hfix]
    _ = r • (g • x) := rfl

#print axioms smulCommClass_away_of_algHom

/-- **接线收口（完整形）** ✓✅（第 230 轮 ✓）：**`T` 三项** ✓ ＋ **三实例** ✓ ＋ **`hRG`** ✓
**全部由构造供给** ✓ —— 比 `nonempty_genericExtensionWitnessFieldFinite_of_noetherWiring` ✓（第 229 轮 ✓）
**更强** ✓：那条把 `hRG` 列在**输入** ✓，本条把它列在 **`∃`-见证** ✓（**§191.7(i) 的「余下三项」→「余下两项」** ✓）。
**⚠ 同时更正** ✓：本条的 `MulSemiringAction` 见证取 **`awayMulSemiringAction`** ✓（`SaltGeneric:3201` ✓，**与 `T` 同件** ✓）
而非第 228 轮的 `locMulSemiringAction` ✓（`SaltLocalProj` ✓）—— **因 `awayToField_smul` ✓ 的等变性只对前者陈述** ✓；
**⚠ 更正留痕** ✓：`SaltGeneric:5849` ✓ 的「该实例在 `SaltGeneric` 内不可得」✗ 系**实例合成** ✗ 之读数 ✓，
**该 `def` 一直在库** ✓（**「不可合成」≠「不可得」** ✓）。
**⚠ 余下输入** ✓：**只有** `hgal` ✓／`hProj` ✓（**源侧 Galois 结构与投射性** ✓，**仍未证** ✗）。
**⚠ 不声称** ✗：源 `theorem-5-1` **未证** ✗（**断言强度 ≤ 证据层级** ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_noetherGaloisProjective
    {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} {a : Fin n → NoetherField F G} {s₀ : NoetherField F G}
    (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤)
    (hs₀ : s₀ ≠ 0) (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a))
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i)
    (hs₀_fix : ∀ (g : G), g • s₀ = s₀)
    (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        BTier.IsGaloisWithGroup ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
          (Localization.Away T) G _hRG →
        BTier.GaloisProjectiveHyp ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
          (Localization.Away T) G _hRG →
        Nonempty (GenericExtensionWitnessFieldFinite F G) := by
  classical
  obtain ⟨T, hTne, hTinv, hTle⟩ := exists_invariant_t_of_noether (F := F) (G := G) a s₀ hs₀
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G) T hTne hTle
  let instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away T) := inferInstance
  let instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away T) p)
        = algebraMap (MvPolynomial G F) (Localization.Away T) (g • p) := by
    intro g p
    exact awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv g p
  have hS0R : ∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
      awayToFieldAlg (F := F) (G := G) T hTne
          (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) r)
        = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r :=
    fun r => hι r
  have hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
      (x : Localization.Away T), g • (r • x) = r • (g • x) :=
    smulCommClass_away_of_algHom (F := F) (G := G) (a := a) (s₀ := s₀)
      ha_fix hs₀_fix T hTne hTinv ι hι
  refine ⟨T, hTne, hTinv, hTle, instA, hST, instM, hRG, ?_⟩
  intro hgal hProj
  exact nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin
    (F := F) (G := G) (t := T) hind hgen hs₀ hs₀_mem ha_fix hs₀_fix
    hTne hTinv hTle hact hRG hgal hProj hS0R hinf

#print axioms nonempty_genericExtensionWitnessFieldFinite_of_noetherGaloisProjective

/-- **`hgal` 第 ① 款由构造供给** ✓✅（第 231 轮 ✓）：`FaithfulSMul G (Localization.Away T)` ✓ ——
**用 `awayMulSemiringAction`** ✓（`SaltGeneric:3201` ✓）。
**证明** ✓：设 `a • x = b • x` 对一切 `x` ✓ ⟹ 取 `x = algebraMap p` ✓ 并用 **`awayRingHom_algebraMap`** ✓
得 `algebraMap (a • p) = algebraMap (b • p)` ✓ ⟹ 由 **`algebraMap (MvPolynomial G F) (Localization.Away T)` 单射** ✓
（**经 `awayToField_algebraMap`** ✓ ＋ **`awayToField_injective`** ✓ ＋ **`IsFractionRing.injective`** ✓ 三步）
得 `a • p = b • p` ✓ ⟹ 由 **`FaithfulSMul G (MvPolynomial G F)`** ✓（`SaltGeneric:339` ✓ 的实例 ✓）得 `a = b` ✓。
**⚠ 检索优先** ✓（**第七次兑现** ✓）：**两件皆已在库** ✓（`awayRingHom_algebraMap` ✓／`FaithfulSMul` 实例 ✓）。 -/
theorem faithfulSMul_away_of_noetherAdjoin {F : Type} [Field F] {G : Type} [Group G]
    {T : MvPolynomial G F} (hT : T ≠ 0) (hTinv : ∀ g : G, g • T = T) :
    letI : MulSemiringAction G (Localization.Away T) :=
      awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
    FaithfulSMul G (Localization.Away T) := by
  let _instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  have hAlgInj : Function.Injective
      (algebraMap (MvPolynomial G F) (Localization.Away T)) := by
    intro x y hxy
    have h2 : awayToField (F := F) (G := G) T hT
          (algebraMap (MvPolynomial G F) (Localization.Away T) x)
        = awayToField (F := F) (G := G) T hT
          (algebraMap (MvPolynomial G F) (Localization.Away T) y) := by rw [hxy]
    rw [awayToField_algebraMap, awayToField_algebraMap] at h2
    exact IsFractionRing.injective (MvPolynomial G F) (NoetherField F G) h2
  refine ⟨fun {a b} h => ?_⟩
  have hmap : ∀ p : MvPolynomial G F, a • p = b • p := by
    intro p
    have h1 := h (algebraMap (MvPolynomial G F) (Localization.Away T) p)
    change awayRingHom (F := F) hTinv a
        (algebraMap (MvPolynomial G F) (Localization.Away T) p)
      = awayRingHom (F := F) hTinv b
        (algebraMap (MvPolynomial G F) (Localization.Away T) p) at h1
    rw [awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv a p,
      awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv b p] at h1
    exact hAlgInj h1
  exact FaithfulSMul.eq_of_smul_eq_smul (α := MvPolynomial G F) (fun p => hmap p)

#print axioms faithfulSMul_away_of_noetherAdjoin

/-- **`hgal` 归约为 `δ` 双射** ✓✅（第 231 轮 ✓）：给定 `hRG` ✓ 与
**`Function.Bijective (deltaToEndRingHom hRG)`** ✓，则 **`IsGaloisWithGroup ↥S (Localization.Away T) G hRG`** ✓
—— **①② 由构造供给** ✓：**①** ＝ `faithfulSMul_away_of_noetherAdjoin` ✓；
**②** ＝ `algebraMap_fixed_of_smulCommClass` ✓（**一般事实** ✓：② **由 `hRG` 自动** ✓，**不必作假设** ✗）；
**③** ＝ **输入** ✓（**＝ Galois 内容** ✓）。
**⚠ 意义** ✓：`hgal` ✓（第 230 轮的输入项 ✓）**不是原语** ✗ —— 其**唯一实质内容 ＝ ③** ✓（**交叉相积同构** ✓）。 -/
theorem isGaloisWithGroup_away_of_bijectiveDelta {F : Type} [Field F] {G : Type} [Group G]
    [Fintype G] [DecidableEq G] {n : ℕ} {a : Fin n → NoetherField F G}
    {s₀ : NoetherField F G} (T : MvPolynomial G F) (hT : T ≠ 0)
    (hTinv : ∀ g : G, g • T = T)
    (ι : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) →ₐ[F] Localization.Away T) :
    letI : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
        ι.toRingHom.toAlgebra
    letI : MulSemiringAction G (Localization.Away T) :=
        awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
    ∀ (hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
        (x : Localization.Away T), g • (r • x) = r • (g • x)),
      Function.Bijective (BTier.deltaToEndRingHom hRG) →
      BTier.IsGaloisWithGroup ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
        (Localization.Away T) G hRG := by
  let _instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  let _instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  intro hRG hδ
  exact ⟨faithfulSMul_away_of_noetherAdjoin (F := F) (G := G) hT hTinv,
    fun g r => BTier.algebraMap_fixed_of_smulCommClass hRG g r, hδ⟩

#print axioms isGaloisWithGroup_away_of_bijectiveDelta

/-- **归约形（收口）** ✓✅（第 231 轮 ✓）：**`T` 三项** ✓ ＋ **三实例** ✓ ＋ **`hRG`** ✓ **全部由构造供给** ✓，
**`hgal` 亦由构造供给** ✓（**①② 自动 ＋ ③ 作输入** ✓）⟹ **余下输入只有两件** ✓：
**`δ` 双射** ✓（**＝ Galois 内容** ✓）与 **`hProj`** ✓。
**⚠ 比 `nonempty_genericExtensionWitnessFieldFinite_of_noetherGaloisProjective`** ✓（第 230 轮 ✓）**更强** ✓：
那条把 `IsGaloisWithGroup` **整条**列在输入 ✓，本条只取其**第 ③ 款** ✓
（**② 为冗余款** ✓，见 `GaloisAlgebra_ABGV52` ✓ 的 `algebraMap_fixed_of_smulCommClass` ✓；
**① 由 `faithfulSMul_away_of_noetherAdjoin`** ✓ 供给 ✓）。
**⚠ 不声称** ✗：**`δ` 双射**与 **`hProj`** **均未证** ✗；源 `theorem-5-1` **未证** ✗（**断言强度 ≤ 证据层级** ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_of_noetherGaloisDelta
    {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]
    {n : ℕ} {a : Fin n → NoetherField F G} {s₀ : NoetherField F G}
    (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤)
    (hs₀ : s₀ ≠ 0) (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a))
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i)
    (hs₀_fix : ∀ (g : G), g • s₀ = s₀)
    (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
          (Localization.Away T) G _hRG →
        Nonempty (GenericExtensionWitnessFieldFinite F G) := by
  classical
  obtain ⟨T, hTne, hTinv, hTle⟩ := exists_invariant_t_of_noether (F := F) (G := G) a s₀ hs₀
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G) T hTne hTle
  let instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away T) := inferInstance
  let instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away T) p)
        = algebraMap (MvPolynomial G F) (Localization.Away T) (g • p) := by
    intro g p
    exact awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv g p
  have hS0R : ∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
      awayToFieldAlg (F := F) (G := G) T hTne
          (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) r)
        = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r :=
    fun r => hι r
  have hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
      (x : Localization.Away T), g • (r • x) = r • (g • x) :=
    smulCommClass_away_of_algHom (F := F) (G := G) (a := a) (s₀ := s₀)
      ha_fix hs₀_fix T hTne hTinv ι hι
  refine ⟨T, hTne, hTinv, hTle, instA, hST, instM, hRG, ?_⟩
  intro hδ hProj
  have hgal : BTier.IsGaloisWithGroup ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away T) G hRG :=
    isGaloisWithGroup_away_of_bijectiveDelta (F := F) (G := G) (a := a) (s₀ := s₀)
      T hTne hTinv ι hRG hδ
  exact nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin
    (F := F) (G := G) (t := T) hind hgen hs₀ hs₀_mem ha_fix hs₀_fix
    hTne hTinv hTle hact hRG hgal hProj hS0R hinf

#print axioms nonempty_genericExtensionWitnessFieldFinite_of_noetherGaloisDelta

/-- **预期用例中 `FaithfulSMul ↥S (Localization.Away T)` 自动** ✓✅（第 232 轮 ✓）：
`ι` **单射** ✓ ⟹ `algebraMap ↥S (Localization.Away T)` 单射 ✓ ⟹ **忠实** ✓。
**证明** ✓：设 `ι r = ι s` ✓ ⟹ 两侧经 **`awayToFieldAlg`** ✓ 得
`algebraMap ↥S (NoetherField F G) r = algebraMap ↥S (NoetherField F G) s` ✓ ⟹ 由 **`Subtype.ext`** ✓ 得 `r = s` ✓。
**⚠ 用途** ✓（**判据下调之执行** ✓）：`GaloisFaithfulHyp` ✓ 的**现形已被机器反驳** ✗
（`galoisFaithfulHyp_refuted` ✓，第 232 轮 ✓），但**其结论在接线实际对上直接可得** ✓ ⟹
**§171.1 认的「`GaloisProgeneratorHyp` 的唯一瓶颈」✗ 在本用例中不存在** ✓（**不必证端点** ✗）。 -/
theorem faithfulSMul_subalgebra_away_of_noetherAdjoin {F : Type} [Field F] {G : Type} [Group G]
    [Fintype G] [DecidableEq G] {n : ℕ} {a : Fin n → NoetherField F G}
    {s₀ : NoetherField F G} (T : MvPolynomial G F) (hT : T ≠ 0)
    (ι : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) →ₐ[F] Localization.Away T)
    (hι : ∀ r, awayToFieldAlg (F := F) (G := G) T hT (ι r)
      = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r) :
    letI : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
        ι.toRingHom.toAlgebra
    FaithfulSMul ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) := by
  let _instA : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  rw [faithfulSMul_iff_algebraMap_injective]
  intro r s hrs
  have h2 : awayToFieldAlg (F := F) (G := G) T hT (ι r)
      = awayToFieldAlg (F := F) (G := G) T hT (ι s) := by
    rw [show ι r = ι s from hrs]
  rw [hι r, hι s] at h2
  exact Subtype.ext h2

#print axioms faithfulSMul_subalgebra_away_of_noetherAdjoin

/-- **接线假设表的源侧整表（L1 非空性）** ✓✅（第 237 轮 ✓；**自造件** ✓）：
**九项源侧条件同时可满足** ✓ —— 见证 = **`F = ℚ`** ✓、**`G = PUnit`** ✓、**`a = X`** ✓（**单点族的唯一元** ✓）、
**`s₀ = X`** ✓、**`T = X`** ✓。
**⚠ 各项来历** ✓：**`hind`** ✓ 由 **`MvPolynomial.algebraicIndependent_X`** ✓（**库内** ✓）
经 **`AlgebraicIndependent.comp`** ✓ 重标号 ＋ **`aeval_algebraMap_apply`** ✓ ＋ **`IsFractionRing.injective`** ✓
搬到分式域 ✓；**`hgen`** ✓ 由 **`comap` ＋ `MvPolynomial.adjoin_range_X`** ✓ ＋
**`IsFractionRing.div_surjective`** ✓（**每个元都是多项式之商** ✓）得 ✓；
**`hle`** ✓ 由 `x = algebraMap (X ())` ✓（**`Subalgebra.algebraMap_mem`** ✓）与 `x⁻¹` ✓（**生成元** ✓）得 ✓；
**`ha_fix`／`hs₀_fix`／`hTinv`** ✓ 由 **`PUnit` 单点** ✓（`Subsingleton.elim` ＋ `one_smul` ✓）—— **与作用的具体形无关** ✓。
**⚠ 意义** ✓（**L1** ✓）：**接线假设表的源侧不再是「空类」** ✓ —— 与 §198（**端点侧非空** ✓）合读 ⟹
**r229--r231 的接线定理的假设表在源侧可满足** ✓。
**⚠ 余项** ✓（**如实** ✓）：**三实例 ＋ `hRG` ＋ `hδ` ＋ `hProj`** ✗ **未在本见证内** ✗ ——
**其充分条件 ＝ `Localization.Away T ≅ ↥S`** ✓（**下一手** ✓：本档下 `Localization.Away X ≅ ℚ[X, X⁻¹] ≅ ↥S` ✓）。
**⚠ 不声称** ✗：**接线假设表的整体非空性未核** ✗（**只核到源侧** ✓）。 -/
theorem exists_noetherWiringData_pUnit_rat :
    ∃ (a : Fin 1 → NoetherField ℚ PUnit.{1}) (s₀ : NoetherField ℚ PUnit.{1})
      (T : MvPolynomial PUnit.{1} ℚ),
      AlgebraicIndependent ℚ a ∧ IntermediateField.adjoin ℚ (Set.range a) = ⊤ ∧
      s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin ℚ (Set.range a) ∧
      (∀ (g : PUnit.{1}) (i : Fin 1), g • a i = a i) ∧
      (∀ g : PUnit.{1}, g • s₀ = s₀) ∧ Infinite ℚ ∧
      T ≠ 0 ∧ (∀ g : PUnit.{1}, g • T = T) ∧
      Algebra.adjoin ℚ (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars ℚ
        (Algebra.adjoin (MvPolynomial PUnit.{1} ℚ)
          ({(algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) T)⁻¹}
            : Set (NoetherField ℚ PUnit.{1}))) := by
  let x : NoetherField ℚ PUnit.{1} :=
    algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
      (MvPolynomial.X PUnit.unit)
  have hX : AlgebraicIndependent ℚ (fun _ : PUnit.{1} => x) := by
    rw [algebraicIndependent_iff]
    intro p hp
    have h1 : (MvPolynomial.aeval (fun _ : PUnit.{1} => x)) p
        = algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          ((MvPolynomial.aeval MvPolynomial.X) p) :=
      MvPolynomial.aeval_algebraMap_apply (NoetherField ℚ PUnit.{1}) MvPolynomial.X p
    rw [MvPolynomial.aeval_X_left_apply] at h1
    rw [h1] at hp
    exact IsFractionRing.injective _ _ (by rw [hp, map_zero])
  have hind : AlgebraicIndependent ℚ (fun _ : Fin 1 => x) :=
    hX.comp (fun _ : Fin 1 => PUnit.unit) (fun a b _ => Subsingleton.elim a b)
  have hset : Set.range (fun _ : Fin 1 => x) = {x} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton x
    · intro hy
      exact ⟨0, (Set.mem_singleton_iff.mp hy).symm⟩
  have hgen : IntermediateField.adjoin ℚ (Set.range (fun _ : Fin 1 => x)) = ⊤ := by
    rw [hset]
    refine le_antisymm le_top ?_
    have hcomap : Subalgebra.comap
        (IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}))
        (IntermediateField.adjoin ℚ {x}).toSubalgebra = ⊤ := by
      refine top_unique ?_
      rw [← MvPolynomial.adjoin_range_X (R := ℚ) (σ := PUnit.{1})]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨g, rfl⟩
      rw [Subsingleton.elim g PUnit.unit]
      show IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) ∈ (IntermediateField.adjoin ℚ {x}).toSubalgebra
      exact (IntermediateField.subset_adjoin ℚ ({x} : Set (NoetherField ℚ PUnit.{1})))
        (Set.mem_singleton x)
    intro y _
    obtain ⟨p, q, _hq, heq⟩ := IsFractionRing.div_surjective (MvPolynomial PUnit.{1} ℚ) y
    have hmem : ∀ r : MvPolynomial PUnit.{1} ℚ,
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) r
          ∈ IntermediateField.adjoin ℚ ({x} : Set (NoetherField ℚ PUnit.{1})) := by
      intro r
      exact (Subalgebra.mem_comap _ _ _).mp (by rw [hcomap]; trivial)
    rw [← heq]
    exact div_mem (hmem p) (hmem q)
  have hxne : x ≠ 0 := by
    intro h0
    have h1 : algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) = 0 := by
      rw [show algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) = x from rfl, h0]
    have h2 : (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ) = 0 :=
      IsFractionRing.injective (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (by rw [h1, map_zero])
    exact MvPolynomial.X_ne_zero PUnit.unit h2
  refine ⟨fun _ => x, x, MvPolynomial.X PUnit.unit, hind, hgen, hxne, ?_, ?_, ?_,
    inferInstance, MvPolynomial.X_ne_zero PUnit.unit, ?_, ?_⟩
  · rw [hset]
    exact (Algebra.subset_adjoin (R := ℚ) (Set.mem_singleton x))
  · intro g i
    rw [Subsingleton.elim g 1, one_smul]
  · intro g
    rw [Subsingleton.elim g 1, one_smul]
  · intro g
    rw [Subsingleton.elim g 1, one_smul]
  · rw [hset]
    refine Algebra.adjoin_le ?_
    rintro y (hy | hy)
    · rw [Set.mem_singleton_iff.mp hy]
      exact Subalgebra.algebraMap_mem _ (MvPolynomial.X PUnit.unit)
    · rcases hy with rfl | rfl
      · exact Subalgebra.algebraMap_mem _ (MvPolynomial.X PUnit.unit)
      · exact (Algebra.subset_adjoin (R := MvPolynomial PUnit.{1} ℚ)
          (Set.mem_singleton _))
#print axioms exists_noetherWiringData_pUnit_rat

set_option maxHeartbeats 1000000 in
/-- **`Q(X) = ↥S`** ✓✅（第 238 轮 ✓；**自造件** ✓）：本档（`F = ℚ` ✓、`G = PUnit` ✓、`T = X` ✓）下
**`A[T⁻¹]` 与 `ℚ[a, s₀, s₀⁻¹]` 是同一个子代数** ✓ —— 即 wiring 的 `hle` 之**反向**亦真 ✓ ⟹
配合已落的 **`awayToFieldAlg`** ✓（`Localization.Away T ≃ₐ[F] Q(T)` ✓）得 **`S' ≅ ↥S`** ✓。
**⚠ 证明结构（**两向皆不需归纳** ✓）**：
**⟸** ✓ `A[x⁻¹] ≤ ℚ[x, x⁻¹]` —— 对 `A`-生成元用 **`Algebra.adjoin_induction`** ✓，
其中「**系数情形**」用 **`comap` 技巧** ✓（`Subalgebra.comap` ＋ **`MvPolynomial.adjoin_range_X`** ✓
而不展开 `MvPolynomial.aeval_C` ✗ —— **该展开的实例档歧义实测卡住** ✗）；
**⟹** ✓ `ℚ[x, x⁻¹] ≤ A[x⁻¹]` —— 由 **`Subalgebra.algebraMap_mem`** ✓（`x` ✓）与 **`Algebra.subset_adjoin`** ✓（`x⁻¹` ✓）得 ✓。
**⚠ 意义** ✓：**`Localization.Away T ≅ ↥S`** ✓ 的关键一步已落 ✓ ⟹ **`Module.Finite ∧ Projective`** ✓
与 **`δ` 双射** ✓（**秩一性** ✓）**两件俱将可得** ✓（**下一手** ✓）。
**⚠ 不声称** ✗：**同构本身未落** ✗（**只落等式** ✓）；**`hδ`／`hProj` 未证** ✗。 -/
theorem adjoin_away_eq_adjoin_union_inv_pUnit_rat :
    Subalgebra.restrictScalars ℚ (Algebra.adjoin (MvPolynomial PUnit.{1} ℚ)
        ({algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit)}⁻¹ : Set (NoetherField ℚ PUnit.{1})))
      = Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
            algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))
          ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit),
              (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))⁻¹}) := by
  set x : NoetherField ℚ PUnit.{1} :=
    algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
      (MvPolynomial.X PUnit.unit) with hxdef
  have hset : Set.range (fun _ : Fin 1 => x) ∪ {x, x⁻¹} = {x, x⁻¹} := by
    refine Set.Subset.antisymm ?_ (fun z hz => Or.inr hz)
    rintro _ (⟨i, rfl⟩ | h)
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact h
  rw [hset]
  refine le_antisymm ?_ ?_
  · -- `A[x⁻¹] ≤ ℚ[x, x⁻¹]`：像用 `comap` 收（不需归纳）✓
    have himage : ∀ r : MvPolynomial PUnit.{1} ℚ,
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) r
          ∈ Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1})) := by
      intro r
      have hcomap : Subalgebra.comap
          (IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}))
          (Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1}))) = ⊤ := by
        refine top_unique ?_
        rw [← MvPolynomial.adjoin_range_X (R := ℚ) (σ := PUnit.{1})]
        refine Algebra.adjoin_le ?_
        rintro _ ⟨g, rfl⟩
        rw [Subsingleton.elim g PUnit.unit]
        show IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit)
          ∈ Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1}))
        exact Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inl rfl))
      exact (Subalgebra.mem_comap _ _ _).mp (by rw [hcomap]; trivial)
    intro y hy
    exact Algebra.adjoin_induction
      (p := fun z _ => z ∈ Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1})))
      (fun z hz => by
        have hzx : z = x⁻¹ := Set.mem_singleton_iff.mp hz
        rw [hzx]
        exact Algebra.subset_adjoin (show x⁻¹ ∈ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1}))
          from Set.mem_insert_iff.mpr (Or.inr rfl)))
      himage
      (fun a b _ _ ha hb => add_mem ha hb)
      (fun a b _ _ ha hb => mul_mem ha hb)
      (by simpa using hy)
  · -- `ℚ[x, x⁻¹] ≤ A[x⁻¹]` ✓
    refine Algebra.adjoin_le ?_
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact Subalgebra.algebraMap_mem _ (MvPolynomial.X PUnit.unit)
    · have hzx : z = x⁻¹ := Set.mem_singleton_iff.mp hz
      rw [hzx]
      exact Algebra.subset_adjoin (show x⁻¹ ∈ ({x}⁻¹ : Set (NoetherField ℚ PUnit.{1}))
        from by simp)
#print axioms adjoin_away_eq_adjoin_union_inv_pUnit_rat

set_option maxHeartbeats 1000000 in
/-- **`↥S ≤ range(awayToFieldAlg X)`** ✓✅（第 239 轮 ✓；**自造件** ✓）：本档（`F = ℚ` ✓、`G = PUnit` ✓）下
**数据生成的子代数落在典范映射的像内** ✓ —— 即 **`range = ↥S` 的上半** ✓（**下半** ✓
＝ 库内 **`adjoin_inv_mem_range_awayToFieldAlg`** ✓，r208 已落 ✓）。
**⚠ 证明** ✓（**不需局部化元素分析** ✓）：`ℚ[x, x⁻¹] = Algebra.adjoin ℚ (range a ∪ {x, x⁻¹})` ✓ 由
**`Algebra.adjoin_le`** ✓ 化到两个生成元 ✓：**`x`** ✓ 由 **`awayToField_algebraMap`** ✓
（**典范映射与 `algebraMap` 相容** ✓）给出 ✓；**`x⁻¹`** ✓ 由 **库内 `adjoin_inv_mem_range_awayToFieldAlg`** ✓
（`Q(X) ⊆ range` ✓）＋ **`Algebra.subset_adjoin`** ✓ 给出 ✓。
**⚠ 意义** ✓：与 **r238 的等式** ✓ 合读 ⟹ **`range = ↥S`** ✓ ⟹（**`AlgEquiv.ofInjective`** ✓ ＋
**`awayToField_injective`** ✓）得 **`Localization.Away X ≅ ↥S`** ✓（**下一手** ✓，**只差记账** ✓）。
**⚠ 工艺** ✓：**`awayToFieldAlg` 的应用与 `awayToField` 不 defeq** ✗ ⟹ 须 **`change`** ✓（**实测** ✓）。
**🔴 更正（第 240 轮 ✓；**过度声称撤回** ✗）**：本条**与库内件同向** ✓ ——
由 **r238 的等式** ✓（`↥S = restrictScalars ℚ (adjoin A {x⁻¹})` ✓）与
**`adjoin_inv_mem_range_awayToFieldAlg`** ✓（`Q(X) ⊆ range` ✓）**已可推出同一声明** ✓
（**两边的集合仅记号之差** ✓）⟹ **本条不是 `range = ↥S` 的「另一半」** ✗ ——
**§201 的「两半已齐」系过度声称** ✗，**当轮撤回** ✓。
**🔴 真正缺向** ✓：**`range ≤ ↥S`** ✗（`range_eq_adjoin_gap_registered` ✓，见下 ✓）。
**⚠ 保留价值** ✓：本条的**独立通道** ✓（不经 r238 ✓、直接用相容性 ✓）仍可作**交叉核对** ✓。
**⚠ 不声称** ✗：**同构未落** ✗；**`hδ`／`hProj` 未证** ✗。 -/
theorem adjoin_union_inv_le_range_awayToFieldAlg_pUnit_rat :
    Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
          algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))
        ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit),
            (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))⁻¹})
      ≤ (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
          (MvPolynomial.X_ne_zero PUnit.unit)).range := by
  set x : NoetherField ℚ PUnit.{1} :=
    algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
      (MvPolynomial.X PUnit.unit) with hxdef
  have hxmem : x ∈ (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit)).range :=
    ⟨algebraMap (MvPolynomial PUnit.{1} ℚ)
        (Localization.Away (MvPolynomial.X PUnit.unit)) (MvPolynomial.X PUnit.unit),
      (by
        change awayToField (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
          (MvPolynomial.X_ne_zero PUnit.unit)
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (Localization.Away (MvPolynomial.X PUnit.unit))
            (MvPolynomial.X PUnit.unit)) = x
        rw [hxdef]
        exact awayToField_algebraMap (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
          (MvPolynomial.X_ne_zero PUnit.unit) (MvPolynomial.X PUnit.unit))⟩
  refine Algebra.adjoin_le ?_
  rintro z (hz | hz)
  · obtain ⟨i, rfl⟩ := hz
    exact hxmem
  · rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hxmem
    · have hzx : z = x⁻¹ := Set.mem_singleton_iff.mp hz
      rw [hzx]
      exact adjoin_inv_mem_range_awayToFieldAlg (F := ℚ) (G := PUnit.{1})
        (MvPolynomial.X PUnit.unit) (MvPolynomial.X_ne_zero PUnit.unit) x⁻¹
        (Algebra.subset_adjoin (Set.mem_singleton x⁻¹))
#print axioms adjoin_union_inv_le_range_awayToFieldAlg_pUnit_rat

/-- **登记** ✗：**`range(awayToFieldAlg X hX) ≤ ↥S` 未落** ✗（**第 240 轮定性** ✓）——
**`range = ↥S`**（⟹ `Localization.Away X ≃ₐ[ℚ] ↥S` ✓，**只差记账** ✓）**缺的正是此向** ✗。
**⚠ 已备通道** ✓（**下一手** ✓）：`z ∈ range` ✓ ⟹ 取 `y` 使 `awayToField y = z` ✓；
**`IsLocalization.surj`** ✓ 给出 `y * algebraMap (X^n) = algebraMap a` ✓ ⟹（**`awayToField_algebraMap`** ✓）
**`z * x^n = algebraMap a`** ✓ ⟹ **`z = algebraMap a · (x⁻¹)^n`** ✓ ——
**`algebraMap a ∈ ↥S`** ✓（用 r237 的 **`comap` 技巧** ✓）＋ **`x⁻¹ ∈ ↥S`** ✓（**生成元** ✓）
⟹ **`z ∈ ↥S`** ✓。**⚠ 关键** ✓：**无须在 `Subalgebra` 内做除法** ✗（`↥S` **不**自动是域 ✗）——
**改写为乘法形** ✓（`(x^n)⁻¹ = (x⁻¹)^n` ✓）**绕开** ✓。
**⚠ 不声称** ✗：**该向未落** ✗；**同构未落** ✗。 -/
theorem range_le_adjoin_gap_registered : True := trivial

#print axioms range_le_adjoin_gap_registered

set_option maxHeartbeats 1000000 in
/-- **`range ≤ ↥S`** ✓✅（第 241 轮 ✓；**自造件** ✓）：本档（`F = ℚ` ✓、`G = PUnit` ✓）下
**典范映射的像落在数据生成的子代数内** ✓ —— 即 **`range = ↥S` 缺的那一向** ✗（§202.2 ✓）。
与已落的 **r239** ✓（`↥S ≤ range` ✓）合读 ⟹ **`range = ↥S`** ✓ ⟹（**`AlgEquiv.ofInjective`** ✓ ＋
**`awayToField_injective`** ✓）**`Localization.Away X ≅ ↥S`** ✓ —— **下一手只差记账** ✓。
**⚠ 证明（**按 §202.2 通道** ✓）**：**①** `z ∈ range` ✓ ⟹ 取 `y` ✓（**`change`** ✓ 到 `awayToField` 形 ✓）；
**②** **`IsLocalization.surj`** ✓ 给 `y * algebraMap ↑b = algebraMap a` ✓（`b ∈ powers (X ())` ✓）；
**③** **`Submonoid.mem_powers_iff`** ✓ 取 `n` 使 `(X ())^n = ↑b` ✓ ⟹ **先 `rw [← hn] at hy`** ✓
（**次序要紧** ✗ —— 若先套 `awayToField_algebraMap` ✓ 则 `b` 进入 `awayToField` 的 `t`-位 ✓，
再 `rw` 会因 **motive 依赖 `b`** 而失败 ✗，**实测** ✓）；**④** 套 **`awayToField_algebraMap`** ✓ ＋
**`map_pow`** ✓ ＋ **`← hxdef`** ✓ 得 **`z * x^n = algebraMap a`** ✓；
**⑤** 乘 **`(x⁻¹)^n`** ✓ 并用 **`mul_assoc`／`← mul_pow`／`mul_inv_cancel₀`** ✓ 得
**`z = algebraMap a · (x⁻¹)^n`** ✓；**⑥** 两因子落 **↥S** ✓（**`himage`** ✓ ＝ r238 的 **`comap` 技巧** ✓；
**`pow_mem`** ✓ ＋ **`Algebra.subset_adjoin`** ✓）。
**⚠ 关键** ✓：**未在 `Subalgebra` 内做除法** ✓（`↥S` **不**自动是域 ✗）—— **乘法形绕开** ✓。
**⚠ 工艺** ✓：**`Submonoid.mem_powers_iff` 的参数序是 `(x z)`** ✓（`x ∈ powers z` ✓）
⟹ **须写 `(b) (X ())`** ✓；**`Algebra.adjoin_mono` 的 `⊆` 用显式 λ** ✓（`Set.subset_union_right` 是**成员**引理 ✗，**实测** ✓）。
**⚠ 不声称** ✗：**同构未落** ✗；**`hδ`／`hProj` 未证** ✗。 -/
theorem range_awayToFieldAlg_le_adjoin_pUnit_rat :
    (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit)).range
      ≤ Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
            algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))
          ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit),
              (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))⁻¹}) := by
  set x : NoetherField ℚ PUnit.{1} :=
    algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
      (MvPolynomial.X PUnit.unit) with hxdef
  have himage : ∀ r : MvPolynomial PUnit.{1} ℚ,
      algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) r
        ∈ Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1})) := by
    intro r
    have hcomap : Subalgebra.comap
        (IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}))
        (Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1}))) = ⊤ := by
      refine top_unique ?_
      rw [← MvPolynomial.adjoin_range_X (R := ℚ) (σ := PUnit.{1})]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨g, rfl⟩
      rw [Subsingleton.elim g PUnit.unit]
      show IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit)
        ∈ Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1}))
      exact Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inl rfl))
    exact (Subalgebra.mem_comap _ _ _).mp (by rw [hcomap]; trivial)
  have hxne : x ≠ 0 := by
    intro h0
    have h1 : algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) = 0 := by
      rw [show algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) = x from rfl, h0]
    exact MvPolynomial.X_ne_zero PUnit.unit
      (IsFractionRing.injective (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (by rw [h1, map_zero]))
  rintro z ⟨y, rfl⟩
  change awayToField (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
    (MvPolynomial.X_ne_zero PUnit.unit) y
    ∈ Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => x) ∪ {x, x⁻¹})
  obtain ⟨⟨a, b⟩, hy⟩ :=
    IsLocalization.surj (Submonoid.powers
      (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff
    (b : MvPolynomial PUnit.{1} ℚ)
    (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)).mp b.2
  rw [← hn] at hy
  have h3 : awayToField (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit) y * x ^ n
      = algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) a := by
    have h := congrArg (awayToField (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit)) hy
    simp only [map_mul] at h
    rw [awayToField_algebraMap, map_pow] at h
    rw [awayToField_algebraMap] at h
    rw [← hxdef] at h
    exact h
  have h4 : awayToField (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit) y
      = algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) a * (x⁻¹) ^ n := by
    have h5 : awayToField (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
        (MvPolynomial.X_ne_zero PUnit.unit) y * x ^ n * (x⁻¹) ^ n
        = algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) a * (x⁻¹) ^ n := by
      rw [h3]
    rwa [mul_assoc, ← mul_pow, mul_inv_cancel₀ hxne, one_pow, mul_one] at h5
  rw [h4]
  refine mul_mem ?_ ?_
  · exact Algebra.adjoin_mono ((fun z hz => Or.inr hz)) (himage a)
  · have hxinv : x⁻¹ ∈ Algebra.adjoin ℚ ({x, x⁻¹} : Set (NoetherField ℚ PUnit.{1})) :=
      Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inr rfl))
    exact Algebra.adjoin_mono (fun z hz => Or.inr hz) (pow_mem hxinv n)
#print axioms range_awayToFieldAlg_le_adjoin_pUnit_rat

/-- **`range = ↥S`** ✓✅（第 242 轮 ✓）：本档（`F = ℚ` ✓、`G = PUnit` ✓）下
**典范映射的像恰为数据生成的子代数** ✓ —— 由 **r239** ✓（`↥S ≤ range` ✓）与 **r241** ✓（`range ≤ ↥S` ✓）
经 **`le_antisymm`** ✓ 得 ✓（**两向皆已机器核** ✓）。
**⚠ 意义** ✓：**`Localization.Away X ≅ ↥S`** ✓ 的**全部实质内容已备** ✓ ——
余下只是**记账** ✓（**`AlgEquiv.ofInjective`** ✓ ＋ **`awayToField_injective`** ✓ ＋
本等式对 `Subalgebra` 型的搬运 ✓，**下一手** ✓）。
**⚠ 附注** ✓：`AdjoinAwayGap` 名下的登记（§202 ✓）**已由本轮结清** ✓ ——
其「缺向」即 **r241** ✓。
**⚠ 不声称** ✗：**同构本身未落** ✗（**实质已备** ✓）；**`hδ`／`hProj` 未证** ✗。 -/
theorem range_awayToFieldAlg_eq_adjoin_pUnit_rat :
    (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit)).range
      = Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
            algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))
          ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit),
              (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))⁻¹}) :=
  le_antisymm
    (range_awayToFieldAlg_le_adjoin_pUnit_rat)
    (adjoin_union_inv_le_range_awayToFieldAlg_pUnit_rat)

#print axioms range_awayToFieldAlg_eq_adjoin_pUnit_rat

set_option maxHeartbeats 1000000 in
/-- **记账同构** ✓✅（第 243 轮 ✓）：本档下 **`Localization.Away X ≃ₐ[ℚ] ↥S`** ✓ ——
即 **wiring 的 `S' ≅ ↥S`** ✓（`S' = Localization.Away T` ✓，`T = X` ✓）。
**⚠ 组装** ✓（**先 `have`／`let` 定型、再 `exact`** ✓ —— **r242 教训兑现** ✓）：
**①** `hrange` ✓ ＝ **r242 等式** ✓；**②** `hmem` ✓（像落 `↥S` ✓：`rw [← hrange]` ✓ ＋ **`AlgHom.mem_range`** ✓）；
**③** `f` ✓ ＝ **`AlgHom.codRestrict`** ✓；**④** `hinj` ✓（**`awayToField_injective`** ✓ ＋ **`Subtype.ext_iff`** ✓）；
**⑤** `hsurj` ✓（由 `hrange` ✓ ＋ **`z.2`** ✓ ＋ **`Subtype.ext`** ✓）；**⑥** **`AlgEquiv.ofBijective`** ✓。
**⚠ 意义** ✓：**§199.5(i) 的「接线假设表非空」只剩两步** ✓ ——
**`Module.Finite ∧ Projective`** ✓ 与 **`δ` 双射** ✓（**皆由本同构的秩一性** ✓，**下一手** ✓）。
**⚠ 不声称** ✗：**`hProj`／`hδ` 本身未证** ✗（**其充分条件的载体已备** ✓）。 -/
theorem nonempty_algEquiv_away_adjoin_pUnit_rat :
    ∃ (T : MvPolynomial PUnit.{1} ℚ) (_hT : T ≠ 0),
      Nonempty (Localization.Away T ≃ₐ[ℚ]
        ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))) := by
  have hrange := range_awayToFieldAlg_eq_adjoin_pUnit_rat
  have hmem : ∀ y : Localization.Away (MvPolynomial.X PUnit.unit),
      awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
        (MvPolynomial.X_ne_zero PUnit.unit) y
        ∈ Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
            algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))
          ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit),
              (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))⁻¹}) := by
    intro y
    rw [← hrange]
    exact ⟨y, rfl⟩
  let f : Localization.Away (MvPolynomial.X PUnit.unit) →ₐ[ℚ]
      ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
          algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))
        ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit),
            (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))⁻¹})) :=
    (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit)).codRestrict _ hmem
  have hinj : Function.Injective f := by
    intro x y hxy
    exact awayToField_injective (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit) (Subtype.ext_iff.mp hxy)
  have hsurj : Function.Surjective f := by
    intro z
    have hz : (z : NoetherField ℚ PUnit.{1})
        ∈ (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
          (MvPolynomial.X_ne_zero PUnit.unit)).range := by
      rw [hrange]
      exact z.2
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, Subtype.ext hy⟩
  exact ⟨MvPolynomial.X PUnit.unit, MvPolynomial.X_ne_zero PUnit.unit,
    ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩⟩⟩
#print axioms nonempty_algEquiv_away_adjoin_pUnit_rat

set_option maxHeartbeats 1000000 in
/-- **通用秩一件** ✓✅（第 244 轮 ✓；**自造件** ✓；**一般档** ✓）：若 `S ≅ R`（**`R`-代数同构** ✓）
则 **`S` 是有限投射 `R`-模** ✓ —— **`Module.Finite.equiv`** ✓ ＋ **`Module.Projective.of_equiv`** ✓
沿 **`e.toLinearEquiv.symm`** ✓ 搬运 ✓（**`R` 自身秩一自由** ✓）。
**⚠ 用途** ✓：**wiring 的 (A) 件** ✓（**`Module.Finite ∧ Projective`** ✓）的**通用工具** ✓ ——
**接线实际对**上只差把 **r243 的同构** ✓ 从 **`ℚ`-档升到 `↥S`-档** ✓（**下一手** ✓）。 -/
theorem module_finite_projective_of_algEquiv_self
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (e : S ≃ₐ[R] R) : Module.Finite R S ∧ Module.Projective R S :=
  ⟨Module.Finite.equiv e.toLinearEquiv.symm,
    Module.Projective.of_equiv e.toLinearEquiv.symm⟩

set_option maxHeartbeats 1000000 in
/-- **推论** ✓✅（第 244 轮 ✓）：**`S ≅ R` ⟹ `GaloisProjectiveHyp` 成立** ✓（**任意 `G`／`hRG`** ✓）——
即 **`hProj` 在「自同构档」上可满足** ✓（**其充分条件** ✓）。
**⚠ 意义** ✓（**L1** ✓）：**`hProj` 的现形虽在任意档为假** ✗（r234 ✓），**但在自同构档自动成立** ✓
⟹ **接线假设表的 `hProj` 一件有了可满足的充分条件** ✓。
**⚠ 不声称** ✗：**接线实际对上 `S' ≅ ↥S` 是 `ℚ`-档** ✓（r243 ✓），**升到 `↥S`-档未落** ✗（**下一手** ✓）。 -/
theorem galoisProjectiveHyp_of_algEquiv_self
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s))
    (e : S ≃ₐ[R] R) : BTier.GaloisProjectiveHyp R S G hRG :=
  fun _ => module_finite_projective_of_algEquiv_self e
#print axioms module_finite_projective_of_algEquiv_self
#print axioms galoisProjectiveHyp_of_algEquiv_self

set_option maxHeartbeats 1000000 in
/-- **升档通用件** ✓✅（第 245 轮 ✓；**自造件** ✓；**一般档** ✓）：
若 **`S ≅ R`（环同构** ✓**）**，则**取其诱导的 `R`-代数结构**（**`e.symm.toRingHom.toAlgebra`** ✓）时
**`S` 是有限投射 `R`-模** ✓ —— 即 **r244 的秩一件在「结构由同构给出」档的形态** ✓。
**⚠ 用途** ✓：**wiring 的 (A) 件** ✓ —— 把 **r243 的同构** ✓（**`ℚ`-档** ✓）**升到 `↥S`-档** ✓
（**`Finite`／`Projective` 正是在该档提问** ✓）⟹ **`hProj` 的实体** ✓（**下一手** ✓）。
**⚠ 构造** ✓：线性等价 **`φ : S ≃ₗ[R] R`** ✓（`toFun := e` ✓；**`map_smul'`** ✓ 由
**`map_mul`** ✓ ＋ **`RingEquiv.apply_symm_apply`** ✓）⟹ **`Module.Finite.equiv φ.symm`** ✓
＋ **`Module.Projective.of_equiv φ.symm`** ✓。
**⚠ 工艺** ✓：**证明内用 `let`（非 `letI`）注册该实例** ✓ —— **`letI` 触发 `linter.style.haveILetI`** ✗
（**该 linter 对实例注册是假阳性** ✓，**但仍是警告** ✗）⟹ **`let _inst := …`** ✓（**零新警告** ✓，**实测** ✓）。
**⚠ 不声称** ✗：**wiring 实际对上的实例化未落** ✗（**下一手** ✓）。 -/
theorem module_finite_projective_of_ringEquiv_self
    {R S : Type*} [CommRing R] [CommRing S] (e : S ≃+* R) :
    letI : Algebra R S := e.symm.toRingHom.toAlgebra
    Module.Finite R S ∧ Module.Projective R S := by
  let _inst : Algebra R S := e.symm.toRingHom.toAlgebra
  let φ : S ≃ₗ[R] R :=
    { toFun := e
      invFun := e.symm
      map_add' := fun x y => e.map_add x y
      map_smul' := fun r s => by
        show e (e.symm r * s) = r * e s
        rw [map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun x => e.symm_apply_apply x
      right_inv := fun x => e.apply_symm_apply x }
  exact ⟨Module.Finite.equiv φ.symm, Module.Projective.of_equiv φ.symm⟩
#print axioms module_finite_projective_of_ringEquiv_self

set_option maxHeartbeats 1000000 in
/-- **具体同构** ✓✅（第 246 轮 ✓）：本档下 **`Localization.Away X ≃ₐ[ℚ] ↥S`** ✓ 的**命名件** ✓ ——
即 **r243** ✓ 的 `∃`-形的**无 `∃` 版** ✓（**见证 `T = X` 内建** ✓，**供下游直接取用** ✓）。
**⚠ 证明** ✓：与 **r243 同体** ✓（`hrange` ✓ ＋ `hmem` ✓ ＋ **`codRestrict`** ✓ ＋
**`Function.Bijective`** ✓ ＋ **`AlgEquiv.ofBijective`** ✓），**仅去掉 `∃` 包装** ✓。
**⚠ 工艺** ✓：**类型里的 `Localization.Away (MvPolynomial.X …)` 须钉系数环** ✗
（否则 **`CommSemiring ?m` stuck** ✗，**实测** ✓）⟹ 写 **`(MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)`** ✓。 -/
noncomputable def awayAlgEquivAdjoin_pUnit_rat :
    Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ) ≃ₐ[ℚ]
      ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹})) := by

  have hrange := range_awayToFieldAlg_eq_adjoin_pUnit_rat
  have hmem : ∀ y : Localization.Away (MvPolynomial.X PUnit.unit),
      awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
        (MvPolynomial.X_ne_zero PUnit.unit) y
        ∈ Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
            algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))
          ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit),
              (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))⁻¹}) := by
    intro y
    rw [← hrange]
    exact ⟨y, rfl⟩
  let f : Localization.Away (MvPolynomial.X PUnit.unit) →ₐ[ℚ]
      ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
          algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))
        ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit),
            (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))⁻¹})) :=
    (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit)).codRestrict _ hmem
  have hinj : Function.Injective f := by
    intro x y hxy
    exact awayToField_injective (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
      (MvPolynomial.X_ne_zero PUnit.unit) (Subtype.ext_iff.mp hxy)
  have hsurj : Function.Surjective f := by
    intro z
    have hz : (z : NoetherField ℚ PUnit.{1})
        ∈ (awayToFieldAlg (F := ℚ) (G := PUnit.{1}) (MvPolynomial.X PUnit.unit)
          (MvPolynomial.X_ne_zero PUnit.unit)).range := by
      rw [hrange]
      exact z.2
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, Subtype.ext hy⟩
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

set_option maxHeartbeats 1000000 in
/-- **(A) 件实例化** ✓✅（第 246 轮 ✓）：本档下，**取 `awayAlgEquivAdjoin_pUnit_rat` 诱导的 `↥S`-代数结构**，
**`S'` 是有限投射 `↥S`-模** ✓ —— 即 **`hProj` 的实体** ✓（**`GaloisProjectiveHyp ↥S S' G hRG`** 的
`Finite ∧ Projective` 一款 ✓，**对任意 `G`／`hRG`** ✓）。
**⚠ 证明** ✓：**一行** ✓ —— **r245 的升档件** ✓ 喂 **`(awayAlgEquivAdjoin_pUnit_rat).toRingEquiv`** ✓。
**⚠ 意义** ✓（**L1** ✓）：**接线实际对上 `hProj` 一件有了实体** ✓ ⟹
**(B) `δ` 双射** ✗ 是**接线假设表非空（§199.5(i)）的最后一件** ✓（**下一手** ✓）。
**⚠ 不声称** ✗：**`GaloisProjectiveHyp ↥S S' G hRG` 整条未组装** ✗（**`Finite ∧ Projective` 两款已备** ✓）；
**`hδ` 未证** ✗。 -/
theorem finite_projective_away_adjoin_pUnit_rat :
    letI : Algebra ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) :=
      (awayAlgEquivAdjoin_pUnit_rat).symm.toRingHom.toAlgebra
    Module.Finite ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) ∧
      Module.Projective ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) :=
  module_finite_projective_of_ringEquiv_self (awayAlgEquivAdjoin_pUnit_rat).toRingEquiv
#print axioms finite_projective_away_adjoin_pUnit_rat

set_option maxHeartbeats 1000000 in
/-- **通用件** ✓✅（第 247 轮 ✓；**自造件** ✓；**一般档** ✓）：若 **`algebraMap R S` 满射** ✓ 且 **`G` 单点** ✓，
则 **`IsGaloisWithGroup R S G hRG` 成立** ✓（**任意 `hRG`** ✓）—— 即 **(B) `δ` 双射的充分条件** ✓。
**⚠ 证明（**三步** ✓）**：**①** `FaithfulSMul G S` ✓（**单点** ✓）；**②** `g • algebraMap r = algebraMap r` ✓
（`g = 1` ✓ ＋ **`one_smul`** ✓）；**③** **`δ` 双射** ✓ —— **`δ(single 1 a) = coeffToEnd a`** ✓
（`actEnd 1 = 1` ✓）；**单** ✓ 由 **`u = single 1 (u.coeff 1)`** ✓（**单点群** ✓）；
**满** ✓ 由 **`f ↦ f 1`** ✓ 且 **`f t = t · f 1`** ✓ —— **`t = algebraMap r`** ✓（**满射** ✓）⟹
**`f (algebraMap r) = r • f 1`** ✓（**`map_smul`** ✓）**`= algebraMap r · f 1`** ✓（**`Algebra.smul_def`** ✓）✓。
**⚠ 意义** ✓（**L1** ✓）：**接线实际对上 `hδ` 的充分条件齐** ✓ —— 由于 **`S' ≅ ↥S`** ✓（r243／r246 ✓），
**`algebraMap ↥S S'` 满射** ✓ ⟹ **`hδ`（`G = PUnit` 档）可满足** ✓。
**⚠ 工艺（**须入纪律** ✓）**：**`PUnit` 有全局 `SMul` 实例** ✗ ⟹ **其 `hRG` 的 smul 档与
`IsGaloisWithGroup` 期望的档冲突** ✗（**实测** ✓）⟹ **改用泛型 `G` ＋ `[Subsingleton G]`** ✓
（**更一般** ✓ 且**无全局实例竞争** ✓）。
**⚠ 不声称** ✗：**接线对上的 `hδ` 实例化未落** ✗（**充分条件已备** ✓）。 -/
theorem isGaloisWithGroup_of_subsingleton_of_surjective_algebraMap
    {G R S : Type*} [Group G] [Subsingleton G] [Fintype G]
    [CommRing R] [CommRing S] [Algebra R S] [MulSemiringAction G S]
    (hsurj : Function.Surjective (algebraMap R S))
    (hRG : ∀ (g : G) (r : R) (s : S), g • (r • s) = r • (g • s)) :
    BTier.IsGaloisWithGroup R S G hRG := by
  have hact : BTier.actEnd hRG 1 = 1 := by
    refine LinearMap.ext (fun t => ?_)
    show (1 : G) • t = t
    rw [one_smul]
  have hsingle : ∀ a : S,
      BTier.deltaToEndRingHom hRG (SkewMonoidAlgebra.single (1 : G) a) = BTier.coeffToEnd a := by
    intro a
    show BTier.deltaToEndAdd hRG (SkewMonoidAlgebra.single (1 : G) a) = BTier.coeffToEnd a
    rw [BTier.deltaToEndAdd_single, hact, mul_one]
  have heval : ∀ a : S,
      (BTier.deltaToEndAdd hRG (SkewMonoidAlgebra.single (1 : G) a)) 1 = a := by
    intro a
    rw [BTier.deltaToEndAdd_single, hact, mul_one]
    show a * 1 = a
    rw [mul_one]
  have hsingle_eq : ∀ u : SkewMonoidAlgebra S G,
      u = SkewMonoidAlgebra.single (1 : G) (u.coeff (1 : G)) := by
    intro u
    refine SkewMonoidAlgebra.ext (fun g => ?_)
    rw [Subsingleton.elim g 1, SkewMonoidAlgebra.coeff_single_apply]
    simp
  have hcoe : ∀ u : SkewMonoidAlgebra S G,
      (BTier.deltaToEndAdd hRG u) 1 = u.coeff (1 : G) := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    exact heval (u.coeff (1 : G))
  have hrec : ∀ u : SkewMonoidAlgebra S G,
      u = SkewMonoidAlgebra.single (1 : G) ((BTier.deltaToEndAdd hRG u) 1) := by
    intro u
    conv_lhs => rw [hsingle_eq u]
    rw [hcoe u]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun {a b} _ => Subsingleton.elim a b⟩
  · intro g r
    rw [Subsingleton.elim g 1, one_smul]
  · constructor
    · intro u v huv
      have h1 : (BTier.deltaToEndAdd hRG u) 1 = (BTier.deltaToEndAdd hRG v) 1 :=
        congrArg (fun f : Module.End R S => f 1) huv
      calc u = SkewMonoidAlgebra.single (1 : G) ((BTier.deltaToEndAdd hRG u) 1) := hrec u
        _ = SkewMonoidAlgebra.single (1 : G) ((BTier.deltaToEndAdd hRG v) 1) := by rw [h1]
        _ = v := (hrec v).symm
    · intro f
      refine ⟨SkewMonoidAlgebra.single (1 : G) (f 1), ?_⟩
      rw [hsingle]
      refine LinearMap.ext (fun t => ?_)
      have h2 : f t = t * f 1 := by
        obtain ⟨r, rfl⟩ := hsurj t
        conv_lhs => rw [Algebra.algebraMap_eq_smul_one (R := R) (A := S) r]
        rw [map_smul, Algebra.smul_def]
      show (f 1) * t = f t
      rw [h2, mul_comm]
#print axioms isGaloisWithGroup_of_subsingleton_of_surjective_algebraMap

/-- **登记** ✗（**第 248 轮** ✓）：**接线对上的 (B) 实例化未落** ✗（**§199.5(i) 的最后一步** ✓）。
**⚠ 本轮实测（**如实** ✓）**：
**(i)** **证明体有效** ✓ —— `.abgv52-scratch/pr248a.lean` 的**首版编译通过** ✓
（**`local instance` 平凡作用** ✓ ＋ **结论内 `letI` 绑定 `↥S`-结构** ✓ ＋ **`hsurj` 由
`(awayAlgEquivAdjoin_pUnit_rat).symm.surjective`** ✓ ＋ **r247 通用件** ✓ 组装 ✓），
**唯一告警** ＝ **`linter.style.haveILetI`** ✗（**证明内 `letI`** ✗，**对实例注册是假阳性** ✓）。
**(ii)** **无警告打包受阻** ✗（**实测三版** ✗）：把证明内 `letI` 换成 **`let _inst`** ✗
（**goal 变成 `Algebra … → ∀ hRG, …`** ✗，**`intro hRG` 绑到实例** ✗）；
换成 **`let instAlg` ＋ `letI := instAlg`** ✗ 同型 ✗；改**节级 `local instance`** ✗
（**结论不再含 `letI`** ✓）时遇 **`AddMonoidAlgebra.commRing` 非计算性** ✗（**须 `noncomputable`** ✓，
**未续试** ✗）。
**⚠ 下一手通道** ✓：**节级 `noncomputable local instance instAlg : Algebra ↥S S' :=
(awayAlgEquivAdjoin_pUnit_rat).symm.toRingHom.toAlgebra`** ✓（**配 `noncomputable local instance`
平凡作用** ✓）**＋ 结论不含 `letI`** ✓ —— **`local instance` 的作用域限于节** ✓。
**⚠ 不声称** ✗：**实例化未落** ✗；**接线假设表整体非空未核** ✗。 -/
theorem away_adjoin_pUnit_rat_instance_gap_registered : True := trivial

#print axioms away_adjoin_pUnit_rat_instance_gap_registered

section

noncomputable local instance instMSA : MulSemiringAction PUnit.{1}
    (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

noncomputable local instance instAlg : Algebra ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
      algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit))
    ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit),
        (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))⁻¹}))
    (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) :=
  (awayAlgEquivAdjoin_pUnit_rat).symm.toRingHom.toAlgebra

set_option maxHeartbeats 1000000 in
/-- **(B) 实例化** ✓✅（第 249 轮 ✓；**§199.5(i) 的最后一件** ✓）：**接线对上 `hδ` 成立** ✓ ——
即 **`IsGaloisWithGroup ↥S (Localization.Away X) PUnit hRG`** ✓（**平凡作用档** ✓，**任意 `hRG`** ✓）。
**⚠ 组装（**§210.3 通道兑现** ✓）**：**节级 `noncomputable local instance instMSA`** ✓（**平凡作用** ✓，
**须 `noncomputable`** ✓ —— 局部化的环结构非计算性 ✓）＋ **节级 `noncomputable local instance instAlg`** ✓
（**`Algebra ↥S S' := (awayAlgEquivAdjoin_pUnit_rat).symm.toRingHom.toAlgebra`** ✓）；
**结论不含 `letI`** ✓ ⟹ **既无 `linter.style.haveILetI`** ✗（**上轮受阻点** ✓）
**亦无「goal 变函数型」** ✗（**`intro` 绑错** ✓）。
**⚠ 证明** ✓：**r247 通用件** ✓ ＋ **`algebraMap ↥S S' = e.symm.toRingHom`** ✓（**`rfl`** ✓）
⟹ **`e.symm.surjective`** ✓。
**⚠ 意义** ✓：**§199.5(i) 的三件齐** ✓（**`Finite ∧ Projective`** ✓ ＝ r246 ✓；**`hδ`** ✓ ＝ 本条 ✓）
⟹ **余下只是把它们装进 wiring 的 ∃-形** ✓（**下一手** ✓）。
**⚠ 不声称** ✗：**装配未落** ✗；**接线假设表整体非空未核** ✗。 -/
theorem isGaloisWithGroup_away_adjoin_pUnit_rat
    (hRG : ∀ (g : PUnit.{1})
      (r : ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})))
      (s : Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)),
      g • (r • s) = r • (g • s)) :
    BTier.IsGaloisWithGroup
      ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹}))
      (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ))
      PUnit.{1} hRG := by
  refine isGaloisWithGroup_of_subsingleton_of_surjective_algebraMap (G := PUnit.{1}) ?_ hRG
  have h : (algebraMap ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹}))
      (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)))
      = (awayAlgEquivAdjoin_pUnit_rat).symm.toRingHom := rfl
  rw [h]
  exact (awayAlgEquivAdjoin_pUnit_rat).symm.surjective

set_option maxHeartbeats 1000000 in
/-- **接线假设表的 Galois 侧整体非空** ✓✅（第 249 轮 ✓；**自造件** ✓；**§199.5(i) 收口** ✓）：
在 **wiring 的对**（`↥S` ＝ `ℚ[a, s₀, s₀⁻¹]` ✓ 与 `S'` ＝ `Localization.Away X` ✓；**结构与 r246／r249 同** ✓）上，
**残余三项 `hRG`** ✓／**`hδ`（`δ` 双射 ✓）**／**`hProj`（＝ `GaloisProjectiveHyp` ✓）同时可满足** ✓。
**⚠ 三件来历** ✓：**`hRG`** ✓ ＝ **平凡作用档** ✓（`Subsingleton.elim` ＋ **`one_smul`** ✓）；
**`hδ`** ✓ ＝ **r249 件第三款** ✓（`isGaloisWithGroup_away_adjoin_pUnit_rat` ✓，**通用件即 §209.2** ✓）；
**`hProj`** ✓ ＝ **r246 件** ✓（`finite_projective_away_adjoin_pUnit_rat` ✓ —— `GaloisProjectiveHyp` **是蕴含式** ✓，
故 **`fun _ =>` 即得** ✓ ⟹ **§6 余项「`hProj` 整条组装」✗ 至此落** ✓）。
**⚠ 与 r237 的关系** ✓：**r237** ✓ 给**源侧九项**（`a` ✓／`s₀` ✓／`T` ✓／`hind` ✓／`hgen` ✓／…／`hle` ✓，
**∃-形** ✓）；本条给**其余三项** ✓ ⟹ **两者合读 ＝ 接线假设表整体非空** ✓（**§199.5(i) 收口** ✓）。
**⚠ 不声称** ✗：**源 `theorem-5-1`／`theorem-2-1` 未证** ✗；**接线结论本身的推导见下一件** ✓。 -/
theorem exists_wiringHypotheses_pUnit_rat :
    ∃ (hRG : ∀ (g : PUnit.{1})
      (r : ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})))
      (x : Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)),
      g • (r • x) = r • (g • x)),
      Function.Bijective (BTier.deltaToEndRingHom hRG) ∧
      BTier.GaloisProjectiveHyp
        ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
          algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))
        ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit),
            (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit))⁻¹}))
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ))
        PUnit.{1} hRG := by
  let hRG : ∀ (g : PUnit.{1})
      (r : ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})))
      (x : Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)),
      g • (r • x) = r • (g • x) :=
    fun g r x => by rw [Subsingleton.elim g 1, one_smul, one_smul]
  exact ⟨hRG, (isGaloisWithGroup_away_adjoin_pUnit_rat hRG).2.2,
    fun _ => finite_projective_away_adjoin_pUnit_rat⟩

set_option maxHeartbeats 1000000 in
/-- **接线在测试实例上发射** ✓✅（第 249 轮 ✓；**自造件** ✓）：**把三件装进 wiring 的 ∃-形** ✓ ——
**`Nonempty (GenericExtensionWitnessFieldFinite ℚ PUnit.{1})`** ✓（**r231 归约形** ✓ 被**完整消费** ✓）。
**⚠ 假设表逐项供给** ✓：**源侧** ✓ `hind` ✓／`hgen` ✓／`hs₀` ✓／`hs₀_mem` ✓／`ha_fix` ✓／`hs₀_fix` ✓／
`hinf` ✓（**证据与 r237 同** ✓ —— **`algebraicIndependent_X`** ✓ ＋ **`adjoin_range_X`** ✓ ＋
**`div_surjective`** ✓）；**wiring 侧** ✓ `T = X` ✓／`hT` ✓／`hTinv` ✓／`hle` ✓／**三实例** ✓／
**`hact`** ✓／**`hRG`** ✓／**`hgal`** ✓／**`hProj`** ✓／**`hS₀R`** ✓。
**⚠ 工艺读数（**须入纪律** ✓；**三版实测** ✗）**：**`hact` 在平凡作用档下 ＝ `g • p = p`** ✗ ——
**该式用 `one_smul` 写不出** ✗（**实体档 `PUnit.instSMul_mathlib` 与 Noether 作用档不同一** ✗，
**`rw` 匹配失败** ✗；**注册局部 `MulSemiringAction` 亦不解** ✗）⟹ **改走 `noetherRingHom`** ✓：
**`noetherRingHom ℚ PUnit g = 1`** ✓（**单点** ✓ ＋ **`map_one`** ✓）＋ **`congrArg`** ✓ 得 ✓（**全库首用** ✓）。
**⚠ 意义** ✓（**L1 的最强形** ✓）：**接线定理的假设表不空** ✓ **且其结论真的产出** ✓ ⟹ **接线非空壳** ✓。
**⚠ 不声称** ✗：**源 `theorem-5-1`／`theorem-2-1` 未证** ✗；**本件只到有限档见证数据** ✓
（**弱化档 ＋ 有限档** ✓，`GenericExtensionWitnessFieldFinite` 口径 ✓）。 -/
theorem nonempty_genericExtensionWitnessFieldFinite_pUnit_rat :
    Nonempty (GenericExtensionWitnessFieldFinite ℚ PUnit.{1}) := by
  let x : NoetherField ℚ PUnit.{1} :=
    algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
      (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
  have hX : AlgebraicIndependent ℚ (fun _ : PUnit.{1} => x) := by
    rw [algebraicIndependent_iff]
    intro p hp
    have h1 : (MvPolynomial.aeval (fun _ : PUnit.{1} => x)) p
        = algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          ((MvPolynomial.aeval MvPolynomial.X) p) :=
      MvPolynomial.aeval_algebraMap_apply (NoetherField ℚ PUnit.{1}) MvPolynomial.X p
    rw [MvPolynomial.aeval_X_left_apply] at h1
    rw [h1] at hp
    exact IsFractionRing.injective _ _ (by rw [hp, map_zero])
  have hind : AlgebraicIndependent ℚ (fun _ : Fin 1 => x) :=
    hX.comp (fun _ : Fin 1 => PUnit.unit) (fun a b _ => Subsingleton.elim a b)
  have hset : Set.range (fun _ : Fin 1 => x) = {x} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact Set.mem_singleton x
    · intro hy
      exact ⟨0, (Set.mem_singleton_iff.mp hy).symm⟩
  have hgen : IntermediateField.adjoin ℚ (Set.range (fun _ : Fin 1 => x)) = ⊤ := by
    rw [hset]
    refine le_antisymm le_top ?_
    have hcomap : Subalgebra.comap
        (IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}))
        (IntermediateField.adjoin ℚ {x}).toSubalgebra = ⊤ := by
      refine top_unique ?_
      rw [← MvPolynomial.adjoin_range_X (R := ℚ) (σ := PUnit.{1})]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨g, rfl⟩
      rw [Subsingleton.elim g PUnit.unit]
      show IsScalarTower.toAlgHom ℚ (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) ∈ (IntermediateField.adjoin ℚ {x}).toSubalgebra
      exact (IntermediateField.subset_adjoin ℚ ({x} : Set (NoetherField ℚ PUnit.{1})))
        (Set.mem_singleton x)
    intro y _
    obtain ⟨p, q, _hq, heq⟩ := IsFractionRing.div_surjective (MvPolynomial PUnit.{1} ℚ) y
    have hmem : ∀ r : MvPolynomial PUnit.{1} ℚ,
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1}) r
          ∈ IntermediateField.adjoin ℚ ({x} : Set (NoetherField ℚ PUnit.{1})) := by
      intro r
      exact (Subalgebra.mem_comap _ _ _).mp (by rw [hcomap]; trivial)
    rw [← heq]
    exact div_mem (hmem p) (hmem q)
  have hxne : x ≠ 0 := by
    intro h0
    have h1 : algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) = 0 := by
      rw [show algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit) = x from rfl, h0]
    have h2 : (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ) = 0 :=
      IsFractionRing.injective (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (by rw [h1, map_zero])
    exact MvPolynomial.X_ne_zero PUnit.unit h2
  have hmem : x ∈ Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => x)) := by
    rw [hset]
    exact Algebra.subset_adjoin (Set.mem_singleton x)
  have hle : Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => x) ∪ {x, x⁻¹}) ≤
      Subalgebra.restrictScalars ℚ
        (Algebra.adjoin (MvPolynomial PUnit.{1} ℚ)
          ({(algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
              (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ))⁻¹}
            : Set (NoetherField ℚ PUnit.{1}))) := by
    rw [hset]
    refine Algebra.adjoin_le ?_
    rintro y (hy | hy)
    · rw [Set.mem_singleton_iff.mp hy]
      exact Subalgebra.algebraMap_mem _
        (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
    · rcases hy with rfl | rfl
      · exact Subalgebra.algebraMap_mem _
          (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
      · exact (Algebra.subset_adjoin (R := MvPolynomial PUnit.{1} ℚ)
          (Set.mem_singleton _))
  have hRG : ∀ (g : PUnit.{1})
      (r : ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})))
      (y : Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)),
      g • (r • y) = r • (g • y) := by
    intro g r y
    rw [Subsingleton.elim g 1, one_smul, one_smul]
  have hS0R : ∀ r : ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})),
      awayToFieldAlg (F := ℚ) (G := PUnit.{1})
          (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
          (MvPolynomial.X_ne_zero PUnit.unit)
          (algebraMap ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
            (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) r)
        = algebraMap ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
            (NoetherField ℚ PUnit.{1}) r := by
    intro r
    have h2 : awayAlgEquivAdjoin_pUnit_rat (awayAlgEquivAdjoin_pUnit_rat.symm r) = r :=
      awayAlgEquivAdjoin_pUnit_rat.apply_symm_apply r
    calc awayToFieldAlg (F := ℚ) (G := PUnit.{1})
          (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
          (MvPolynomial.X_ne_zero PUnit.unit)
          (algebraMap ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
            (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) r)
        = awayToFieldAlg (F := ℚ) (G := PUnit.{1})
            (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
            (MvPolynomial.X_ne_zero PUnit.unit)
            (awayAlgEquivAdjoin_pUnit_rat.symm r) := rfl
      _ = (awayAlgEquivAdjoin_pUnit_rat (awayAlgEquivAdjoin_pUnit_rat.symm r)
            : NoetherField ℚ PUnit.{1}) := rfl
      _ = (r : NoetherField ℚ PUnit.{1}) := by rw [h2]
      _ = algebraMap ↥(Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
              algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))
            ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit),
                (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                  (MvPolynomial.X PUnit.unit))⁻¹}))
            (NoetherField ℚ PUnit.{1}) r := rfl
  exact nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin
    (F := ℚ) (G := PUnit.{1}) (a := fun _ : Fin 1 => x) (s₀ := x)
    (t := (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ))
    hind hgen hxne hmem
    (fun g i => by rw [smul_algebraMap_noether, smul_X_noether,
      congrArg MvPolynomial.X (Subsingleton.elim (g * PUnit.unit) PUnit.unit)])
    (fun g => by rw [smul_algebraMap_noether, smul_X_noether,
      congrArg MvPolynomial.X (Subsingleton.elim (g * PUnit.unit) PUnit.unit)])
    (MvPolynomial.X_ne_zero PUnit.unit)
    (fun g => by rw [smul_X_noether,
      congrArg MvPolynomial.X (Subsingleton.elim (g * PUnit.unit) PUnit.unit)])
    hle
    (fun (g : PUnit.{1}) (p : MvPolynomial PUnit.{1} ℚ) => by
      have h1 : noetherRingHom ℚ PUnit.{1} g = 1 := by
        rw [Subsingleton.elim g 1, map_one]
      have key := congrArg
        (fun e : MvPolynomial PUnit.{1} ℚ ≃+* MvPolynomial PUnit.{1} ℚ => e p) h1
      exact (congrArg (algebraMap (MvPolynomial PUnit.{1} ℚ)
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)))
        key).symm)
    hRG (isGaloisWithGroup_away_adjoin_pUnit_rat hRG)
    (fun _ => finite_projective_away_adjoin_pUnit_rat) hS0R (inferInstance : Infinite ℚ)

end
#print axioms isGaloisWithGroup_away_adjoin_pUnit_rat
#print axioms exists_wiringHypotheses_pUnit_rat
#print axioms nonempty_genericExtensionWitnessFieldFinite_pUnit_rat


/-! ## **§0 判据一族 · 第五条**：`GaloisProjectiveSectionHyp` 的 **F-代数档反驳**（第 250 轮）

**⚠ 位置说明** ✓：家族其余四件（① ② ③ ④ ✓）落在 `GaloisAlgebra_ABGV52` ✓；本件落在**本文件** ✓ ——
理由 ＝ **`GaloisAlgebra` 在 `FILES` 序中先于本文件** ✗ ⟹ 家族文件**看不见 r247 通用件** ✗
（`isGaloisWithGroup_of_subsingleton_of_surjective_algebraMap` ✓，本文件 `:1154` ✓；**实测** ✗）
⟹ 本件须落在**能同时看见二者**的文件 ✓（本文件 ＋ 新增 `import ABGV52.GaloisAlgebra_ABGV52` ✓）。 -/

section GaloisProjectiveSectionRefutation

/-- **反例的 `↥S`-结构** ✓：`Polynomial ℚ → ℚ` 取 **`X ↦ 0`** ✓（**`Polynomial.aeval 0`** ✓）——
**该结构不是全局实例** ✗（mathlib **无** `Algebra (Polynomial ℚ) ℚ` ✓，**实测** ✗）⟹ 须**节级 `local instance`** ✓。 -/
noncomputable local instance instA250 : Algebra (Polynomial ℚ) ℚ :=
  (Polynomial.aeval (0 : ℚ)).toRingHom.toAlgebra

/-- **反例的 `G`-作用** ✓：**`G = PUnit`** ✓ 的**平凡作用** ✓ —— 同为**非全局实例** ✗（**实测** ✗）。 -/
noncomputable local instance instMSA250 : MulSemiringAction PUnit.{1} ℚ :=
  { smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_zero := fun _ => rfl
    smul_add := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }

set_option maxHeartbeats 1000000 in
/-- **`GaloisProjectiveSectionHyp` 现形（`F`-代数档）的反驳** ✓✅（第 250 轮 ✓；**非空洞** ✓）：
存在 **`F = ℚ`** ✓、**`G = PUnit`** ✓、**`R = Polynomial ℚ`** ✓、**`S = ℚ`** ✓（**结构 `X ↦ 0`** ✓）、
**`M = Polynomial ℚ`** ✓、**`f` ＝ 结构映射** ✓，使 **`IsGaloisWithGroup R S G hRG` 成立** ✓ 而
**`GaloisProjectiveSectionHyp ℚ PUnit` 不成立** ✗ ⟹ **其「实体」不可证** ✗。
**⚠ 前件（非空洞 ✓）**：**r247 通用件** ✓（**`G` 单点** ✓ ＋ **`algebraMap Polynomial ℚ ℚ` 满射** ✓ ——
**`q = aeval 0 (C q)`** ✓）⟹ **`IsGaloisWithGroup` 成立** ✓。
**⚠ 反驳步** ✓：设 **`p := δ 1`** ✓ ⟹ **`1 = f p`** ✓（截面条件 ✓）与
**`X * p = δ (X • 1) = δ 0 = 0`** ✓（**`R`-线性** ✓ ＋ **`X • 1 = 0`** ✓）⟹
**`Polynomial ℚ` 是整环** ✓ ＋ **`X ≠ 0`** ✓ ⟹ **`p = 0`** ✓ ⟹ **`1 = f 0 = 0`** ✗（**`one_ne_zero`** ✓）。
**⚠ 工艺读数（须入纪律 ✓）**：本件是**首个须节级 `local instance` 的反驳件** ✓ ——
**`Algebra (Polynomial ℚ) ℚ`** ✓ 与 **`MulSemiringAction PUnit ℚ`** ✓ **皆非全局实例** ✗（**实测** ✗），
而反例的**参数 `hRG` 的类型含 `r • t`** ✓ ⟹ 须**节级实例**方能**写出陈述本身** ✓
（**结论内 `letI`** 按 §210.2 ① 记为由 linter 计警告 ✗ ⟹ **不用** ✗）。
**⚠ 意义** ✓：**§0 判据一族第五条收束** ✓（**① ② ③ ④ 反驳** ✗ ＋ **⑤ 反驳** ✗ ＋ **⑥ 未判定** ⚠）⟹
**§197.3「`F`-代数档不受波及」的旧口径作废** ✗ —— **`F`-代数档亦不能救截面存在性** ✗
（**连带**：**`Module.Finite`／`Module.Projective`** 在该档同样不能由判据推出 ✗）⟹
蓝图第 9 步的 **`hproj` 输入** ✓（`SaltLem12_ABGV52:274` ✓）须**按 ④ 的先例「在预期用例上重建」** ✓。
**⚠ 不声称** ✗：**不**声称**预期用例**（源侧 `S'/R` 为 `G`-Galois ✓ ＋ 局部化 ✓）中截面不存在 ✗
（**相反** ✓ —— 那是源侧断言 ✓，**未落** ✗）；**`R[G]`-投射性** ✗ 与 **`proposition-0-2(b)`** ✗ 不在本件射程 ✓。 -/
theorem galoisProjectiveSectionHyp_refuted :
    ∃ hRG : ∀ (g : PUnit.{1}) (r : Polynomial ℚ) (t : ℚ), g • (r • t) = r • (g • t),
      BTier.IsGaloisWithGroup (Polynomial ℚ) ℚ PUnit.{1} hRG ∧
        ¬ BTier.GaloisProjectiveSectionHyp ℚ PUnit.{1} := by
  let _instT : IsScalarTower ℚ (Polynomial ℚ) ℚ :=
    IsScalarTower.of_algebraMap_eq (fun q => by
      show q = Polynomial.aeval (0 : ℚ) (Polynomial.C q)
      simp)
  let hRG : ∀ (g : PUnit.{1}) (r : Polynomial ℚ) (t : ℚ), g • (r • t) = r • (g • t) :=
    fun g r t => rfl
  have hsurj : Function.Surjective (algebraMap (Polynomial ℚ) ℚ) := by
    intro q
    exact ⟨Polynomial.C q, by
      show Polynomial.aeval (0 : ℚ) (Polynomial.C q) = q
      simp⟩
  have hgal : BTier.IsGaloisWithGroup (Polynomial ℚ) ℚ PUnit.{1} hRG :=
    isGaloisWithGroup_of_subsingleton_of_surjective_algebraMap (G := PUnit.{1}) hsurj hRG
  refine ⟨hRG, hgal, fun h => ?_⟩
  obtain ⟨δ, hδ, _hδg⟩ :=
    h (R := Polynomial ℚ) (S := ℚ) hRG hgal (M := Polynomial ℚ)
      (Algebra.linearMap (Polynomial ℚ) ℚ)
      (fun g m => rfl)
      (fun s => hsurj s)
  have hf1 : algebraMap (Polynomial ℚ) ℚ (δ 1) = 1 := hδ 1
  have hX1 : (Polynomial.X : Polynomial ℚ) • (1 : ℚ) = 0 := by
    rw [Algebra.smul_def]
    show Polynomial.aeval (0 : ℚ) Polynomial.X * 1 = 0
    simp
  have hp : (Polynomial.X : Polynomial ℚ) * δ 1 = 0 := by
    calc (Polynomial.X : Polynomial ℚ) * δ 1
        = (Polynomial.X : Polynomial ℚ) • δ 1 := rfl
      _ = δ ((Polynomial.X : Polynomial ℚ) • (1 : ℚ)) := (map_smul δ _ _).symm
      _ = δ 0 := by rw [hX1]
      _ = 0 := map_zero δ
  have hXne : (Polynomial.X : Polynomial ℚ) ≠ 0 := Polynomial.X_ne_zero
  have hzero : δ 1 = 0 := by
    rcases mul_eq_zero.mp hp with h' | h'
    · exact absurd h' hXne
    · exact h'
  have hone : (1 : ℚ) = 0 := by
    rw [← hf1, hzero, map_zero]
  exact one_ne_zero hone

end GaloisProjectiveSectionRefutation

#print axioms galoisProjectiveSectionHyp_refuted


/-! ## **⑥ 的判定 · 反例实例 ＋ 关键引理**（第 251 轮）

**靶点** ✓：⚠ **⑥ `GaloisDescentHyp` ＋ `GaloisFiniteGenerationDescentHyp` 的真值判定** ✓。
**⚠ 本轮结果** ✓：**归约** ✓ —— **反例实例已落** ✓（其 **Galois 谓词成立** ✓）＋ **关键引理已落** ✓
（**有限生成 ⟹ 只涉及有限多个变量** ✓）；**余下一步 ＝ 张量／基变换 ＋ 维数** ✗（**登记** ✓）。
**⚠ 位置** ✓：同 §250 的反驳件 ✓（`GaloisAlgebra` 先于本文件 ⟹ 家族文件看不见 r247 通用件 ✗）。 -/

section GaloisDescentHypRefutation

/-- **反例实例的结构映射** ✓：**`MvPolynomial ℕ ℚ → ℚ`** ✓ 取 **所有坐标 ＝ 1 的点** ✓（**`aeval (fun _ => 1)`** ✓）。
**⚠ 选点理由** ✓：**无穷多个坐标非零** ✓ ⟹ 其**核（极大理想）不有限生成** ✗
（**有限个坐标非零** ✓ 时核 ＝ **`(X_1,…,X_N)`** ✓ **有限生成** ✓ ⟹ **另选点** ✓）；
**该结构不是全局实例** ✗（**实测** ✗）⟹ **节级 `local instance`** ✓。 -/
noncomputable local instance instA251 : Algebra (MvPolynomial ℕ ℚ) ℚ :=
  (MvPolynomial.aeval (fun _ : ℕ => (1 : ℚ))).toRingHom.toAlgebra

/-- **反例实例的 `G`-作用** ✓：**`G = PUnit`** ✓ 的**平凡作用** ✓（**非全局实例** ✗）。 -/
noncomputable local instance instMSA251 : MulSemiringAction PUnit.{1} ℚ :=
  { smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_zero := fun _ => rfl
    smul_add := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }

/-- **反例实例的前件成立** ✓✅（第 251 轮 ✓）：**`IsGaloisWithGroup (MvPolynomial ℕ ℚ) ℚ PUnit hRG`** ✓
（**任意 `hRG`** ✓）—— 由 **r247 通用件** ✓（**`G` 单点** ✓ ＋ **`algebraMap` 满射** ✓：
**`q = aeval (fun _ => 1) (C q)`** ✓）。
**⚠ 意义** ✓：**⑥ 的两个端点在这一实例上都有前件** ✓ ⟹ **该实例是判定 ⑥ 的合法试验台** ✓。 -/
theorem exists_isGaloisWithGroup_mvPolynomial_allOnes :
    ∃ hRG : ∀ (g : PUnit.{1}) (r : MvPolynomial ℕ ℚ) (t : ℚ),
      g • (r • t) = r • (g • t),
      BTier.IsGaloisWithGroup (MvPolynomial ℕ ℚ) ℚ PUnit.{1} hRG :=
  ⟨fun g r t => rfl,
    isGaloisWithGroup_of_subsingleton_of_surjective_algebraMap (G := PUnit.{1})
      (by
        intro q
        exact ⟨MvPolynomial.C q, by
          show MvPolynomial.aeval (fun _ : ℕ => (1 : ℚ)) (MvPolynomial.C q) = q
          simp⟩)
      _⟩

/-- **关键引理（⑥ 反驳的桥）** ✓✅（第 251 轮 ✓；**自造件** ✓）：**有限生成 `ℚ`-代数** ✓ 打到
**`MvPolynomial ℕ ℚ`** ✓ 的**像只涉及有限多个变量** ✓ —— 即 **∃ `n`，像 ⊆ `ℚ[X_0,…,X_{n-1}]`** ✓。
**⚠ 证明** ✓：**`Algebra.FiniteType.out`** ✓ 给**有限生成集** ✓（`Subalgebra.fg_def` ✓）⟹
**像 ⊆ `adjoin ℚ (φ '' t)`** ✓（**`AlgHom.map_adjoin`** ✓）⟹ **每个生成元的支撑有限** ✓
（**`Finset.sup`** ✓ 取上界 ✓）⟹ **逐项按 `as_sum` ＋ `monomial_eq` 展开即入 `adjoin`** ✓。
**⚠ 用途** ✓：**任何候选 `R''`（有限生成 ✓）的像都落在有限多个变量的子代数里** ✓ ⟹
**张量 `S'' ⊗_{R''} R` 仍带无穷多个自由变量** ✓ ⟹ **不可能 ≅ ℚ** ✗（**余下一步** ✗）。 -/
theorem exists_variables_bound_of_finiteType (R'' : Type) [CommRing R'']
    [Algebra ℚ R''] [Algebra.FiniteType ℚ R''] (φ : R'' →ₐ[ℚ] MvPolynomial ℕ ℚ) :
    ∃ (n : ℕ), ∀ x : R'', φ x ∈ Algebra.adjoin ℚ
      (Set.range (fun i : Fin n => (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℚ))) := by
  classical
  obtain ⟨t, htfin, ht⟩ := Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := ℚ) (A := R''))
  let B : R'' → ℕ := fun a => (φ a).support.sup (fun m => m.support.sup fun i => i + 1)
  refine ⟨htfin.toFinset.sup B + 1, ?_⟩
  have hgen : ∀ a ∈ t, φ a ∈ Algebra.adjoin ℚ
      (Set.range (fun i : Fin (htfin.toFinset.sup B + 1) =>
        (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℚ))) := by
    intro a ha
    have hle : ∀ m ∈ (φ a).support, ∀ i ∈ m.support, i < htfin.toFinset.sup B + 1 := by
      intro m hm i hi
      have h1 : i < B a := lt_of_lt_of_le (Finset.le_sup (f := fun i => i + 1) hi)
        (Finset.le_sup (f := fun m => m.support.sup fun i => i + 1) hm)
      have h2 : B a ≤ htfin.toFinset.sup B := Finset.le_sup (htfin.mem_toFinset.mpr ha)
      omega
    rw [MvPolynomial.as_sum (φ a)]
    refine Subalgebra.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.monomial_eq]
    refine mul_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun i hi => ?_)
    exact Subalgebra.pow_mem _
      (Algebra.subset_adjoin (show (MvPolynomial.X i : MvPolynomial ℕ ℚ) ∈
        Set.range (fun j : Fin (htfin.toFinset.sup B + 1) =>
          (MvPolynomial.X (j : ℕ) : MvPolynomial ℕ ℚ)) from
        ⟨⟨i, hle m hm i hi⟩, rfl⟩)) _
  have himage : ∀ x : R'', φ x ∈ Algebra.adjoin ℚ (φ '' (t : Set R'')) := by
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (t : Set R'') := by rw [ht]; trivial
    have hx' : φ x ∈ Subalgebra.map φ (Algebra.adjoin ℚ (t : Set R'')) := ⟨x, hx, rfl⟩
    rwa [AlgHom.map_adjoin] at hx'
  intro x
  refine Algebra.adjoin_le ?_ (himage x)
  rintro _ ⟨a, ha, rfl⟩
  exact hgen a ha

/-- **登记** ✗：**⑥ 的反驳余下一步** ✓ —— **张量／基变换 ＋ 维数** ✗（**本轮未落** ✗）。
**⚠ 已备** ✓：**反例实例** ✓（`exists_isGaloisWithGroup_mvPolynomial_allOnes` ✓，**前件成立** ✓）
＋ **关键引理** ✓（`exists_variables_bound_of_finiteType` ✓，**像只涉及有限多变量** ✓）。
**⚠ 余步的精确形** ✓：设 **`R'' → R`** ✓ 的像 ⊆ **`R₀ := ℚ[X_0,…,X_{n-1}]`** ✓（**关键引理** ✓）；
则 **`S'' ⊗_{R''} R ≅ (S'' ⊗_{R''} R₀) ⊗_{R₀} R`** ✓（**张量结合** ✓）；
而 **`R ≅ MvPolynomial τ R₀`** ✓（**`τ := {m // n ≤ m}`** ✓；**`MvPolynomial.sumAlgEquiv`** ✓ ＋ **重标号** ✓）
⟹ **`S'' ⊗_{R''} R ≅ MvPolynomial τ (S'' ⊗_{R''} R₀)`** ✓（**`MvPolynomial.algebraTensorAlgEquiv`** ✓）
⟹ **`τ ≠ ∅`** ✓ ⟹ **若首因子 ≠ 0 则 `ℚ`-维 ≥ 2** ✗，**若 ＝ 0 则张量 ＝ 0** ✗ ⟹ **皆 ≇ ℚ** ✗
（**`MvPolynomial.basisMonomials`** ✓ 给基 ✓ ⟹ **`1` 与 `X_m` 线性无关** ✓）。
**⚠ 不声称** ✗：**⑥ 未判定** ✗（**只到归约** ✓）；**不**声称两个端点为假 ✗（**余步未落** ✗）；
**不**声称预期用例中下降不成立 ✗。 -/
theorem galoisDescentHyp_reduction_registered : True := trivial

end GaloisDescentHypRefutation

#print axioms exists_isGaloisWithGroup_mvPolynomial_allOnes
#print axioms exists_variables_bound_of_finiteType
#print axioms galoisDescentHyp_reduction_registered


/-! ## **⑥ 的余步 · 第 5 步（维数）落库**（第 252 轮）

**⚠ 本轮落** ✓：§213.3 的**第 5 步**（**「`MvPolynomial τ T` 永不 `≅ ℚ`」** ✓）；
**余** ✗：**第 2–4 步**（**张量结合** ✓ ＝ **`Algebra.TensorProduct.assoc`** ✓ **已实测在库** ✓；
**`R ≅ MvPolynomial τ R₀` 的 `R₀`-代数搬运** ✗）。 -/

section GaloisDescentHypTensorStep

/-- **维数步（⑥ 反驳的第 5 步）** ✓✅（第 252 轮 ✓；**自造件** ✓）：**非平凡 `ℚ`-代数 `T`** ✓ 上
**非空变量集 `σ`** ✓ 的**多项式环不 `≅ ℚ`** ✓ —— 即 **`¬ Nonempty (MvPolynomial σ T ≃ₐ[ℚ] ℚ)`** ✓。
**⚠ 证明（两分支 ✓）** ✓：设 **`φ`** ✓ 为该同构 ✓、取 **`m : σ`** ✓；
**若 `φ (X m) = 0`** ✓ ⟹ **`X m = 0`** ✗（**`φ.injective`** ✓ ＋ **`X_ne_zero`** ✓）矛盾 ✓；
**若 `φ (X m) ≠ 0`** ✓ ⟹ **`X m = C (algebraMap ℚ T (φ (X m)))`** ✓（**`φ.commutes`** ✓）
⟹ 取 **`coeff (single m 1)`** ✓ 两侧：**左 ＝ 1** ✓（**`coeff_X_same`** ✓）、**右 ＝ 0** ✓
（**`coeff_C`** ✓ ＋ **`single m 1 ≠ 0`** ✓）⟹ **`1 = 0`** ✗（**`one_ne_zero`** ✓）。
**⚠ 用途** ✓：**⑥ 的余步（张量／基变换）一旦把张量写成 `MvPolynomial τ T`（`τ` 非空 ✓）** ✓，
本条**立即给出 ≇ ℚ** ✗ ⟹ **⑥ 两端点同时被反驳** ✗。 -/
theorem not_nonempty_algEquiv_rat_of_mvPolynomial (T : Type) [CommRing T] [Algebra ℚ T]
    [Nontrivial T] (σ : Type) [Nonempty σ] :
    ¬ Nonempty (MvPolynomial σ T ≃ₐ[ℚ] ℚ) := by
  classical
  rintro ⟨φ⟩
  obtain ⟨m⟩ := ‹Nonempty σ›
  have hX : φ (MvPolynomial.X m) ≠ 0 := by
    intro h
    exact MvPolynomial.X_ne_zero m (φ.injective (by rw [h, map_zero]))
  have hfix : MvPolynomial.X m
      = MvPolynomial.C (algebraMap ℚ T (φ (MvPolynomial.X m))) := by
    have hC : MvPolynomial.C (algebraMap ℚ T (φ (MvPolynomial.X m)))
        = algebraMap ℚ (MvPolynomial σ T) (φ (MvPolynomial.X m)) := by
      rw [MvPolynomial.C_eq_algebraMap, IsScalarTower.algebraMap_apply ℚ T (MvPolynomial σ T)]
    apply φ.injective
    rw [hC, φ.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hc := congrArg (fun p => p.coeff (Finsupp.single m 1)) hfix
  rw [MvPolynomial.coeff_X_same, MvPolynomial.coeff_C] at hc
  have hne : ¬ (0 = Finsupp.single m 1) := by
    intro h0
    have h1 : (1 : ℕ) = 0 := Finsupp.single_eq_zero.mp h0.symm
    exact one_ne_zero h1
  rw [if_neg hne] at hc
  exact one_ne_zero hc

/-- **登记** ✗：**⑥ 反例余下的第 2–4 步** ✓ —— **张量结合 ＋ `R₀`-代数搬运 ＋ 基变换** ✗。
**⚠ 已 `#check` 实测在库** ✓（**故非「须自造」** ✓）：**`Algebra.TensorProduct.assoc`** ✓
（**`≃ₐ` 形** ✓）、**`MvPolynomial.algebraTensorAlgEquiv`** ✓、**`MvPolynomial.sumAlgEquiv`** ✓、
**`MvPolynomial.renameEquiv`** ✓。
**⚠ 余步的形** ✓：**像 ⊆ `R₀`** ✓ ⟹ **`S'' ⊗_{R''} R ≅ S'' ⊗_{R''} R₀ ⊗_{R₀} R`** ✓（结合 ✓）
⟹ **`R ≅ₐ[R₀] MvPolynomial τ R₀`** ✓（**`τ := {m : ℕ // n ≤ m}`** ✓）⟹
**`≅ MvPolynomial τ (S'' ⊗_{R''} R₀)`** ✓（基变换 ✓）⟹ **本条（第 5 步）给出 ≇ ℚ** ✗。
**⚠ 不声称** ✗：**⑥ 未判定** ✗；**不**声称两端点为假 ✗。 -/
theorem galoisDescentHyp_tensorStep_registered : True := trivial

end GaloisDescentHypTensorStep

#print axioms not_nonempty_algEquiv_rat_of_mvPolynomial
#print axioms galoisDescentHyp_tensorStep_registered

/-! ## **⑥ 第二端点 `GaloisFiniteGenerationDescentHyp ℚ PUnit.{1}` 的机器反驳**（第 253 轮）

**靶点** ✓：`BTier.GaloisFiniteGenerationDescentHyp ℚ PUnit.{1}` ✓（`GaloisAlgebra_ABGV52.lean:591` ✓）。
**⚠ 位置** ✓：本文件**先于**家族文件 ✓，故 ⑥ 的判定件只能落在此处 ✓（同 §251／§252 两件 ✓）。

**本轮落** ✓✅：① **结构引理** ✓ `mvPolynomial_algEquiv_adjoinR253` ✓
（`R ≅ₐ[R₀] MvPolynomial τ R₀` ✓，`R₀ := ℚ[X_0,…,X_{n-1}]` ✓）；② **端点反驳** ✓
`galoisFiniteGenerationDescentHyp_refuted` ✓ —— 即 **⑥ 的第二端点现形为假** ✗。
**⚠ 不声称** ✗：**不**声称源 `[Sal78b]` 的下降陈述为假 ✗；**不**声称第一端点 `GaloisDescentHyp`
已判定 ✗（其反驳**未落** ✗，见本条**不声称**款 ✓）。 -/

section GaloisFiniteGenerationDescentHypRefuted

/-- **反例实例的结构映射** ✓：`MvPolynomial ℕ ℚ → ℚ` 取**所有坐标 ＝ 1 的点** ✓（复用 §251 的档 ✓）。 -/
noncomputable local instance instA253 : Algebra (MvPolynomial ℕ ℚ) ℚ :=
  (MvPolynomial.aeval (fun _ : ℕ => (1 : ℚ))).toRingHom.toAlgebra

/-- **反例实例的 `G`-作用** ✓：`G = PUnit.{1}` 的**平凡作用** ✓（复用 §251 的档 ✓）。 -/
noncomputable local instance instMSA253 : MulSemiringAction PUnit.{1} ℚ :=
  { smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_zero := fun _ => rfl
    smul_add := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }

/-! ### 1. 结构引理：`R ≅ₐ[R₀] MvPolynomial τ R₀` ✓ -/

/-- **`τ`**：下标 **≥ `n`** 的变量集 ✓ —— 即 `R₀` **之外**的变量 ✓。 -/
abbrev tauR253 (n : ℕ) := {m : ℕ // n ≤ m}

/-- **`R₀ := ℚ[X_0,…,X_{n-1}]`** ✓：`R` 中**前 `n` 个变量**生成的 `ℚ`-子代数 ✓。 -/
abbrev adjoinR253 (n : ℕ) : Subalgebra ℚ (MvPolynomial ℕ ℚ) :=
  Algebra.adjoin ℚ (Set.range (fun i : Fin n => (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℚ)))

variable {n : ℕ}

/-- **前 `n` 个变量属于 `R₀`** ✓（`i : Fin n` ✓）。 -/
lemma X_mem_adjoinR253 (i : Fin n) :
    (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℚ) ∈ adjoinR253 n :=
  Algebra.subset_adjoin ⟨i, rfl⟩

/-- **前向映射** ✓：`MvPolynomial τ R₀ →ₐ[R₀] R` ✓（`X ⟨m,h⟩ ↦ X m` ✓，`τ`-变量保持 ✓）。 -/
def toR253 : MvPolynomial (tauR253 n) ↥(adjoinR253 n) →ₐ[↥(adjoinR253 n)] MvPolynomial ℕ ℚ :=
  MvPolynomial.aeval (fun m : tauR253 n => (MvPolynomial.X (m : ℕ) : MvPolynomial ℕ ℚ))

/-- **回缩 `ρ`** ✓：`R →ₐ[ℚ] MvPolynomial τ R₀` ✓ —— **前 `n` 个变量送进系数环** ✓、
**`τ`-变量保持** ✓。**用途** ✓：证 `toR253` **单** ✓（`ρ ∘ toR253 = id` ✓）。 -/
def rhoR253 : MvPolynomial ℕ ℚ →ₐ[ℚ] MvPolynomial (tauR253 n) ↥(adjoinR253 n) :=
  MvPolynomial.aeval (fun i : ℕ =>
    if h : i < n then
      MvPolynomial.C (⟨MvPolynomial.X i, X_mem_adjoinR253 ⟨i, h⟩⟩ : ↥(adjoinR253 n))
    else MvPolynomial.X ⟨i, le_of_not_gt h⟩)

/-- `ρ` 在**小变量**上的取值 ✓（`i < n` ✓）。 -/
lemma rhoR253_X_lt (i : ℕ) (h : i < n) :
    rhoR253 (MvPolynomial.X i)
      = MvPolynomial.C (⟨MvPolynomial.X i, X_mem_adjoinR253 ⟨i, h⟩⟩ : ↥(adjoinR253 n)) := by
  rw [rhoR253, MvPolynomial.aeval_X]; simp [h]

/-- `ρ` 在 **`τ`-变量**上的取值 ✓（`n ≤ i` ✓）。 -/
lemma rhoR253_X_ge (i : ℕ) (h : n ≤ i) :
    rhoR253 (MvPolynomial.X i) = MvPolynomial.X (⟨i, h⟩ : tauR253 n) := by
  rw [rhoR253, MvPolynomial.aeval_X]
  simp [not_lt.mpr h]

/-- `toR253` 在 **`τ`-变量**上的取值 ✓。 -/
lemma toR253_X (m : tauR253 n) :
    toR253 (MvPolynomial.X m) = (MvPolynomial.X (m : ℕ) : MvPolynomial ℕ ℚ) := by
  rw [toR253, MvPolynomial.aeval_X]

/-- `toR253` 在**常多项式**上的取值 ✓。 -/
lemma toR253_C (a : ↥(adjoinR253 n)) :
    toR253 (MvPolynomial.C a) = (a : MvPolynomial ℕ ℚ) :=
  AlgHom.commutes toR253 a

/-- **`ρ` 固定 `R₀`** ✓：`ρ a = C a` ✓（`a : ↥R₀` ✓；对 `a ∈ adjoin ℚ (range X)` 归纳 ✓）。 -/
lemma rhoR253_fixes (a : ↥(adjoinR253 n)) :
    rhoR253 (a : MvPolynomial ℕ ℚ) = MvPolynomial.C a := by
  have key : ∀ x : MvPolynomial ℕ ℚ, ∀ (hx : x ∈ adjoinR253 n),
      rhoR253 x = MvPolynomial.C (⟨x, hx⟩ : ↥(adjoinR253 n)) := by
    intro x
    refine Algebra.adjoin_induction
      (p := fun x hx => rhoR253 x = MvPolynomial.C (⟨x, hx⟩ : ↥(adjoinR253 n))) ?_ ?_ ?_ ?_
    · rintro x ⟨i, rfl⟩
      rw [rhoR253_X_lt _ i.2]
    · intro q
      rw [AlgHom.commutes, MvPolynomial.C_eq_algebraMap,
        IsScalarTower.algebraMap_apply ℚ ↥(adjoinR253 n) (MvPolynomial (tauR253 n) ↥(adjoinR253 n))]
      exact congrArg MvPolynomial.C (Subtype.ext rfl)
    · intro x y hx hy ihx ihy
      rw [map_add, ihx, ihy]
      exact (map_add MvPolynomial.C _ _).symm
    · intro x y hx hy ihx ihy
      rw [map_mul, ihx, ihy]
      exact (map_mul MvPolynomial.C _ _).symm
  exact key a a.2

/-- **`ρ ∘ toR253 = id`** ✓（`MvPolynomial.induction_on` ✓：`C` 档 ✓／`+` 档 ✓／`*X` 档 ✓）。 -/
lemma rhoR253_toR253 (x : MvPolynomial (tauR253 n) ↥(adjoinR253 n)) : rhoR253 (toR253 x) = x := by
  induction x using MvPolynomial.induction_on with
  | C a => rw [toR253_C, rhoR253_fixes]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    have h2 : toR253 (MvPolynomial.X i) = (MvPolynomial.X (i : ℕ) : MvPolynomial ℕ ℚ) := toR253_X i
    rw [h2, rhoR253_X_ge _ i.2]

/-- **每个变量都在 `toR253` 的像里** ✓（`i < n` ✓ 取 `C ⟨X i,_⟩` ✓；`n ≤ i` ✓ 取 `X ⟨i,_⟩` ✓）。 -/
lemma X_mem_toR253_range (i : ℕ) :
    (MvPolynomial.X i : MvPolynomial ℕ ℚ) ∈ (toR253 (n := n)).range := by
  rcases lt_or_ge i n with h | h
  · exact ⟨MvPolynomial.C (⟨MvPolynomial.X i, X_mem_adjoinR253 ⟨i, h⟩⟩ : ↥(adjoinR253 n)),
      toR253_C _⟩
  · exact ⟨MvPolynomial.X (⟨i, h⟩ : tauR253 n), toR253_X ⟨i, h⟩⟩

/-- **`toR253` 双射** ✓：**单** ✓ 由 `ρ ∘ toR253 = id` ✓；**满** ✓ 由 `adjoin_range_X` ✓
（每个 `X i` 都在像里 ✓ ⟹ `⊤ = adjoin ℚ (range X) ≤ range` ✓）。 -/
theorem toR253_bijective : Function.Bijective (toR253 (n := n)) := by
  refine ⟨fun x y hxy => ?_, ?_⟩
  · rw [← rhoR253_toR253 x, hxy, rhoR253_toR253 y]
  · rw [← AlgHom.range_eq_top]
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin ℚ (Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have hle : Algebra.adjoin ℚ (Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ))
        ≤ (toR253 (n := n)).range.restrictScalars ℚ :=
      Algebra.adjoin_le (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        exact X_mem_toR253_range i)
    exact hle hy

/-- **结构引理** ✓✅（第 253 轮 ✓；**自造件** ✓）：**`R ≅ₐ[R₀] MvPolynomial τ R₀`** ✓ ——
即 `MvPolynomial ℕ ℚ` 是**以 `R₀` 为系数环、`τ`-变量为自由变量**的多项式环 ✓
（`R₀ := ℚ[X_0,…,X_{n-1}]` ✓、`τ := {m // n ≤ m}` ✓）。
**证明** ✓：**`toR253`** ✓（`X ⟨m,h⟩ ↦ X m` ✓）**双射** ✓ —— **单** ✓ 由显式回缩 `ρ` ✓
（`ρ ∘ toR253 = id` ✓）；**满** ✓ 由 `X i` 分两档落入像 ✓（`i < n` ✓ ／ `n ≤ i` ✓）
＋ `MvPolynomial.adjoin_range_X` ✓。
**用途** ✓：把 `S'' ⊗_{R''} R` 的**右因子**换成 `R₀ ⊗[ℚ] MvPolynomial τ ℚ` ✓，
配 **`MvPolynomial.algebraTensorAlgEquiv`** ✓ 得 `MvPolynomial τ (S'' ⊗_{R''} R₀)` ✓。
**⚠ 不声称** ✗：只声称**同构存在** ✓（不提自由基的具体写法 ✗）；**不**声称 `n` 最小 ✗。 -/
theorem mvPolynomial_algEquiv_adjoinR253 (n : ℕ) :
    Nonempty (MvPolynomial (tauR253 n) ↥(adjoinR253 n) ≃ₐ[↥(adjoinR253 n)] MvPolynomial ℕ ℚ) :=
  ⟨AlgEquiv.ofBijective toR253 toR253_bijective⟩

#print axioms mvPolynomial_algEquiv_adjoinR253

/-! ### 2. 端点反驳 ✓ -/

set_option maxHeartbeats 1000000 in
/-- **⑥ 第二端点的反驳** ✓✅（第 253 轮）：**`¬ BTier.GaloisFiniteGenerationDescentHyp ℚ PUnit.{1}`** ✓。
**反例实例** ✓：`F = ℚ` ✓、`G = PUnit.{1}` ✓、`R = MvPolynomial ℕ ℚ` ✓、`S = ℚ` ✓，
结构映射 ＝ **全 1 点** ✓（`aeval (fun _ => 1)` ✓）、`G` **平凡作用** ✓。
**证明骨架** ✓：设 `h` 为该端点 ✓，由 `exists_isGaloisWithGroup_mvPolynomial_allOnes` ✓ 取
`R''`／`S''` ✓ 与 **`ℚ ≃ₐ[ℚ] S'' ⊗_{R''} R`** ✓；① **有限生成 ⟹ 像只涉及有限多变量** ✓
（`exists_variables_bound_of_finiteType` ✓）⟹ `R'' → R` **过 `R₀`** ✓；② **结构引理** ✓
（`mvPolynomial_algEquiv_adjoinR253` ✓）⟹ **`R ≅ₐ[R₀] MvPolynomial τ R₀`** ✓；③ **张量结合** ✓
（`Algebra.TensorProduct.assoc` ✓）＋ **基变换** ✓（`MvPolynomial.algebraTensorAlgEquiv` ✓）
⟹ **`S'' ⊗_{R''} R ≅ₐ[ℚ] MvPolynomial τ (S'' ⊗_{R''} R₀)`** ✓；④ **`τ ≠ ∅`** ✓（`n ≤ n` ✓）；
**若 `T := S'' ⊗_{R''} R₀` 非平凡** ✓ ⟹ **`not_nonempty_algEquiv_rat_of_mvPolynomial`** ✓ 立得矛盾 ✓；
**若 `T` 平凡** ✓ ⟹ `MvPolynomial τ T` **平凡** ✓ ⟹ **`ℚ` 平凡** ✗ 矛盾 ✓（两档皆闭 ✓）。
**⚠ 不声称** ✗：**不**声称源 `[Sal78b]` 的下降陈述为假 ✗（本条只反驳**本工程 ⑥ 的具名端点** ✓）；
**不**声称第一端点 `GaloisDescentHyp` 已判定 ✗（**同一反例实例**与同一骨架**逐字可搬** ✓，
但其尾项为 `S ≃ₐ[F] S'' ⊗ R'' ⊗ R` 的**同形**①，**本轮未落** ✗，另立**余步** ✗）；
**不**声称反例在 `G` 非单点档成立 ✗。 -/
theorem galoisFiniteGenerationDescentHyp_refuted :
    ¬ BTier.GaloisFiniteGenerationDescentHyp ℚ PUnit.{1} := by
  intro h
  obtain ⟨hRG, hgal⟩ := exists_isGaloisWithGroup_mvPolynomial_allOnes
  obtain ⟨R'', hcR'', haR'', haR''R, hstR''R, hftR'', S'', hcS'', haS'', haR''S'',
    hstR''S'', hmsa'', hRG'', hgal'', ⟨e⟩⟩ := h (MvPolynomial ℕ ℚ) ℚ hRG hgal
  obtain ⟨n, hn⟩ := exists_variables_bound_of_finiteType R''
    (IsScalarTower.toAlgHom ℚ R'' (MvPolynomial ℕ ℚ))
  let R₀ : Subalgebra ℚ (MvPolynomial ℕ ℚ) := adjoinR253 n
  let τ := tauR253 n
  let ψ : R'' →ₐ[ℚ] MvPolynomial ℕ ℚ := IsScalarTower.toAlgHom ℚ R'' (MvPolynomial ℕ ℚ)
  have hψ : ∀ x : R'', ψ x ∈ R₀ := hn
  let ψ₀ : R'' →ₐ[ℚ] ↥R₀ := ψ.codRestrict R₀ hψ
  let _instA : Algebra R'' ↥R₀ := ψ₀.toRingHom.toAlgebra
  let _instST1 : IsScalarTower ℚ R'' ↥R₀ :=
    IsScalarTower.of_algebraMap_eq (fun a => (ψ₀.commutes a).symm)
  let _instST2 : IsScalarTower R'' ↥R₀ (MvPolynomial ℕ ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  let _instSCC1 : SMulCommClass ℚ R'' ↥R₀ :=
    ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  let _instST3 : IsScalarTower R'' ↥R₀ (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ) := inferInstance
  obtain ⟨θ⟩ := mvPolynomial_algEquiv_adjoinR253 n
  let θD : MvPolynomial ℕ ℚ ≃ₐ[↥R₀] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ) :=
    θ.symm.trans (MvPolynomial.algebraTensorAlgEquiv (R := ℚ) (A := ↥R₀) (σ := τ)).symm
  let θR'' : MvPolynomial ℕ ℚ ≃ₐ[R''] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ) :=
    AlgEquiv.restrictScalars R'' θD
  let step1 : (S'' ⊗[R''] MvPolynomial ℕ ℚ) ≃ₐ[R'']
      (S'' ⊗[R''] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S'' ≃ₐ[R''] S'') θR''
  let step2 : (S'' ⊗[R''] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ)) ≃ₐ[R'']
      ((S'' ⊗[R''] ↥R₀) ⊗[ℚ] MvPolynomial τ ℚ) :=
    (Algebra.TensorProduct.assoc (R := ℚ) (S := R'') (T := R'') (A := S'') (C := ↥R₀)
      (D := MvPolynomial τ ℚ)).symm
  let step3 : ((S'' ⊗[R''] ↥R₀) ⊗[ℚ] MvPolynomial τ ℚ) ≃ₐ[ℚ]
      MvPolynomial τ (S'' ⊗[R''] ↥R₀) :=
    (MvPolynomial.algebraTensorAlgEquiv (R := ℚ) (A := S'' ⊗[R''] ↥R₀) (σ := τ)).restrictScalars ℚ
  have hcomp : ℚ ≃ₐ[ℚ] MvPolynomial τ (S'' ⊗[R''] ↥R₀) :=
    e.trans (((step1.trans step2).restrictScalars ℚ).trans step3)
  by_cases hT : Nontrivial (S'' ⊗[R''] ↥R₀)
  · exact @not_nonempty_algEquiv_rat_of_mvPolynomial (S'' ⊗[R''] ↥R₀) _ _ hT τ
      ⟨⟨n, le_rfl⟩⟩ ⟨hcomp.symm⟩
  · have hTsub : Subsingleton (S'' ⊗[R''] ↥R₀) := not_nontrivial_iff_subsingleton.mp hT
    let _instSub : Subsingleton (MvPolynomial τ (S'' ⊗[R''] ↥R₀)) := inferInstance
    exact one_ne_zero (hcomp.injective (Subsingleton.elim (hcomp 1) (hcomp 0)))

#print axioms galoisFiniteGenerationDescentHyp_refuted

end GaloisFiniteGenerationDescentHypRefuted


/-! ## **⑥ 第一端点 `GaloisDescentHyp ℚ PUnit.{1}` 的机器反驳**（第 254 轮）

**靶点** ✓：`BTier.GaloisDescentHyp ℚ PUnit.{1}` ✓（`GaloisAlgebra_ABGV52.lean:497` ✓）。
**⚠ 位置** ✓：本文件**先于**家族文件 ✓，故 ⑥ 的判定件只能落在此处 ✓（同 §251／§252／§253 三件 ✓）。

**本轮落** ✓✅：`galoisDescentHyp_refuted` ✓ —— 即 **⑥ 的第一端点现形为假** ✗；
与第 253 轮的第二端点 ✓ 合，**⑥ 的两个具名端点均已判定为假** ✗。
**⚠ 复用** ✓（**不重定义** ✗）：结构引理 `mvPolynomial_algEquiv_adjoinR253` ✓（`:1938` ✓）、
维数步 `not_nonempty_algEquiv_rat_of_mvPolynomial` ✓（`:1754` ✓）、反例实例
`exists_isGaloisWithGroup_mvPolynomial_allOnes` ✓（`:1660` ✓）、变量界
`exists_variables_bound_of_finiteType` ✓（`:1680` ✓）。

**⚠ 与第二端点的两处差别** ✓：**①** `GaloisDescentHyp` 对 `R' : Subalgebra F R` **全称量化** ✓
⟹ 反驳取 **`R' := ⊥`** ✓（**一个**特例即足以反驳全称形 ✓）；**②** 结论**只**给
`Algebra.FiniteType ↥⊥ R''` ✓ 而**不给** `Algebra.FiniteType ℚ R''` ✗ ⟹ 须先做**基变换** ✓
（定理体第 ① 步 ✓）。**其余骨架逐字可搬** ✓（张量结合 ✓／基变换 ✓／`τ ≠ ∅` ✓／两档收口 ✓）。

**⚠ 不声称** ✗：**不**声称源 `[Sal78b]`（印 528 ✓）的下降陈述为假 ✗；**不**声称 `G` **非单点**档
成立 ✗；**不**声称预期用例（如 `R' ⊆ R` 上有限型 ✓）中下降不成立 ✗。 -/

section GaloisDescentHypRefuted

/-- **反例实例的结构映射** ✓：`MvPolynomial ℕ ℚ → ℚ` 取**所有坐标 ＝ 1 的点** ✓
（**复用 §251 的档** ✓；**该结构不是全局实例** ✗ ⟹ **节级 `local instance`** ✓）。 -/
noncomputable local instance instA254 : Algebra (MvPolynomial ℕ ℚ) ℚ :=
  (MvPolynomial.aeval (fun _ : ℕ => (1 : ℚ))).toRingHom.toAlgebra

/-- **反例实例的 `G`-作用** ✓：`G = PUnit.{1}` 的**平凡作用** ✓（**复用 §251 的档** ✓）。 -/
noncomputable local instance instMSA254 : MulSemiringAction PUnit.{1} ℚ :=
  { smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_zero := fun _ => rfl
    smul_add := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }

/-! ### 端点反驳 ✓ -/

set_option maxHeartbeats 1000000 in
/-- **⑥ 第一端点的反驳** ✓✅（第 254 轮）：**`¬ BTier.GaloisDescentHyp ℚ PUnit.{1}`** ✓。
**反例实例** ✓：`F = ℚ` ✓、`G = PUnit.{1}` ✓、`R = MvPolynomial ℕ ℚ` ✓、`S = ℚ` ✓，
结构映射 ＝ **全 1 点** ✓、`G` **平凡作用** ✓（与第 253 轮**同一实例** ✓）；`R'` 取 **`⊥`** ✓。
**证明骨架** ✓：设 `h` 为该端点 ✓，由 `exists_isGaloisWithGroup_mvPolynomial_allOnes` ✓ 取
`R''`／`S''` ✓ 与 **`ℚ ≃ₐ[ℚ] S'' ⊗_{R''} R`** ✓；① **基变换** ✓：`R' = ⊥` ⟹
**`algebraMap ℚ ↥⊥` 满** ✓（`Algebra.mem_bot` ✓ 逐元素给原像 ✓）⟹ **`Algebra.FiniteType ℚ ↥⊥`** ✓
（`Algebra.FiniteType.of_surjective` ✓）⟹ **`Algebra.FiniteType ℚ R''`** ✓
（`Algebra.FiniteType.trans` ✓ ＋ 结论给的 **`IsScalarTower ℚ ↥⊥ R''`** ✓）；
② **有限生成 ⟹ 像只涉及有限多变量** ✓（`exists_variables_bound_of_finiteType` ✓）
⟹ `R'' → R` **过 `R₀`** ✓（`R₀ := ℚ[X_0,…,X_{n-1}]` ✓）；③ **结构引理** ✓
（`mvPolynomial_algEquiv_adjoinR253` ✓ ⟹ **`R ≅ₐ[R₀] MvPolynomial τ R₀`** ✓）＋ **张量结合** ✓
（`Algebra.TensorProduct.assoc` ✓）＋ **基变换** ✓（`MvPolynomial.algebraTensorAlgEquiv` ✓）
⟹ **`S'' ⊗_{R''} R ≅ₐ[ℚ] MvPolynomial τ (S'' ⊗_{R''} R₀)`** ✓；
④ **`τ ≠ ∅`** ✓（`⟨n, le_rfl⟩` ✓）；**若 `T := S'' ⊗_{R''} R₀` 非平凡** ✓ ⟹
**`not_nonempty_algEquiv_rat_of_mvPolynomial`** ✓ 立得矛盾 ✓；**若 `T` 平凡** ✓ ⟹ `MvPolynomial τ T`
**平凡** ✓ ⟹ **`ℚ` 平凡** ✗ 矛盾 ✓（两档皆闭 ✓）。
**未用输入** ✓：结论给的 `Function.Injective (algebraMap R'' S'')` ✓ 与
`IsGaloisWithGroup R'' S'' G hRG''` ✓ **在本骨架中不用** ✓（**登记** ✓）。
**⚠ 不声称** ✗：**不**声称源 `[Sal78b]` 的下降陈述为假 ✗ —— 本条**只**反驳**本工程 ⑥ 的具名端点** ✓，
且**只以 `R' = ⊥` 一档**反驳该全称形 ✓；**不**声称 `G` **非单点**档成立 ✗；
**不**声称该端点在**预期用例**（如 `R' ⊆ R` 上有限型 ✓）中为假 ✗。 -/
theorem galoisDescentHyp_refuted : ¬ BTier.GaloisDescentHyp ℚ PUnit.{1} := by
  intro h
  obtain ⟨hRG, hgal⟩ := exists_isGaloisWithGroup_mvPolynomial_allOnes
  obtain ⟨R'', hcR'', haR''F, haR''bot, hstBotR'', haR''R, hstFR'', hstBotR''R, hftBotR'',
    S'', hcS'', haS''F, haR''S'', hstR''S'', hinjR''S'', hmsa'', hRG'', hgal'', ⟨e⟩⟩ :=
    h (MvPolynomial ℕ ℚ) ℚ hRG hgal (⊥ : Subalgebra ℚ (MvPolynomial ℕ ℚ))
  have hsurjBot : Function.Surjective
      (algebraMap ℚ ↥(⊥ : Subalgebra ℚ (MvPolynomial ℕ ℚ))) := by
    intro x
    obtain ⟨q, hq⟩ := Set.mem_range.mp (Algebra.mem_bot.mp x.2)
    exact ⟨q, Subtype.ext hq⟩
  have hftBot : Algebra.FiniteType ℚ ↥(⊥ : Subalgebra ℚ (MvPolynomial ℕ ℚ)) :=
    Algebra.FiniteType.of_surjective
      (Algebra.ofId ℚ ↥(⊥ : Subalgebra ℚ (MvPolynomial ℕ ℚ))) hsurjBot
  let _instFT : Algebra.FiniteType ℚ R'' :=
    Algebra.FiniteType.trans (R := ℚ) (S := ↥(⊥ : Subalgebra ℚ (MvPolynomial ℕ ℚ)))
      (A := R'') hftBot hftBotR''
  obtain ⟨n, hn⟩ := exists_variables_bound_of_finiteType R''
    (IsScalarTower.toAlgHom ℚ R'' (MvPolynomial ℕ ℚ))
  let R₀ : Subalgebra ℚ (MvPolynomial ℕ ℚ) := adjoinR253 n
  let τ := tauR253 n
  let ψ : R'' →ₐ[ℚ] MvPolynomial ℕ ℚ := IsScalarTower.toAlgHom ℚ R'' (MvPolynomial ℕ ℚ)
  have hψ : ∀ x : R'', ψ x ∈ R₀ := hn
  let ψ₀ : R'' →ₐ[ℚ] ↥R₀ := ψ.codRestrict R₀ hψ
  let _instA : Algebra R'' ↥R₀ := ψ₀.toRingHom.toAlgebra
  let _instST1 : IsScalarTower ℚ R'' ↥R₀ :=
    IsScalarTower.of_algebraMap_eq (fun a => (ψ₀.commutes a).symm)
  let _instST2 : IsScalarTower R'' ↥R₀ (MvPolynomial ℕ ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  let _instSCC1 : SMulCommClass ℚ R'' ↥R₀ :=
    ⟨fun a b c => by simp only [Algebra.smul_def]; ring⟩
  let _instST3 : IsScalarTower R'' ↥R₀ (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ) := inferInstance
  obtain ⟨θ⟩ := mvPolynomial_algEquiv_adjoinR253 n
  let θD : MvPolynomial ℕ ℚ ≃ₐ[↥R₀] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ) :=
    θ.symm.trans (MvPolynomial.algebraTensorAlgEquiv (R := ℚ) (A := ↥R₀) (σ := τ)).symm
  let θR'' : MvPolynomial ℕ ℚ ≃ₐ[R''] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ) :=
    AlgEquiv.restrictScalars R'' θD
  let step1 : (S'' ⊗[R''] MvPolynomial ℕ ℚ) ≃ₐ[R'']
      (S'' ⊗[R''] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S'' ≃ₐ[R''] S'') θR''
  let step2 : (S'' ⊗[R''] (↥R₀ ⊗[ℚ] MvPolynomial τ ℚ)) ≃ₐ[R'']
      ((S'' ⊗[R''] ↥R₀) ⊗[ℚ] MvPolynomial τ ℚ) :=
    (Algebra.TensorProduct.assoc (R := ℚ) (S := R'') (T := R'') (A := S'') (C := ↥R₀)
      (D := MvPolynomial τ ℚ)).symm
  let step3 : ((S'' ⊗[R''] ↥R₀) ⊗[ℚ] MvPolynomial τ ℚ) ≃ₐ[ℚ]
      MvPolynomial τ (S'' ⊗[R''] ↥R₀) :=
    (MvPolynomial.algebraTensorAlgEquiv (R := ℚ) (A := S'' ⊗[R''] ↥R₀) (σ := τ)).restrictScalars ℚ
  have hcomp : ℚ ≃ₐ[ℚ] MvPolynomial τ (S'' ⊗[R''] ↥R₀) :=
    e.trans (((step1.trans step2).restrictScalars ℚ).trans step3)
  by_cases hT : Nontrivial (S'' ⊗[R''] ↥R₀)
  · exact @not_nonempty_algEquiv_rat_of_mvPolynomial (S'' ⊗[R''] ↥R₀) _ _ hT τ
      ⟨⟨n, le_rfl⟩⟩ ⟨hcomp.symm⟩
  · have hTsub : Subsingleton (S'' ⊗[R''] ↥R₀) := not_nontrivial_iff_subsingleton.mp hT
    let _instSub : Subsingleton (MvPolynomial τ (S'' ⊗[R''] ↥R₀)) := inferInstance
    exact one_ne_zero (hcomp.injective (Subsingleton.elim (hcomp 1) (hcomp 0)))

#print axioms galoisDescentHyp_refuted

end GaloisDescentHypRefuted


/-! ## **两条源陈述的具名残余归约**（第 259 轮）—— 环档桥 ＋ 两处归约 ＋ **已登记路线的空洞判定** ＋ 修正方向

**⚠ 起点** ✓（**承任务书** ✓）：两条**源陈述**仍未证 ✗ ——
`Theorem51Statement`（`SaltGeneric_ABGV52.lean:257` ✓）与 `Theorem21Statement`（同件 `:191` ✓）。
本轮**不**重证它们 ✗，而是把「还缺什么」落成**两个具名残余** ✓、把可达部分落库 ✓，
并对**已登记的 r206 路线**做 **L1 在住性判定** ✓。

**🔴 五件** ✓（探针 `.abgv52-scratch/probe-r259{e,f,h}.lean` ✓ **rc=0** ✓、**零警告** ✓）：
**①** **环档桥** ✓（`RealizationRingTierBridge` ✓）—— 两条源陈述**共用**的**唯一档位缺口** ✓：
`BTier.RealizationProperty` 的 `L` 量词是 **`[CommRing L]`** ✗，而库内装配链只供给
**`[Field L]` ＋ `[FiniteDimensional K L]`** ✓（§4.56 ✓，`RealizationPropertyFieldFinite` ✓）；
**②** **归约（`theorem-5-1`）** ✓：`NoetherWiringResidual` ✓（r206 表 ∃-打包）＋ 环档桥 ⟹ `Theorem51Statement` ✓；
**③** **归约（`theorem-2-1`）** ✓：`Thm21ClausesResidual` ✓（源 §2 构造，第三款取**有限域档** ✓）＋ 环档桥
⟹ `Theorem21Statement` ✓；
**④** **Noether 侧接线表的 10 行机器可造** ✓（`noetherWiringMachinery_of_sourceData` ✓）——
**解 r217／r227 登记的文件级实例障碍** ✓✅（`SaltLocalProj` 的 `locMulSemiringAction` 一族 ✗ 与本件 §4.4 的
`MvPolynomial` 作用 ✗ 此前**无文件同时可见** ✗；**本件两件皆见** ✓）；
**⑤** **路线空洞判定 ＋ 修正方向** ✓（**本轮主发现** ✓）：残余 ② 的**两行**（`hgen` ✗ 与 `ha_fix` ✗）
**不可同真** ✓ —— `subsingleton_of_fixed_generating` ✓（＋ Noether 作用的忠实性 ✓）⟹
`noetherWiringResidual_empty_of_nontrivial` ✓：**`G` 非平凡时该表为空** ✗ ⟹
**r206／§4.61 的端到端路线不可能达到源陈述** ✗；**修正方向** ✓ ＝ 把源侧数据取在**不动域 `L^G`** 上 ✓
（源文用法 ✓；库内 `exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver` ✓ 正是该形 ✓，
本轮落 `exists_fixed_transcendenceBasis_of_isRationalOver` ✓：**修正后的数据行由源假设直接产出** ✓✅）。

**⚠ 三条诚实账** ✓（逐条**机器核** ✓，非沿用旧注 ✗）：
**(i)** 源 `theorem-5-1` 的**结论**是**环档**见证 ✗（源印 254 ✓「`L` is not necessarily a field」✓）；
库内**可达**的是**有限域档** ✓（§4.56 ✓）⟹ 残余 ① **不可去** ✗（**除非**重建 CHR 代数版 ✗）；
**(ii)** 残余 ②（r206 表）**在 `G` 非平凡档为空** ✗（⑤ ✓）⟹ 归约 ② **对非平凡 `G` 空洞** ✗（**不声称**它是通路 ✗）；
**(iii)** 归约 ③ 的残余**非空洞** ✓（只要求三款齐备的载体存在 ✓）⟹ **`theorem-2-1` 侧的归约是本轮唯一非空洞者** ✓。

**🔴 不声称** ✗：**不**声称两条源陈述已证 ✗；**不**声称残余 ① 可去 ✗；**不**声称残余 ② 非空 ✗
（**已机器判空** ✗）；**不**声称 r206 表的**修正形**已组装 ✗（只落其**数据行** ✓，见 §D ✓）；
**不**声称 `genericExtensionWitnessFieldFinite_gap_registered` 一族旧注被改写 ✗（**留痕** ✓）。

**无 sorry、无自造公理** ✓；公理门见文末 ✓。 -/

/-! ### A. 残余 ①：(c) 款**环档桥**（两条源陈述共用） -/

section RingTierBridge

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G]

/-- **残余 ①（具名）**：(c) 款的**环档桥** ✓ —— 「**有限域档** `(c)` ⟹ **源形环档** `(c)`」✓。

**⚠ 为何是两条源陈述的公共残余** ✓：`GenericExtensionWitness.isGeneric` ✗ 与
`GenericExtensionWitnessFieldFinite.isGeneric` ✓ 的**前两款逐字相同** ✓（`(a)` 局部化多项式环 ✓／
`(b)` `IsGaloisWithGroup` ✓），**只差第三款** ✓；而**档位缺口**与 `F`／`G`／载体**无关** ✓
（缺口 ＝ 量词域的 `[Field L]` ✗ vs `[CommRing L]` ✗ ＋ 有限性 ✗，§4.53 ✓／§4.56 ✓）。

**⚠ 数学内容** ✓（**未落** ✗）：须**环上 Galois 理论（CHR 代数版）** ✓ —— 即「`L/K` `G`-Galois
⟹ `L` 是有限多个域的直和，且各分量 `G`-Galois」✓（源 `proposition-0-5` ✓ 印 254 明写
「`L` is the direct sum of fields」✓），再逐分量用**有限域档** `(c)` ✓ 拼回 ✓。
**⚠ 强度序（已落** ✓**）**：`realizationPropertyFieldFinite_of_realizationProperty` ✓ ——
**环档 ⟹ 有限域档** ✓（**逆未证** ✗，**登记** ✓）。
**🔴 不声称** ✗：**不**声称本残余可证 ✗（其**实体**＝ CHR 代数版 ✗，**未落** ✗）；
**不**声称其前件与结论等价 ✗（**只**落了**单向**强度序 ✓）。 -/
def RealizationRingTierBridge (F : Type) [Field F] (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S], RealizationPropertyFieldFinite F G R S → BTier.RealizationProperty F G R S

/-- **强度序（可证方向）** ✓：**环档 ⟹ 有限域档** ✓ —— 把有限域档的量词实例（含
`[Field L]` ＋ `[FiniteDimensional K L]` ✓）喂给环档形即可 ✓。
**⚠ 方向性** ✓：**逆方向**（有限域档 ⟹ 环档 ✗）**未证** ✗ —— 那**正是**残余 ① ✓。
**⚠ 判别力** ✓：本条 ＋ `RealizationRingTierBridge` ✓ 合读即「残余 ① 的**前件弱于**其结论」✓
（故残余 ① **不是** `Iff` 的同义反复 ✗）。 -/
theorem realizationPropertyFieldFinite_of_realizationProperty {R S : Type}
    [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S] [IsScalarTower F R S]
    (h : BTier.RealizationProperty F G R S) : RealizationPropertyFieldFinite F G R S := by
  intro K _ _ L _ _ _ _ _ _ hKL hgal
  exact h K L hKL hgal

/-- **(c) 款：有限域档 ＋ 残余 ① ⟹ 环档** ✓：`IsGenericExtension` 的**前两款逐字搬运** ✓
（`h.1` ✓／`h.2.1` ✓），第三款由桥填 ✓。
**⚠ 用途** ✓：残余 ②／③ 的归约**共用此件** ✓。
**🔴 不声称** ✗：**不**声称本件给出**无条件**的环档 `(c)` ✗（**前两款**本就在两档中相同 ✓，
本件**只**搬运它们 ✗）；**不**声称残余 ① 已证 ✗。 -/
theorem isGenericExtension_of_fieldFinite_and_ringBridge {R S : Type}
    [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S] [IsScalarTower F R S]
    [MulSemiringAction G S]
    {hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)}
    (hb : RealizationRingTierBridge F G) (h : IsGenericExtensionFieldFinite F G R S hRG) :
    BTier.IsGenericExtension F G R S hRG :=
  ⟨h.1, h.2.1, hb R S h.2.2⟩

/-- **见证层：有限档见证 ＋ 残余 ① ⟹ 源形见证** ✓：
`obtain` 出的**实例场**由结构字段自动注册 ✓（与 `SaltGeneric:5623` ✓ 的**反向件**同款工艺 ✓）。
**🔴 不声称** ✗：**不**声称有限档见证**存在** ✗（其存在性 ＝ 各档装配的事 ✓，本件**只**搬运 ✓）；
**不**声称残余 ① 已证 ✗。 -/
theorem nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge
    (hb : RealizationRingTierBridge F G)
    (h : Nonempty (GenericExtensionWitnessFieldFinite F G)) :
    Nonempty (GenericExtensionWitness F G) := by
  obtain ⟨R, S, hRG, hisg⟩ := h
  exact ⟨R, S, hRG, isGenericExtension_of_fieldFinite_and_ringBridge hb hisg⟩

/-- **结论侧核心** ✓：`Infinite F → Nonempty (GenericExtensionWitness F G)` ⟹ `Theorem51Statement F G` ✓。

**⚠ 意义（结构性观察** ✓**）**：源陈述的结论**不含 `L`** ✗ ⟹ 其 `L`-量词与 `IsRationalOver F L^G` 前提
在本步**闲置** ✓ —— 源侧它们是**数据的来源** ✓（不动域有理 ⟹ 数据 ✓），**不是结论的一部分** ✗
（**本轮发现 ⑤ 的修正方向** ✓ 正建在此观察上 ✓）。
**⚠ 不声称** ✗：**不**声称逆方向（`Theorem51Statement ⟹ 核心` ✗ —— 须先给一个满足前提的 `L` ✗）。 -/
theorem theorem51Statement_of_witness (h : Infinite F → Nonempty (GenericExtensionWitness F G)) :
    Theorem51Statement F G :=
  fun hinf _ _ _ _ _ _ => h hinf

#print axioms RealizationRingTierBridge
#print axioms realizationPropertyFieldFinite_of_realizationProperty
#print axioms isGenericExtension_of_fieldFinite_and_ringBridge
#print axioms nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge
#print axioms theorem51Statement_of_witness

end RingTierBridge

/-! ### B. 残余 ②：Noether 侧接线表（r206 假设表的 ∃-打包）＋ **归约（源 `theorem-5-1`）** -/

section NoetherWiringResidual

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **残余 ②（具名）**：**r206 定理**（`nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin` ✓，
`SaltGeneric_ABGV52.lean:5789` ✓）的**整张假设表**的 ∃-打包 ✓ ——
「**Noether 载体的接线数据存在**」✓（**与 `L` 无关** ✗，见 `theorem51Statement_of_witness` ✓）。

**⚠ 十八行** ✓（∃-绑定 9 行：`n` ✓／`a` ✓／`s₀` ✓／`t` ✓／三实例 ✓／`ht` ✓／`hRG` ✓；
合取 12 行：`hind` ✓／`hgen` ✓／`hs₀` ✓／`hs₀_mem` ✓／`ha_fix` ✓／`hs₀_fix` ✓／
`(∀ g, g • t = t)` ✓／`hle` ✓／`hact_map` ✓／`hgal` ✓／`hProj` ✓／`hS₀R` ✓）。
**逐行归类** ✓（**本轮实测** ✓）：**10 行机器可造** ✓（§C ✓）；**其余 8 行** ✗ ＝
源侧数据 6 行 ✗（`hind` ✓／`hgen` ✓／`hs₀` ✓／`hs₀_mem` ✓／`ha_fix` ✓／`hs₀_fix` ✓）
＋ 两具名端点 2 行 ✗（`hgal` ✓／`hProj` ✓）。
**🔴 且 `hgen` ＋ `ha_fix` 不可同真** ✗（**§D 机器判定** ✓）⟹ **本残余在 `G` 非平凡档为空** ✗
（**不声称**它是通路 ✗）。 -/
def NoetherWiringResidual (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    [DecidableEq G] : Prop :=
  ∃ (n : ℕ) (a : Fin n → NoetherField F G) (s₀ : NoetherField F G) (t : MvPolynomial G F)
    (_ : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t))
    (_ : IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t))
    (_ : MulSemiringAction G (Localization.Away t))
    (ht : t ≠ 0)
    (hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
      (x : Localization.Away t), g • (r • x) = r • (g • x)),
    AlgebraicIndependent F a ∧
      IntermediateField.adjoin F (Set.range a) = ⊤ ∧
      s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin F (Set.range a) ∧
      (∀ (g : G) (i : Fin n), g • a i = a i) ∧
      (∀ (g : G), g • s₀ = s₀) ∧
      (∀ g : G, g • t = t) ∧
      (Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)))) ∧
      (∀ (g : G) (p : MvPolynomial G F),
        g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
          = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p)) ∧
      BTier.IsGaloisWithGroup ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
        (Localization.Away t) G hRG ∧
      BTier.GaloisProjectiveHyp ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
        (Localization.Away t) G hRG ∧
      (∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
        awayToFieldAlg (F := F) (G := G) t ht
            (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
              (Localization.Away t) r)
          = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r)

set_option maxHeartbeats 1000000 in
/-- **归约（源 `theorem-5-1`）** ✓：**残余 ② ＋ 残余 ① ⟹ `Theorem51Statement F G`** ✓。

**⚠ 证明体（一句）** ✓：把残余 ② 的十八行**逐位喂给 r206** ✓（`nonempty_..._of_noetherAdjoin` ✓，
**不重证** ✓），得**有限档**见证 ✓；再经残余 ①（`nonempty_..._of_fieldFinite_and_ringBridge` ✓）
搬成**源形**见证 ✓。**⚠ `L` 与 `hL` 全程闲置** ✓（＝ `theorem51Statement_of_witness` ✓ 的观察 ✓）。
**🔴 不声称** ✗：**不**声称残余 ② 非空 ✗（**其空性见 §D** ✓）⟹ 本条对**非平凡 `G`** 是**条件式空洞** ✗；
**不**声称两条源陈述已证 ✗。 -/
theorem theorem51Statement_of_noetherWiringResidual_and_ringBridge
    (hb : RealizationRingTierBridge F G) (hw : NoetherWiringResidual F G) :
    Theorem51Statement F G := by
  intro hinf L _ _ _ _ _
  obtain ⟨n, a, s₀, t, instA, instT, instM, ht, hRG, hind, hgen, hs₀, hs₀_mem, ha_fix,
    hs₀_fix, htinv, hle, hact_map, hgal, hProj, hS₀R⟩ := hw
  exact nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge hb
    (nonempty_genericExtensionWitnessFieldFinite_of_noetherAdjoin hind hgen hs₀ hs₀_mem
      ha_fix hs₀_fix ht htinv hle hact_map hRG hgal hProj hS₀R hinf)

#print axioms NoetherWiringResidual
#print axioms theorem51Statement_of_noetherWiringResidual_and_ringBridge

end NoetherWiringResidual

/-! ### C. 残余 ③：`theorem-2-1` 侧（源 §2 构造 ＋ 有限域档 `(c)`）＋ **归约** -/

section Thm21Residual

/-- **残余 ③（具名）**：**源 §2 的构造** ✓ —— `SaltmanCondition A F` ⟹ 存在载体 `(R, S)` 使
**(a) 款** ✓ ＋ **(b) 款** ✓ ＋ **(c) 款取有限域档** ✓ 三款齐备 ✓。

**⚠ 与源 `theorem-2-1` 的差** ✓：**只差第三款的档位** ✓（源要**环档** ✓）⟹ 残余 ③ **弱于**源结论 ✓
（`realizationPropertyFieldFinite_of_realizationProperty` ✓ 给强度序 ✓）。
**⚠ 数学内容** ✓（**未落** ✗）：Saltman 1982 §2 的构造（`A` 有限交换 ＋ `2^r` 条件 ⟹ generic Galois
extension 存在 ✓，源印 257 `theorem-2-1` ✓）—— 库内**无任何**该构造件 ✗（`GenericExtensionWitness` ✓
此前**只在陈述侧**出现 ✓）。
**🔴 非空洞性** ✓：本残余**不**含 r206 表的两行冲突 ✗ ⟹ **非空洞** ✓（三款齐备的载体存在性本身不自相矛盾 ✓；
`A = PUnit` ✓ 档由 r249 ✓ 的见证**间接**支持 ✓ —— **⚠ 但 r249 的见证是有限档 ＋ 弱化档** ✗，**不**直接充当本残余 ✗）。 -/
def Thm21ClausesResidual (A : Type) [Group A] [Fintype A] (F : Type) [Field F] : Prop :=
  SaltmanCondition A F →
    ∃ (R S : Type) (_ : CommRing R) (_ : CommRing S) (_ : Algebra F R) (_ : Algebra R S)
      (_ : Algebra F S) (_ : IsScalarTower F R S) (_ : MulSemiringAction A S)
      (hRG : ∀ (g : A) (r : R) (t : S), g • (r • t) = r • (g • t)),
      (∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
        w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
      BTier.IsGaloisWithGroup R S A hRG ∧ RealizationPropertyFieldFinite F A R S

/-- **归约（源 `theorem-2-1`）** ✓：**残余 ③ ＋ 残余 ① ⟹ `Theorem21Statement A F`** ✓。

**⚠ 证明体** ✓：`SaltmanCondition` 前提交给残余 ③ ✓ ⟹ 取 `(R, S)` 与三款 ✓ ⟹
第三款经残余 ① 升为**环档** ✓ ⟹ 打包源形见证 ✓（`GenericExtensionWitness` ✓ 的**实例字段**由
`obtain` 出的实例注册 ✓）。
**⚠ 意义** ✓：本条是**本轮唯一非空洞**的归约 ✓（**不声称**残余 ③ 已证 ✗ —— 它是源 §2 的构造 ✗）。 -/
theorem theorem21Statement_of_clausesResidual_and_ringBridge
    (A : Type) [Group A] [Fintype A] (F : Type) [Field F]
    (hres : Thm21ClausesResidual A F) (hb : RealizationRingTierBridge F A) :
    Theorem21Statement A F := by
  intro hC
  obtain ⟨R, S, _hcR, _hcS, _haFR, _haRS, _haFS, _hst, _hmsa, hRG, ha, hgal, hc⟩ := hres hC
  exact ⟨R, S, hRG, ha, hgal, hb R S hc⟩

#print axioms Thm21ClausesResidual
#print axioms theorem21Statement_of_clausesResidual_and_ringBridge

end Thm21Residual

/-! ### D. **路线空洞的机器判定**：r206 表的两行 `hgen` ✗ 与 `ha_fix` ✗ 不可同真 -/

section FixedGeneratingRefutation

variable {F : Type} [Field F] {G : Type} [Group G]

set_option maxHeartbeats 1000000 in
/-- **L1 判定（本轮主发现** ✓）**：`G`-不变族**不**能生成 `L`（`G` 非平凡时）** ✓ ——
`ha_fix` ✗ ＋ `hgen` ✗ ⟹ **`Subsingleton G`** ✓。

**证明** ✓（**四步** ✓）：**①** 由 `IntermediateField.adjoin_induction` ✓ 证「`\mathrm{adjoin}_F(a)` 的
**每个**元素被 `G` **固定**」✓ —— `a`-支用 `ha_fix` ✓、`\mathrm{algebraMap}`-支用
`smul_C_noether` ✓ ＋ 塔式 ✓（`g \bullet (c \cdot 1) = c \cdot (g \bullet 1)` ✓）、
`+`／`*`／`\cdot^{-1}`-支用 `smul\_add` ✓／`smul\_mul'` ✓／`smul\_inv_0'` ✓；
**②** 由 `hgen` ✓ 得 `\top \subseteq L^G` ✓ ⟹ **每个** `x` 被每个 `g` 固定 ✓；
**③** 由 `FaithfulSMul G L` ✓（Noether 作用**忠实** ✓，`SaltGeneric` §4.4 ✓）＋ `eq_of_smul_eq_smul` ✓
得 `g = 1` ✓（`h` 同）✓；**④** 故 `Subsingleton G` ✓。

**🔴 要害** ✓：本条的**两行**正是 r206 表（≈ §4.61 ✓）的**第 2 行与第 5 行** ✓ ⟹
**该表在 `G` 非平凡档为空** ✗（**目标为假** ✗，**非**材料不可得 ✗）。
**⚠ 几何直觉** ✓：`L/L^G` 是**有限**扩张（Artin ✓）而 `a` 在 `L^G` 内 ⟹ `a` 至多生成 `L^G` ✗，
**不可能**生成 `L` ✗ —— 源文用 `a` 时它**本就在** `L^G` **内** ✓（见 §E ✓）。
**🔴 不声称** ✗：**不**声称源 `theorem-5-1` 的证明有误 ✗ —— 被判定的是**库内 r206 的编码** ✗
（把 `\mathrm{adjoin} = \top` 写在 `L` 上 ✗ 而固定性写在 `a` 上 ✗）；**不**声称 §4.60 的子代数档空洞 ✗
（该档取**任意** `S` ✓，**另需审计** ✗，**登记** ✓）。 -/
theorem subsingleton_of_fixed_generating {n : ℕ} {a : Fin n → NoetherField F G}
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤) : Subsingleton G := by
  have hfixed : ∀ x : NoetherField F G, x ∈ IntermediateField.adjoin F (Set.range a) →
      ∀ g : G, g • x = x := by
    intro x
    refine IntermediateField.adjoin_induction F (s := Set.range a)
      (motive := fun x _ => ∀ g : G, g • x = x) ?_ ?_ ?_ ?_ ?_
    · rintro y ⟨i, rfl⟩ g
      exact ha_fix g i
    · intro c g
      rw [show algebraMap F (NoetherField F G) c
          = algebraMap (MvPolynomial G F) (NoetherField F G) (MvPolynomial.C c) from
        (IsScalarTower.algebraMap_apply F (MvPolynomial G F) (NoetherField F G) c).symm,
        smul_algebraMap_noether, smul_C_noether]
    · intro x y _ _ hx hy g
      rw [smul_add, hx g, hy g]
    · intro x _ hx g
      rw [smul_inv₀', hx g]
    · intro x y _ _ hx hy g
      rw [smul_mul', hx g, hy g]
  refine ⟨fun g h => ?_⟩
  have hg : g = 1 := eq_of_smul_eq_smul fun x => by
    rw [hfixed x (by rw [hgen]; trivial) g, one_smul]
  have hh : h = 1 := eq_of_smul_eq_smul fun x => by
    rw [hfixed x (by rw [hgen]; trivial) h, one_smul]
  rw [hg, hh]

#print axioms subsingleton_of_fixed_generating

end FixedGeneratingRefutation

section NoetherWiringEmptiness

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **残余 ② 的空性判定** ✓（**本轮主发现** ✓）：**`G` 非平凡 ⟹ `NoetherWiringResidual F G` 为假** ✗。

**证明** ✓（**两句** ✓）：`obtain` 出表的两行 `ha_fix` ✗／`hgen` ✗ ✓，由
`subsingleton_of_fixed_generating` ✓ 得 `Subsingleton G` ✓，与 `Nontrivial G` ✓ 矛盾 ✓
（`not_subsingleton_iff_nontrivial` ✓）。
**🔴 后果** ✓：`theorem51Statement_of_noetherWiringResidual_and_ringBridge` ✓ **对非平凡 `G` 空洞** ✗
⟹ **r206／§4.61 路线**（自 r205 ✓ 起 5 轮接线 ✓ 的全部端到端件 ✓）**不可能**达到源陈述 ✗。
**⚠ 修正方向** ✓：见 §E ✓（数据取在 `L^G` 上 ✓）。
**🔴 不声称** ✗：**不**声称 `G` 平凡档的表非空 ✗（r249 ✓ 在 `\mathbb{Q}`／`PUnit` 上**逐行供给**并发射 ✓，
**但未打包为本残余的项** ✗ —— **登记** ✓）；**不**声称源定理为假 ✗。 -/
theorem noetherWiringResidual_empty_of_nontrivial [Nontrivial G] :
    ¬ NoetherWiringResidual F G := by
  rintro ⟨n, a, s₀, t, _instA, _instT, _instM, _ht, _hRG, hind, hgen, hs₀, hs₀_mem, ha_fix, -⟩
  exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial G›)
    (subsingleton_of_fixed_generating ha_fix hgen)

#print axioms noetherWiringResidual_empty_of_nontrivial

end NoetherWiringEmptiness

/-! ### E. **修正方向**：源侧数据取在**不动域 `L^G`** 上（源文用法 ✓）—— 该数据行**由源假设直接产出** ✓✅ -/

section FixedTranscendenceBasis

variable {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] {G : Type} [Group G]
variable [MulSemiringAction G L] [SMulCommClass G F L]

/-- **修正后的源侧数据** ✓✅（**本轮落** ✓）：由**源假设** `IsRationalOver F L^G` ✓ **直接产出**
**`G`-不变**的超越基 ✓ —— 即「`a` **在 `L^G` 内** ✓ ＋ 代数无关 ✓ ＋ **生成 `L^G`** ✓」✓。

**⚠ 与残余 ② 第 2 行的**唯一**差别** ✓：`\mathrm{adjoin}` 取自 **`L^G`** ✓（＝ 载体
`↥(\mathrm{FixedPoints.intermediateField}\ F\ G)` ✓，其 `\mathrm{Field}` ✓／`\mathrm{Algebra}\ F` ✓
两实例可合成 ✓、隶属形与「被每个 `g` 固定」**定义相等** ✓），**非** `L` ✗ ⟹
**§D 的两行冲突消失** ✓（`ha_fix` 由隶属**自动**给出 ✓）。
**⚠ 一致性** ✓：`exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver` ✓（`SaltGeneric:1503` ✓，
**r151** ✓）**正是**该形用件 ✓ —— 即**库内早有正确用件** ✓，r206 ✗ 把它用在了 `K = L` 上 ✗。
**🔴 不声称** ✗：**不**声称「修正后的整条链」已组装 ✗ —— 落在本条的**只有数据行** ✓；
链条其余件（`awayToFieldAlg` ✓ 一族）**以 `\mathrm{NoetherField}` 为环境域** ✗（`SaltGeneric` §4.39–§4.42 ✓）
⟹ **改接须把环境域换成 `L^G`** ✗（**下一手** ✓，**登记** ✓）；**不**声称源 `theorem-5-1` 已证 ✗。 -/
theorem exists_fixed_transcendenceBasis_of_isRationalOver
    (h : IsRationalOver F ↥(FixedPoints.intermediateField (F := F) (E := L) G)) :
    ∃ (n : ℕ) (a : Fin n → ↥(FixedPoints.intermediateField (F := F) (E := L) G)),
      AlgebraicIndependent F a ∧
        IntermediateField.adjoin F (Set.range a) = ⊤ ∧
        (∀ (g : G) (i : Fin n),
          g • ((a i : ↥(FixedPoints.intermediateField (F := F) (E := L) G)) : L)
            = ((a i : ↥(FixedPoints.intermediateField (F := F) (E := L) G)) : L)) := by
  obtain ⟨n, a, hind, hgen⟩ :=
    exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver
      (K := ↥(FixedPoints.intermediateField (F := F) (E := L) G)) h
  exact ⟨n, a, hind, hgen, fun g i => (a i).2 g⟩

#print axioms exists_fixed_transcendenceBasis_of_isRationalOver

end FixedTranscendenceBasis

/-! ### F. 残余 ② 的**10 行机器可造**（**解 r217／r227 的文件级实例障碍** ✓✅） -/

section NoetherWiringMachinery

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

set_option maxHeartbeats 1000000 in
/-- **10 行机器可造** ✓✅（**库内首件** ✓）：**源侧数据 ＋ 不动性** ⟹ 残余 ② 的
**接线行**（`t` ✓／`ht` ✓／不变化 ✓／三实例 ✓／`hle` ✓／`hact_map` ✓／`hRG` ✓／`hS₀R` ✓）**存在** ✓。

**⚠ 三件来历** ✓（**皆库内** ✓，**不新造** ✗）：
**①** `t` ✓（**非零** ✓ ＋ **不变化** ✓ ＋ **包含** ✓）＝ `exists_invariant_t_of_noether` ✓（§4.37 ✓，
`SaltGeneric:2983` ✓，**r215–r217** ✓）；
**②** `\mathrm{Algebra}` ＋ `\mathrm{IsScalarTower}` ✓ ＝ `exists_algebra_structure_away_of_noetherAdjoin` ✓
（§4.42 ✓，**r226** ✓）—— 其 `\iota` ✓ 同时给 `hS₀R` ✓；
**③** `\mathrm{MulSemiringAction}\ G\ (\mathrm{Localization.Away}\ t)` ✓ ＝
`awayMulSemiringAction` ✓（§4.39 ✓，`SaltGeneric:3201` ✓）＋ **`hact_map`** ✓ ＝
`awayRingHom_algebraMap` ✓（**同一 `smul` 定义** ✓：`smul\ g = \mathrm{awayRingHom}\ ht\ g` ✓）。

**⚠ `hRG` 的推导** ✓（**本轮新证** ✓，**四步** ✓）：`g \bullet (r \bullet x) = r \bullet (g \bullet x)` ✓
（`r \bullet x = \iota r \cdot x` ✓）⟸ **`g \bullet \iota r = \iota r`** ✓ ⟸
（`awayToField_injective` ✓）`\mathrm{awayToField}(g \bullet \iota r) = \mathrm{awayToField}(\iota r)` ✓
⟸（`awayToField_smul` ✓，§4.40 ✓）`g \bullet \mathrm{awayToField}(\iota r) = \mathrm{awayToField}(\iota r)` ✓
⟸（`hS₀R` ✓ ＋ **`smul_eq_self_of_mem_adjoin_of_fixed`** ✓，§4.47 ✓）
`g \bullet (\mathrm{algebraMap}\ r) = \mathrm{algebraMap}\ r` ✓。
**⚠ 意义** ✓：**r227 登记的三式（甲／乙／丙）不必走** ✗ —— 本件**同时看见**
`SaltLocalProj` 的局部化作用族 ✓ 与 §4.4 的 `\mathrm{MvPolynomial}` 作用 ✓，
而**正解** ＝ **不搬实例** ✗，改用**本件 §4.39 的 Noether 专用作用** ✓（`awayMulSemiringAction` ✓，
**已在两侧之一** ✓）⟹ **文件级障碍消失** ✓。
**🔴 不声称** ✗：**不**声称本件与残余 ② 的 ∃ 是**同一**见证 ✗（两处 ∃ **各自**给见证 ✓；
拼接须把 `t`／实例提到**类型层** ✗ ＝ r217 登记的同一障碍 ✗，
**但**本件已把「该行**是否可造**」判定为**是** ✓）；**不**声称 `hind`／`hgen`／`hs₀_mem` 已造 ✗。 -/
theorem noetherWiringMachinery_of_sourceData {n : ℕ} (a : Fin n → NoetherField F G)
    (s₀ : NoetherField F G) (hs₀ : s₀ ≠ 0)
    (ha_fix : ∀ (g : G) (i : Fin n), g • a i = a i) (hs₀_fix : ∀ (g : G), g • s₀ = s₀) :
    ∃ (t : MvPolynomial G F) (ht : t ≠ 0)
      (_ : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t))
      (_ : IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t))
      (_ : MulSemiringAction G (Localization.Away t)),
      (∀ g : G, g • t = t) ∧
      (Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}) ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)))) ∧
      (∀ (g : G) (p : MvPolynomial G F),
        g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
          = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p)) ∧
      (∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
        (x : Localization.Away t), g • (r • x) = r • (g • x)) ∧
      (∀ r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})),
        awayToFieldAlg (F := F) (G := G) t ht
            (algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t) r)
          = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r) := by
  obtain ⟨t, ht, htinv, hle⟩ := exists_invariant_t_of_noether (F := F) (G := G) a s₀ hs₀
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G) t ht hle
  let _ : Algebra ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (Localization.Away t) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))
      (Localization.Away t) := inferInstance
  let _ : MulSemiringAction G (Localization.Away t) := awayMulSemiringAction (F := F) htinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
        = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p) :=
    fun g p => awayRingHom_algebraMap (F := F) htinv g p
  have hfix : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹}))), g • ι r = ι r := by
    intro g r
    apply awayToField_injective (F := F) (G := G) t ht
    rw [show awayToField (F := F) (G := G) t ht (g • ι r)
        = awayToField (F := F) (G := G) t ht (awayRingHom (F := F) htinv g (ι r)) from rfl,
      awayToField_smul (F := F) (G := G) (t := t) htinv ht g (ι r),
      show awayToField (F := F) (G := G) t ht (ι r)
        = algebraMap ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) (NoetherField F G) r
        from hι r]
    exact smul_eq_self_of_mem_adjoin_of_fixed (F := F) (G := G) ha_fix hs₀_fix g r.property
  have hRG : ∀ (g : G) (r : ↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})))
      (x : Localization.Away t), g • (r • x) = r • (g • x) := by
    intro g r x
    show g • (ι r * x) = ι r * (g • x)
    rw [smul_mul', hfix g r]
  exact ⟨t, ht, ι.toRingHom.toAlgebra, hST, awayMulSemiringAction (F := F) htinv, htinv, hle,
    hact, hRG, fun r => hι r⟩

/-- **L1 非空探针** ✓：本件**假设类非空** ✓ —— 取 `n = 0` ✓（`a := \mathrm{Fin.elim}_0` ✓，空族）、
`s₀ := 1` ✓（`1 \neq 0` ✓、`g \bullet 1 = 1` ✓）⟹ 三项假设**同时可满足** ✓
（**故本件不是空壳** ✓，与残余 ② **不同** ✗ —— 后者含 §D 的两行冲突 ✗）。
**🔴 不声称** ✗：本探针**只**证**假设类非空** ✓，**不**构造 `t`／实例／四行 ✗
（那些由 `noetherWiringMachinery_of_sourceData` ✓ 在**一般档**给出 ✓）；
**不**声称本件与残余 ② 的 ∃ 是同一见证 ✗。 -/
theorem noetherWiringMachinery_hypotheses_nonempty (F : Type) [Field F] (G : Type) [Group G]
    [Fintype G] [DecidableEq G] :
    ∃ (n : ℕ) (a : Fin n → NoetherField F G) (s₀ : NoetherField F G), s₀ ≠ 0 ∧
      (∀ (g : G) (i : Fin n), g • a i = a i) ∧ (∀ (g : G), g • s₀ = s₀) :=
  ⟨0, Fin.elim0, 1, one_ne_zero, fun _ i => i.elim0, fun _ => smul_one _⟩

#print axioms noetherWiringMachinery_of_sourceData
#print axioms noetherWiringMachinery_hypotheses_nonempty

end NoetherWiringMachinery

/-! ### G. 登记（**逐条如实** ✓，**不声称**款在各件** ✓） -/

/-- **登记** ✗：**残余与可达性的总账**（本轮）——
**①** `Theorem51Statement`（`SaltGeneric:257` ✓）：残余 ②（**非平凡档空** ✗，§D ✓）＋ 残余 ①（**未证** ✗）
⟹ **两处皆缺** ✗；**②** `Theorem21Statement`（`SaltGeneric:191` ✓）：残余 ③（**未证** ✗，＝ 源 §2 构造 ✗）
＋ 残余 ① ⟹ **缺一处 ＋ 公共桥** ✗；**③** **公共残余** ＝ 残余 ①（CHR 代数版 ✗）。
**⚠ 下一手（三式** ✓**）**：**(甲)** 按 §E ✓ 把环境域换成 `L^G` ✓ **重接**链条（**本轮主建议** ✓）；
**(乙)** 落残余 ①（CHR 代数版：`G`-Galois 环 ＝ 域直和 ＋ 逐分量 ✓）；**(丙)** 落残余 ③（源 §2 构造 ✗）。
**🔴 不声称** ✗：**不**声称 (甲)(乙)(丙) 任一已落 ✗。 -/
theorem sourceStatementResiduals_registered : True := trivial

/-- **登记** ✗：**旧注的审计口径** —— `SaltGeneric` §4.60 ✓（`theorem51_endToEnd_wired_registered` ✓）
与 §4.61 ✓（`theorem51_dataChain_gap_registered` ✓）记「余 ＝ 两项具名端点 ＋ 数据构造链」✗ ——
**本轮修正** ✓：**该账不完整** ✗（漏了 §D 的两行冲突 ✗）⟹ 两件的**结论**（有限档见证 ✓）**仍成立** ✓ 但
**对非平凡 `G` 空洞** ✗ ⟹ **不得**读作「端到端已通」✗（**原注照原样保留** ✓，**不改写他件** ✗）。
**⚠ §4.60 的子代数档**（`nonempty_genericExtensionWitnessFieldFinite_of_subalgebra` ✓）：取**任意**子代数 ✓
＋ `hS_fix` ✗（**不**经 `hgen` ✓）⟹ **本轮未判定其空性** ✗（**另需审计** ✗，**登记** ✓）。 -/
theorem oldEndToEndAudit_corrected : True := trivial

/-- **登记** ✗：**残余 ② 的 `PUnit` 档**（＝ 唯一可能有内容的档 ✓）：r249 ✓
（`nonempty_genericExtensionWitnessFieldFinite_pUnit_rat` ✓，`SaltThm38_ABGV52.lean:1363` ✓）
**逐行供给**该表并在测试实例上**发射** ✓✅ + `exists_wiringHypotheses_pUnit_rat` ✓（`:1313` ✓）给三残余 ✓
+ r237 ✓ 给源侧九项 ✓ ⟹ 该档**表非空** ✓（**但未打包为残余 ② 的项** ✗ ——
打包须把 `t`／实例提到类型层 ✗，**或**重跑 r249 的构造 ✓，**两者本轮皆未落** ✗）。
**🔴 不声称** ✗：**不**声称 `PUnit` 档已给出 `Theorem51Statement` ✗（**缺**残余 ① ✗）。 -/
theorem noetherWiringResidual_pUnit_registered : True := trivial

#print axioms sourceStatementResiduals_registered
#print axioms oldEndToEndAudit_corrected
#print axioms noetherWiringResidual_pUnit_registered

/-! ### H. **改接（`L^G` 读法）**：不动域数据 ＋ **分式环无关的 `(a)` 款机器** ＋ **残余 ④（新）** ＋ **L1 非空探针** -/

/-- **⚠ 本节缘起（r259 的机器判定** ✓**）**：§D ✓ 判定 r206 表（残余 ② ✓，`NoetherWiringResidual` ✓）在
**`G` 非平凡档为空** ✗ —— 其两行 `hgen` ✓（`\mathrm{adjoin}_F a = \top`，**读在 `L`** ✗）与
`ha_fix` ✓（**读在 `L` 的元素上** ✗）**不可同真** ✓（`subsingleton_of_fixed_generating` ✓）。

**⚠ 修正方向** ✓（**源文用法** ✓）：把**源侧数据** `a`／`s_0` **读在不动域 `L^G`** ✓（§E ✓，
`↥(\mathrm{FixedPoints.intermediateField}\ F\ G)` ✓）—— 于是 `\mathrm{adjoin}` 取**在 `L^G` 内** ✓、
`ha_fix` 由**隶属定义自动成立** ✓ ⟹ §D 的两行冲突**消失** ✓✅。

**⚠ 本节（甲）组：数据沿「子代数/中间域强制」的搬运三式** ✓
（**⚠ 三式皆**双向或**所需单向** ✓，**逐条注明** ✓）。

**🔴 不声称** ✗：**不**声称两条源陈述已证 ✗（源 `theorem-5-1` ✓／`theorem-2-1` ✓ **仍未证** ✗）；
**不**声称残余 ①（环档桥 ✓）已证 ✗（**仍共享、仍开** ✗）；**不**声称 r206 路线可用 ✗
（**非平凡 `G` 档已判定为空** ✗，§D ✓；**其定理一律原样保留** ✓，本节**只追加** ✓）。 -/
theorem fixedPointRewiring_scope_registered : True := trivial

section FixedPointRewiring

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **不动域载体（`L^G`，`L = \mathrm{NoetherField}\ F\ G`）** ✓：源侧数据**读取之处** ✓
（§E ✓ 的 `\mathrm{FixedPoints.intermediateField}` ✓；隶属形 ＝ 「被每个 `g` 固定」✓，**定义相等** ✓）。
**⚠ 实例** ✓：`\mathrm{Field}` ✓／`\mathrm{Algebra}\ F` ✓／`\mathrm{IsScalarTower}\ F\ \cdot\ L` ✓ **皆可合成** ✓（实测 ✓）。 -/
abbrev NoetherInvariantField (F : Type) [Field F] (G : Type) [Group G] : Type :=
  ↥(FixedPoints.intermediateField (F := F) (E := NoetherField F G) G)

/-- **wiring 载体（**强制转换后**在 `L` 中的 `F[a, s_0, s_0^{-1}]`）** ✓：新残余与新归约**共用**的 `\uparrow S` ✓
（**与 r206 的载体同形** ✓，**只把 `a`／`s_0` 换成强制转换** ✓）。 -/
abbrev noetherFixedCarrier (F : Type) [Field F] (G : Type) [Group G] {n : ℕ}
    (a : Fin n → NoetherInvariantField F G) (s₀ : NoetherInvariantField F G) :
    Subalgebra F (NoetherField F G) :=
  Algebra.adjoin F (Set.range (fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    ∪ {((s₀ : NoetherInvariantField F G) : NoetherField F G),
       (((s₀ : NoetherInvariantField F G) : NoetherField F G))⁻¹})

/-- **(甲) ① 代数无关沿子代数强制** ✓✅（**双向** ✓）：`\mathrm{AlgebraicIndependent}\ F\ x` ✓
（在 `\uparrow S` **内** ✓）⟺ 其**强制像族**在 `A` 内代数无关 ✓。
**证明** ✓（**两向** ✓）：**关键件** ＝ mathlib **`\mathrm{Subalgebra.mvPolynomial\_aeval\_coe}`** ✓
（`\mathrm{aeval}\ (\uparrow \circ x)\ p = \uparrow(\mathrm{aeval}\ x\ p)` ✓）＋ **`\mathrm{Subtype.ext}`** ✓
（`\mathrm{AlgebraicIndependent}` ✓ **就是** `\mathrm{aeval}` 的单射性 ✓，`\mathrm{RingTheory.AlgebraicIndependent.Defs:54}` ✓）。
**⚠ 用途** ✓：新归约的 `hind` ✓（`L^G` ⟹ `L` ✓，**`.mp`** ✓）与探针的 `hind` ✓（`L` ⟹ `L^G` ✓，**`.mpr`** ✓）。
**🔴 不声称** ✗：**不**声称 `x` 与强制像族的**其他**性质（如 `\mathrm{adjoin}` 顶 ✓）同样搬运 ✗
（**那须单列** ✓，见 ③ ✓）。 -/
theorem algebraicIndependent_coe_iff_of_subalgebra {F A ι : Type} [CommRing F] [CommRing A]
    [Algebra F A] (S : Subalgebra F A) (x : ι → ↥S) :
    AlgebraicIndependent F x ↔ AlgebraicIndependent F (fun i => (x i : A)) := by
  constructor
  · intro h p q hpq
    refine h (Subtype.ext ?_)
    simpa only [Subalgebra.mvPolynomial_aeval_coe] using hpq
  · intro h p q hpq
    refine h ?_
    rw [Subalgebra.mvPolynomial_aeval_coe S x p, Subalgebra.mvPolynomial_aeval_coe S x q, hpq]

#print axioms algebraicIndependent_coe_iff_of_subalgebra

/-- **(甲) ② `\mathrm{adjoin}` 隶属沿子代数强制** ✓（**单向** ✓：`L^G` ⟹ `L` ✓）：
`s \in \mathrm{Algebra.adjoin}\ F\ (\mathrm{range}\ a)` ✓（**在 `\uparrow S` 内** ✓）⟹
强制像在 `A` 的 `\mathrm{range}` 的 `\mathrm{adjoin}` 内 ✓。
**证明** ✓：**`\mathrm{AlgHom.map\_adjoin}`** ✓（`(\mathrm{adjoin}\ F\ s).\mathrm{map}\ \varphi = \mathrm{adjoin}\ F\ (\varphi\ ''\ s)` ✓）
＋ **`\mathrm{Set.range\_comp}`** ✓ ＋ **`\mathrm{Algebra.subset\_adjoin}`** 的直接搬运 ✓。
**⚠ 用途** ✓：新归约的 `hs_0 \in F[a]` ✓（(a) 款机器的**输入** ✓）。
**🔴 不声称** ✗：**不**声称**逆向**（`L` ⟹ `L^G` ✓）成立 ✗ —— 它**不**由本式给出 ✗
（`L` 中的 `\mathrm{adjoin}` **更大** ✗：系数可取遍 `L^G` ✓，**探针侧**因此改取 `s_0 = 1` ✓，见下 ✓）。 -/
theorem mem_adjoin_coe_of_mem_adjoin {F A ι : Type} [CommRing F] [CommRing A] [Algebra F A]
    (S : Subalgebra F A) {x : ↥S} {a : ι → ↥S}
    (hx : x ∈ Algebra.adjoin F (Set.range a)) :
    (x : A) ∈ Algebra.adjoin F (Set.range (fun i => (a i : A))) := by
  have himg : (Subalgebra.val S) '' Set.range a = Set.range (fun i => (a i : A)) := by
    rw [← Set.range_comp]
    congr 1
  have h1 : ((Algebra.adjoin F (Set.range a)).map (Subalgebra.val S))
      = Algebra.adjoin F ((Subalgebra.val S) '' Set.range a) := AlgHom.map_adjoin _ _
  have h2 : (Subalgebra.val S) x ∈ (Algebra.adjoin F (Set.range a)).map (Subalgebra.val S) :=
    ⟨x, hx, rfl⟩
  rwa [h1, himg] at h2

#print axioms mem_adjoin_coe_of_mem_adjoin

/-- **(甲) ③ 中间域 `\mathrm{adjoin}` 的「顶／满」沿强制搬运** ✓✅（**双向** ✓）：
`\mathrm{IntermediateField.adjoin}\ F\ (\mathrm{range}\ a) = \top` ✓（**在 `\uparrow I` 内** ✓）⟺
`\mathrm{IntermediateField.adjoin}\ F\ (\mathrm{range}\ (\uparrow \circ a)) = I` ✓（**在 `L` 内** ✓）。
**⚠ 为什么不用代数档** ✓（**本轮实测** ✗）：mathlib 的代数档等式
`(\mathrm{IntermediateField.adjoin}\ F\ s).\mathrm{toSubalgebra} = \mathrm{Algebra.adjoin}\ F\ s` ✓
**须 `[\mathrm{Algebra.IsAlgebraic}\ F\ L]`** ✗（`\mathrm{IntermediateField.adjoin\_toSubalgebra}` ✓）——
**本题不满足** ✗（`L = F(x_\sigma)` **超越** ✓）⟹ **代数档搬运是错的口径** ✗（**不可用** ✗，
**本轮一度误设** ✓✓，**据实登记** ✓）；**正解** ＝ **中间域档** ✓。
**证明** ✓：**`\mathrm{IntermediateField.adjoin\_map}`** ✓ ＋ **`\mathrm{IntermediateField.map\_injective}`** ✓
（域同态的 `\mathrm{map}` **单** ✓）＋ **`\mathrm{IntermediateField.map}\ \uparrow\ \top = I`** ✓（**两向** ✓：
`\mathrm{mem\_map}` ✓ 一支 ＋ 隶属 `x.2` ✓ 一支）。
**⚠ 用途** ✓：新残余第 2 行 `hgen` ✓（**读在 `L^G`** ✓，**＝ 改接的要害** ✓）的**探针** ✓（`L` ⟹ `L^G` ✓，**`.mpr`** ✓）。
**🔴 不声称** ✗：**不**声称本式能搬运**其它**谓词（如 `\mathrm{IsRationalOver}` ✓）✗。 -/
theorem intermediateField_adjoin_eq_top_iff_of_val {L : Type} [Field L] [Algebra F L]
    (I : IntermediateField F L) {ι : Type} (a : ι → ↥I) :
    IntermediateField.adjoin F (Set.range a) = ⊤ ↔
      IntermediateField.adjoin F (Set.range (fun i => (a i : L))) = I := by
  have himg : (IntermediateField.val I) '' Set.range a = Set.range (fun i => (a i : L)) := by
    rw [← Set.range_comp]
    congr 1
  have hmap : IntermediateField.map (IntermediateField.val I)
      (IntermediateField.adjoin F (Set.range a))
      = IntermediateField.adjoin F (Set.range (fun i => (a i : L))) := by
    rw [IntermediateField.adjoin_map, himg]
  have htop : IntermediateField.map (IntermediateField.val I) (⊤ : IntermediateField F ↥I) = I := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, -, rfl⟩ := (IntermediateField.mem_map (⊤ : IntermediateField F ↥I)).mp hy
      exact x.2
    · intro y hy
      exact (IntermediateField.mem_map (⊤ : IntermediateField F ↥I)).mpr ⟨⟨y, hy⟩, trivial, rfl⟩
  constructor
  · intro h
    rw [← hmap, h, htop]
  · intro h
    refine IntermediateField.map_injective (IntermediateField.val I) ?_
    rw [hmap, h, htop]

#print axioms intermediateField_adjoin_eq_top_iff_of_val

end FixedPointRewiring

/-! ### I. **(乙) `(a)` 款的**分式环无关形**（r188 的 `\mathrm{IsFractionRing}` 假设被消）** ＋ **(丙) 残余 ④ 与探针** -/

/-- **⚠ 为什么这一件是改接的实质** ✓✅：r188 ✓ 的 **(a) 款具名件**
`exists_algEquiv_localizationAway_of_adjoin_union_inv` ✓（`SaltGeneric:4506` ✓）的假设表含
**`[\mathrm{IsFractionRing}\ \uparrow A_0\ K]`** ✓，其**唯一来源**是 **`hgen`（域生成）** ✓
（r168 ② ✓ `isFractionRing_adjoin_of_adjoin_eq_top` ✓）—— 而 r206 ✓ **把 `hgen` 读在 `L` 上** ✗
⟹ 该假设在 `L^G` 读法下**不可得** ✗（`L = \mathrm{Frac}(F[x_\sigma])` **不是** `F[a]` 的分式环 ✗）。
**本轮读数** ✓：**该假设其实是多余的** ✓ —— `(a)` 款所需的**只是**「`A_0[s^{-1}]` 是 `A_0` 在 `s` 处的局部化」✓，
**只需** `A_0 \to K` **单** ✓ ＋ `s \neq 0` ✓（**不**需 `K = \mathrm{Frac}(A_0)` ✗）。 -/
theorem awayLocalizationFree_scope_registered : True := trivial

section AwayLocalizationFree

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] [FaithfulSMul A K]

set_option maxHeartbeats 1000000 in
/-- **(乙) ① 分式环无关的局部化结构** ✓✅（**库内首件** ✓）：
`A_0 := A` ✓、`s \neq 0` ✓、`A \to K` **单**（`\mathrm{FaithfulSMul}` ✓）⟹
**`A[s^{-1}]` 是 `A` 在 `s` 的幂处的局部化** ✓ —— **去掉了 `[\mathrm{IsFractionRing}\ A\ K]`** ✗。
**证明** ✓（**三款直造** ✓，入口 **`isLocalization\_iff`** ✓）：
**`\mathrm{map\_units}`** ✓ ＝ `s` 在 `\mathrm{adjoin}\ A\ \{s^{-1}\}` 中**可逆** ✓（逆元 ＝ 生成元 ✓，
乘积 `= 1` 在 `K` 中算 ✓，用 **`\mathrm{IsScalarTower.algebraMap\_apply}`** ✓ ＋ `\mathrm{mul\_inv\_cancel_0}` ✓）；
**`\mathrm{surj}`** ✓ ＝ **库内 r163 ✓ 的 `exists\_pow\_mul\_eq\_of\_mem\_adjoin\_inv`** ✓
（**只**需 `[\mathrm{CommRing}\ A]` ✓／`[\mathrm{Field}\ K]` ✓／`[\mathrm{Algebra}\ A\ K]` ✓／`[\mathrm{FaithfulSMul}\ A\ K]` ✓ —— **无分式环** ✗）；
**`\mathrm{exists\_of\_eq}`** ✓ ＝ 强制到 `K` 后用 **`\mathrm{FaithfulSMul.algebraMap\_injective}`** ✓，取 `c = 1` ✓。
**🔴 不声称** ✗：**不**声称 `\mathrm{IsLocalization.Away}` 的**任何**下游件（如 `\mathrm{AlgEquiv}` ✓）已随之落 ✗
（**那在 (乙) ② 单列** ✓）；**不**声称 r164／r165 的**旧件**（带 `\mathrm{IsFractionRing}` ✓）被取代 ✗
（**原样保留** ✓，**本节只追加** ✓）。 -/
theorem isLocalization_away_adjoin_inv_of_faithfulSMul (s : A) (hs : s ≠ 0) :
    IsLocalization.Away s ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) := by
  have hsK : algebraMap A K s ≠ 0 := fun h0 =>
    hs (FaithfulSMul.algebraMap_injective A K (by rw [h0, map_zero]))
  refine (isLocalization_iff (M := Submonoid.powers s)
    (S := ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)))).mpr ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : A) s).mp y.2
    have hmem : (algebraMap A K s)⁻¹ ∈ Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K) :=
      Algebra.subset_adjoin (Set.mem_singleton _)
    have hprod : algebraMap A ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) s
        * (⟨(algebraMap A K s)⁻¹, hmem⟩ :
            ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K))) = 1 := by
      apply Subtype.ext
      change algebraMap ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) K
          (algebraMap A ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) s)
          * (algebraMap A K s)⁻¹ = (1 : K)
      rw [← IsScalarTower.algebraMap_apply A
        ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) K s]
      exact mul_inv_cancel₀ hsK
    have hunit : IsUnit (algebraMap A ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) s) :=
      isUnit_iff_exists_inv.mpr ⟨_, hprod⟩
    rw [← hn, map_pow]
    exact hunit.pow n
  · intro z
    obtain ⟨n, a, ha⟩ := exists_pow_mul_eq_of_mem_adjoin_inv (A := A) (K := K) s hs z z.2
    refine ⟨(a, ⟨s ^ n, Submonoid.pow_mem (Submonoid.powers s)
      ((Submonoid.mem_powers_iff s s).mpr ⟨1, pow_one s⟩) n⟩), ?_⟩
    apply Subtype.ext
    show (z : K) * algebraMap A K (s ^ n) = algebraMap A K a
    rw [map_pow]
    exact ha
  · intro x y hxy
    refine ⟨1, ?_⟩
    have hK : algebraMap A K x = algebraMap A K y := by
      have h1 := congrArg (algebraMap
        ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) K) hxy
      rwa [← IsScalarTower.algebraMap_apply A
          ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) K x,
        ← IsScalarTower.algebraMap_apply A
          ↥(Algebra.adjoin A ({(algebraMap A K s)⁻¹} : Set K)) K y] at h1
    rw [FaithfulSMul.algebraMap_injective A K hK]

end AwayLocalizationFree

#print axioms isLocalization_away_adjoin_inv_of_faithfulSMul

section AwayClauseWithoutTop

variable {F K : Type} [Field F] [Field K] [Algebra F K] {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- **(乙) ② `(a)` 款「无 `hgen` 形」** ✓✅（**本轮主落** ✓）：**代数无关** ✓ ＋ `s_0 \neq 0` ✓ ＋
**`s_0 \in F[a]`** ✓ ⟹ `\exists w \neq 0,\ \uparrow F[a, s_0, s_0^{-1}] \simeq_F \mathrm{Localization.Away}\ w` ✓
—— **假设表比 r188 ✓ 少一行 `hgen`（域生成）** ✗。
**⚠ 证明体** ✓（**三件复合** ✓，**不重证** ✗）：**①** r158 ✓ 的**多项式环识别**
`\mathrm{nonempty\_algEquiv\_mvPolynomial\_adjoin}` ✓（**只**需 `hind` ✓）；**②** (乙) ① ✓ 的
**分式环无关局部化** ✓（**消掉** `\mathrm{IsFractionRing}` ✗）＋ **`\mathrm{IsLocalization.algEquiv}`** ✓；
**③** r188 ✓ 的**载体桥**（`\mathrm{Algebra.adjoin\_union\_eq\_adjoin\_adjoin}` ✓ ＋ `s_0 \in F[a]` ✓ 约去 `\{s_0\}` ✓）。
**⚠ 意义（＝**改接的实质** ✓）**：r206 ✓ 之所以**必须**把 `hgen` 读在 `L` 上 ✗，**唯一原因**是本件的 `hgen` ✗；
**本件落地 ⟹ `hgen` 不再是 `(a)` 款的输入** ✓ ⟹ **`L^G` 读法下 `(a)` 款照样可得** ✓✅
（新归约经此件产出 `(a)` 款 ✓，**残余 ④ 因此不必含 `(a)` 款为一行** ✓）。
**🔴 不声称** ✗：**不**声称 r188 ✓ 的旧件被取代 ✗（**原样保留** ✓，**本节只追加** ✓）；
**不**声称 `hgen` 可删 ✗（它仍是**源侧资格行** ✓：数据须是 `L^G` 的**超越基** ✓）。 -/
theorem exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul
    {a : Fin n → K} {s₀ : K} (hind : AlgebraicIndependent F a) (hs₀ : s₀ ≠ 0)
    (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a)) :
    ∃ w : MvPolynomial (Fin n) F, w ≠ 0 ∧
      Nonempty (↥(Algebra.adjoin F (Set.range a ∪ {s₀, s₀⁻¹})) ≃ₐ[F] Localization.Away w) := by
  classical
  obtain ⟨e⟩ := nonempty_algEquiv_mvPolynomial_adjoin (K := K) hind
  let A₀ : Subalgebra F K := Algebra.adjoin F (Set.range a)
  let s' : ↥A₀ := ⟨s₀, hs₀_mem⟩
  have hs'val : algebraMap ↥A₀ K s' = s₀ := rfl
  have hs' : s' ≠ 0 := fun h => hs₀ (congrArg Subtype.val h)
  have hloc : IsLocalization.Away s' ↥(Algebra.adjoin ↥A₀ {(algebraMap ↥A₀ K s')⁻¹}) :=
    isLocalization_away_adjoin_inv_of_faithfulSMul (A := ↥A₀) (K := K) s' hs'
  let χ : Localization.Away s' ≃ₐ[↥A₀] ↥(Algebra.adjoin ↥A₀ {(algebraMap ↥A₀ K s')⁻¹}) :=
    IsLocalization.algEquiv (Submonoid.powers s') _ _
  obtain ⟨ψ⟩ := nonempty_algEquiv_localizationAway_map e (e.symm s')
  rw [e.apply_symm_apply s'] at ψ
  have h2 : Algebra.adjoin ↥A₀ {s₀, s₀⁻¹}
      = Algebra.adjoin ↥A₀ {(algebraMap ↥A₀ K s')⁻¹} := by
    refine le_antisymm ?_ ?_
    · rw [Algebra.adjoin_le_iff]
      rintro y (hy | hy)
      · rw [hy]
        exact Subalgebra.algebraMap_mem _ s'
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, hs'val]
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    · rw [Algebra.adjoin_le_iff]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy, hs'val]
      exact Algebra.subset_adjoin (by simp)
  have h1 := Algebra.adjoin_union_eq_adjoin_adjoin F (Set.range a) {s₀, s₀⁻¹}
  refine ⟨e.symm s', (algEquiv_ne_zero_iff e.symm).mpr hs', ?_⟩
  exact ⟨(Subalgebra.equivOfEq _ _
    (h1.trans (congrArg (Subalgebra.restrictScalars F) h2))).trans
      (ψ.trans (χ.restrictScalars F)).symm⟩

#print axioms exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul

end AwayClauseWithoutTop

/-- **(乙) ③ `PUnit` 档：不动域 ＝ 全空间** ✓✅：`G = \mathrm{PUnit}`（**单点** ✓）时
`\mathrm{FixedPoints.intermediateField}\ F\ (\mathrm{NoetherField}\ F\ \mathrm{PUnit})\ \mathrm{PUnit} = \top` ✓。
**证明** ✓：`\top \le \cdot` ✓ 支由 **隶属形** ✓（`\mathrm{FixedPoints.mem\_intermediateField\_iff}` ✓）
化到「`g \bullet x = x`」✓，再用 **`\mathrm{MulSemiringAction.toRingEquiv}`** ✓
（**它是 `G \to^* (L \simeq^* L)`** ✓）＋ **`\mathrm{Subsingleton.elim}`** ✓ ＋ **`\mathrm{map\_one}`** ✓ 得作用 ≡ `1` ✓
（**⚠ 不得用 `\mathrm{one\_smul}`** ✗：`\mathrm{PUnit}` **另有** mathlib 的**泛用** `\mathrm{MulAction}` 实例 ✓
⟹ `\mathrm{rw}` 匹配到**另一个** `\mathrm{SMul}` 档 ✗，**本轮实测** ✗；**正解 ＝ 走环自同构** ✓）。
**⚠ 用途** ✓：L1 探针的**中间域档搬运** ✓（`intermediateField_adjoin_eq_top_iff_of_val` ✓）。
**🔴 不声称** ✗：**不**声称 `G` 非平凡档的不动域是 `\top` ✗（**恰恰相反** ✗）。 -/
theorem noetherInvariantField_pUnit {F : Type} [Field F] :
    FixedPoints.intermediateField (F := F) (E := NoetherField F PUnit.{1}) PUnit.{1} = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  rw [FixedPoints.mem_intermediateField_iff]
  intro g
  have hfun : (MulSemiringAction.toRingEquiv PUnit.{1} (NoetherField F PUnit.{1})) g
      = RingEquiv.refl (NoetherField F PUnit.{1}) := by
    rw [Subsingleton.elim g 1, map_one]
    rfl
  have h2 : ((MulSemiringAction.toRingEquiv PUnit.{1} (NoetherField F PUnit.{1})) g) x = x :=
    congrArg (fun e : NoetherField F PUnit.{1} ≃+* NoetherField F PUnit.{1} => e x) hfun
  rwa [MulSemiringAction.toRingEquiv_apply_apply] at h2

#print axioms noetherInvariantField_pUnit

/-! ### J. **(丙) 残余 ④（新，具名）** ＋ **归约（源 `theorem-5-1`）** -/

section FixedWiringResidual

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **残余 ④（新，具名）** ✓：**改接后的 wiring 表** —— **源侧数据 `a`／`s_0` 读在不动域 `L^G`** ✓
（`\mathrm{NoetherInvariantField}\ F\ G` ✓，§H ✓），**其余各行与残余 ②（`NoetherWiringResidual` ✓）同形** ✓
（`t` ✓／三实例 ✓／`ht` ✓／`t` 不变化 ✓／`hle` ✓／`hact_{\rm map}` ✓／`hRG` ✓／
**两项具名端点** `hgal` ✓／`hProj` ✓／`hS_0R` ✓），**逐行以强制转换后的数据表述** ✓。

**⚠ 与残余 ② 的**唯一实质差别** ✓✅**：第 2 行 `hgen` ✓ ＝
`\mathrm{IntermediateField.adjoin}\ F\ (\mathrm{range}\ a) = \top` ✓ ——
**取在 `L^G` 内** ✓（残余 ② 取在 `L` 内 ✗）。**⚠ 后果** ✓：`ha_fix` ✓（第 5 行）与 `hs_0`-不动 ✓（第 6 行）
**由隶属定义自动成立** ✓（`(a\ i).2` ✓／`s_0.2` ✓）⟹ **§D 的两行冲突消失** ✓✅
（残余 ② 在该档**为空** ✗，§D ✓；残余 ④ **非空** ✓，见 §K 的机器探针 ✓）。

**⚠ 十八行** ✓（∃-绑定 9 行 ✓／合取 12 行 ✓，**与残余 ② 逐位对应** ✓ ——
故两者可**逐行对读** ✓，**差别只在 `hgen` 的域** ✓）。
**⚠ 数据部分的**来源** ✓**：`a`／`s_0` 由**源假设** `\mathrm{IsRationalOver}\ F\ L^G` ✓ 产出 ✓
（§E ✓ 的 `exists_fixed_transcendenceBasis_of_isRationalOver` ✓；**机器验证**见
`exists_fixedWiringData_of_isRationalOver` ✓，**本节后** ✓）。
**⚠ 未消费行（**如实登记** ✗）**：`hgen` ✓ 在**归约中不被消费** ✗ —— 归约的 `(a)` 款经
**(乙) ②** ✓（**无 `hgen` 形** ✓）产出 ✓ ⟹ `hgen` 是**源侧资格行** ✓（数据须是 `L^G` 的**超越基** ✓），
**本条只登记** ✓，**不声称它多余** ✗（**候选用法**：`hind + hgen \Rightarrow \mathrm{IsRationalOver}\ F\ L^G` ✓，
**未落** ✗，**登记为下一手** ✓）。
**🔴 不声称** ✗：**不**声称本残余可证 ✗（**两项具名端点** `hgal` ✓／`hProj` ✓ **无证明** ✗
—— 端点的**实体**＝源 `proposition-0-2(c)` ✓／`(a)` ✓，**在册** ✗）；**不**声称残余 ① 已证 ✗；
**不**声称源 `theorem-5-1` 已证 ✗。 -/
def NoetherWiringResidualFixed (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    [DecidableEq G] : Prop :=
  ∃ (n : ℕ) (a : Fin n → NoetherInvariantField F G) (s₀ : NoetherInvariantField F G)
    (t : MvPolynomial G F)
    (_ : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away t))
    (_ : IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away t))
    (_ : MulSemiringAction G (Localization.Away t))
    (ht : t ≠ 0)
    (hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀)) (x : Localization.Away t),
      g • (r • x) = r • (g • x)),
    AlgebraicIndependent F a ∧
      IntermediateField.adjoin F (Set.range a) = ⊤ ∧
      s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin F (Set.range a) ∧
      (∀ (g : G) (i : Fin n),
        g • ((a i : NoetherInvariantField F G) : NoetherField F G)
          = ((a i : NoetherInvariantField F G) : NoetherField F G)) ∧
      (∀ g : G, g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
        = ((s₀ : NoetherInvariantField F G) : NoetherField F G)) ∧
      (∀ g : G, g • t = t) ∧
      (noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)))) ∧
      (∀ (g : G) (p : MvPolynomial G F),
        g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
          = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p)) ∧
      BTier.IsGaloisWithGroup ↥(noetherFixedCarrier F G a s₀) (Localization.Away t) G hRG ∧
      BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a s₀) (Localization.Away t) G hRG ∧
      (∀ r : ↥(noetherFixedCarrier F G a s₀),
        awayToFieldAlg (F := F) (G := G) t ht
            (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away t) r)
          = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r)

set_option maxHeartbeats 1000000 in
/-- **归约（源 `theorem-5-1`，改接版）** ✓✅：**残余 ④ ＋ 残余 ① ⟹ `Theorem51Statement F G`** ✓。

**⚠ 证明体** ✓（**三步** ✓）：**①** 把 `L^G` 数据**强制搬进 `L`** ✓ —— `hind` ✓（(甲) ① ✓，`.mp` ✓）、
`hs_0` ✓（隶属单射 ✓）、`s_0 \in F[a]` ✓（(甲) ② ✓）；**②** **(a) 款由 (乙) ② 产出** ✓✅
（**不再**经 r188 ✓，**故不需 `hgen`** ✗）；**③** 余行**逐位喂给 §4.60** ✓
（`nonempty\_genericExtensionWitnessFieldFinite\_of\_subalgebra` ✓，**不重证** ✓），
其中 `hS_{\rm fix}` ✓ 由 **§4.47** ✓（`smul\_eq\_self\_of\_mem\_adjoin\_of\_fixed` ✓）从**两条不动行**得 ✓；
再经**残余 ①** ✓（`nonempty\_...\_of\_fieldFinite\_and\_ringBridge` ✓）搬成**源形见证** ✓。
**⚠ `L` 与 `hL` 全程闲置** ✓（`theorem51Statement_of_witness` ✓ 的观察 ✓）。
**🔴 不声称** ✗：**不**声称残余 ④ 可证 ✗（**两项具名端点** ✗）；**不**声称残余 ① 已证 ✗；
**不**声称两条源陈述已证 ✗。 -/
theorem theorem51Statement_of_noetherWiringResidualFixed_and_ringBridge
    (hb : RealizationRingTierBridge F G) (hw : NoetherWiringResidualFixed F G) :
    Theorem51Statement F G := by
  intro hinf L _ _ _ _ _
  obtain ⟨n, a, s₀, t, instA, instT, instM, ht, hRG, hind, _hgen, hs₀, hs₀_mem, ha_fix, hs₀_fix,
    htinv, hle, hact_map, hgal, hProj, hS₀R⟩ := hw
  have hindL : AlgebraicIndependent F
      (fun i => ((a i : NoetherInvariantField F G) : NoetherField F G)) :=
    (algebraicIndependent_coe_iff_of_subalgebra
      (FixedPoints.intermediateField (F := F) (E := NoetherField F G) G).toSubalgebra a).mp hind
  have hs₀L : ((s₀ : NoetherInvariantField F G) : NoetherField F G) ≠ 0 :=
    fun h => hs₀ (Subtype.ext h)
  have hs₀_memL : ((s₀ : NoetherInvariantField F G) : NoetherField F G)
      ∈ Algebra.adjoin F
        (Set.range (fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))) :=
    mem_adjoin_coe_of_mem_adjoin
      (FixedPoints.intermediateField (F := F) (E := NoetherField F G) G).toSubalgebra hs₀_mem
  have ha := exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul
    hindL hs₀L hs₀_memL
  exact nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge hb
    (nonempty_genericExtensionWitnessFieldFinite_of_subalgebra
      (S := noetherFixedCarrier F G a s₀) ht htinv hle
      (smul_eq_self_of_mem_adjoin_of_fixed ha_fix hs₀_fix) hact_map hRG hgal hProj hS₀R hinf
      ⟨n, ha⟩)

#print axioms NoetherWiringResidualFixed
#print axioms theorem51Statement_of_noetherWiringResidualFixed_and_ringBridge

end FixedWiringResidual

/-! ### K. **L1 非空探针**：残余 ④ 的**数据部分非空** ✓✅（**两式**：一般档（条件）＋ `ℚ`／`PUnit` 档（无条件）） -/

section FixedWiringDataProbe

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- **L1 非空探针 ①（一般档，**由源假设**）** ✓✅：**源假设** `\mathrm{IsRationalOver}\ F\ L^G` ✓ ⟹
**残余 ④ 的数据部分非空** ✓ —— 即 §D ✓ 判定为空的那**两行冲突**在改接后**不再出现** ✓✅。
**⚠ 证明** ✓（**两行** ✓）：**§E** ✓ 的 `exists\_fixed\_transcendenceBasis\_of\_isRationalOver` ✓ 直接给
`a` ✓（代数无关 ✓ ＋ 生成 `L^G` ✓ ＋ **被每个 `g` 固定** ✓）；取 **`s_0 := 1`** ✓
（`1 \neq 0` ✓；`1 \in F[a]` ✓ **因任何子代数含 `1`** ✓）。
**⚠ 判别力** ✓：本条是**定理**（**非**断言 ✗）—— **`hgen` 读在 `L` 的旧读法下** ✗ 本条**不可能**成立 ✓
（§D ✓）；**若把第 2 行的域改回 `L`** ✗，本证明**立即失败** ✗（`hind` 与 `hgen` 的类型不匹配 ✗）。
**🔴 不声称** ✗：**不**声称残余 ④ 本身非空 ✗（**另两行** `hgal` ✓／`hProj` ✓ **不在本探针内** ✗）；
**不**声称 `\mathrm{IsRationalOver}\ F\ L^G` 可证 ✗（**那正是 Noether 问题** ✓，`G = C_{47}` ✓ 时为假 ✓）。 -/
theorem exists_fixedWiringData_of_isRationalOver
    (h : IsRationalOver F (NoetherInvariantField F G)) :
    ∃ (n : ℕ) (a : Fin n → NoetherInvariantField F G) (s₀ : NoetherInvariantField F G),
      AlgebraicIndependent F a ∧ IntermediateField.adjoin F (Set.range a) = ⊤ ∧
        s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin F (Set.range a) := by
  obtain ⟨n, a, hind, hgen, _hfix⟩ :=
    exists_fixed_transcendenceBasis_of_isRationalOver (F := F) (G := G) (L := NoetherField F G) h
  exact ⟨n, a, 1, hind, hgen, one_ne_zero, one_mem _⟩

#print axioms exists_fixedWiringData_of_isRationalOver

end FixedWiringDataProbe


section AdjoinTransportAlongEquiv

variable {F : Type} [Field F] {E E' : Type} [Field E] [Field E'] [Algebra F E] [Algebra F E']

/-- **(甲) ④ 中间域 `adjoin` 的顶沿 `AlgEquiv` 搬运** ✓✅（**双向** ✓）：
`\mathrm{adjoin}_F(\mathrm{range}\ a) = \top` ✓ ⟺ 其**沿 `e` 的像族**的 `\mathrm{adjoin}` 为 `\top` ✓。
**证明** ✓：**`\mathrm{IntermediateField.adjoin\_map}`** ✓ ＋ **`\mathrm{IntermediateField.map\_injective}`** ✓
＋ `\mathrm{map}\ e\ \top = \top` ✓（**满射** ✓：`y = e (e^{-1} y)` ✓）。
**⚠ 用途** ✓：`\mathbb{Q}`／`\mathrm{PUnit}` 档的 `hgen` ✓ 探针（**先把 `L^G = \top` 化成 `\mathrm{AlgEquiv}`** ✓，
**避开**在目标里 `\mathrm{rw}` 掉 `\uparrow I` 的**依赖类型** ✗ —— **本轮实测**：`\mathrm{rw}\ [h_I]` 报
`motive is not type correct` ✗，**因 `a'` 的类型依赖 `I`** ✓）。
**🔴 不声称** ✗：**不**声称本式能搬运**其它**谓词 ✗。 -/
theorem intermediateField_adjoin_eq_top_iff_of_algEquiv (e : E ≃ₐ[F] E') {ι : Type} (a : ι → E) :
    IntermediateField.adjoin F (Set.range a) = ⊤ ↔
      IntermediateField.adjoin F (Set.range (fun i => e (a i))) = ⊤ := by
  have himg : (e : E →ₐ[F] E') '' Set.range a = Set.range (fun i => e (a i)) := by
    rw [← Set.range_comp]
    congr 1
  have hmap : IntermediateField.map (e : E →ₐ[F] E') (IntermediateField.adjoin F (Set.range a))
      = IntermediateField.adjoin F (Set.range (fun i => e (a i))) := by
    rw [IntermediateField.adjoin_map, himg]
  have htop : IntermediateField.map (e : E →ₐ[F] E') (⊤ : IntermediateField F E) = ⊤ := by
    refine le_antisymm le_top ?_
    intro y _
    exact (IntermediateField.mem_map (⊤ : IntermediateField F E)).mpr
      ⟨e.symm y, trivial, e.apply_symm_apply y⟩
  constructor
  · intro h
    rw [← hmap, h, htop]
  · intro h
    refine IntermediateField.map_injective (e : E →ₐ[F] E') ?_
    rw [hmap, h, htop]

#print axioms intermediateField_adjoin_eq_top_iff_of_algEquiv

end AdjoinTransportAlongEquiv

/-! ### L. **L1 非空探针 ②（`\mathbb{Q}`／`\mathrm{PUnit}` 档，**无条件**）** -/

/-- **L1 非空探针 ②（`F = \mathbb{Q}` ✓／`G = \mathrm{PUnit}` ✓ 档，**无条件**）** ✓✅：
**残余 ④ 的数据部分在测试实例上非空** ✓ —— 见证 ＝ `n = 1` ✓、`a` ＝ r237 ✓ 的见证者之**强制像** ✓、
`s_0 := 1` ✓。
**⚠ 两行来历** ✓：**①** `hind` ✓（**读在 `L^G`** ✓）＝ r237 ✓ 的 `hind` ✓（**读在 `L`** ✓）沿
**(甲) ①** ✓ 的 **`.mpr`** ✓ 搬入 ✓；**②** `hgen` ✓（**读在 `L^G`** ✓，**＝ 改接的要害行** ✓）＝
r237 ✓ 的 `hgen` ✓（**读在 `L`** ✓）沿 **(甲) ④** ✓ 的 **`.mpr`** ✓ 搬入 ✓，
其中 `L^G = \top` ✓ 由 **`noetherInvariantField_pUnit`** ✓ 化成 **`\mathrm{AlgEquiv}`** ✓
（`\mathrm{IntermediateField.equivOfEq}` ✓ ＋ **`\mathrm{IntermediateField.topEquiv}`** ✓）——
**⚠ 不走代数档** ✗（代数档等式须 `[\mathrm{Algebra.IsAlgebraic}\ F\ L]` ✗，本题**超越** ✗）。
**⚠ `s_0 := 1` 的理由** ✓（**如实** ✗）：把 r237 的 `s_0 \in F[a]` ✓（**读在 `L`** ✓）**拉回** `L^G` ✗
须另证（**该方向不属本节两式** ✗，**本轮未落** ✗）；而 `s_0` 在残余 ④ 中**只受两条约束** ✓
（`s_0 \neq 0` ✓ ＋ `s_0 \in F[a]` ✓），`1` **两条皆满足** ✓ ⟹ **取 `1` 即可** ✓。
**🔴 不声称** ✗：**不**声称残余 ④ **整体**非空 ✗ —— `hgal` ✓／`hProj` ✓ 与 wiring 各行
（`t` ✓／三实例 ✓／`hle` ✓／`hact_{\rm map}` ✓／`hS_0R` ✓）**不在本探针内** ✗：
r249 ✓ 逐行供给的是**残余 ② 的表** ✓（**读在 `L`** ✓），**未打包为残余 ④ 的项** ✗（**登记** ✓，
**下一手** ✓）；**不**声称两条源陈述已证 ✗。 -/
theorem exists_fixedWiringData_pUnit_rat :
    ∃ (n : ℕ) (a : Fin n → NoetherInvariantField ℚ PUnit.{1})
      (s₀ : NoetherInvariantField ℚ PUnit.{1}),
      AlgebraicIndependent ℚ a ∧ IntermediateField.adjoin ℚ (Set.range a) = ⊤ ∧
        s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin ℚ (Set.range a) := by
  obtain ⟨a, -, -, hind, hgen, -, -, -, -, -, -, -, -⟩ := exists_noetherWiringData_pUnit_rat
  have hI : FixedPoints.intermediateField (F := ℚ) (E := NoetherField ℚ PUnit.{1}) PUnit.{1} = ⊤ :=
    noetherInvariantField_pUnit
  let a' : Fin 1 → NoetherInvariantField ℚ PUnit.{1} := fun i => ⟨a i, by rw [hI]; trivial⟩
  refine ⟨1, a', 1, ?_, ?_, one_ne_zero, one_mem _⟩
  · exact (algebraicIndependent_coe_iff_of_subalgebra
      (FixedPoints.intermediateField (F := ℚ) (E := NoetherField ℚ PUnit.{1}) PUnit.{1}).toSubalgebra
      a').mpr (by simpa using hind)
  · refine (intermediateField_adjoin_eq_top_iff_of_algEquiv
      ((IntermediateField.equivOfEq hI).trans IntermediateField.topEquiv) a').mpr ?_
    show IntermediateField.adjoin ℚ (Set.range (fun _ : Fin 1 =>
      ((IntermediateField.equivOfEq hI).trans IntermediateField.topEquiv) (a' _))) = ⊤
    exact hgen

#print axioms exists_fixedWiringData_pUnit_rat


/-! ### N. **(丙) 机器件的**不动域版**（r259 ✓ 的 `noetherWiringMachinery_of_sourceData` ✓ 的改接形）** -/

section FixedWiringMachinery

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

set_option maxHeartbeats 1000000 in
/-- **(丙) 机器 6 行的不动域版** ✓✅：**不动域数据** `a` ✓／`s_0` ✓ ＋ **两条不动行** ✓ ⟹
**残余 ④ 的机器各行**（`t` ✓／三实例 ✓／`ht` ✓／`t` 不变化 ✓／`hle` ✓／`hact_map` ✓／`hRG` ✓／`hS_0R` ✓）**存在** ✓
—— 即 **r259 ✓ 的 `noetherWiringMachinery_of_sourceData` ✓**（**读在 `L`** ✓）**的不动域形** ✓。
**⚠ 证明** ✓（**一步** ✓）：把**不动域数据**经**强制转换**搬进 `L` ✓（`hs_0 \neq 0` ✓ 由**隶属单射** ✓，
**两条不动行原样可用** ✓ —— **其类型本就是「强制转换后的元素」** ✓，**此即改接的便利处** ✓），
再**逐位喂给 r259** ✓（**不重证** ✓）。
**⚠ 用途** ✓：探针 ③ ✓（**数据 ＋ 机器 ＝ 残余 ④ 减两行端点** ✓，**已消费本件** ✓）。
**🔴 不声称** ✗：**不**声称 `t` 唯一 ✗（**r259 ✓ 的 `t` 是**构造产出**** ✓，`\mathrm{Classical.choose}` 档 ✓）；
**不**声称两项具名端点（`hgal` ✓／`hProj` ✓）随之可得 ✗（**它们不在 r259 的输出内** ✗）。 -/
theorem exists_noetherFixedWiringMachinery {n : ℕ} (a : Fin n → NoetherInvariantField F G)
    (s₀ : NoetherInvariantField F G) (hs₀ : s₀ ≠ 0)
    (ha_fix : ∀ (g : G) (i : Fin n),
      g • ((a i : NoetherInvariantField F G) : NoetherField F G)
        = ((a i : NoetherInvariantField F G) : NoetherField F G))
    (hs₀_fix : ∀ g : G, g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
        = ((s₀ : NoetherInvariantField F G) : NoetherField F G)) :
    ∃ (t : MvPolynomial G F) (ht : t ≠ 0)
      (_ : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away t))
      (_ : IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away t))
      (_ : MulSemiringAction G (Localization.Away t)),
      (∀ g : G, g • t = t) ∧
      (noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹} : Set (NoetherField F G)))) ∧
      (∀ (g : G) (p : MvPolynomial G F),
        g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
          = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p)) ∧
      (∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀)) (x : Localization.Away t),
        g • (r • x) = r • (g • x)) ∧
      (∀ r : ↥(noetherFixedCarrier F G a s₀),
        awayToFieldAlg (F := F) (G := G) t ht
            (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away t) r)
          = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r) := by
  have hs₀L : ((s₀ : NoetherInvariantField F G) : NoetherField F G) ≠ 0 :=
    fun h => hs₀ (Subtype.ext h)
  exact noetherWiringMachinery_of_sourceData (F := F) (G := G)
    (fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    ((s₀ : NoetherInvariantField F G) : NoetherField F G) hs₀L ha_fix hs₀_fix

#print axioms exists_noetherFixedWiringMachinery

end FixedWiringMachinery

/-! ### M. **L1 非空探针 ③／④：残余 ④ **减去两项具名端点**后**整体非空**（数据 ＋ 机器各行） -/

section FixedWiringMachineryProbe

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

set_option maxHeartbeats 1000000 in
/-- **L1 非空探针 ③（一般档，由源假设）** ✓✅：**源假设** `\mathrm{IsRationalOver}\ F\ L^G` ✓ ⟹
**残余 ④ 除两项具名端点外的**全部行**同时成立** ✓ —— 即 **数据 6 行** ✓ ＋ **机器 6 行** ✓
（`ht` ✓／`t` 不变化 ✓／`hle` ✓／`hact_{\rm map}` ✓／`hRG` ✓／`hS_0R` ✓ ＋ **三实例** ✓）。
**⚠ 证明** ✓（**三步** ✓，**不新造** ✗）：**①** 探针 ① ✓ 给**数据**（`a` ✓／`s_0` ✓ 及其四行 ✓）；
**②** 数据**强制搬进 `L`** ✓（(甲) ① ✓ 的 `.mp` ✓；`hs_0 \neq 0` ✓ 由隶属单射 ✓；
**两条不动行** ✓ 由**隶属定义** ✓ `(a\ i).2` ✓／`s_0.2` ✓ —— **§D 的冲突在此彻底消失** ✓✅）；
**③** **r259 ✓ 的 `noetherWiringMachinery_of_sourceData`** ✓ 一次产出**机器 6 行 ＋ 三实例** ✓。
**⚠ 与残余 ④ 的差** ✓（**精确** ✓）：**只差两行** ✗ ＝ **`hgal`** ✓（`\mathrm{IsGaloisWithGroup}` ✓）
＋ **`hProj`** ✓（`\mathrm{GaloisProjectiveHyp}` ✓）—— 即**源 `proposition-0-2` 的两条端点** ✓
（**在册、无证明** ✗）。⟹ **残余 ④ 的空洞性风险全部集中在两项具名端点** ✓（**此即本探针的读数** ✓）。
**🔴 不声称** ✗：**不**声称残余 ④ **整体**非空 ✗（**两行端点在探针之外** ✗）；
**不**声称 `\mathrm{IsRationalOver}\ F\ L^G` 可证 ✗（**那是 Noether 问题** ✓）；
**不**声称 `hgal`／`hProj` 可证 ✗。 -/
theorem exists_fixedWiringData_and_machinery_of_isRationalOver
    (h : IsRationalOver F (NoetherInvariantField F G)) :
    ∃ (n : ℕ) (a : Fin n → NoetherInvariantField F G) (s₀ : NoetherInvariantField F G)
      (t : MvPolynomial G F)
      (_ : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away t))
      (_ : IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away t))
      (_ : MulSemiringAction G (Localization.Away t))
      (ht : t ≠ 0),
      AlgebraicIndependent F a ∧ IntermediateField.adjoin F (Set.range a) = ⊤ ∧
        s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin F (Set.range a) ∧
        (∀ (g : G) (i : Fin n),
          g • ((a i : NoetherInvariantField F G) : NoetherField F G)
            = ((a i : NoetherInvariantField F G) : NoetherField F G)) ∧
        (∀ g : G, g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
          = ((s₀ : NoetherInvariantField F G) : NoetherField F G)) ∧
        (∀ g : G, g • t = t) ∧
        (noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
          (Algebra.adjoin (MvPolynomial G F)
            ({(algebraMap (MvPolynomial G F) (NoetherField F G) t)⁻¹}
              : Set (NoetherField F G)))) ∧
        (∀ (g : G) (p : MvPolynomial G F),
          g • (algebraMap (MvPolynomial G F) (Localization.Away t) p)
            = algebraMap (MvPolynomial G F) (Localization.Away t) (g • p)) ∧
        (∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀)) (x : Localization.Away t),
          g • (r • x) = r • (g • x)) ∧
        (∀ r : ↥(noetherFixedCarrier F G a s₀),
          awayToFieldAlg (F := F) (G := G) t ht
              (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away t) r)
            = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r) := by
  obtain ⟨n, a, s₀, hind, hgen, hs₀, hs₀_mem⟩ := exists_fixedWiringData_of_isRationalOver h
  have ha_fix : ∀ (g : G) (i : Fin n),
      g • ((a i : NoetherInvariantField F G) : NoetherField F G)
        = ((a i : NoetherInvariantField F G) : NoetherField F G) := fun _ i => (a i).2 _
  have hs₀_fix : ∀ g : G, g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
      = ((s₀ : NoetherInvariantField F G) : NoetherField F G) := fun _ => s₀.2 _
  obtain ⟨t, ht, instA, instT, instM, htinv, hle, hact_map, hRG, hS₀R⟩ :=
    exists_noetherFixedWiringMachinery a s₀ hs₀ ha_fix hs₀_fix
  exact ⟨n, a, s₀, t, instA, instT, instM, ht, hind, hgen, hs₀, hs₀_mem, ha_fix, hs₀_fix,
    htinv, hle, hact_map, hRG, hS₀R⟩

#print axioms exists_fixedWiringData_and_machinery_of_isRationalOver

end FixedWiringMachineryProbe


/-! ### O. **登记（r260 总账，逐条如实）** -/

/-- **登记** ✓：**r260 的总账** ——
**(甲) 已落** ✓✅：**数据沿强制转换的搬运四式** ✓（AI ✓（双向 ✓）／`\mathrm{adjoin}` 隶属 ✓（单向 ✓）／
`\mathrm{adjoin}` 顶（中间域档 ✓，双向 ✓）／`\mathrm{adjoin}` 顶沿 `\mathrm{AlgEquiv}` ✓（双向 ✓））；
**(乙) 已落** ✓✅：**分式环无关的 `(a)` 款两件** ✓ —— `\mathrm{IsLocalization.Away}` 结构 ✓
（**去掉 r165 ✓ 的 `[\mathrm{IsFractionRing}\ A\ K]`** ✗）＋ **`(a)` 款无 `hgen` 形** ✓
（**去掉 r188 ✓ 的 `hgen`** ✗）；
**(丙) 已落** ✓✅：**机器 6 行的不动域版** ✓（`exists_noetherFixedWiringMachinery` ✓）；
**(丁) 已落** ✓✅：**残余 ④** ✓（`NoetherWiringResidualFixed` ✓）＋ **归约** ✓
（`theorem51Statement_of_noetherWiringResidualFixed_and_ringBridge` ✓）＋ **L1 探针三式** ✓
（① 一般档数据 ✓（条件 ✓）／② `\mathbb{Q}`／`\mathrm{PUnit}` 档数据 ✓（**无条件** ✓）／
③ 一般档**数据 ＋ 机器** ✓（**＝ 残余 ④ 减两行端点** ✓，条件 ✓））。
**⚠ 未落** ✗（**逐条** ✓）：**(i)** 把**两项具名端点** ✓ 与**机器各行**装进**残余 ④ 的整项** ✗
（**卡点已定位** ✓：r249 ✓ 的 `hgal` ✓／`hProj` ✓ 见证**钉在 `t = X`** ✓ 与**其载体** ✓，
而 (丙) ✓ 产出的 `t` 是**构造性的**（`\mathrm{Classical.choose}` 档 ✓）⟹ **两者不同一** ✗；
**⚠ 且** `\mathbb{Q}`／`\mathrm{PUnit}` 档**另有一层障碍** ✗：`\mathrm{PUnit}` 在 mathlib **另有泛用**
`\mathrm{MulAction}` ✓ ⟹ **语句里的 `\bullet` 与 `\mathrm{Noether}` 作用档可能不同一** ✗
（**本轮实测** ✓：`(a\ i).2` 与目标里的 `\bullet` 类型不符 ✗；r249 ✓ 的工艺读数同款 ✓））；
**(ii)** 两条源陈述 ✓（`Theorem51Statement` ✓／`Theorem21Statement` ✓）**仍未证** ✗；
**(iii)** **残余 ①** ✓（`RealizationRingTierBridge` ✓，CHR 代数版 ✗）**仍开** ✓、**两路共享** ✓；
**(iv)** **`hgen` 的消费件** ✗（`hind + hgen \Rightarrow \mathrm{IsRationalOver}\ F\ L^G` ✓）**未落** ✗
（**故 `hgen` 在归约中不被消费** ✗ —— **如实登记** ✓）。
**🔴 不声称** ✗：**不**声称 (i)--(iv) 任一已落 ✗；**不**声称残余 ④ **整体**非空 ✗；
**不**声称两条源陈述已证 ✗；**不**声称 r206 路线可用 ✗（**非平凡 `G` 档为空** ✗，§D ✓，
**其定理原样保留** ✓）。 -/
theorem noetherWiringResidualFixed_registered : True := trivial

#print axioms noetherWiringResidualFixed_registered


/-! ### P. **r261：`hgen` 的消费件** ✓ —— **相干引理**（数据行 ⟺ 源假设）＋ **加强归约** ✓

**⚠ 本节缘起** ✓（**r260 登记的未落项** ✗，§O ✓ 的 **(iv)** ✓）：§J ✓ 的残余 ④
（`NoetherWiringResidualFixed` ✓）第 2 行 `hgen` ✓（`\mathrm{adjoin}_F(\mathrm{range}\ a) = \top` ✓，
**读在 `L^G`** ✓）在归约 ✓ 中**不被消费** ✗（归约的 `(a)` 款经 (乙) ② ✓ 产出 ✓，**无 `hgen` 形** ✓）。
r260 ✓ 登记的候选件 ＝ `\mathrm{AlgebraicIndependent}\ F\ a` ✓ ＋ `\mathrm{adjoin} = \top` ✓
`\Rightarrow \mathrm{IsRationalOver}\ F\ L^G` ✓ —— **本轮落** ✓✅（**判为真** ✓，**见 §P.1** ✓）。

**⚠ 先定谓词** ✓（**同名两件取哪一件** ✓）：本链（`SaltThm38` ✓ ← `SaltGeneric` ✓）用的是
**`SaltGeneric_ABGV52.lean:210`** ✓ 的 `\mathrm{IsRationalOver}` ✓ —— **基 `F`** ✓、
右端 `K \simeq_F \mathrm{FractionRing}(\mathrm{MvPolynomial}\ (\mathrm{Fin}\ n)\ F)` ✓。
**另一件同名者** ✗（`SaltRatOver_ABGV52.lean:72` ✓，**基 `L`** ✓、右端 `EM.rationalFunctionField L n` ✓）
**不在本链的 import 闭包内** ✓（**本轮实测** ✓：`SaltThm38` ✓ 的闭包 38 件**不含** `SaltRatOver` ✓；
后者**只**被 `ProcConsume` ✓ 引 ✓）—— **⚠ 登记** ✓：**两件同名** ✗ **分居两条不相交分支** ✓
（**同时引二者即撞名** ✗）；**本件不动** ✗，**只登记** ✓。

**⚠ 三条结果** ✓：**①** **相干引理** ✓（§P.2 ✓，**锐形** ✓：同构**取生成元个数 `n`** ✓）；
**②** **双侧等价** ✓（§P.3 ✓：`\exists n\,a,\ \mathrm{hind} \wedge \mathrm{hgen}` ✓ ⟺
`\mathrm{IsRationalOver}` ✓，**逆向 ＝ r151 ✓ 的
`exists\_algebraicIndependent\_adjoin\_eq\_top\_of\_isRationalOver`** ✓）
⟹ **残余 ④ 的数据行与源假设 `\mathrm{IsRationalOver}\ F\ L^G` ✓ 等价** ✓✅（§P.5 ✓）；
**③** **加强归约** ✓（§P.7 ✓：残余 ④ ＋ 残余 ① ⟹ `\mathrm{Theorem51Statement}` ✓ **且**
`\mathrm{IsRationalOver}\ F\ L^G` ✓ —— **`hgen` 在此被消费** ✓✅）。

**🔴 后果（承重，如实登记** ✓**）**：由 **②** ✓，**残余 ④ 的数据行 ⟹ Noether 问题在 `G` 上为真** ✓
（该 `L = F(x_\sigma)` ✓ 即 `\mathrm{NoetherField}` ✓，**与源 `theorem-5-1` ✓ 的 `L^G` ✓ 同一个** ✓）
⟹ **残余 ④ 在「Noether 问题为假」的 `G` 上为假** ✗（源 `remark` ✓ 印 275 ✓ 逐字：
「The **converse** of `theorem-5-1` is **false**. `C_{47}` has a generic extension over `Q`, but
**Swan showed Noether's Problem false** for this group」✓ —— **⚠ 该外部结果本件未形式化** ✗
⟹ **本节不声称 `C_{47}` 档为假** ✗，**只声称上述蕴含** ✓，**并把它登记为下一手的口径问题** ✓）。

**🔴 不声称** ✗：**不**声称两条源陈述已证 ✗；**不**声称残余 ①（`RealizationRingTierBridge` ✓）已证 ✗；
**不**声称残余 ④ 整体非空 ✗（**两项具名端点** ✓ 在探针之外 ✗）。 -/

section HgenCoherence

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- **相干引理（**锐形**）** ✓✅：`a` 在 `F` 上**代数无关** ✓ ＋ 其**域 `adjoin` 为 `\top`** ✓ ⟹
**`K \simeq_F F(t_1,\dots ,t_n)`** ✓ —— **⚠ 锐在 `n`** ✓：同构**取生成元个数** ✓
（**不是**「某 `n`」✗；理由：`F(a_1,\dots ,a_n)` ✓ 由**代数无关** ✓ 直接同构于**变元的有理函数域** ✓）。
**证明** ✓（**库内两件拼接** ✓，**不新造** ✗）：mathlib **`\mathrm{AlgebraicIndependent.aevalEquivField}`** ✓
（`RingTheory/AlgebraicIndependent/Adjoin.lean:41` ✓）
＝ `\mathrm{FractionRing}(\mathrm{MvPolynomial}\ \iota\ F) \simeq_F \uparrow(\mathrm{adjoin}_F(\mathrm{range}\ x))` ✓；
再经 **`\mathrm{IntermediateField.equivOfEq}`** ✓（喂 `hgen` ✓）＋
**`\mathrm{IntermediateField.topEquiv}`** ✓（`FieldTheory/IntermediateField/Adjoin/Defs.lean:239` ✓）收 ✓。
**⚠ 用途** ✓：§P.5 ✓（源假设的回收 ✓）＋ §P.7 ✓（加强归约 ✓）。
**🔴 不声称** ✗：**不**声称 `hgen` 可去 ✗（**去之则本式对一般的给定 `a` 为假** ✗ ——
**判别力见证见 §P.8** ✓，**⚠ 只覆盖空族档** ✗，**非空族档登记为未落** ✗）。 -/
theorem nonempty_algEquiv_fractionRing_of_algebraicIndependent_adjoin_eq_top {n : ℕ}
    {a : Fin n → K} (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤) :
    Nonempty (K ≃ₐ[F] FractionRing (MvPolynomial (Fin n) F)) :=
  ⟨((hind.aevalEquivField.trans (IntermediateField.equivOfEq hgen)).trans
    IntermediateField.topEquiv).symm⟩

#print axioms nonempty_algEquiv_fractionRing_of_algebraicIndependent_adjoin_eq_top

/-- **相干引理（`\exists`-形，即 r260 ✓ 登记的候选件** ✓✅**）**：**`\mathrm{IsRationalOver}\ F\ K`** ✓
—— 本链 ✓ 的谓词档 ✓（`SaltGeneric:210` ✓）。
**证明** ✓：**一行** ✓ —— 锐形 ✓ 喂 `n` ✓。 -/
theorem isRationalOver_of_algebraicIndependent_adjoin_eq_top {n : ℕ} {a : Fin n → K}
    (hind : AlgebraicIndependent F a) (hgen : IntermediateField.adjoin F (Set.range a) = ⊤) :
    IsRationalOver F K :=
  ⟨n, nonempty_algEquiv_fractionRing_of_algebraicIndependent_adjoin_eq_top hind hgen⟩

#print axioms isRationalOver_of_algebraicIndependent_adjoin_eq_top

/-- **双侧等价** ✓✅（**本节的**相干性**核心** ✓）：`\mathrm{IsRationalOver}\ F\ K` ✓ ⟺
**存在**一代数无关族 ✓ 其**域 `adjoin` 为 `\top`** ✓。
**证明** ✓（**两向各一件** ✓）：**⟸** ＝ 上件 ✓；**⟹** ＝ **r151 ✓ 的
`exists\_algebraicIndependent\_adjoin\_eq\_top\_of\_isRationalOver`** ✓（`SaltGeneric:1503` ✓，
**同构 ⟹ 取出变元族** ✓）—— **故两向皆库内既有件** ✓，本件**只连线** ✓。
**⚠ 意义** ✓：**「`\mathrm{hind}` ＋ `\mathrm{hgen}`」这一对** ✓ **恰是源假设** ✓
（**既不更强也不更弱** ✓）⟹ 残余 ④ 的数据 6 行 ✓ **不是**额外汇线 ✗（见 §P.5 ✓）。
**🔴 不声称** ✗：**不**声称**单独**任一行等价于源假设 ✗（**两行缺一不可** ✗；
**⚠ `hind` 不可去**：**见证**＝§P.8 ✓ **只覆盖空族** ✗；**`hgen` 不可去**：**本轮未落见证** ✗）。 -/
theorem exists_algebraicIndependent_adjoin_eq_top_iff_isRationalOver :
    (∃ (n : ℕ) (a : Fin n → K), AlgebraicIndependent F a ∧
      IntermediateField.adjoin F (Set.range a) = ⊤) ↔ IsRationalOver F K :=
  ⟨fun ⟨_, _, hind, hgen⟩ => isRationalOver_of_algebraicIndependent_adjoin_eq_top hind hgen,
    exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver⟩

#print axioms exists_algebraicIndependent_adjoin_eq_top_iff_isRationalOver

/-- **L1 非空探针** ✓✅（**假设类非空** ✓ ＋ **本引理的正例对照** ✓）：**在 `F(t_1,\dots ,t_n)` 自身上**
（`K := \mathrm{FractionRing}(\mathrm{MvPolynomial}\ (\mathrm{Fin}\ n)\ F)` ✓，**无条件** ✓）
**同时给出一对满足两行的数据** ✓ **并**由**相干引理** ✓（**本件的证明确实调用它** ✓）**收回结论** ✓。
**证明** ✓：**正向等价** ✓（`isRationalOver_self` ✓ ＋ **r151** ✓）给数据 ✓，再喂 §P.2 ✓。
**⚠ 判别力** ✓：本件是**定理**（**非**断言 ✗）—— **若相干引理的任一行被改坏** ✗，**本件编译失败** ✓
（**根因** ✓：`hind` ✓ 与 `hgen` ✓ **在此数据上都是真的** ✓，**且结论非平凡** ✓）。
**🔴 不声称** ✗：**不**声称该数据族**唯一** ✗。 -/
theorem exists_coherenceData_fractionRing (F : Type u) [Field F] (n : ℕ) :
    ∃ (m : ℕ) (a : Fin m → FractionRing (MvPolynomial (Fin n) F)),
      AlgebraicIndependent F a ∧ IntermediateField.adjoin F (Set.range a) = ⊤ ∧
        IsRationalOver F (FractionRing (MvPolynomial (Fin n) F)) := by
  obtain ⟨m, a, hind, hgen⟩ :=
    exists_algebraicIndependent_adjoin_eq_top_of_isRationalOver (F := F)
      (K := FractionRing (MvPolynomial (Fin n) F)) (isRationalOver_self F n)
  exact ⟨m, a, hind, hgen,
    isRationalOver_of_algebraicIndependent_adjoin_eq_top hind hgen⟩

#print axioms exists_coherenceData_fractionRing

end HgenCoherence

section HgenCoherenceNoether

variable {F : Type} [Field F] {G : Type} [Group G]

/-- **相干引理的**不动域专用形** ✓✅**：数据取在 `L^G` ✓（`\mathrm{NoetherInvariantField}\ F\ G` ✓，§H ✓）——
即 **§J ✓ 的残余 ④ 的**同两款载体** ✓（**归约所用的那两款** ✓）。
**证明** ✓：**一行** ✓（一般档 ✓ 的直接用点 ✓，**不重证** ✗）。
**⚠ 用途** ✓：§P.5 ✓／§P.6 ✓／§P.7 ✓ **三处** ✓。
**🔴 不声称** ✗：**不**声称 `\mathrm{IsRationalOver}\ F\ L^G` 可证 ✗（**那正是 Noether 问题** ✓，
**`G = C_{47}` ✓ 时为假** ✓ —— **⚠ 源侧** ✓，**本件未形式化** ✗）。 -/
theorem isRationalOver_noetherInvariantField_of_algebraicIndependent_adjoin_eq_top {n : ℕ}
    {a : Fin n → NoetherInvariantField F G} (hind : AlgebraicIndependent F a)
    (hgen : IntermediateField.adjoin F (Set.range a) = ⊤) :
    IsRationalOver F (NoetherInvariantField F G) :=
  isRationalOver_of_algebraicIndependent_adjoin_eq_top hind hgen

#print axioms isRationalOver_noetherInvariantField_of_algebraicIndependent_adjoin_eq_top

/-- **残余 ④ 的数据行 ⟺ 源假设** ✓✅（**本轮的**主件** ✓**）：**源假设** `\mathrm{IsRationalOver}\ F\ L^G` ✓
（**与 `Theorem51Statement` ✓ 的前提逐字同款** ✓）**⟺** **数据 6 行** ✓
（`\exists n,a,s_0` ✓ ＋ `hind` ✓ ＋ `hgen` ✓ ＋ `s_0 \neq 0` ✓ ＋ `s_0 \in F[a]` ✓
—— **即 r260 ✓ 的 `exists\_fixedWiringData\_of\_isRationalOver` ✓ 的整个右端** ✓）。
**证明** ✓：**⟹** ＝ **r260 ✓ 的探针 ①** ✓（**原样** ✓，**不重证** ✗）；
**⟸** ＝ **§P.4** ✓（**`hgen` 在此被消费** ✓✅；**⚠ `s_0` 两行不承重** ✓ —— `s_0 := 1` ✓ 即可满足 ✓）。
**⚠ 意义** ✓（**解 r260 的未消费登记** ✓✅）：**数据行与源假设等价** ✓ ⟹
`hgen` ✓ **既不可去** ✗ **也非多余** ✗ —— 它**正是源假设的域生成半** ✓
（**§D ✓ 判定为空的那一款读法** ✗ 是**把源假设读错了域** ✗）。
**🔴 不声称** ✗：**不**声称残余 ④ **整项**等价于源假设 ✗（**机器 6 行** ✓ 与**两项具名端点** ✓
**不在**本件的右端 ✗ —— **端点是附加的** ✓；**「数据 ＋ 机器」由源假设可造** ✓ 见 r260 ✓ 的探针 ③ ✓）。 -/
theorem isRationalOver_noetherInvariantField_iff_exists_fixedWiringData :
    IsRationalOver F (NoetherInvariantField F G) ↔
      ∃ (n : ℕ) (a : Fin n → NoetherInvariantField F G) (s₀ : NoetherInvariantField F G),
        AlgebraicIndependent F a ∧ IntermediateField.adjoin F (Set.range a) = ⊤ ∧
          s₀ ≠ 0 ∧ s₀ ∈ Algebra.adjoin F (Set.range a) :=
  ⟨exists_fixedWiringData_of_isRationalOver,
    fun ⟨_, _, _, hind, hgen, _, _⟩ =>
      isRationalOver_noetherInvariantField_of_algebraicIndependent_adjoin_eq_top hind hgen⟩

#print axioms isRationalOver_noetherInvariantField_iff_exists_fixedWiringData

end HgenCoherenceNoether

section HgenCoherenceResidual

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **残余 ④ ⟹ 源假设** ✓✅（**`hgen` 的第一处消费** ✓）：**残余 ④ 的第 1、2 两行** ✓
（`hind` ✓ ＋ `hgen` ✓，**分别即 §P.4 的两条前提** ✓）**⟹** `\mathrm{IsRationalOver}\ F\ L^G` ✓。
**证明** ✓：`\mathrm{obtain}` ✓ 出 18 行 ✓，**只喂第 1、2 行** ✓（**其余 16 行原样闲置** ✓，
**不重证** ✗）＋ §P.4 ✓。
**⚠ 意义（承重** ✓**）**：**残余 ④ 蕴含 Noether 问题在 `G` 上为真** ✓（`L^G` ✓ 即 Noether 构造 ✓）
⟹ **它不是「比源假设更弱的一组机器行」** ✓，而是**把源假设写成了数据行** ✓✅。
**🔴 不声称** ✗：**不**声称 `\mathrm{IsRationalOver}\ F\ L^G` 本身可证 ✗（**那是 Noether 问题** ✓）；
**不**声称 `C_{47}` 档为假 ✗（**须 Swan 1969** ✓，**未形式化** ✗，**只登记口径** ✓）。 -/
theorem isRationalOver_noetherInvariantField_of_noetherWiringResidualFixed
    (hw : NoetherWiringResidualFixed F G) :
    IsRationalOver F (NoetherInvariantField F G) := by
  obtain ⟨n, a, _s₀, _t, _iA, _iT, _iM, _ht, _hRG, hind, hgen, _rest⟩ := hw
  exact isRationalOver_noetherInvariantField_of_algebraicIndependent_adjoin_eq_top hind hgen

#print axioms isRationalOver_noetherInvariantField_of_noetherWiringResidualFixed

set_option maxHeartbeats 1000000 in
/-- **加强归约** ✓✅（**`hgen` 的第二处消费，即 r260 归约的加强形** ✓）：**残余 ④ ＋ 残余 ① ⟹
`\mathrm{Theorem51Statement}\ F\ G` **且** `\mathrm{IsRationalOver}\ F\ L^G`** ✓。
**⚠ 与 r260 ✓ 的归约 ✓ 的关系** ✓（**原样保留** ✓，**只追加** ✓）：第一合取**就是** r260 ✓ 的归约 ✓
（**不重证** ✗）；**新增的第二合取** ✓ **必须**消费 `hgen` ✓（**§P.6** ✓）—— 故本件**严格强于** r260 ✓ 的归约 ✓，
且**把 r260 ✓ 登记的**未消费** ✗ 变成**已消费** ✓✅。
**⚠ 为什么不在 r260 ✓ 的定理体里消费** ✗（**如实** ✓）：**只追加** ✓ 的约束下**不得改**旧定理 ✓；
且 r260 ✓ 的**证明路**（(乙) ② ✓）**在数学上确实不需要** `hgen` ✗ ⟹ **旧定理无需修改** ✓：
`hgen` 的**承重处**在于**它使数据行与源假设等价** ✓（§P.5 ✓），而**不是**在于旧的证明路 ✓。
**🔴 不声称** ✗：**不**声称第二合取可去残余 ④ 的其余行 ✗；**不**声称源陈述已证 ✗
（**残余 ①** ✓ 与**两项具名端点** ✓ **仍开** ✓）。 -/
theorem theorem51Statement_and_isRationalOver_of_noetherWiringResidualFixed_and_ringBridge
    (hb : RealizationRingTierBridge F G) (hw : NoetherWiringResidualFixed F G) :
    Theorem51Statement F G ∧ IsRationalOver F (NoetherInvariantField F G) :=
  ⟨theorem51Statement_of_noetherWiringResidualFixed_and_ringBridge hb hw,
    isRationalOver_noetherInvariantField_of_noetherWiringResidualFixed hw⟩

#print axioms theorem51Statement_and_isRationalOver_of_noetherWiringResidualFixed_and_ringBridge

end HgenCoherenceResidual

section HgenCoherenceDiscrimination

/-- **判别力见证（`hind` 不蕴含 `hgen`）** ✓（**⚠ 只覆盖空族档** ✗，**如实登记** ✓）：
在 `K = F(x)` ✓（`\mathrm{FractionRing}(\mathrm{MvPolynomial}\ (\mathrm{Fin}\ 1)\ F)` ✓）上取**空族** ✓
（`a : \mathrm{Fin}\ 0 \to K` ✓）—— **`hind` 真** ✓（**空族恒代数无关** ✓，
`algebraicIndependent_empty_type` ✓）**而 `\mathrm{adjoin}_F \emptyset = \bot \neq \top`** ✓
（**`x` 不是常数** ✓：若 `x = \mathrm{algebraMap}\ c` ✓ 则 `X_0 = C\ c` ✗，
**用 `\mathrm{eval}` 在 `1` 与 `0` 两点取值** ✓ 得 `c = 1` ✓ 与 `c = 0` ✓ ⟹ `1 = 0` ✗）。
**⚠ 读数** ✓：**两行逻辑独立** ✓ ⟹ **§P.2 的两条前提缺一不可** ✓（**本件给的是「去 `hgen` 则结论无从谈起」的**
实例** ✓ —— **不是**「去掉 `hgen` 后 §P.2 为假」的证明 ✗，**因为 `\mathrm{IsRationalOver}` 是 `\exists n` 形** ✓，
**空族档下结论仍真** ✓）。
**⚠ 未落** ✗（**下一手** ✓）：**非空族档**的见证 ✓（`K = F(x_0,x_1)` ✓、`a = (x_0)` ✓）须
`x_1 \notin F(x_0)` ✓ —— **域档的 `\mathrm{option\_iff}`** ✓（**mathlib 只有子代数档** ✗，
`RingTheory/AlgebraicIndependent/Transcendental.lean:101` ✓ 的 `\mathrm{adjoin}` ✓ 是**子代数** ✓）
**或 `\mathrm{trdeg}` 论证** ✓，**本轮未落** ✗。
**🔴 不声称** ✗：**不**声称 §P.2 的两条前提**不**能同时满足 ✗（**恰恰相反** ✓，§P.3 ✓ 的探针 ✓ 给出同时满足的一族 ✓）。 -/
theorem exists_algebraicIndependent_not_adjoin_eq_top (F : Type u) [Field F] :
    ∃ (a : Fin 0 → FractionRing (MvPolynomial (Fin 1) F)),
      AlgebraicIndependent F a ∧ IntermediateField.adjoin F (Set.range a) ≠ ⊤ := by
  refine ⟨fun i => i.elim0, algebraicIndependent_empty_type, ?_⟩
  rw [Set.range_eq_empty, IntermediateField.adjoin_empty]
  intro h
  have hmem : algebraMap (MvPolynomial (Fin 1) F) (FractionRing (MvPolynomial (Fin 1) F))
      (MvPolynomial.X 0) ∈ (⊥ : IntermediateField F (FractionRing (MvPolynomial (Fin 1) F))) := by
    rw [h]; trivial
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h2 : algebraMap (MvPolynomial (Fin 1) F) (FractionRing (MvPolynomial (Fin 1) F))
      (MvPolynomial.C c) = algebraMap (MvPolynomial (Fin 1) F)
        (FractionRing (MvPolynomial (Fin 1) F)) (MvPolynomial.X 0) := by
    have hC : (algebraMap F (MvPolynomial (Fin 1) F)) c = MvPolynomial.C c := rfl
    rw [← hC, ← IsScalarTower.algebraMap_apply F (MvPolynomial (Fin 1) F)
      (FractionRing (MvPolynomial (Fin 1) F)) c]
    exact hc
  have h3 : (MvPolynomial.C c : MvPolynomial (Fin 1) F) = MvPolynomial.X 0 :=
    IsFractionRing.injective (MvPolynomial (Fin 1) F)
      (FractionRing (MvPolynomial (Fin 1) F)) h2
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (1 : F))) h3
  have h0 := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (0 : F))) h3
  simp at h1 h0
  exact one_ne_zero (h1.symm.trans h0)

#print axioms exists_algebraicIndependent_not_adjoin_eq_top

/-- **L1 非空探针（目标档：`\mathbb{Q}`／`\mathrm{PUnit}`，无条件** ✓✅**）**：
`\mathrm{IsRationalOver}\ \mathbb{Q}\ L^{\mathrm{PUnit}}` ✓ —— **残余 ④ 的数据行在该档无条件可满足** ✓
（**由 r260 ✓ 的探针 ②** ✓：**数据 6 行** ✓ **已无条件供给** ✓），**再经 §P.4** ✓ **收回源假设** ✓。
**⚠ 意义** ✓：**§P.4 在目标载体的一个实例上被无条件实例化** ✓（**L1** ✓）——
即 `G = \mathrm{PUnit}` ✓ 档的 Noether 问题为真 ✓（**`L^G = \top`** ✓，`L = F(x)` ✓ **有理** ✓）。
**🔴 不声称** ✗：**不**声称一般 `G` 档成立 ✗。 -/
theorem isRationalOver_noetherInvariantField_pUnit_rat :
    IsRationalOver ℚ (NoetherInvariantField ℚ PUnit.{1}) := by
  obtain ⟨_n, a, _s₀, hind, hgen, _hs₀, _hmem⟩ := exists_fixedWiringData_pUnit_rat
  exact isRationalOver_noetherInvariantField_of_algebraicIndependent_adjoin_eq_top hind hgen

#print axioms isRationalOver_noetherInvariantField_pUnit_rat

end HgenCoherenceDiscrimination

/-! ### Q. **登记（r261 总账，逐条如实）** -/

/-- **登记** ✓：**r261 的总账** ——
**(甲) 已落** ✓✅：**相干引理两式** ✓（**锐形** ✓（`n` 同 ✓）＋ `\exists`-形 ✓）＋
**双侧等价** ✓（**逆向复用 r151** ✓）＋ **不动域专用形** ✓ ＋ **数据行 ⟺ 源假设** ✓（**主件** ✓）＋
**残余 ④ ⟹ 源假设** ✓ ＋ **加强归约** ✓（**新增 `\mathrm{IsRationalOver}\ F\ L^G` 合取** ✓，
**`hgen` 在此被消费** ✓✅）＋ **L1 探针两式** ✓（**一般档** ✓：`F(t_1,\dots ,t_n)` ✓ 上同时给数据与结论 ✓；
**目标档** ✓：`\mathbb{Q}`／`\mathrm{PUnit}` ✓ **无条件** ✓）＋ **判别力见证一式** ✓（**空族档** ✓）。
**⚠ 未落** ✗（**逐条，含理由** ✓）：**(i)** **非空族档的判别力见证** ✗（`x_1 \notin F(x_0)` ✓ 须
**域档 `\mathrm{option\_iff}`** ✓ 或 `\mathrm{trdeg}` 论证 ✓，**mathlib 未给该形** ✗，**本轮实测** ✓）；
**(ii)** **`C_{47}` 档的否证** ✗（须 **Swan 1969** ✓，**外部结果未形式化** ✗ —— **⚠ 口径问题** ✓：
**由 §P.5 知** ✓ **残余 ④ 蕴含 Noether 问题为真** ✓ ⟹ **凡 Noether 问题为假的 `G`** ✓
**残余 ④ 必假** ✗ ⟹ **该残余的正确用法是「在源假设之下」** ✓（**源 `theorem-5-1` ✓ 本就如此** ✓），
**不得追求无条件证明** ✗）；**(iii)** r260 ✓ 的 **(i)** ✓（**两项具名端点与机器各行装进残余整项** ✗，
**卡点已定位** ✓，**与本节无关** ✓）；**(iv)** 两条源陈述 ✓ **仍未证** ✗；**(v)** 残余 ① ✓ **仍开** ✗（**两路共享** ✓）。
**🔴 不声称** ✗：**不**声称 (i)--(v) 任一已落 ✗；**不**声称两条源陈述已证 ✗；**不**声称残余 ④ 整体非空 ✗。 -/
theorem hgenCoherence_registered : True := trivial

#print axioms hgenCoherence_registered
/-! ### 4.63 **残余 ①（环档桥）的**根因**与**修正形**：`Subsingleton G` 档**已证** -/

open BTier

section RingTierBridgeRootCause

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G]

set_option maxHeartbeats 1000000 in
/-- **零环是 `G`-Galois 的（`G` 亚单档）** ✓：`S = 0`（Lean 取 `PUnit` 的环结构 ✓）时判据三款
**全部自动成立** ✓ —— ① `\mathrm{FaithfulSMul}` ✓ 由 `G` 亚单 ✓；② 环同态款 ✓ 由单点性 ✓；
③ `\delta` 双射 ✓ 由两侧同为单点 ✓。
**🔴 根因** ✓：源 `definition-1-1`(c) 的 `L`-**量词**在库内取**全部** `\mathrm{CommRing}` ✓
⟹ **零环是合法目标** ✗；而源侧 `S/R` `G`-Galois **蕴含** `S` 有限生成投射于 `R`（`proposition-0-2`(a) ✓，
引 [CHR68] p. 13 ✓）—— 零环**秩 0** ✗ 而 `G = \mathrm{PUnit}` 档源侧秩为 `1` ✗
⟹ **零环不在源的量词域内** ✗、却在**库内判据**的量词域内 ✓。
**⚠ 不声称** ✗：**不**声称原形为假已证 ✗（见本节末登记 ✓）。 -/
theorem isGaloisWithGroup_zeroRing_of_subsingleton {K : Type} [CommRing K]
    [MulSemiringAction G PUnit] (hG : Subsingleton G)
    (hKL : ∀ (g : G) (r : K) (t : PUnit), g • (r • t) = r • (g • t)) :
    BTier.IsGaloisWithGroup K PUnit G hKL := by
  have hsingle : ∀ a : PUnit,
      deltaToEndAdd hKL (SkewMonoidAlgebra.single (1 : G) a) = coeffToEnd a := by
    intro a
    rw [deltaToEndAdd_single]
    have hact : actEnd hKL (1 : G) = 1 := by ext t
    rw [hact, mul_one]
  have hsingle_eq : ∀ u : SkewMonoidAlgebra PUnit G,
      u = SkewMonoidAlgebra.single (1 : G) (u.coeff 1) := by
    intro u
    refine SkewMonoidAlgebra.ext (fun g => ?_)
    rw [hG.elim g 1, SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
  have hcoeff : ∀ u : SkewMonoidAlgebra PUnit G, (deltaToEndAdd hKL u) 1 = u.coeff 1 := by
    intro u
    rw [hsingle_eq u]
  refine ⟨⟨fun {a b : G} _ => hG.elim a b⟩, fun g r => Subsingleton.elim _ _, ?_⟩
  constructor
  · intro u v huv
    have h1 : u.coeff 1 = v.coeff 1 := by
      have h2 : (deltaToEndAdd hKL u) 1 = (deltaToEndAdd hKL v) 1 :=
        congrArg (fun f : Module.End K PUnit => f 1) huv
      exact (hcoeff u).symm.trans (h2.trans (hcoeff v))
    rw [hsingle_eq u, hsingle_eq v, h1]
  · intro f
    refine ⟨SkewMonoidAlgebra.single (1 : G) (f 1), ?_⟩
    show deltaToEndAdd hKL (SkewMonoidAlgebra.single (1 : G) (f 1)) = f
    rw [hsingle]
    ext t

set_option maxHeartbeats 1000000 in
/-- **零环不是域** ✓（**机器核** ✓）：`\mathrm{Field}\ \mathrm{PUnit}` 蕴含非平凡 ✓ 而 `\mathrm{PUnit}` 单点 ✗
⟹ 矛盾 ✓。**⚠ 意义** ✓：域档 `(c)` 的量词域含 `[\mathrm{Field}\ L]` ✓ ⟹ **零环不在其中** ✗
—— 故**「域档 ⟹ 环档」不能由域档的实例集单独供给** ✗（量词域之差是本档的**结构缺口** ✓）。 -/
theorem pUnit_not_field : ¬ Nonempty (Field PUnit.{1}) := by
  rintro ⟨hF⟩
  let _instF : Field PUnit.{1} := hF
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial PUnit.{1})
  exact hab (Subsingleton.elim a b)

end RingTierBridgeRootCause

section FiniteDimensionalOne

variable {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Module.Finite K L]

set_option maxHeartbeats 1000000 in
/-- **域上 `1` 维非平凡结合代数 ≅ 基域** ✓：`\mathrm{algebraMap}` 单射 ✓（`\mathrm{FaithfulSMul}` ✓）
＋ 两侧 `\mathrm{finrank}` 相等 ✓ ⟹ 双射 ✓ ⟹ `K`-代数同构 ✓。
**⚠ 用途** ✓：`|G| = 1` 档的环档目标由本条**分类** ✓（＝ 修正形证明的**唯一**结构性输入 ✓）。 -/
theorem nonempty_algEquiv_of_finrank_eq_one (h : Module.finrank K L = 1) :
    Nonempty (L ≃ₐ[K] K) := by
  have hinj : Function.Injective (Algebra.linearMap K L) :=
    FaithfulSMul.algebraMap_injective K L
  have hfr : Module.finrank K K = Module.finrank K L := by
    rw [Module.finrank_self K, h]
  have hsurj : Function.Surjective (Algebra.linearMap K L) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
  refine ⟨(AlgEquiv.ofLinearEquiv (LinearEquiv.ofBijective (Algebra.linearMap K L)
    ⟨hinj, hsurj⟩) ?_ ?_).symm⟩
  · simp [Algebra.linearMap]
  · intro x y
    simp [Algebra.linearMap]

end FiniteDimensionalOne

section SelfTrivialGroupFieldTier

variable {F : Type} [Field F]

set_option maxHeartbeats 1000000 in
/-- **域档 `(c)` 款在 `(R, S) = (F, F)`、`G = \mathrm{PUnit}` 上成立** ✓：`L` 域 ＋ `|G| = 1`
⟹ 秩定理给 `[L : K] = 1` ✓ ⟹ `L \cong K` ✓，再与 `F \otimes_F K \cong K` 复合 ✓。
**⚠ 意义** ✓：前件在该载体上**非空** ✓ ⟹ 原形若要被反驳，**必须**落在环档一侧 ✓（见登记 ✓）。 -/
theorem realizationPropertyFieldFinite_self_trivialGroup :
    RealizationPropertyFieldFinite F PUnit.{1} F F := by
  intro K _ _ L _ _ _ _ _ _ hKL hgal
  refine ⟨Algebra.ofId F K, ?_⟩
  let _inst : Algebra F K := (Algebra.ofId F K).toRingHom.toAlgebra
  have hcard : Fintype.card PUnit.{1} = 1 := Fintype.card_unique
  have hfin : Module.finrank K L = 1 := by
    rw [BTier.finrank_eq_card_of_isGaloisWithGroup hKL hgal, hcard]
  obtain ⟨e⟩ := nonempty_algEquiv_of_finrank_eq_one (K := K) (L := L) hfin
  have h1 : K ≃ₐ[K] (TensorProduct F K F) := (Algebra.TensorProduct.rid F K K).symm
  exact ⟨e.trans h1⟩

end SelfTrivialGroupFieldTier

section RingTierBridgeFinite

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G]

set_option maxHeartbeats 1000000 in
/-- **残余 ① 的修正形（非退化 ＋ 有限档）** ✓：把 `L`-量词收到**源侧有效域** ✓ ——
`[\mathrm{Nontrivial}\ L]` ✓（排除零环 ✗）＋ `[\mathrm{Module.Finite}\ K\ L]` ✓
（＝ 源 `proposition-0-2`(a) 的**有限生成投射**后果 ✓，库内对应 `\mathrm{GaloisProjectiveHyp}` ✓）。
**⚠ 与旧形的强度序** ✓：旧形 ⟹ 本形 ✓（`realizationRingTierBridgeFinite_of_realizationRingTierBridge` ✓）；
**反向未证** ✗（**且**零环即是差别的见证 ✓，见 `isGaloisWithGroup_zeroRing_of_subsingleton` ✓）。
**⚠ 档位** ✓：本形**弱于** `\mathrm{RealizationRingTierBridge}`（原形 ✓）⟹ 若原形可证则本形可证 ✓，
**反向未证** ✗（**不声称**两者等价 ✗）。 -/
def RealizationRingTierBridgeFinite (F : Type) [Field F] (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra F R] [Algebra R S] [Algebra F S]
    [IsScalarTower F R S], RealizationPropertyFieldFinite F G R S →
      ∀ (K : Type) [Field K] [Algebra F K]
        (L : Type) [CommRing L] [Nontrivial L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
        [MulSemiringAction G L] [Module.Finite K L]
        (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t)),
        BTier.IsGaloisWithGroup K L G hKL →
          ∃ (φ : R →ₐ[F] K),
            letI : Algebra R K := φ.toRingHom.toAlgebra
            Nonempty (L ≃ₐ[K] (TensorProduct R K S))

set_option maxHeartbeats 1000000 in
/-- **强度序（可证方向）** ✓：**原形 ⟹ 修正形** ✓ —— 把修正形的量词实例喂给原形即可 ✓
（`\mathrm{Nontrivial}` ✓ 与 `\mathrm{Module.Finite}` ✓ 是**加**在量词域上的前提 ✓）。
**⚠ 判别力** ✓：零环档使**反向不可能由域档供给** ✗（`pUnit_not_field` ✓ ⟹ 零环不在域档量词域 ✓）。 -/
theorem realizationRingTierBridgeFinite_of_realizationRingTierBridge
    (h : RealizationRingTierBridge F G) : RealizationRingTierBridgeFinite F G := by
  intro R S _ _ _ _ _ _ hfield K _ _ L _ _ _ _ _ _ _ hKL hgal
  exact h R S hfield K L hKL hgal

set_option maxHeartbeats 1000000 in
/-- **`K` 在自身上是 `G`-Galois（`G` 亚单、作用平凡）** ✓：三款直接验 ✓ —— ① ✓；② 平凡作用 ✓；
③ `\delta` 双射 ✓（单射：`u = \mathrm{single}\ 1\ (u.\mathrm{coeff}\ 1)` ✓；满射：每个 `K`-线性自同态
`f` 都是 `x \mapsto x \cdot f(1)` ✓ ＝ `\delta(\mathrm{single}\ 1\ (f\ 1))` ✓）。
**⚠ 用途** ✓：修正形证明中把**域档假设实例化于 `L' = K`** ✓ 所需的 Galois 实例 ✓。 -/
theorem isGaloisWithGroup_self_of_subsingleton {K : Type} [Field K] [MulSemiringAction G K]
    (hG : Subsingleton G)
    (hKK : ∀ (g : G) (r : K) (t : K), g • (r • t) = r • (g • t)) :
    BTier.IsGaloisWithGroup K K G hKK := by
  have hsingle : ∀ a : K,
      deltaToEndAdd hKK (SkewMonoidAlgebra.single (1 : G) a) = coeffToEnd a := by
    intro a
    rw [deltaToEndAdd_single]
    have hact : actEnd hKK (1 : G) = 1 := by
      refine LinearMap.ext (fun x => ?_)
      simp [actEnd]
    rw [hact, mul_one]
  have hsingle_eq : ∀ u : SkewMonoidAlgebra K G,
      u = SkewMonoidAlgebra.single (1 : G) (u.coeff 1) := by
    intro u
    refine SkewMonoidAlgebra.ext (fun g => ?_)
    rw [hG.elim g 1, SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
  have hcoeff : ∀ u : SkewMonoidAlgebra K G, (deltaToEndAdd hKK u) 1 = u.coeff 1 := by
    intro u
    rw [hsingle_eq u, hsingle]
    simp [coeffToEnd]
  refine ⟨⟨fun {a b : G} _ => hG.elim a b⟩, fun g r => ?_, ?_⟩
  · rw [hG.elim g 1]; simp
  constructor
  · intro u v huv
    have h1 : u.coeff 1 = v.coeff 1 := by
      have h2 : (deltaToEndAdd hKK u) 1 = (deltaToEndAdd hKK v) 1 :=
        congrArg (fun f : Module.End K K => f 1) huv
      exact (hcoeff u).symm.trans (h2.trans (hcoeff v))
    rw [hsingle_eq u, hsingle_eq v, h1]
  · intro f
    refine ⟨SkewMonoidAlgebra.single (1 : G) (f 1), ?_⟩
    show deltaToEndAdd hKK (SkewMonoidAlgebra.single (1 : G) (f 1)) = f
    rw [hsingle]
    refine LinearMap.ext (fun x => ?_)
    have hfx : f x = x * f 1 := by
      simpa [smul_eq_mul] using (map_smul f x (1 : K))
    show f 1 * x = f x
    rw [hfx, mul_comm]

set_option maxHeartbeats 1000000 in
/-- **🔴 本轮主结论：修正形在 `\mathrm{Subsingleton}\ G` 档成立（无条件** ✓✅**）**：
`R`／`S`／`F` **任意** ✓，只要 `G` 亚单 ✓ —— 环档目标 `L` 被**分类**为 `K` ✓
（秩定理 `[L : K] = |G| = 1` ✓ ＋ `nonempty_algEquiv_of_finrank_eq_one` ✓），
而 `L' = K` 的域档实例给 `\varphi` ✓ 与 `K \cong S \otimes_R K` ✓ ⟹ 复合即得 ✓。
**⚠ 意义** ✓：修正形**非空洞** ✓（不是「换个说法」✗）；**且**证明只用了**两件**结构性输入 ✓
（秩定理 ✓ ＋ 域档假设在 `L' = K` 的实例 ✓）⟹ 一般 `G` 档所缺的**正是**「`L` 的分类」✓
（源 `proposition-0-5` ✓：`L` 是域的直和 ✓／`L \cong \mathrm{Ind}_H^G(eL)` ✓／正规基 ✓／代数无关性 ✓
—— **库内与 mathlib 均未落** ✗）。
**🔴 不声称** ✗：**不**声称原形（`RealizationRingTierBridge` ✓）已证或已驳 ✗；
**不**声称一般 `G` 档的修正形已证 ✗。 -/
theorem realizationRingTierBridgeFinite_of_subsingleton (hG : Subsingleton G) :
    RealizationRingTierBridgeFinite F G := by
  intro R S _ _ _ _ _ _ hfield K _ _ L _ _ _ _ _ _ _ hKL hgal
  have hcard : Fintype.card G = 1 := by
    have h1 : Fintype.card G ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => hG.elim a b)
    have h0 : 0 < Fintype.card G := Fintype.card_pos
    omega
  have hfin : Module.finrank K L = 1 := by
    rw [BTier.finrank_eq_card_of_isGaloisWithGroup hKL hgal, hcard]
  obtain ⟨eL⟩ := nonempty_algEquiv_of_finrank_eq_one (K := K) (L := L) hfin
  let _instK : MulSemiringAction G K :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
  have hKK : ∀ (g : G) (r : K) (t : K), g • (r • t) = r • (g • t) := fun g r t => rfl
  have hgalKK : BTier.IsGaloisWithGroup K K G hKK := isGaloisWithGroup_self_of_subsingleton hG hKK
  obtain ⟨φ, ⟨eK⟩⟩ := hfield K K hKK hgalKK
  exact ⟨φ, ⟨eL.trans eK⟩⟩

#print axioms isGaloisWithGroup_zeroRing_of_subsingleton
#print axioms pUnit_not_field
#print axioms nonempty_algEquiv_of_finrank_eq_one
#print axioms realizationPropertyFieldFinite_self_trivialGroup
#print axioms RealizationRingTierBridgeFinite
#print axioms realizationRingTierBridgeFinite_of_realizationRingTierBridge
#print axioms isGaloisWithGroup_self_of_subsingleton
#print axioms realizationRingTierBridgeFinite_of_subsingleton

end RingTierBridgeFinite

section CarrierShapedResiduals

variable {G : Type} [Group G] [Fintype G] {F : Type} [Field F]

set_option maxHeartbeats 1000000 in
/-- **源 `theorem-2-1` 侧的载体形残余**（环档 `(c)` 款整项入残余 ⟹ 归约**不再需要环档桥**）。 -/
def Thm21RingTierResidual (A : Type) [Group A] [Fintype A] (F : Type) [Field F] : Prop :=
  SaltmanCondition A F →
    ∃ (R S : Type) (_ : CommRing R) (_ : CommRing S) (_ : Algebra F R) (_ : Algebra R S)
      (_ : Algebra F S) (_ : IsScalarTower F R S) (_ : MulSemiringAction A S)
      (hRG : ∀ (g : A) (r : R) (t : S), g • (r • t) = r • (g • t)),
      (∃ (n : ℕ) (w : MvPolynomial (Fin n) F),
        w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
      BTier.IsGaloisWithGroup R S A hRG ∧ BTier.RealizationProperty F A R S

set_option maxHeartbeats 1000000 in
/-- **归约（源 `theorem-2-1`，无环档桥）** ✓：残余（载体形 ✓）⟹ 源陈述 ✓。 -/
theorem theorem21Statement_of_ringTierResidual (A : Type) [Group A] [Fintype A]
    (F : Type) [Field F] (hres : Thm21RingTierResidual A F) : Theorem21Statement A F := by
  intro hC
  obtain ⟨R, S, _hcR, _hcS, _haFR, _haRS, _haFS, _hst, _hmsa, hRG, ha, hgal, hc⟩ := hres hC
  exact ⟨R, S, hRG, ha, hgal, hc⟩

set_option maxHeartbeats 1000000 in
/-- **强度序** ✓：旧残余 ＋ 原形环档桥 ⟹ 载体形残余 ✓（**逐字**同一构造 ✓）。 -/
theorem thm21RingTierResidual_of_clausesResidual_and_ringBridge (A : Type) [Group A] [Fintype A]
    (F : Type) [Field F] (hres : Thm21ClausesResidual A F)
    (hb : RealizationRingTierBridge F A) : Thm21RingTierResidual A F := by
  intro hC
  obtain ⟨R, S, hcR, hcS, haFR, haRS, haFS, hst, hmsa, hRG, ha, hgal, hc⟩ := hres hC
  exact ⟨R, S, hcR, hcS, haFR, haRS, haFS, hst, hmsa, hRG, ha, hgal, hb R S hc⟩

set_option maxHeartbeats 1000000 in
/-- **源 `theorem-5-1` 侧的载体形残余**（环档 `(c)` 款整项入残余 ⟹ 归约**不再需要环档桥**）。 -/
def NoetherRingTierResidual (F : Type) [Field F] (G : Type) [Group G] [Fintype G]
    [DecidableEq G] : Prop :=
  Infinite F →
    ∃ (R S : Type) (_ : CommRing R) (_ : CommRing S) (_ : Algebra F R) (_ : Algebra R S)
      (_ : Algebra F S) (_ : IsScalarTower F R S) (_ : MulSemiringAction G S)
      (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)),
      (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
        Nonempty (R ≃ₐ[F] Localization.Away w)) ∧
      BTier.IsGaloisWithGroup R S G hRG ∧ BTier.RealizationProperty F G R S

set_option maxHeartbeats 1000000 in
/-- **归约（源 `theorem-5-1`，无环档桥）** ✓。 -/
theorem theorem51Statement_of_noetherRingTierResidual [DecidableEq G]
    (h : NoetherRingTierResidual F G) : Theorem51Statement F G := by
  intro hinf L _ _ _ _ _
  obtain ⟨R, S, _hcR, _hcS, _haFR, _haRS, _haFS, _hst, _hmsa, hRG, ha, hgal, hc⟩ := h hinf
  exact ⟨R, S, hRG, ha, hgal, hc⟩

#print axioms Thm21RingTierResidual
#print axioms theorem21Statement_of_ringTierResidual
#print axioms thm21RingTierResidual_of_clausesResidual_and_ringBridge
#print axioms NoetherRingTierResidual
#print axioms theorem51Statement_of_noetherRingTierResidual



/-! ### 4.64 **登记（r262 总账，逐条如实）** -/

/-- **登记** ✓：**残余 ①（`RealizationRingTierBridge`，原形）的状态** ——
**(甲) 已落** ✓✅：**根因** ✓（零环是库内合法 `G`-Galois 目标 ✓，`G` 亚单档 ✓；
`pUnit_not_field` ✓ ⟹ 它**不在**域档量词域内 ✓）；**域档前件在该载体上非空** ✓
（`realizationPropertyFieldFinite_self_trivialGroup` ✓）；**修正形** ✓（`RealizationRingTierBridgeFinite` ✓）
＋ **其 `\mathrm{Subsingleton}\ G` 档的证明** ✓✅（`realizationRingTierBridgeFinite_of_subsingleton` ✓）；
**两条源陈述的**无桥**归约** ✓✅（`theorem21Statement_of_ringTierResidual` ✓／
`theorem51Statement_of_noetherRingTierResidual` ✓ —— 环档 `(c)` 款整项**收进载体形残余** ✓）。
**(乙) 未落** ✗（**逐条，含理由** ✓）：**(i)** **原形的机器反驳** ✗ —— 计划路线（零环目标 ＋
`F \otimes_F F` 非平凡 ✓）在**形式化**时受阻 ✓：`RealizationProperty` 结论中的
`\mathrm{letI} : \mathrm{Algebra}\ R\ K := \varphi.\mathrm{toRingHom.toAlgebra}` ✓（**遮蔽** ✓）
使该结论的实例在 `R = K = S = F` 档出现**两个候选** ✗（`\mathrm{instAlgebra}` ✗ 与
`\mathrm{leftAlgebra}` ✗：实测报错「synthesized … instAlgebra, inferred … leftAlgebra」✓），
而取**非平凡底域** `K = F(t)` ✓ 时张量的 `\mathrm{Semiring}`／`\mathrm{Algebra}\ K` 实例在
**遮蔽语境**下不可合成 ✗（实测「failed to synthesize `\mathrm{Semiring}\ (K \otimes_F F)`」✓）
⟹ 该反驳须先把 `\mathrm{RealizationProperty}` 的 `\mathrm{letI}` 结构改成**显式参数** ✓
（**口径变更** ✗，**不在本轮** ✗）；**(ii)** **一般 `G` 档的判别力** ✗ —— 零环在 `G` 非平凡时
**不是** `G`-Galois ✓（`\mathrm{FaithfulSMul}` 款即排除 ✓；`isGaloisWithGroup_zeroRing_of_subsingleton`
的 `hG` 前提正是它 ✓）⟹ **原形在一般档的真值仍未判定** ⚠；**(iii)** 修正形的一般 `G` 档 ✗ ——
所需输入 ＝ 源 `proposition-0-5` ✓ 的**分类**（`L` 是域的直和 ✓／`L \cong \mathrm{Ind}_H^G(eL)` ✓／
正规基 ✓／代数无关性 ✓），**库内与 mathlib 均未落** ✗（mathlib 的 Artin 界／`\mathrm{FixedPoints}`／
正规基定理**均只域档** ✗）；**(iv)** 两条源陈述 ✓ **仍未证** ✗（且 §D 已判残余 ② 在 `G` 非平凡档为空 ✗）。
**🔴 不声称** ✗：**不**声称原形已证 ✗；**不**声称原形已驳 ✗（(i) 未落 ✓）；
**不**声称修正形的一般 `G` 档已证 ✗；**不**声称两条源陈述已证 ✗。 -/
theorem ringTierBridge_residual_registered : True := trivial

#print axioms ringTierBridge_residual_registered

end CarrierShapedResiduals


/-! ### 4.65 **残余 ①（环档桥）的机器反驳**（r263 ✓：`Subsingleton G` 档 ✓；见证 ＝ **零环** ✓）

**⚠ 起点** ✓（承 r262 §4.63／§4.64 ✓）：残余 ①（`RealizationRingTierBridge` ✓，**原形** ✓）
当时**既未证也未驳** ✗ —— 反驳路线卡在**编码层** ✗（`RealizationProperty` 结论里的
`letI` 遮蔽使张量实例不可指名 ✗，探针 `probe-r262k` ✓ 可复现 ✓）。
**本轮处置** ✓：在**不触碰旧 `def`** ✗ 的前提下另立**显式实例形** ✓
（`GenericExtension_ABGV52` 的 `RealizationPropertyExplicit` ✓，两向强度序皆已证 ✓
⟹ 与旧形**等价** ✓），再在**该形**上做退化目标反驳 ✓✅，最后经**逆否**回到**源形环档** ✓。 -/

section RingTierBridgeRefuted

variable {F : Type} [Field F]

set_option maxHeartbeats 1000000 in
/-- **有限域档在自身上成立（`G` 亚单档）** ✓✅：`L` 域 ＋ `|G| = 1` ✓ ⟹ 秩定理给 `[L : K] = 1` ✓
⟹ `L ≅ K` ✓（`nonempty_algEquiv_of_finrank_eq_one` ✓），再与 `F ⊗_F K ≅ K` ✓ 复合 ✓。
**⚠ 地位** ✓：本件是**反驳的「前件为真」那一半** ✓ —— 反驳 `RealizationRingTierBridge F G` ✓ 须
「**有限域档**在 `(R, S) = (F, F)` 上**真** ✓」（本件 ✓）＋「**环档**在**同载体**上**假** ✗」
（`not_realizationProperty_self_of_subsingleton` ✓）。
**⚠ 与 r262 件的关系** ✓：`realizationPropertyFieldFinite_self_trivialGroup` ✓（`G = PUnit` 专用 ✓）
**一字不动** ✓；本件是其 `Subsingleton G` 推广 ✓（`Fintype.card G = 1` 由亚单性算出 ✓）。 -/
theorem realizationPropertyFieldFinite_self_of_subsingleton {G : Type} [Group G] [Fintype G]
    (hG : Subsingleton G) : RealizationPropertyFieldFinite F G F F := by
  intro K _ _ L _ _ _ _ _ _ hKL hgal
  refine ⟨Algebra.ofId F K, ?_⟩
  let _inst : Algebra F K := (Algebra.ofId F K).toRingHom.toAlgebra
  have hcard : Fintype.card G = 1 := by
    have h1 : Fintype.card G ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => hG.elim a b)
    have h0 : 0 < Fintype.card G := Fintype.card_pos
    omega
  have hfin : Module.finrank K L = 1 := by
    rw [BTier.finrank_eq_card_of_isGaloisWithGroup hKL hgal, hcard]
  obtain ⟨e⟩ := nonempty_algEquiv_of_finrank_eq_one (K := K) (L := L) hfin
  have h1 : K ≃ₐ[K] (TensorProduct F K F) := (Algebra.TensorProduct.rid F K K).symm
  exact ⟨e.trans h1⟩

set_option maxHeartbeats 1000000 in
/-- **🔴 退化目标反驳（显式实例形）** ✓✅：`G` 亚单 ⟹ `RealizationPropertyExplicit F G F F` **假** ✗。
**⚠ 见证（逐项）** ✓：`R = S = F` ✓／`K = F` ✓／`L ＝ 零环` ✓（取 `PUnit` ✓，其环结构即零环 ✓）；
`G` 在 `L` 上的作用取**平凡** ✓（`Subsingleton G` ⟹ 唯一 ✓；本件就地给出该 `MulSemiringAction` ✓）。
**⚠ 两件输入** ✓：① **前件为真** ✓：零环是**库内合法**的 `G`-Galois 目标 ✓
（`isGaloisWithGroup_zeroRing_of_subsingleton` ✓ —— 正是 r262 定位的**根因** ✓）；
② **结论为假** ✗：`∃φ A` 给出的张量 `F ⊗[F] F` ✓ **非平凡** ✓
（`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain` ✓：`F` 是域 ⟹
`A.algebraMap` 单射 ✓）而 `L` **亚单** ✓ ⟹ 由
`not_nonempty_algEquiv_of_subsingleton_of_nontrivial` ✓ 得**无** `F`-代数同构 ✓ ⟹ 矛盾 ✓。
**⚠ 关键工艺** ✓（**正是 r262 卡住处** ✓）：张量的两个 `Module` 实例以 `@TensorProduct` ✓ **指名** ✓
—— 左槽 `@Algebra.toModule F F _ _ A` ✓（`φ`-诱导 ✓）、右槽 `@Algebra.toModule F F _ _ (Algebra.id F)` ✓
（环境实例 ✓）；桥引理的两个 `Algebra` 实例作**显式变元** ✓ ⟹ 由 **unify**（对齐具体张量实例 ✓）
而非 **synth** 决定 ✓。
**🔴 不声称** ✗：**不**声称 `G` **非**亚单档的反驳 ✗ —— 零环在 `G` 非平凡时**不是** `G`-Galois ✓
（`FaithfulSMul` 款即排除 ✓），故该档须另找退化目标 ✓（见文末登记 (丙) ✓）。 -/
theorem not_realizationPropertyExplicit_self_of_subsingleton {G : Type} [Group G] [Fintype G]
    (hG : Subsingleton G) : ¬ BTier.RealizationPropertyExplicit F G F F := by
  intro h
  let _instMSA : MulSemiringAction G PUnit.{1} :=
    { smul := fun _ _ => PUnit.unit
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
  have hKL : ∀ (g : G) (r : F) (t : PUnit.{1}), g • (r • t) = r • (g • t) :=
    fun _ _ _ => Subsingleton.elim _ _
  have hgal : BTier.IsGaloisWithGroup F PUnit.{1} G hKL :=
    isGaloisWithGroup_zeroRing_of_subsingleton (G := G) (K := F) hG hKL
  obtain ⟨_, A, _, hP⟩ := h F PUnit.{1} hKL hgal
  have hnt : Nontrivial (@TensorProduct F _ F F _ _ (@Algebra.toModule F F _ _ A)
      (@Algebra.toModule F F _ _ (Algebra.id F))) :=
    @Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F F F _ _ _
      A (Algebra.id F) (RingHom.injective _) (RingHom.injective _) _ _
  exact BTier.not_nonempty_algEquiv_of_subsingleton_of_nontrivial (K := F) (L := PUnit.{1})
    (T := @TensorProduct F _ F F _ _ (@Algebra.toModule F F _ _ A)
      (@Algebra.toModule F F _ _ (Algebra.id F))) _ _ inferInstance hnt hP

set_option maxHeartbeats 1000000 in
/-- **🔴 退化目标反驳（源形环档）** ✓✅：由显式实例形 ＋ **旧 ⟹ 新** ✓
（`BTier.realizationPropertyExplicit_of_realizationProperty` ✓）的**逆否** ✓ 得旧形为假 ✗。
**⚠ 意义** ✓：**源形**（＝两条源陈述所用之档 ✓）本身在 `G` 亚单档**不成立** ✗ ——
故「有限域档 ⟹ 环档」**不可**作为无条件桥 ✗。 -/
theorem not_realizationProperty_self_of_subsingleton {G : Type} [Group G] [Fintype G]
    (hG : Subsingleton G) : ¬ BTier.RealizationProperty F G F F :=
  fun h => not_realizationPropertyExplicit_self_of_subsingleton (F := F) hG
    (BTier.realizationPropertyExplicit_of_realizationProperty h)

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 本轮主结论：残余 ①（原形环档桥）在 `Subsingleton G` 档被机器反驳** ✓✅：
`RealizationRingTierBridge F G` ＝ 「有限域档 ⟹ 环档」✓，本件给**反例三件套** ✓ ——
载体 `(R, S) = (F, F)` ✓、前件 `RealizationPropertyFieldFinite F G F F` ✓（上件 ✓）、
结论 `BTier.RealizationProperty F G F F` ✓ **假** ✗（上件 ✓）。
**⚠ 档位** ✓：`G` **亚单** ✓（＝源侧「秩 1」档 ✓；零环恰是库内判据在此档**多收**的目标 ✗）。
**⚠ 后果** ✓：旧归约链中**以环档桥为假设者** ✗（`RealizationRingTierBridge F G` ✓）
在 `G` 亚单档**不可实例化** ✗ ⟹ 该路线在平凡群档**终结** ✗；
**修正形** ✓（`RealizationRingTierBridgeFinite` ✓）**不退** ✓✅（其亚单档已证 ✓，
且本反驳**解释了**为何须加 `[Nontrivial L]` ✓／`[Module.Finite K L]` ✓ 两前提 ✓）。
**🔴 不声称** ✗：**不**声称 `G` **非**亚单档的桥已驳 ✗（见文末登记 ✓）；**不**声称两条源陈述已证 ✗。 -/
theorem not_realizationRingTierBridge_of_subsingleton {G : Type} [Group G] [Fintype G]
    (hG : Subsingleton G) : ¬ RealizationRingTierBridge F G := by
  intro hb
  exact not_realizationProperty_self_of_subsingleton (F := F) hG
    (hb F F (realizationPropertyFieldFinite_self_of_subsingleton (F := F) hG))

/-- **推论（平凡群档）** ✓：`G = PUnit`（＝**平凡群** ✓）时环档桥被驳 ✗。 -/
theorem not_realizationRingTierBridge_trivialGroup :
    ¬ RealizationRingTierBridge F PUnit.{1} :=
  not_realizationRingTierBridge_of_subsingleton (F := F) (G := PUnit.{1})
    (inferInstance : Subsingleton PUnit.{1})

/-- **登记** ✓：**残余 ①（`RealizationRingTierBridge` ✓ **原形** ✓）的终态** ——
**(甲) 已落** ✓✅：**机器反驳** ✓（`Subsingleton G` 档 ✓，本轮 ✓）—— 见证 ＝ **零环** ✓
（**前件真** ✓：`realizationPropertyFieldFinite_self_of_subsingleton` ✓；
**结论假** ✗：`not_realizationProperty_self_of_subsingleton` ✓）；**显式实例形** ✓
＋ **两向强度序** ✓（`GenericExtension_ABGV52` ✓ ⟹ 两编码**等价** ✓✅）。
**(乙) 后果（逐条）** ✓：**(i)** 旧归约链中**以环档桥为假设者** ✗ ——
`thm21RingTierResidual_of_clausesResidual_and_ringBridge` ✓／
`isGenericExtension_of_fieldFinite_and_ringBridge` ✓／
`nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge` ✓ ——
在 `G` 亚单档**不可实例化** ✗（其假设已假 ✓）⟹ 该路线在平凡群档**终结** ✗；
**⚠ 与 r262 一致** ✓：修正方向本就落在**载体形残余** ✓（`Thm21RingTierResidual` ✓／
`NoetherRingTierResidual` ✓，**不含**环档桥 ✓）⟹ **两条源陈述的归约不受影响** ✓✅；
**(ii)** **修正形** ✓（`RealizationRingTierBridgeFinite` ✓：量词加 `[Nontrivial L]` ✓ ＋
`[Module.Finite K L]` ✓）**不退** ✓✅ —— `realizationRingTierBridgeFinite_of_subsingleton` ✓ 已在册 ✓，
且本反驳**恰好解释了**为何须加该两前提 ✓（零环被排除 ✓）；**(iii)** 域档前件在载体上**非空** ✓
（r262 ✓ `realizationPropertyFieldFinite_self_trivialGroup` ✓）⟹ 本反驳**非空洞** ✓✅。
**(丙) 未落** ✗（**逐条，含理由** ✓）：**(iv)** **`G` 非亚单档的反驳** ✗ —— 零环不是 `G`-Galois ✓
（`FaithfulSMul` 款 ✓）⟹ 候选退化目标 ＝ **分裂 `G`-Galois 代数** ✓ `K^G` ✓（正则置换作用 ✓；
`|G| ≥ 2` 时 `K^G ≇ K` ✓ 由**幂等元计数** ✓：域只有 `0, 1` 两个幂等元 ✓ 而 `K^G` 有 `|G|` 个 ✓）
—— 须先落 `IsGaloisWithGroup K (K^G) G` ✓（δ 双射 ＝ 维数计数 ＋ 单射 ✓），**库内未落** ✗；
**(v)** 两条源陈述 ✓ **仍未证** ✗。
**🔴 不声称** ✗：**不**声称 `G` 非亚单档的桥已驳 ✗；**不**声称原形**一般档**的真值已定 ✗
（**只**判亚单档为**假** ✓）；**不**声称两条源陈述已证 ✗。 -/
theorem ringTierBridge_refuted_registered : True := trivial

#print axioms realizationPropertyFieldFinite_self_of_subsingleton
#print axioms not_realizationPropertyExplicit_self_of_subsingleton
#print axioms not_realizationProperty_self_of_subsingleton
#print axioms not_realizationRingTierBridge_of_subsingleton
#print axioms not_realizationRingTierBridge_trivialGroup
#print axioms ringTierBridge_refuted_registered

end RingTierBridgeRefuted


/-! ### 4.66 **分裂 `G`-Galois 代数 `K^G`**（r264 ✓：库内**首个非平凡** `G`-Galois 实例 ✓✅）

**⚠ 起点** ✓（承 §4.65 登记 (丙)(iv) ✓）：r263 把残余 ①（环档桥 `RealizationRingTierBridge` ✓）
的 `Subsingleton G` 档**机器反驳** ✓✅，并把**非亚单档**的候选退化目标登记为
**分裂 `G`-Galois 代数** ✓ `K^G` ✓（＝函数空间 `G → K` ✓，坐标**正则置换** ✓），
但**其前置件**（`IsGaloisWithGroup K (G → K) G` ✓）**库内未落** ✗。本轮**落**该前置件 ✓✅。

**⚠ 机制** ✓（**δ 双射 ＝ 维数计数 ＋ 单射** ✓，五步 ✓）：
**① 忠实性** ✓：取 `f = Pi.single 1 1` ✓，在坐标 `g` 处取值 ✓ 得 `g⁻¹ * g = 1` 与
`Pi.single 1 1 g` ✓ 的比较 ⟹ `g = 1` ✓（用 `K` 域 ⟹ `1 ≠ 0` ✓）；
**② ② 款自动** ✓（由 `hRG` ✓ ＋ `algebraMap_fixed_of_smulCommClass` ✓）；
**③ 两边 `K`-维数** ✓：左 ＝ `finrank K (SkewMonoidAlgebra (G → K) G)` ＝ `|G| · |G|` ✓
（`coeffLinearEquiv` ✓ ＋ `Finsupp.linearEquivFunOnFinite` ✓ ＋ `LinearEquiv.curry` ✓ ＋
`finrank_fintype_fun_eq_card` ✓），右 ＝ `finrank K (Module.End K (G → K))` ＝ `|G| · |G|` ✓
（`Module.finrank_linearMap` ✓）；
**④ 单射** ✓（**系数提取** ✓）：取测试函数 `t = Pi.single h 1` ✓，公式
`δ x t = Σ_g (coeff g x) * (g • t)` ✓（**归纳** ✓，`deltaToEndAdd_single` ✓ ＋ `Finset.sum_eq_single` ✓）
＋ 在坐标 `j` 处取值 ✓ 抽出**唯一**贡献项 ✓（`g⁻¹ * j = h ↔ g = j * h⁻¹` ✓）
⟹ `(coeff (j * h⁻¹) x) j = 0` ✓（对一切 `j, h` ✓）⟹ 换元 `j := h`、`h := g⁻¹ * h` ✓ 得 `coeff g x = 0` ✓
⟹ `x = 0` ✓（`SkewMonoidAlgebra.ext` ✓）；
**⑤ 双射** ✓：`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ✓（维数相等 ✓ ＋ 单射 ✓）。

**⚠ 口径** ✓：正则作用以**具名定义** ✓ `regularSMul` ✓／`regularMSA` ✓ 给出 ✓，
经 `attribute [local instance]` ✓ **限本文件**注册 ✓（**不**污染全库实例表 ✓）——
下游取用时写 `let _inst : MulSemiringAction G (G → K) := regularMSA G K` ✓（`let`-绑定与其值 defeq ✓）。
**⚠ 档位** ✓：本件只用 `[Field K]` ✓ ＋ `[Group G] [Fintype G]` ✓（**无**其它有限性／分离性输入 ✗）。
**🔴 不声称** ✗：**不**声称 `K^G` 是域 ✗（`|G| ≥ 2` 时它**有零因子** ✗，见 §4.67 ✓）；
**不**声称它可作**有限域档**的见证 ✗（有限域档的 `L` 是**域** ✓，而 `K^G` 不是 ✗ —— 这正是残余 ①
非亚单档的**卡点** ✓，见 §4.67 登记 ✓）；**不**声称两条源陈述已证 ✗。 -/

section SplitGaloisAlgebra

/-- **正则置换作用（`SMul` 层）** ✓：`(g • f) h = f (g⁻¹ * h)` ✓
（＝ `G` 在自身上的**左正则**作用所诱导的坐标置换 ✓）。
**⚠ 为何具名** ✓：mathlib **无**该作用的实例 ✗（实测 `synthInstanceFailed` ✓）；
具名 ＋ `attribute [local instance]` ✓ 使**陈述**层可用 ✓ 而**不**污染全库 ✓。 -/
@[instance_reducible] def regularSMul (G : Type*) [Group G] (K : Type*) : SMul G (G → K) :=
  ⟨fun g f h => f (g⁻¹ * h)⟩

attribute [local instance] regularSMul

/-- **取值式** ✓：钉住作用在坐标上的形式 ✓（`rfl` 型 ✓ ⟹ 外形改动即编译失败 ✓）。 -/
@[simp] lemma regularSMul_apply {G : Type*} [Group G] {K : Type*} (g : G) (f : G → K) (h : G) :
    (g • f) h = f (g⁻¹ * h) := rfl

/-- **正则置换作用（`MulSemiringAction` 层）** ✓：逐条验证 ✓ ——
`G` 的作用是**环自同构** ✓（逐坐标 ✓），故 `smul_zero`／`smul_add`／`smul_mul`／`smul_one` 全为逐点等式 ✓。
**⚠ 工艺** ✓：字段证明须**先** `rw [regularSMul_apply]`（或 `inv_one`／`mul_inv_rev` ＋ `mul_assoc` ✓）再 `simp` ✓ ——
直接 `simp [regularSMul]` **不**能穿过 `HSMul`-包装 ✗（实测：`simp` made no progress ✓）。 -/
@[instance_reducible] def regularMSA (G : Type*) [Group G] (K : Type*) [Semiring K] :
    MulSemiringAction G (G → K) where
  toSMul := regularSMul G K
  one_smul f := by ext h; rw [regularSMul_apply, inv_one, one_mul]
  mul_smul g₁ g₂ f := by ext h; rw [regularSMul_apply, mul_inv_rev, mul_assoc]; simp
  smul_zero g := by ext h; rw [regularSMul_apply]; rfl
  smul_add g f₁ f₂ := by ext h; rw [regularSMul_apply]; simp
  smul_mul g f₁ f₂ := by ext h; rw [regularSMul_apply]; simp
  smul_one g := by ext h; rw [regularSMul_apply]; rfl

attribute [local instance] regularMSA

/-- **作用与 `K`-纯量交换** ✓（＝判据的 `hRG` 输入 ✓）：`(g • (r • t)) h = r * t (g⁻¹ * h)` ✓
＝ `(r • (g • t)) h` ✓（逐坐标 ✓）。 -/
lemma regular_smul_comm {G : Type*} [Group G] {K : Type*} [Semiring K] :
    ∀ (g : G) (r : K) (t : G → K), g • (r • t) = r • (g • t) := by
  intro g r t
  ext h
  rw [regularSMul_apply]
  simp

/-- **单点函数的作用** ✓：`g • Pi.single h a = Pi.single (g * h) a` ✓
（`(g • f) j = f (g⁻¹ * j)` ✓ ⟹ `g⁻¹ * j = h ↔ j = g * h` ✓）。 -/
lemma regularMSA_single {G : Type*} [Group G] {K : Type*} [Semiring K] [DecidableEq G]
    (g h : G) (a : K) :
    g • (Pi.single h a : G → K) = Pi.single (g * h) a := by
  ext j
  rw [regularSMul_apply]
  by_cases hj : j = g * h
  · subst hj
    rw [show g⁻¹ * (g * h) = h by rw [← mul_assoc, inv_mul_cancel, one_mul],
      Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (i := g * h) (i' := j) hj,
      Pi.single_eq_of_ne (i := h) (i' := g⁻¹ * j) (fun hc => hj (by
        rw [← hc, ← mul_assoc, mul_inv_cancel, one_mul]))]

/-- **忠实性** ✓（判据第 ① 款 ✓）：`g • f = f`（对一切 `f` ✓）取 `f = Pi.single 1 1` ✓，
在坐标 `g` 处取值 ✓ 得 `1 = (Pi.single 1 1) g` ✓ ⟹ `g ≠ 1 ⟹ 1 = 0` ✗（`K` 域 ✓）⟹ `g = 1` ✓。
**⚠ 用点** ✓：**须** `Nontrivial K` ✓。 -/
lemma faithfulSMul_regular {G : Type*} [Group G] {K : Type*} [Semiring K] [Nontrivial K] :
    FaithfulSMul G (G → K) where
  eq_of_smul_eq_smul {a b} hab := by
    classical
    have h := congrFun (hab (Pi.single (1 : G) (1 : K))) a
    rw [regularSMul_apply, inv_mul_cancel, Pi.single_eq_same, regularSMul_apply] at h
    by_cases hba : b = a
    · exact hba.symm
    · rw [Pi.single_eq_of_ne (i := (1 : G)) (i' := b⁻¹ * a) (fun hc => hba
        (inv_mul_eq_one.mp hc))] at h
      exact absurd h one_ne_zero

section DeltaFormula

variable {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]

/-- **δ 的求和公式** ✓（单射证明的**主引理** ✓）：`δ x t = Σ_g (coeff g x) * (g • t)` ✓ ——
由 `SkewMonoidAlgebra.induction_on` ✓（`zero` ✓／`single` ✓／`add` ✓）归纳：
`single` 档用 `deltaToEndAdd_single` ✓ ＋ `Finset.sum_eq_single` ✓（`coeff_single_apply` ✓），
`add` 档用 `coeff_add` ✓ ＋ `add_mul` ✓ ＋ `Finset.sum_add_distrib` ✓。 -/
lemma deltaToEndRingHom_apply (x : SkewMonoidAlgebra (G → K) G) (t : G → K) :
    deltaToEndRingHom (regular_smul_comm (G := G) (K := K)) x t
      = ∑ g : G, x.coeff g * (g • t) := by
  classical
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | single g₀ s =>
    change deltaToEndAdd (regular_smul_comm (G := G) (K := K))
        (SkewMonoidAlgebra.single g₀ s) t
      = ∑ g : G, (SkewMonoidAlgebra.single g₀ s).coeff g * (g • t)
    rw [deltaToEndAdd_single, Module.End.mul_apply]
    change s * (g₀ • t) = ∑ g : G, (SkewMonoidAlgebra.single g₀ s).coeff g * (g • t)
    rw [Finset.sum_eq_single g₀]
    · rw [SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
    · intro b _ hb
      rw [SkewMonoidAlgebra.coeff_single_apply, if_neg (fun hc => hb hc.symm), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ g₀) hb
  | add f h hf hh =>
    rw [map_add, LinearMap.add_apply, hf, hh]
    simp only [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul,
      Finset.sum_add_distrib]

/-- **δ 单射** ✓（判据第 ③ 款的**一半** ✓，§4.66 机制 ④ ✓）：设 `δ z = 0` ✓（`z = x - y` ✓），
取 `t = Pi.single h 1` ✓ 并用求和公式 ✓ ＋ `Finset.sum_eq_single (j * h⁻¹)` ✓
抽出唯一贡献项 ✓ ⟹ `(coeff (j * h⁻¹) z) j = 0` ✓（对一切 `j, h` ✓）；
换元 `j := h`、`h := g⁻¹ * h` ✓ 得 `coeff g z = 0` ✓ ⟹ `z = 0` ✓（`SkewMonoidAlgebra.ext` ✓）。 -/
lemma injective_deltaToEndRingHom :
    Function.Injective (deltaToEndRingHom (regular_smul_comm (G := G) (K := K))) := by
  classical
  intro x y hxy
  have hz : deltaToEndRingHom (regular_smul_comm (G := G) (K := K)) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hstep : ∀ (j h' : G), (x - y).coeff (j * h'⁻¹) j = 0 := by
    intro j h'
    have h0 : (deltaToEndRingHom (regular_smul_comm (G := G) (K := K)) (x - y))
        (Pi.single h' (1 : K)) j = 0 := by rw [hz]; rfl
    rw [deltaToEndRingHom_apply, Finset.sum_apply] at h0
    have h1 : ∑ g : G, ((x - y).coeff g * (g • (Pi.single h' (1 : K) : G → K))) j
        = ((x - y).coeff (j * h'⁻¹)
            * ((j * h'⁻¹) • (Pi.single h' (1 : K) : G → K))) j := by
      refine Finset.sum_eq_single (j * h'⁻¹) ?_ ?_
      · intro b _ hb
        rw [Pi.mul_apply, regularMSA_single,
          Pi.single_eq_of_ne (i := b * h') (i' := j) (fun hc =>
            hb (by rw [hc, mul_assoc, mul_inv_cancel, mul_one])), mul_zero]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    rw [h1] at h0
    rw [Pi.mul_apply, regularMSA_single,
      show j * h'⁻¹ * h' = j by rw [mul_assoc, inv_mul_cancel, mul_one],
      Pi.single_eq_same, mul_one] at h0
    exact h0
  have hcoeff : ∀ g : G, (x - y).coeff g = 0 := by
    intro g
    ext h
    have h2 := hstep h (g⁻¹ * h)
    rwa [show h * (g⁻¹ * h)⁻¹ = g by
      rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]] at h2
  exact sub_eq_zero.mp (SkewMonoidAlgebra.ext hcoeff)

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 本轮主结果：分裂 `G`-Galois 代数** ✓✅：`IsGaloisWithGroup K (G → K) G` ✓ ——
**库内首个非平凡** `G`-Galois 实例 ✓（此前库内只有零环档 ✓ 与源侧数据档 ✓）。
**⚠ 证明** ✓（五步 ✓，见本 § 开头机制表 ✓）：忠实性 ✓ ＋ ② 款 ✓ ＋ `δ` 单射 ✓ ＋
**两侧维数相等** ✓ ＋ `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ✓。
**⚠ 工艺** ✓（**本件的两处实例** ✗）：`Module.Finite K (SkewMonoidAlgebra (G → K) G)` **无**实例 ✗
（实测 `synthInstanceFailed` ✓）⟹ 由 `coeffLinearEquiv` ✓ ＋ `Module.Finite.equiv` ✓
**就地注册** ✓（`let _instFinSkew` ✓ —— 不用 `haveI` ✗）；`FiniteDimensional K (SkewMonoidAlgebra …)` ✓
是 `Module.Finite` ✓ 的**缩写** ✓ ⟹ 一步到位 ✓。
**⚠ 维数工艺** ✓：`Module.finrank_finsupp` ✓ 要求 `ι` 与 `M` **同宇宙** ✗
（其签名 `∀ (R) (M) {ι : Type u_4}` ✓；实测 `G : Type u_1` 与 `G → K : Type (max u_1 u_2)` ✗ 不同 ⟹ 不可用 ✗）
⟹ 改走 **`Finsupp.linearEquivFunOnFinite` ✓ ＋ `LinearEquiv.curry` ✓ ＋ `finrank_fintype_fun_eq_card` ✓**
（三者对宇宙**无**该限制 ✓）。
**🔴 不声称** ✗：**不**声称 `K^G` 是域 ✗；**不**声称残余 ① 已驳 ✗（见 §4.67 ✓）。 -/
theorem isGaloisWithGroup_regularAction :
    IsGaloisWithGroup K (G → K) G (regular_smul_comm (G := G) (K := K)) := by
  classical
  let _instFinSkew : Module.Finite K (SkewMonoidAlgebra (G → K) G) :=
    Module.Finite.equiv (SkewMonoidAlgebra.coeffLinearEquiv (S := K) (k := G → K) (G := G)).symm
  refine ⟨faithfulSMul_regular (G := G) (K := K),
    fun g r => algebraMap_fixed_of_smulCommClass
      (regular_smul_comm (G := G) (K := K)) g r, ?_⟩
  have hinj := injective_deltaToEndRingHom (G := G) (K := K)
  have hsmul : ∀ (k : K) (x : SkewMonoidAlgebra (G → K) G),
      deltaToEndRingHom (regular_smul_comm (G := G) (K := K)) (k • x)
        = k • deltaToEndRingHom (regular_smul_comm (G := G) (K := K)) x := by
    intro k x
    induction x using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | single g a =>
      rw [SkewMonoidAlgebra.smul_single]
      change deltaToEndAdd (regular_smul_comm (G := G) (K := K))
          (SkewMonoidAlgebra.single g (k • a))
        = k • deltaToEndAdd (regular_smul_comm (G := G) (K := K))
            (SkewMonoidAlgebra.single g a)
      rw [deltaToEndAdd_single, deltaToEndAdd_single]
      apply LinearMap.ext
      intro y
      change (k • a) * (g • y) = k • (a * (g • y))
      exact smul_mul_assoc k a (g • y)
  let δL : SkewMonoidAlgebra (G → K) G →ₗ[K] Module.End K (G → K) :=
    { toFun := deltaToEndRingHom (regular_smul_comm (G := G) (K := K))
      map_add' := map_add _
      map_smul' := hsmul }
  have hskew : Module.finrank K (SkewMonoidAlgebra (G → K) G)
      = Fintype.card G * Fintype.card G := by
    rw [(SkewMonoidAlgebra.coeffLinearEquiv (S := K) (k := G → K) (G := G)).finrank_eq,
      (Finsupp.linearEquivFunOnFinite K (G → K) G).finrank_eq,
      (LinearEquiv.curry K K G G).symm.finrank_eq]
    simp
  have hend : Module.finrank K (Module.End K (G → K))
      = Fintype.card G * Fintype.card G := by
    rw [Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card]
  have hfin : Module.finrank K (SkewMonoidAlgebra (G → K) G)
      = Module.finrank K (Module.End K (G → K)) := by rw [hskew, hend]
  have hinjL : Function.Injective δL := hinj
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinjL⟩

end DeltaFormula

#print axioms regularSMul_apply
#print axioms regular_smul_comm
#print axioms regularMSA_single
#print axioms faithfulSMul_regular
#print axioms deltaToEndRingHom_apply
#print axioms injective_deltaToEndRingHom
#print axioms isGaloisWithGroup_regularAction

end SplitGaloisAlgebra

/-! ### 4.67 **分裂代数的幂等元** ＋ **残余 ①（非亚单档）的精确登记**（r264 ✓）

**⚠ 目标** ✓：承 §4.65 登记 (丙)(iv) ✓ —— 非亚单档的候选退化目标 ＝ 分裂代数 `K^G` ✓；
本节的**两件** ✓：**①** `K^G ≇ K`（`|G| ≥ 2` ✓）的**机器证明** ✓✅；
**②** 幂等元版**桥引理** ✓（＝把「`L` 有非平凡幂等元 ✓ ＋ `T` 无 ✓」翻成「无 `K`-代数同构」✓）。

**🔴 残余 ①（非亚单档）的终态** ✓（**逐条如实** ✓）：
**(甲) 已落** ✓✅：**前置件** ✓（§4.66 `isGaloisWithGroup_regularAction` ✓，
**库内首个非平凡** `G`-Galois 实例 ✓）；**幂等元计数** ✓（`piSelf_not_algEquiv_self` ✓）；
**桥引理** ✓（`not_nonempty_algEquiv_of_idempotent_of_idempotentFree` ✓）。
**(乙) 卡点（精确）** ✗：**反驳须**「有限域档在**某** `(R,S)` 上**真** ✓」＋「环档在**同载体**上**假** ✗」——
**退化载体 `(R,S) = (F,F)`** ✓：环档**确实假** ✗（见证 ＝ `K := F` ✓、`L := K^G` ✓，
由 (甲) 的幂等元计数 ✓ 与前置件 ✓）**但**前置件（有限域档）在该载体上**假** ✗ ——
`RealizationPropertyFieldFinite F G F F` ✓ 展开后要求
「**一切**有限 `G`-Galois 域扩张 `L/K`（`K ⊇ F` ✓）满足 `L ≅ K` ✓」✗
（`|G| ≥ 2` 时取任一非平凡扩张即违 ✗）。**⟹ `(F,F)` 路线在 `|G| ≥ 2` 档死** ✗。
**(丙) 编码层卡点**（**可复现** ✓，探针 `.abgv52-scratch/probe-r264m.lean` ✓）✗：
把 (乙) 的断言写成机器定理（`¬ RealizationProperty F G F F` ✓）时，`RealizationProperty` ✓ 结论里的
`letI : Algebra R K := φ.toRingHom.toAlgebra` ✓（**遮蔽** ✓）与 `RealizationPropertyExplicit` ✓ 的
`∃ A : Algebra R K` ✓ 使**同一类型上出现两个 `Algebra` 候选** ✗：实测报错
「**Type mismatch**：`AlgHom.id F F` has type `@AlgHom F F F … A A` but is expected to have type
`@AlgHom F F F … (Algebra.id F) (Algebra.id F)`」✓ 与
「**synthesized type class instance is not definitionally equal to expression inferred by typing rules**：
synthesized `@Function.algebra F G F … A`，inferred `… (Algebra.id F)`」✓ ——
即 r262 的**同一编码层**卡点 ✗（r263 之所以能在**亚单档**穿过 ✓，是因为其见证是**零环** ✓，
断言只需 `Subsingleton`／`Nontrivial` ✓ 这类**与代数结构无关**的谓词 ✓；
而幂等元断言**必须**指名张量的**乘法** ✓ ⟹ 须先把张量的实例**逐槽指名** ✓ ——
**本轮已在 §4.68 完成** ✓✅（`selfTensor` ✓ 把张量实例**固定一次** ✓ ＋ `@AlgHom.commutes` ✓ **逐槽指名** ✓：
上述**两处报错均消失** ✓，`not_realizationPropertyExplicit_self_of_two_le_card` ✓ 与
`not_realizationProperty_self_of_two_le_card` ✓ 已落地 ✓）。
**(丁) 有限域档的真实卡点** ✗（**数学内容** ✓，**非**编码 ✗）：要 (乙) 的「有限域档为真」 ✓，
须在**非退化** `(R,S)` ✓（**源侧 generic object** ✓：`R` 局部化多项式环 ✓、
`S = Localization.Away t` ✓）上落 `RealizationPropertyFieldFinite` ✓ —— 那**正是**源
`theorem-5-1`／`theorem-2-1` ✓ 的主线残余 ✓（库内已有
`realizationPropertyFieldFinite_of_sourceData` ✓ 把该档**压到源侧数据** ✓，但其**数据**（`hgal` ✓／`hProj` ✓／
`hS₀R` ✓／`hRQ` ✓／`hRGpoint` ✓）**仍未落** ✗）。
**⚠ 分类（规则 17）** ✓：缺失对象 ＝ **有限域档在非退化载体上的证明** ✓（＝主线**证明义务** ✓，
**非**观测数据 ✗，**亦非**「可算未算」✗）⟹ **不**登记为**材料阻断** ✗；
且其**载体**（源侧数据 ✓）**已在库内具名** ✓ ⟹ 属**主线**残余 ✓，**不**另立新阻断 ✓。
**(戊) 未落** ✗：**(i)** 非亚单档环档桥的**无条件**机器反驳 ✗ —— **载体侧已齐** ✓✅
（环档在 `(F,F)` 上**无条件假** ✓，§4.68 ✓；**条件反驳** ✓（有限域档 ⟹ 桥假 ✓）亦已落 ✓），
**唯一**缺口 ＝ **(丁) 的有限域档** ✓（`(F,F)` 档**假** ✗ —— §4.69 已备好其**消费者** ✓：
**任一**非平凡 `G`-Galois 域扩张即证其假 ✓；非退化档 ＝ 主线残余 ✓）；
**(ii)** 两条源陈述 ✓ **仍未证** ✗（承 §4.65 ✓）。
**🔴 不声称** ✗：**不**声称非亚单档的桥已驳 ✗；**不**声称 `(F,F)` 的有限域档**已被机器反驳** ✗
（其**数学否定** ✓ 须先在库内**构造**一个非平凡 `G`-Galois 域扩张 ✓ —— **未落** ✗，列为下一手 ✓；
**该步的接线件**已在 §4.69 落地 ✓）；
**不**声称两条源陈述已证 ✗。 -/

section SplitAlgebraIdempotents

variable {G : Type} [Fintype G] {K : Type} [Field K]

set_option maxHeartbeats 1000000 in
/-- **非平凡幂等元存在** ✓（`|G| ≥ 2` ✓）：取 `g ≠ h`（`Fintype.exists_pair_of_one_lt_card` ✓）
与坐标 `g` 的**指示函数** `u = Pi.single g 1` ✓：`u * u = u` ✓（逐坐标 ✓）、
`u ≠ 0` ✓（`u g = 1 ≠ 0` ✓）、`u ≠ 1` ✓（`u h = 0 ≠ 1` ✓）。 -/
theorem piSelf_exists_nontrivial_idempotent (hcard : 2 ≤ Fintype.card G) :
    ∃ u : G → K, u * u = u ∧ u ≠ 0 ∧ u ≠ 1 := by
  classical
  obtain ⟨g, h, hgh⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card G)
  refine ⟨Pi.single g 1, ?_, ?_, ?_⟩
  · ext j
    by_cases hj : j = g
    · subst hj; simp
    · simp [hj]
  · intro hzero
    have h2 := congrFun hzero g
    simp at h2
  · intro hone
    have h2 := congrFun hone h
    simp [Pi.single_eq_of_ne (i := g) (i' := h) hgh.symm] at h2

set_option maxHeartbeats 1000000 in
/-- **🔴 `K^G ≇ K`** ✓✅（`|G| ≥ 2` ✓）：设 `e : K^G ≃ₐ[K] K` ✓，取非平凡幂等元 `u` ✓（上件 ✓）
⟹ `e u` 是 `K` 的幂等元 ✓ ⟹ `e u = 0 ∨ e u = 1` ✓（**域内** `x * x = x ⟹ x (x - 1) = 0` ✓
＋ `mul_eq_zero` ✓）⟹ `u = 0 ∨ u = 1` ✓（`e` 单射 ✓ ＋ `map_zero`／`map_one` ✓）—— 与 `u` 非平凡矛盾 ✗。
**⚠ 地位** ✓：本件是**分裂代数**作为「退化目标」的**判别力** ✓（§4.65 (丙)(iv) 的预期 ✓ 已落地 ✓）。 -/
theorem piSelf_not_algEquiv_self (hcard : 2 ≤ Fintype.card G) :
    ¬ Nonempty ((G → K) ≃ₐ[K] K) := by
  classical
  rintro ⟨e⟩
  obtain ⟨u, hu, hu0, hu1⟩ := piSelf_exists_nontrivial_idempotent (G := G) (K := K) hcard
  have he : e u * e u = e u := by rw [← map_mul, hu]
  have h0 : e u * (e u - 1) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  rcases (mul_eq_zero.mp h0) with hz | hone
  · exact hu0 (e.injective (by rw [hz, map_zero]))
  · exact hu1 (e.injective (by rw [sub_eq_zero.mp hone, map_one]))

set_option maxHeartbeats 1000000 in
/-- **桥引理（幂等元版）** ✓（§4.65 的 `not_nonempty_algEquiv_of_subsingleton_of_nontrivial` ✓ 的**对偶** ✓）：
`L` 有**非平凡幂等元** ✓ ＋ `T` 的幂等元**只有 `0, 1`** ✓ ⟹ **无** `K`-代数同构 `L ≃ₐ[K] T` ✓
（同构把幂等元搬到幂等元 ✓，`e 0 = 0` ✓／`e 1 = 1` ✓ ＋ 单射 ✓）。
**⚠ 工艺** ✓（**与 r263 同款** ✓）：两个 `Algebra` 实例作**显式变元** ✓（`aL` ✓／`aT` ✓，**非** instance binder ✗）
⟹ 下游应用时由 **unify** ✓（对齐具体张量实例 ✓）而非 **synth** ✗ 决定 ✓ ——
这是穿过 `letI` 遮蔽的关键 ✓（`linter.unusedVariables` 由 `let _instL`／`let _instT` 命名规避 ✓）。 -/
theorem not_nonempty_algEquiv_of_idempotent_of_idempotentFree {K L T : Type*} [CommSemiring K]
    [Semiring L] [Semiring T] (aL : Algebra K L) (aT : Algebra K T)
    (hL : ∃ u : L, u * u = u ∧ u ≠ 0 ∧ u ≠ 1)
    (hT : ∀ u : T, u * u = u → u = 0 ∨ u = 1) :
    ¬ Nonempty (@AlgEquiv K L T _ _ _ aL aT) := by
  let _instL : Algebra K L := aL
  let _instT : Algebra K T := aT
  rintro ⟨e⟩
  obtain ⟨u, hu, hu0, hu1⟩ := hL
  have he : e u * e u = e u := by rw [← map_mul, hu]
  rcases hT (e u) he with hz | hone
  · exact hu0 (e.injective (by rw [hz, map_zero]))
  · exact hu1 (e.injective (by rw [hone, map_one]))

set_option maxHeartbeats 1000000 in
/-- **登记（非亚单档）** ✓：残余 ①（环档桥 ✓）**非亚单档**的终态 ——
**A**（已落 ✓✅）：前置件 ✓（§4.66 ✓）／幂等元计数 ✓（`piSelf_not_algEquiv_self` ✓）／
桥引理 ✓（`not_nonempty_algEquiv_of_idempotent_of_idempotentFree` ✓）。
**B**（卡点 ✗）：反驳须**非退化**载体上的有限域档 ✓（源侧 generic object ✓，其数据未落 ✗）；
退化载体 `(F,F)` 的环档**确实假** ✗，但其有限域档**假** ✗ ⟹ 该路线**死** ✗。
**C**（编码层 ✗）：写成机器定理时尚有 `letI` 遮蔽导致的**实例二义** ✗
（探针 `.abgv52-scratch/probe-r264m.lean` ✓ 可复现 ✓）。
**D**（下一手 ✓）：**①** 库内构造**一个非平凡 `G`-Galois 域扩张** ✓（如 `ℂ/ℝ` ＋ `G = ZMod 2` ✓，
δ 双射由 `finrank ℝ ℂ = 2` ✓ ＋ 单射 ✓）⟹ 可把 `(F,F)` 的有限域档**机器反驳** ✗✅，
从而把「`(F,F)` 路线已死」从**数学断言** ✓ 升级为**机器读数** ✓；
**②** 源侧数据（`hgal` ✓／`hProj` ✓／`hS₀R` ✓／`hRQ` ✓／`hRGpoint` ✓）⟹ 非退化载体上的有限域档 ✓
⟹ 非亚单档反驳 ✓（**须先过 C** ✓）。
**🔴 不声称** ✗：**不**声称本件给出反驳 ✗（**只**给出**前置件 ＋ 判别力 ＋ 卡点定位** ✓）。 -/
theorem ringTierBridge_nonSingleton_registered : True := trivial

#print axioms piSelf_exists_nontrivial_idempotent
#print axioms piSelf_not_algEquiv_self
#print axioms not_nonempty_algEquiv_of_idempotent_of_idempotentFree
#print axioms ringTierBridge_nonSingleton_registered

end SplitAlgebraIdempotents

/-! ### 4.68 **退化载体 `(F,F)` 的环档反驳 ＋ 条件桥反驳**（r264 ✓：环档在 `(F,F)` 上**无条件假** ✓✅）

**⚠ 起点** ✓（承 §4.67 的登记 ✓）：§4.67 已落**前置件** ✓（分裂代数 `G`-Galois ✓）、
**幂等元计数** ✓（`K^G ≇ K` ✓）与**幂等元版桥引理** ✓；本轮把三者**接成反驳** ✓✅。

**⚠ 主张（逐条，**不**越界 ✓）**：
**①** `¬ RealizationPropertyExplicit F G F F` ✓（`|G| ≥ 2` ✓）—— **显式实例形**的环档在 `(F,F)` 上**假** ✗；
**②** `¬ RealizationProperty F G F F` ✓ —— **源形**环档在同载体上**假** ✗（由 ① ＋ **旧 ⟹ 新** ✓ 的**逆否** ✓）；
**③** `RealizationPropertyFieldFinite F G F F → ¬ RealizationRingTierBridge F G` ✓ —— **条件桥反驳** ✓
（＝「若有限域档在 `(F,F)` 上真 ✓，则环档桥**被分裂代数反驳** ✓」）。
**⚠ 机制** ✓（① 的证明链 ✓，**四步** ✓）：`obtain ⟨φ, A, hA, hP⟩` ✓ ⟹
**(a)** `A = Algebra.id F` ✓（`φ` 是 `F` 的**唯一** `F`-代数自同态 ✓ —— `AlgHom.commutes` ✓ ＋
`algebra_ext_of_algebraMap_eq` ✓ ⟹ `A.algebraMap = RingHom.id F` ✓）；
**(b)** `hP` 沿 (a) **搬运** ✓（`▸` ✓：两边都写成**同一显式实例式** ✓ ⟹ motive 的实例元变量由 **unify** 定 ✓）；
**(c)** 典范张量 `F ⊗_F F` 的**幂等元只有 `0, 1`** ✓（`Algebra.TensorProduct.rid` ✓ 把它送到 `F` ✓，
再用**域内** `x * x = x ⟹ x = 0 ∨ x = 1` ✓）；
**(d)** 分裂代数的**非平凡幂等元** ✓（§4.67 ✓）＋ **桥引理** ✓（§4.67 ✓，两 `Algebra` 实例作**显式变元** ✓
⟹ 由 **unify** 决定 ✓）。
**⚠ 关键技术读数** ✓（**r262／r263 卡点的突破** ✓，两处 ✓）：**(i)** 陈述里的张量**必须写成显式实例式** ✓
（`@TensorProduct F _ F F _ _ (@Algebra.toModule F F _ _ A) (@Algebra.toModule F F _ _ (Algebra.id F))` ✓，
本 § 用 `abbrev selfTensor` ✓ 把它**固定一次** ✓）；**(ii)** `AlgHom.commutes` ✓ 等引理在 `A` 进语境后
会**误取** `A` 作 `Algebra F F` 实例 ✗（实测报错「synthesized `A` / inferred `Algebra.id F`」✓）
⟹ **须**写成 `@AlgHom.commutes F F F _ _ _ (Algebra.id F) (Algebra.id F) φ x` ✓（**逐槽指名** ✓）。
**🔴 不声称** ✗：**不**声称 ③ 的**前件**成立 ✗ —— 恰恰相反：`(F,F)` 的有限域档要求
「一切有限 `G`-Galois 域扩张 `L/K`（`K ⊇ F`）满足 `L ≅ K`」✗（`|G| ≥ 2` 时**假** ✗，见 §4.67 (乙) ✓）
⟹ ③ **不**给出**无条件**反驳 ✗（**它**给出的是**卡点的精确定位** ✓：非亚单档的反驳**等价于**在
**非退化**载体上落有限域档 ✓ ＝ 源侧主线残余 ✓）。
**🔴 不声称** ✗：**不**声称非亚单档的桥已驳 ✗；**不**声称两条源陈述已证 ✗。 -/

section RingTierSelfRefuted

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G]

attribute [local instance] regularSMul regularMSA

/-- **自张量 `F ⊗_F F`（第一因子取给定 `Algebra F F` ✓，第二因子取 `Algebra.id F` ✓）** ✓：
**具名一次** ✓ ⟹ 下游一切陈述共用**同一批**实例项 ✓ —— 这是穿过 `letI` 遮蔽的关键工艺 ✓
（r262／r263 的实例二义 ✗ 在此被**固定** ✓）。 -/
abbrev selfTensor (F : Type) [Field F] (A : Algebra F F) : Type :=
  @TensorProduct F _ F F _ _ (@Algebra.toModule F F _ _ A) (@Algebra.toModule F F _ _ (Algebra.id F))

set_option maxHeartbeats 1000000 in
/-- **典范自张量的幂等元只有 `0, 1`** ✓：`Algebra.TensorProduct.rid F F F : F ⊗_F F ≃ₐ[F] F` ✓ 把幂等元送到 `F` ✓；
`F` 域 ⟹ `x * x = x ⟹ x (x - 1) = 0 ⟹ x = 0 ∨ x = 1` ✓（`mul_eq_zero` ✓）；
回拉用 `rid` 的**单射** ✓ ＋ `map_zero` ✓／`map_one` ✓。 -/
lemma selfTensor_idem (u : selfTensor F (Algebra.id F)) (hu : u * u = u) : u = 0 ∨ u = 1 := by
  have h1 : (Algebra.TensorProduct.rid F F F) u * (Algebra.TensorProduct.rid F F F) u
      = (Algebra.TensorProduct.rid F F F) u := by rw [← map_mul, hu]
  have h2 : (Algebra.TensorProduct.rid F F F) u
      * ((Algebra.TensorProduct.rid F F F) u - 1) = 0 := by
    rw [mul_sub, mul_one, h1, sub_self]
  rcases (mul_eq_zero.mp h2) with h3 | h3
  · left
    refine (Algebra.TensorProduct.rid F F F).injective ?_
    rw [h3, map_zero]
  · right
    refine (Algebra.TensorProduct.rid F F F).injective ?_
    rw [sub_eq_zero.mp h3, map_one]

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 环档在 `(F,F)` 上假（显式实例形）** ✓✅：`|G| ≥ 2` ⟹
`¬ RealizationPropertyExplicit F G F F` ✓ —— 见证 ＝ `K := F` ✓、`L := G → F` ✓（分裂代数 ✓，
由 §4.66 前置件 ✓ 是 `F`-上 `G`-Galois ✓）。
**⚠ 证明四步** ✓（见本 § 开头机制表 ✓）：`A = Algebra.id F` ✓（**唯一自同态** ✓）⟹
张量沿 (a) **搬运** ✓ ⟹ **幂等元计数** ✓（`selfTensor_idem` ✓ ＋ `piSelf_exists_nontrivial_idempotent` ✓）
⟹ **桥引理** ✓（`not_nonempty_algEquiv_of_idempotent_of_idempotentFree` ✓，两 `Algebra` 实例**由 unify 定** ✓）。
**⚠ 工艺** ✓：`AlgHom.commutes` ✓ **须**逐槽指名 ✗（否则误取 `A` ✗，实测报错
「synthesized `A` / inferred `Algebra.id F`」✓）。 -/
theorem not_realizationPropertyExplicit_self_of_two_le_card (hcard : 2 ≤ Fintype.card G) :
    ¬ RealizationPropertyExplicit F G F F := by
  classical
  have hL : ∃ u : G → F, u * u = u ∧ u ≠ 0 ∧ u ≠ 1 :=
    piSelf_exists_nontrivial_idempotent (G := G) (K := F) hcard
  have hcanon : ∀ u : selfTensor F (Algebra.id F), u * u = u → u = 0 ∨ u = 1 :=
    fun u hu => selfTensor_idem (F := F) u hu
  intro h
  let _instMSA : MulSemiringAction G (G → F) := regularMSA G F
  have hKL : ∀ (g : G) (r : F) (t : G → F), g • (r • t) = r • (g • t) :=
    regular_smul_comm (G := G) (K := F)
  have hgal : IsGaloisWithGroup F (G → F) G hKL :=
    isGaloisWithGroup_regularAction (G := G) (K := F)
  obtain ⟨φ, A, hA, hP⟩ := h F (G → F) hKL hgal
  have hφ : ∀ x : F, φ x = x := by
    intro x
    exact @AlgHom.commutes F F F _ _ _ (Algebra.id F) (Algebra.id F) φ x
  have hAA : A = Algebra.id F := by
    apply algebra_ext_of_algebraMap_eq
    intro x
    show A.algebraMap x = (Algebra.id F).algebraMap x
    rw [show A.algebraMap x = φ x from by rw [hA]; rfl]
    exact hφ x
  have hT : ∀ u : selfTensor F A, u * u = u → u = 0 ∨ u = 1 := hAA ▸ hcanon
  exact not_nonempty_algEquiv_of_idempotent_of_idempotentFree (K := F) (L := G → F)
    (T := selfTensor F A) _ _ hL hT hP

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 环档在 `(F,F)` 上假（源形）** ✓✅：`|G| ≥ 2` ⟹ `¬ RealizationProperty F G F F` ✓ ——
由**显式实例形**的反驳 ✓ ＋ **旧 ⟹ 新** ✓（`realizationPropertyExplicit_of_realizationProperty` ✓）的**逆否** ✓。
**⚠ 意义** ✓：源形（＝两条源陈述所用之档 ✓）在 `(F,F)` 上**不成立** ✗ ⟹ 桥的**结论侧**在该载体上
**必然假** ✗ —— 故 `(F,F)` 路线**唯一**缺口 ＝ **前件（有限域档）** ✓（下件 ✓）。 -/
theorem not_realizationProperty_self_of_two_le_card (hcard : 2 ≤ Fintype.card G) :
    ¬ RealizationProperty F G F F :=
  fun h => not_realizationPropertyExplicit_self_of_two_le_card (F := F) (G := G) hcard
    (realizationPropertyExplicit_of_realizationProperty h)

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 条件桥反驳（退化载体 `(F,F)`）** ✓✅：**若**有限域档在 `(F,F)` 上**真** ✓
（`RealizationPropertyFieldFinite F G F F` ✓）**则**环档桥 `RealizationRingTierBridge F G` ✓ **假** ✗
（`|G| ≥ 2` ✓）。
**⚠ 地位** ✓（**精确** ✓）：本件把非亚单档反驳的**全部缺口**压到**单一前件** ✓ ——
即 `(F,F)` 的有限域档 ✓；而该前件**恰好假** ✗（§4.67 (乙) ✓：它要求一切有限 `G`-Galois 域扩张平凡 ✓）
⟹ **本件不构成无条件反驳** ✗（**如 §4.68 头注 (🔴) 所述** ✓）。
**⚠ 用途** ✓：**下一手**若在**非退化**载体（源侧 generic object ✓）上落有限域档 ✓，
把本件的 `(F,F)` 换成该载体 ✓ 即得**无条件反驳** ✓（**须**先把张量的实例逐槽指名 ✓，见 (丙) ✓）。 -/
theorem not_realizationRingTierBridge_of_fieldTier_self (hcard : 2 ≤ Fintype.card G)
    (hFF : RealizationPropertyFieldFinite F G F F) : ¬ RealizationRingTierBridge F G :=
  fun hb => not_realizationProperty_self_of_two_le_card (F := F) (G := G) hcard (hb F F hFF)

#print axioms selfTensor_idem
#print axioms not_realizationPropertyExplicit_self_of_two_le_card
#print axioms not_realizationProperty_self_of_two_le_card
#print axioms not_realizationRingTierBridge_of_fieldTier_self

end RingTierSelfRefuted

/-! ### 4.69 **`(F,F)` 有限域档的消费者**（r264 ✓：任一非平凡 `G`-Galois 域扩张 ⟹ `(F,F)` 档假 ✓✅）

**⚠ 起点** ✓（承 §4.67 (丁) ✓／§4.68 ✓）：非亚单档反驳的**唯一**缺口 ＝ 有限域档在**某** `(R,S)` 上为真 ✓；
而 §4.67 已指出 `(F,F)` 档**假** ✗（它要求一切有限 `G`-Galois 域扩张平凡 ✓）。
本件把该**断言**升级为**定理** ✓✅：**给**一个非平凡扩张 ✓（`L/K` 有限 ✓ ＋
`IsGaloisWithGroup K L G` ✓ ＋ `¬ Nonempty (L ≃ₐ[K] K)` ✓）⟹
`¬ RealizationPropertyFieldFinite F G F F` ✓。

**⚠ 机制** ✓（**三步** ✓，且**不**触发 §4.67 (丙) 的编码卡点 ✓✅）：由该档取 `(K, L)` ✓ 得
`∃ φ : F →ₐ[F] K` ✓ ＋（`letI` 遮蔽下）`Nonempty (L ≃ₐ[K] (K ⊗_F F))` ✓；**关键工艺** ✓：
`let _inst : Algebra F K := φ.toRingHom.toAlgebra` ✓ **就地**把 `letI`-遮蔽的实例**具名** ✓
（`let`-绑定与其值 ***defeq*** ✓ ⟹ 张量实例**对齐** ✓），再用
`Algebra.TensorProduct.rid F K K : (K ⊗_F F) ≃ₐ[K] K` ✓ **复合** ✓ ⟹ `Nonempty (L ≃ₐ[K] K)` ✓
—— 与 `hne` ✓ 矛盾 ✓。
**⚠ 与 §4.67 (丙) 之别** ✓：本件的 `∃` **只**绑定 `φ` ✓（**不**绑定 `Algebra F K` ✓）⟹
`A`-型实例污染**不存在** ✗ ⟹ **无需** `selfTensor` 式逐槽指名 ✓（**实测一次通过** ✓，探针
`.abgv52-scratch/probe-r264p.lean` ✓，**零警告** ✓）。
**⚠ 用途** ✓（**把下一手接线完毕** ✓）：非亚单档反驳的路线图现为
**①**（可选，判别力）库内构造一个非平凡 `G`-Galois 域扩张 ✓（如 `ℂ/ℝ` ＋ `G` 为二阶群 ✓：
δ 双射由 `finrank ℝ ℂ = 2` ✓ ＋ `t = 1`／`t = I` 两处取值 ✓ 导单射 ✓）⟹ 由本件得 `(F,F)` 档假 ✗
（＝「`(F,F)` 路线已死」的**机器读数** ✓）；**②** 在**非退化**载体上落有限域档 ✓（＝主线残余 ✓）
⟹ 由 §4.68 的条件反驳 ✓ 得**无条件**桥反驳 ✓✅。
**⚠ 分类（规则 17）** ✓：本件**不**使缺口变为材料阻断 ✗ —— 缺的仍是**主线证明义务** ✓
（源侧数据 ✓），**非**观测数据 ✗。
**🔴 不声称** ✗：**不**声称 `(F,F)` 的有限域档**已被无条件**机器反驳 ✗（**须先**给出一个非平凡
`G`-Galois 域扩张 ✓ —— **未落** ✗，列为下一手 ① ✓）；**不**声称非亚单档的桥已驳 ✗；
**不**声称两条源陈述已证 ✗。 -/

section FieldTierSelfRefuted

set_option maxHeartbeats 1000000 in
/-- **🔴 非平凡 `G`-Galois 域扩张 ⟹ `(F,F)` 有限域档假** ✓✅：设 `K ⊇ F` ✓、`L/K` 有限 ✓、
`L` 上 `G` 作用使 `K`-判据成立 ✓、且 `L ≄ K` ✓（**非平凡** ✓）⟹
`¬ RealizationPropertyFieldFinite F G F F` ✓。
**⚠ 证明** ✓：反证 ✓ —— 该档给出 `φ` ✓ 与 `K`-代数同构 `L ≅ K ⊗_F F` ✓；
`let _inst` ✓ 具名遮蔽实例 ✓ ＋ `Algebra.TensorProduct.rid F K K` ✓（**右单位** ✓）复合 ✓
得 `L ≅ K` ✓，与 `hne` ✗ 矛盾 ✓。
**⚠ 地位** ✓：本件是 §4.67 (丁) 所述「`(F,F)` 路线已死」的**接线件** ✓ ——
**任一**非平凡 `G`-Galois 域扩张即**证其假** ✓（**不**依赖 `K = F` ✓／**不**依赖 `G` 的阶 ✓）。 -/
theorem not_realizationPropertyFieldFinite_self_of_not_algEquiv_self
    {F : Type} [Field F] {G : Type} [Group G] [Fintype G]
    {K : Type} [Field K] [Algebra F K] {L : Type} [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower F K L] [FiniteDimensional K L] [MulSemiringAction G L]
    (hKL : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hgal : IsGaloisWithGroup K L G hKL) (hne : ¬ Nonempty (L ≃ₐ[K] K)) :
    ¬ RealizationPropertyFieldFinite F G F F := by
  intro h
  obtain ⟨φ, hP⟩ := h K L hKL hgal
  let _inst : Algebra F K := φ.toRingHom.toAlgebra
  obtain ⟨e⟩ := hP
  exact hne ⟨e.trans (Algebra.TensorProduct.rid F K K)⟩

#print axioms not_realizationPropertyFieldFinite_self_of_not_algEquiv_self

end FieldTierSelfRefuted

/-! ### 4.70 **源侧 generic object 上的有限域档**：**两行残余**（`δ` 双射 ＋ `hProj`）（第 265 轮）

**⚠ 起点** ✓（**承 §4.56** ✓（`realizationPropertyFieldFinite_of_sourceData` ✓）／**§4.62** ✓（`SaltGeneric` ✓
的**载体具体化谓词级件** ✓）／**r228--r231** ✓（`T` 三项 ✓／三实例 ✓／`hRG` ✓／`hact` ✓／`hS_0R` ✓
**全由构造供给** ✓）／**r260** ✓（不动域改接 ✓，残余 ④ ✓））：
在**源侧 generic object**（Noether 域的不动子代数 `L^G` 中取数据 `a` ✓／`s_0` ✓，
载体 ＝ `noetherFixedCarrier F G a s_0` ✓，`S` ＝ `Localization.Away T` ✓）上，
**有限域档** `RealizationPropertyFieldFinite` ✓ 此前**只有**「**十八槽源侧数据**」的形 ✓
（§4.56 ✓：**4 数据** ✓（`t` ✓／`ht` ✓／`ht_inv` ✓／`hinf` ✓）＋ **7 具名行** ✓
（`hact_map` ✓／`hRG` ✓／`hgal` ✓／`hProj` ✓／`hS_0R` ✓／`hRQ` ✓／`hRGpoint` ✓）＋ **7 实例** ✓），
**未按 r228--r231 的构造供给收口** ✗。

**🔴 本轮断指** ✓（**六件** ✓；**探针** ✓ `.abgv52-scratch/probe-r265c.lean` ✓／`probe-r265e.lean` ✓／
`probe-r265j.lean` ✓／`probe-r265k.lean` ✓ **rc=0** ✓、**零警告** ✓）：
**①** `realizationPropertyFieldFinite_pUnit_rat_genericObject` ✓✅ —— **`ℚ`／`PUnit` 档的**
**无条件**有限域档实例 ✓（**非退化载体** ✓：`R = ↥S` ✓ 而 `S ≠ R` ✓ —— 与 §4.63 的 `(F,F)` 退化作别 ✓）；
**②** `exists_realizationPropertyFieldFinite_of_noetherFixedWiring` ✓✅ —— **两行残余归约** ✓：
`T` ✓／`ht` ✓／`T` 不变化 ✓／`hle` ✓／三实例 ✓／`hact_map` ✓／`hRG` ✓／`hS_0R` ✓ **全由构造供给** ✓
⟹ 余下**只有两行** ✓：**`δ` 双射** ✓（＝ **Galois 内容** ✓；`IsGaloisWithGroup` 的 ① 由
`faithfulSMul_away_of_noetherAdjoin` ✓、② 由 `algebraMap_fixed_of_smulCommClass` ✓ 供给 ✓）与 **`hProj`** ✓；
**③** **三款齐备** ✓✅（`exists_isGenericExtensionFieldFinite_of_noetherFixedWiring` ✓）——
同 ∃-包 ✓，唯结论取 **`IsGenericExtensionFieldFinite`** ✓（**(a)** ✓ ＋ **(b)** ✓ ＋ **(c)** ✓）：
**(a) 款亦已落** ✓✅（**r260 §I** ✓：`exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul` ✓，
**无 `hgen` 形** ✓），**代价** ＝ 两行**数据** ✓（`hind` ✓／`s_0 ∈ F[a]` ✓，**读在 `L^G`** ✓）；
**④** **源形见证（＋残余 ①）** ✓✅（`exists_genericExtensionWitness_of_noetherFixedWiring_and_ringBridge` ✓）——
**对 §J 归约的严格加强** ✓：**残余 ④（21 行）⟹ 数据两行 ＋ 端点两行** ✓；
**⑤** **`s_0 := 1` 档** ✓（`exists_realizationPropertyFieldFinite_of_noetherFixedWiring_one` ✓）——
**`hs_0` 假设亦被消去** ✓（`s_0 := 1` ✓ 满足 ✓）⟹ (c) 款的外层输入**只剩** `a` ✓ 与 `[Infinite F]` ✓；
**⑥** **残余 ③ 的同一收口** ✓✅（`exists_thm21ClausesResidual_of_noetherFixedWiring` ✓）——
**源 `theorem-2-1` 侧的具名残余** ✓（`Thm21ClausesResidual` ✓，**＝ 源 §2 的构造** ✓，**库内此前无构造件** ✗）
**与残余 ④ 由同一件供给** ✓✅ ⟹ **两行残余 ＋ 一行数据确为两条源陈述的**公共输入** ✓**。

**⚠ 残余表（源侧 generic object 上的有限域档，逐行）** ✓（**本轮实数** ✓）：

| 行 | 状态 | 根据 |
|---|---|---|
| `t` ✓／`t ≠ 0` ✓／`g • t = t` ✓ | **已落** ✓✅ | `exists_invariant_t_of_noether` ✓（SaltGeneric:2983 ✓），本件**构造** ✓ |
| `hle` ✓（载体 ⊆ `M[T⁻¹]` ✓） | **已落** ✓✅ | 同上 ✓（`hTle` ✓），本件**构造** ✓ |
| `[Algebra ↥S S']` ✓／`[IsScalarTower …]` ✓／`[MulSemiringAction G S']` ✓ | **已落** ✓✅ | `exists_algHom_away_of_noetherAdjoin` ✓（r228 ✓）／`awayMulSemiringAction` ✓（SaltGeneric:3201 ✓） |
| `hact_map` ✓ | **已落** ✓✅ | `awayRingHom_algebraMap` ✓（SaltGeneric ✓），本件**构造** ✓ |
| `hRG` ✓ | **已落** ✓✅ | `smulCommClass_away_of_algHom` ✓（r230 ✓），本件**构造** ✓ |
| `hS_0R` ✓ | **已落** ✓✅ | r229 ✓（`ι` 的刻画式 ✓），本件**构造** ✓ |
| `hRQ` ✓／`hRGpoint` ✓ | **已落** ✓✅（**已消** ✗） | §4.47 ✓（载体具体化 ✓）；§4.62 ✓ 的假设表已不含 ✓ |
| `hS_fix` ✓（逐点不动 ✓） | **已落** ✓✅ | `smul_eq_self_of_mem_adjoin_of_fixed` ✓（§4.47 ✓；`L^G` 读法下由 `.2` ✓ 直接给 ✓） |
| **(a) 款** ✓（`↥S ≃_F Localization.Away w` ✓） | **已落** ✓✅ | **r260 §I** ✓（`exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul` ✓，**无 `hgen`** ✓）＋ (甲) ①② 的搬运 ✓；**`③` 件已消费** ✓ |
| **`a`** ✓（`L^G` 中的数据族 ✓） | **已落**（**条件** ✓） | r260 §E ✓（`exists_fixed_transcendenceBasis_of_isRationalOver` ✓，**源假设 `IsRationalOver F L^G`** ✓）；**⚠ 该假设本身 ＝ Noether 问题** ✓ |
| **`hind`** ✓（`a` 在 `F` 上代数无关 ✓） | **已落**（**条件** ✓） | 同上 ✓；**⚠ 无条件可得性未落** ✗（启发式 ✓：`trdeg_F L^G = |G|` ✓ ⟹ `G` 非平凡时存在 ✓） |
| `s_0 ≠ 0` ✓／`s_0 ∈ F[a]` ✓ | **已落** ✓✅（**可免** ✓） | `s_0 := 1` ✓（**③／⑤ 件** ✓） |
| **`δ` 双射** ✓ | **仍开** ✗ | 交叉相积同构 ✓（源 `proposition-0-5` ✓／CHR 代数版 ✗，**在册** ✗）；**`ℚ`／`PUnit` 档已落** ✓✅（r249 ✓：满射 ⟹ 双射 ✓） |
| **`hProj`** ✓ | **仍开** ✗ | 源 `proposition-0-2(a)` ✓（`[CHR68]` p. 13 ✓）；**⚠ 其「任意档」现形已被机器反驳** ✗（`galoisProjectiveHyp_refuted` ✓，r234 ✓）⟹ **须按预期用例读** ✓；**`ℚ`／`PUnit` 档已落** ✓✅（r246 ✓） |
| **残余 ①** ✓（**环档桥** ✓） | **仍开** ✗ | 只影响**源形**（**④ 件** ✓）；**(c) 款与三款齐备形（②／③）不需要它** ✓ |
| `Infinite F` ✓ | **假设** ✓ | 源 `theorem-5-1` 的「`F` infinite」✓ |

**⚠ 两档的口径** ✓（**勿混用** ✗）：**(c) 款** ✓（②／⑤ 件 ✓）**只需** `a` ✓ 与 `s_0 ≠ 0` ✓（**`a` 任意** ✓）；
**三款齐备形** ✓（③ 件 ✓）**另需** `hind` ✓／`hs_0 ∈ F[a]` ✓（**(a) 款的输入** ✓）；
**源形** ✓（④ 件 ✓）**再加残余 ①** ✓。

**🔴 不声称** ✗：**不**声称 `δ` 双射 ✗／**`hProj`** ✗ 已证（**两行皆开** ✗）；
**不**声称残余 ①（**环档桥** ✓）已证 ✗；**不**声称 `\exists a,\ \mathrm{AlgebraicIndependent}\ F\ a`（`L^G` 中 ✓）
**无条件可证** ✗；**不**声称源 `theorem-5-1` ✓／`theorem-2-1` ✓ 已证 ✗；**不**声称 §4.69 的 `(F,F)` 路线可用 ✗
（**已机器判定为假** ✗）；**不**声称本件给出桥的无条件反驳 ✗（**须先把有限域档落在 `(F,F)` 上** ✗，
**而它恰假** ✗）。**⚠ 无 sorry、无自造公理** ✓；公理门见下 ✓。 -/

section FiniteFieldTierGenericObject

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **`ℚ`／`PUnit` 档的 generic object 载体** ✓：`x := algebraMap (MvPolynomial PUnit ℚ) (NoetherField ℚ PUnit) X` ✓，
载体 ＝ `ℚ[x] ∪ {x, x⁻¹}` ✓ —— **与 r249 ✓ 的接线载体逐字同款** ✓（**非退化** ✓：`S ≠ R` ✓）。 -/
abbrev pUnitGenericCarrier : Subalgebra ℚ (NoetherField ℚ PUnit.{1}) :=
  Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})

section

noncomputable local instance instMSA265 : MulSemiringAction PUnit.{1}
    (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

noncomputable local instance instAlg265 : Algebra ↥(pUnitGenericCarrier)
    (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) :=
  (awayAlgEquivAdjoin_pUnit_rat).symm.toRingHom.toAlgebra

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 `ℚ`／`PUnit` 档：源侧 generic object 上的有限域档（无条件** ✓✅**）** ——
`RealizationPropertyFieldFinite ℚ PUnit ↥S (Localization.Away X)` ✓，`S` ＝ `pUnitGenericCarrier` ✓。
**⚠ 意义** ✓（**L1 的最强形** ✓）：**表内每一行都被实例化** ✓ ——
`T = X` ✓（`ht` ✓／不变化 ✓）／三实例 ✓／`hle` ✓（`adjoin_away_eq_adjoin_union_inv_pUnit_rat` ✓
的反向 ＋ `Set.inv_singleton` ✓）／`hS_fix` ✓（`smul_eq_self_of_mem_adjoin_of_fixed` ✓）／`hact_map` ✓
（经 `noetherRingHom` ✓）／`hRG` ✓（平凡作用 ✓）／**`hgal`** ✓（r249 ✓）／**`hProj`** ✓（r246 ✓）／
`hS_0R` ✓（`awayAlgEquivAdjoin_pUnit_rat.apply_symm_apply` ✓）⟹
**两行残余在该档双双落地** ✓✅ ⟹ **本件是残余表的正例对照** ✓（L19 ✓：**结论非平凡** ✓ ——
它是**全称**有限 `PUnit`-`G`-Galois 扩张的分类 ✓，与 §4.63 的 `(F,F)` 档**不同载体** ✓）。
**⚠ 工艺读数** ✓（**须入纪律** ✓）：**不得**为 `hx_fix` 一族写**带类型的 `have`** ✗ ——
`PUnit` 的**泛用 `SMul`** ✓ 会**抢先**被选上 ✓（实测报错「`synthesized PUnit.instSMul_mathlib` /
`inferred instSMulZeroClass.toSMul`」✓）⟹ **正解** ＝ 把 λ 直接放在**期望类型会传播**的实参位 ✓
（本件对 `smul_eq_self_of_mem_adjoin_of_fixed` ✓ 即如此 ✓）。
**⚠ 断言强度 ≤ 证据层级** ✓：**不声称** `G` **非平凡**档已落 ✗（**`PUnit` 亚单** ✓，
两行残余的**一般档**仍开 ✗）；**不声称**源陈述已证 ✗。
**⚠ 判别力（L43）** ✓：**变异件负例已实跑** ✓ —— **同款**（把 `hProj` ✗／`hδ` ✗ 换成 `True` ✓）
见 `.abgv52-scratch/probe-r265f.lean` ✓ **rc≠0** ✓（**M1／M2** ✓）；本件的**每一行**都在证明体内
**作为实参被消费** ✓（`hle` ✓／`hS_fix` ✓／`hact_map` ✓／`hRG` ✓／`hgal` ✓／`hProj` ✓／`hS_0R` ✓ ——
**无一行可省** ✗）。 -/
theorem realizationPropertyFieldFinite_pUnit_rat_genericObject :
    RealizationPropertyFieldFinite ℚ PUnit.{1} ↥(pUnitGenericCarrier)
      (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) := by
  have hEq : Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 =>
        algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
          (MvPolynomial.X PUnit.unit))
      ∪ {algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit),
          (algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹})
      = Subalgebra.restrictScalars ℚ
          (Algebra.adjoin (MvPolynomial PUnit.{1} ℚ)
            ({(algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
                (MvPolynomial.X PUnit.unit))⁻¹} : Set (NoetherField ℚ PUnit.{1}))) := by
    rw [← adjoin_away_eq_adjoin_union_inv_pUnit_rat, Set.inv_singleton]
  have hle : pUnitGenericCarrier ≤ Subalgebra.restrictScalars ℚ
      (Algebra.adjoin (MvPolynomial PUnit.{1} ℚ)
        ({(algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
            (MvPolynomial.X PUnit.unit))⁻¹} : Set (NoetherField ℚ PUnit.{1}))) :=
    le_of_eq hEq
  have hRG : ∀ (g : PUnit.{1}) (r : ↥(pUnitGenericCarrier))
      (y : Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)),
      g • (r • y) = r • (g • y) := by
    intro g r y
    rw [Subsingleton.elim g 1, one_smul, one_smul]
  have hS0R : ∀ r : ↥(pUnitGenericCarrier),
      awayToFieldAlg (F := ℚ) (G := PUnit.{1})
          (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
          (MvPolynomial.X_ne_zero PUnit.unit)
          (algebraMap ↥(pUnitGenericCarrier)
            (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) r)
        = algebraMap ↥(pUnitGenericCarrier) (NoetherField ℚ PUnit.{1}) r := by
    intro r
    have h2 : awayAlgEquivAdjoin_pUnit_rat (awayAlgEquivAdjoin_pUnit_rat.symm r) = r :=
      awayAlgEquivAdjoin_pUnit_rat.apply_symm_apply r
    calc awayToFieldAlg (F := ℚ) (G := PUnit.{1})
          (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
          (MvPolynomial.X_ne_zero PUnit.unit)
          (algebraMap ↥(pUnitGenericCarrier)
            (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)) r)
        = awayToFieldAlg (F := ℚ) (G := PUnit.{1})
            (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)
            (MvPolynomial.X_ne_zero PUnit.unit)
            (awayAlgEquivAdjoin_pUnit_rat.symm r) := rfl
      _ = (awayAlgEquivAdjoin_pUnit_rat (awayAlgEquivAdjoin_pUnit_rat.symm r)
            : NoetherField ℚ PUnit.{1}) := rfl
      _ = (r : NoetherField ℚ PUnit.{1}) := by rw [h2]
      _ = algebraMap ↥(pUnitGenericCarrier) (NoetherField ℚ PUnit.{1}) r := rfl
  exact realizationPropertyFieldFinite_of_subalgebra (F := ℚ) (G := PUnit.{1})
    (S := pUnitGenericCarrier)
    (t := (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ))
    (MvPolynomial.X_ne_zero PUnit.unit)
    (fun g => by rw [smul_X_noether,
      congrArg MvPolynomial.X (Subsingleton.elim (g * PUnit.unit) PUnit.unit)])
    hle
    (smul_eq_self_of_mem_adjoin_of_fixed (F := ℚ) (G := PUnit.{1})
      (a := fun _ : Fin 1 => algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit))
      (s₀ := algebraMap (MvPolynomial PUnit.{1} ℚ) (NoetherField ℚ PUnit.{1})
        (MvPolynomial.X PUnit.unit))
      (fun g _ => by rw [smul_algebraMap_noether, smul_X_noether,
        congrArg MvPolynomial.X (Subsingleton.elim (g * PUnit.unit) PUnit.unit)])
      (fun g => by rw [smul_algebraMap_noether, smul_X_noether,
        congrArg MvPolynomial.X (Subsingleton.elim (g * PUnit.unit) PUnit.unit)]))
    (fun (g : PUnit.{1}) (p : MvPolynomial PUnit.{1} ℚ) => by
      have h1 : noetherRingHom ℚ PUnit.{1} g = 1 := by
        rw [Subsingleton.elim g 1, map_one]
      have key := congrArg
        (fun e : MvPolynomial PUnit.{1} ℚ ≃+* MvPolynomial PUnit.{1} ℚ => e p) h1
      exact (congrArg (algebraMap (MvPolynomial PUnit.{1} ℚ)
        (Localization.Away (MvPolynomial.X PUnit.unit : MvPolynomial PUnit.{1} ℚ)))
        key).symm)
    hRG (isGaloisWithGroup_away_adjoin_pUnit_rat hRG)
    (fun _ => finite_projective_away_adjoin_pUnit_rat) hS0R (inferInstance : Infinite ℚ)

#print axioms realizationPropertyFieldFinite_pUnit_rat_genericObject

end

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 两行残余归约（源侧 generic object 上的有限域档）** ✓✅：**不动域数据** `a` ✓（`L^G` 中 ✓）
＋ `s_0 ≠ 0` ✓ ＋ `[Infinite F]` ✓ ⟹ **存在** `T` ✓（及其三实例 ✓／`ht` ✓／不变化 ✓／`hle` ✓／`hRG` ✓），
使 **`δ` 双射** ✓ ＋ **`hProj`** ✓ ⟹
`RealizationPropertyFieldFinite F G ↥(noetherFixedCarrier F G a s_0) (Localization.Away T)` ✓。

**⚠ 与 §4.56 的强度序** ✓（**严格变短** ✓，**逐行** ✓）：§4.56 的假设表**十八槽** ✓
（**4 数据** ✓：`t` ✓／`ht` ✓／`ht_inv` ✓／`hinf` ✓；**7 具名行** ✓：`hact_map` ✓／`hRG` ✓／`hgal` ✓／
`hProj` ✓／`hS_0R` ✓／`hRQ` ✓／`hRGpoint` ✓；**7 实例** ✓：`[CommRing R]` ✓／`[Algebra R S']` ✓／
`[Algebra F R]` ✓／`[IsScalarTower F R S']` ✓／`[MulSemiringAction G S']` ✓／
`[Algebra R (NoetherField F G)]` ✓／`[IsScalarTower F R (NoetherField F G)]` ✓），
本件**只留两行** ✓（`δ` ✓／`hProj` ✓）——
其余**全部由构造供给** ✓（r171 ✓／r228--r231 ✓ ＋ §4.47 ✓／§4.62 ✓）。
**⚠ `hgal` 的去向** ✓：`IsGaloisWithGroup` **三款**中 ② **自动** ✓（`algebraMap_fixed_of_smulCommClass` ✓）、
① ＝ `faithfulSMul_away_of_noetherAdjoin` ✓（构造 ✓）⟹ **①② 不在假设表内** ✓，
**③（`δ` 双射）** ✓ 成为**唯一**输入 ✓（**＝ Galois 内容** ✓，与 r231 ✓ 的判据下调同款 ✓）。
**⚠ 外层输入** ✓：`hind` ✓／`hgen` ✓ **不出现** ✓（**如实** ✓：`RealizationPropertyFieldFinite` ＝ (c) 款 ✓，
**不含** (a) 款 ✓；(a) 款**另立** ✓ —— **下一件** ✓（r260 §I ✓，**无 `hgen` 形** ✓）✓）。
**🔴 不声称** ✗：**不**声称 `δ` 双射可证 ✗／**`hProj`** 可证 ✗（**两行皆开** ✗）；
**不**声称本件给出源形（**环档** ✓）见证 ✗（**须残余 ①** ✓）；**不**声称两条源陈述已证 ✗。
**⚠ 判别力（L43）** ✓：**变异件负例已实跑** ✓（`.abgv52-scratch/probe-r265f.lean` ✓ **rc≠0** ✓）——
**M2** ＝ 把 `Function.Bijective (deltaToEndRingHom _hRG) →` ✗ 换成 `True →` ✗（**证明体逐字照抄** ✓）
⟹ `hgal` **无从构造** ✗ ⟹ **编译失败** ✓；**M1** ＝ 同款把 `hProj` ✗ 换成 `True` ✗ ⟹
`realizationPropertyFieldFinite_of_subalgebra` ✓ 的 `hProj` **无从供给** ✗ ⟹ **编译失败** ✓。 -/
theorem exists_realizationPropertyFieldFinite_of_noetherFixedWiring
    {n : ℕ} {a : Fin n → NoetherInvariantField F G} {s₀ : NoetherInvariantField F G}
    (hs₀ : s₀ ≠ 0) (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) G _hRG →
        RealizationPropertyFieldFinite F G ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) := by
  classical
  have hs₀L : ((s₀ : NoetherInvariantField F G) : NoetherField F G) ≠ 0 :=
    fun h => hs₀ (Subtype.ext h)
  have ha_fix : ∀ (g : G) (i : Fin n),
      g • ((a i : NoetherInvariantField F G) : NoetherField F G)
        = ((a i : NoetherInvariantField F G) : NoetherField F G) :=
    fun g i => (a i).2 g
  have hs₀_fix : ∀ g : G,
      g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
        = ((s₀ : NoetherInvariantField F G) : NoetherField F G) :=
    fun g => s₀.2 g
  obtain ⟨T, hTne, hTinv, hTle⟩ := exists_invariant_t_of_noether (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) hs₀L
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) T hTne hTle
  let instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) :=
    inferInstance
  let instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away T) p)
        = algebraMap (MvPolynomial G F) (Localization.Away T) (g • p) :=
    fun g p => awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv g p
  have hS0R : ∀ r : ↥(noetherFixedCarrier F G a s₀),
      awayToFieldAlg (F := F) (G := G) T hTne
          (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) r)
        = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r :=
    fun r => hι r
  have hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
      (x : Localization.Away T), g • (r • x) = r • (g • x) :=
    smulCommClass_away_of_algHom (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G))
      ha_fix hs₀_fix T hTne hTinv ι hι
  have hSfix : ∀ (g : G) {x : NoetherField F G},
      x ∈ noetherFixedCarrier F G a s₀ → g • x = x :=
    smul_eq_self_of_mem_adjoin_of_fixed (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) ha_fix hs₀_fix
  refine ⟨T, hTne, hTinv, hTle, instA, hST, instM, hRG, ?_⟩
  intro hδ hProj
  have hgal : BTier.IsGaloisWithGroup ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away T) G hRG :=
    ⟨faithfulSMul_away_of_noetherAdjoin (F := F) (G := G) (T := T) hTne hTinv,
      fun g r => BTier.algebraMap_fixed_of_smulCommClass hRG g r, hδ⟩
  exact realizationPropertyFieldFinite_of_subalgebra (F := F) (G := G)
    (S := noetherFixedCarrier F G a s₀) (t := T) hTne hTinv hTle hSfix hact hRG hgal hProj
    hS0R hinf

#print axioms exists_realizationPropertyFieldFinite_of_noetherFixedWiring

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 三款齐备（源侧 generic object 上的有限档见证数据）** ✓✅：同一 ∃-包 ✓，唯结论取
**`IsGenericExtensionFieldFinite F G ↥S (Localization.Away T) hRG`** ✓（**(a)** ✓ ＋ **(b)** ✓ ＋ **(c)** ✓ 三款 ✓）——
即 **`GenericExtensionWitnessFieldFinite` ✓ 的 `isGeneric` 场** ✓（**源 `theorem-5-1` 的有限档孪生之输入** ✓）。
**⚠ 新增的 (a) 款** ✓（**r260 §I** ✓，**已落** ✓✅）：由 `hind` ✓（`L^G` 读法 ✓）经 **(甲) ①** ✓
（`algebraicIndependent_coe_iff_of_subalgebra` ✓）搬到 `L` ✓、由 `hs_0 ∈ F[a]` ✓ 经 **(甲) ②** ✓
（`mem_adjoin_coe_of_mem_adjoin` ✓）搬到 `L` ✓，再喂 **`exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul`** ✓
（**无 `hgen` 形** ✓，r260 ✓）⟹ `∃ w ≠ 0, ↥S ≃_F Localization.Away w` ✓（**取 `m := n`** ✓）。
**⚠ 内容** ✓（**如实** ✓）：**(c)** 款**不新证** ✗（**本件在 `exists_realizationPropertyFieldFinite_of_noetherFixedWiring` ✓ 的
∃-包上工作** ✓ —— **`obtain` 后原地消费** ✓，**与该件同假设表** ✓ ＋ `hind` ✓／`hs_0 ∈ F[a]` ✓ 两行新输入 ✓）。
**🔴 不声称** ✗：**不**声称 `δ` 双射 ✗／**`hProj`** ✗ 可证（**两行仍开** ✗）；
**不**声称 `hind` ✓（`L^G` 的代数无关族 ✓）无条件可得 ✗
（**源侧**由 `IsRationalOver F L^G` ✓ 经 r260 §E ✓ 供给 ✓；**其本身** ＝ Noether 问题 ✓，`C_{47}` 档**为假** ✓）；
**不**声称源 `theorem-5-1` ✓ 已证 ✗（**须残余 ①** ✓）。 -/
theorem exists_isGenericExtensionFieldFinite_of_noetherFixedWiring
    {n : ℕ} {a : Fin n → NoetherInvariantField F G} {s₀ : NoetherInvariantField F G}
    (hind : AlgebraicIndependent F a)
    (hs₀ : s₀ ≠ 0) (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a))
    (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) G _hRG →
        IsGenericExtensionFieldFinite F G ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) _hRG := by
  classical
  have hs₀L : ((s₀ : NoetherInvariantField F G) : NoetherField F G) ≠ 0 :=
    fun h => hs₀ (Subtype.ext h)
  have hindL : AlgebraicIndependent F
      (fun i => ((a i : NoetherInvariantField F G) : NoetherField F G)) :=
    (algebraicIndependent_coe_iff_of_subalgebra
      (FixedPoints.intermediateField (F := F) (E := NoetherField F G) G).toSubalgebra a).mp hind
  have hs₀_memL : ((s₀ : NoetherInvariantField F G) : NoetherField F G)
      ∈ Algebra.adjoin F
        (Set.range (fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))) :=
    mem_adjoin_coe_of_mem_adjoin
      (FixedPoints.intermediateField (F := F) (E := NoetherField F G) G).toSubalgebra hs₀_mem
  have ha : ∃ (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
      Nonempty (↥(noetherFixedCarrier F G a s₀) ≃ₐ[F] Localization.Away w) :=
    exists_algEquiv_localizationAway_of_adjoin_union_inv_of_faithfulSMul
      (F := F) (K := NoetherField F G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) hindL hs₀L hs₀_memL
  have ha_fix : ∀ (g : G) (i : Fin n),
      g • ((a i : NoetherInvariantField F G) : NoetherField F G)
        = ((a i : NoetherInvariantField F G) : NoetherField F G) :=
    fun g i => (a i).2 g
  have hs₀_fix : ∀ g : G,
      g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
        = ((s₀ : NoetherInvariantField F G) : NoetherField F G) :=
    fun g => s₀.2 g
  obtain ⟨T, hTne, hTinv, hTle⟩ := exists_invariant_t_of_noether (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) hs₀L
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) T hTne hTle
  let instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) :=
    inferInstance
  let instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away T) p)
        = algebraMap (MvPolynomial G F) (Localization.Away T) (g • p) :=
    fun g p => awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv g p
  have hS0R : ∀ r : ↥(noetherFixedCarrier F G a s₀),
      awayToFieldAlg (F := F) (G := G) T hTne
          (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) r)
        = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r :=
    fun r => hι r
  have hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
      (x : Localization.Away T), g • (r • x) = r • (g • x) :=
    smulCommClass_away_of_algHom (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G))
      ha_fix hs₀_fix T hTne hTinv ι hι
  have hSfix : ∀ (g : G) {x : NoetherField F G},
      x ∈ noetherFixedCarrier F G a s₀ → g • x = x :=
    smul_eq_self_of_mem_adjoin_of_fixed (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) ha_fix hs₀_fix
  refine ⟨T, hTne, hTinv, hTle, instA, hST, instM, hRG, ?_⟩
  intro hδ hProj
  have hgal : BTier.IsGaloisWithGroup ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away T) G hRG :=
    ⟨faithfulSMul_away_of_noetherAdjoin (F := F) (G := G) (T := T) hTne hTinv,
      fun g r => BTier.algebraMap_fixed_of_smulCommClass hRG g r, hδ⟩
  exact ⟨⟨n, ha⟩, hgal,
    realizationPropertyFieldFinite_of_subalgebra (F := F) (G := G)
      (S := noetherFixedCarrier F G a s₀) (t := T) hTne hTinv hTle hSfix hact hRG hgal hProj
      hS0R hinf⟩

#print axioms exists_isGenericExtensionFieldFinite_of_noetherFixedWiring

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 源形见证（源侧 generic object ＋ 残余 ①）** ✓✅：在上面 ∃-包内把 `IsGenericExtensionFieldFinite` ✓ 经
**残余 ①** ✓（`nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge` ✓）搬成**源形** ✓
`Nonempty (GenericExtensionWitness F G)` ✓。
**⚠ 意义** ✓（**对 §J 的归约的严格加强** ✓，**逐条** ✓）：§J 的 `theorem51Statement_of_noetherWiringResidualFixed_and_ringBridge` ✓
以 **残余 ④**（`NoetherWiringResidualFixed` ✓，**21 行** ✓）为假设 ✓；本件**把该表压到** ✓
**数据两行** ✓（`a` ✓／`hind` ✓；`s_0` 两行可由 `s_0 := 1` ✓ 免去 ✓）＋ **端点两行** ✓（`δ` ✓／`hProj` ✓）
＋ **残余 ①** ✓ —— 因为 **§J 表内的**全部机器行 ✓（`t` ✓／三实例 ✓／`hle` ✓／`hact_map` ✓／`hRG` ✓／`hS_0R` ✓）
**与 (a) 款** ✓ **已由 r171 ✓／r228--r231 ✓／r260 §I** ✓ **构造供给** ✓。
**⚠ 与 `Theorem51Statement` 的**一步之差** ✗**（**如实** ✓）：本件结论是 **`Nonempty (GenericExtensionWitness F G)`** ✓
（**与 `L` 无关** ✓，见 `theorem51Statement_of_witness` ✓）；要得 `Theorem51Statement F G` ✓ 尚须把
**`\exists a,\ \mathrm{AlgebraicIndependent}\ F\ a`**（`L^G` 中 ✓）**从源假设 `IsRationalOver F L^G` ✓ 抽出** ✓
—— **而**该源假设是**给定 `L` 的** ✗，其不动域**不是**本件的 `\mathrm{NoetherInvariantField}\ F\ G` ✗
（**故这一步不是同一条** ✗，**登记为本轮余项** ✗，r261 ✓ §P.5 ✓ 的等价式**只对 Noether 自身的 `L^G`** ✓）。
**🔴 不声称** ✗：**不**声称 `\exists a,\ \mathrm{AlgebraicIndependent}\ F\ a`（`L^G` 中 ✓）**无条件可证** ✗
（**启发式** ✓：`\mathrm{trdeg}_F L^G = |G|` ✓ ⟹ `G` 非平凡时存在 ✓；**库内未落** ✗）；
**不**声称 `δ` ✓／`hProj` ✓ 可证 ✗；**不**声称残余 ① 可去 ✗；**不**声称两条源陈述已证 ✗。 -/
theorem exists_genericExtensionWitness_of_noetherFixedWiring_and_ringBridge
    (hb : RealizationRingTierBridge F G)
    {n : ℕ} {a : Fin n → NoetherInvariantField F G} {s₀ : NoetherInvariantField F G}
    (hind : AlgebraicIndependent F a) (hs₀ : s₀ ≠ 0)
    (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a)) (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) G _hRG →
        Nonempty (GenericExtensionWitness F G) := by
  obtain ⟨T, hTne, hTinv, hle, instA, instT, instM, hRG, hbody⟩ :=
    exists_isGenericExtensionFieldFinite_of_noetherFixedWiring (F := F) (G := G)
      (a := a) (s₀ := s₀) hind hs₀ hs₀_mem hinf
  refine ⟨T, hTne, hTinv, hle, instA, instT, instM, hRG, ?_⟩
  intro hδ hProj
  have hisg := hbody hδ hProj
  exact nonempty_genericExtensionWitness_of_fieldFinite_and_ringBridge hb
    ⟨{ R := ↥(noetherFixedCarrier F G a s₀), S := Localization.Away T, hRG := hRG,
       isGeneric := hisg }⟩

#print axioms exists_genericExtensionWitness_of_noetherFixedWiring_and_ringBridge

end FiniteFieldTierGenericObject

section Thm21ClausesFromFixedWiring

variable {A : Type} [Group A] [Fintype A] [DecidableEq A] {F : Type} [Field F]

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 残余 ③（源 `theorem-2-1` 侧）的同一收口** ✓✅：同一 ∃-包 ✓，唯结论取
**`Thm21ClausesResidual A F`** ✓（本件 §C ✓ 的具名残余 ✓：「**源 §2 的构造**」✓）——
即 `Theorem21Statement` ✓ 的归约所需的那一项 ✓（`theorem21Statement_of_clausesResidual_and_ringBridge` ✓ ＋ 残余 ① ⟹ 源陈述 ✓）。
**⚠ 意义** ✓（**正是任务书所指的**共享输入** ✓**）：**残余 ③** ✓（`Thm21ClausesResidual` ✓，**源 §2 的构造** ✗，
**库内此前无任何构造件** ✗）**与残余 ④** ✓（**Noether 侧** ✓）**现由同一件供给** ✓✅ ——
两者的**残留同为两行** ✓（`δ` ✓／`hProj` ✓）＋ **一行数据** ✓（`\exists a,\ \mathrm{AlgebraicIndependent}\ F\ a`，`L^G` 中 ✓）
⟹ **源侧 generic object 的有限档三款是两条源陈述的**公共输入** ✓**（**本条即其机器读数** ✓）。
**⚠ 证明** ✓（**一步** ✓，**不新造** ✗）：`obtain` ③ 件 ✓ 的 ∃-包后**重新打包** ✓ 为
`Thm21ClausesResidual` ✓ 的 ∃-形 ✓（**三款** ✓ 由 `IsGenericExtensionFieldFinite` ✓ 的**投影** ✓ 给出 ✓，
**实例由 ∃-绑定就地供给** ✓）。
**⚠ 与 `SaltmanCondition` 的关系** ✓（**如实** ✓）：本件**不消费** `SaltmanCondition A F` ✓ ——
残余 ③ 是**蕴含式** ✓，本件对**任意** `A`／`F`（`[DecidableEq A]` ✓）给出 `SaltmanCondition → (⋯)` ✓
（**故 `Theorem21Statement` 的该行**不依赖 Saltman 条件** ✓**）——
**⚠ 这不使源陈述已证** ✗（**残余 ①** ✓ 仍开 ✓）。
**⚠ 数据行** ✓：`hind` ✓／`hs_0` ✓／`hs_0 \in F[a]` ✓（`s_0 := 1` ✓ 可免后两行 ✓）；`\exists a` 同 ③ 件 ✓。
**🔴 不声称** ✗：**不**声称 `δ` 双射 ✗／**`hProj`** ✗ 可证 ✗；**不**声称残余 ① 已证 ✗；
**不**声称 `Theorem21Statement` ✓ 已证 ✗。 -/
theorem exists_thm21ClausesResidual_of_noetherFixedWiring
    {n : ℕ} {a : Fin n → NoetherInvariantField F A} {s₀ : NoetherInvariantField F A}
    (hind : AlgebraicIndependent F a) (hs₀ : s₀ ≠ 0)
    (hs₀_mem : s₀ ∈ Algebra.adjoin F (Set.range a)) (hinf : Infinite F) :
    ∃ (T : MvPolynomial A F) (_hT : T ≠ 0) (_hTinv : ∀ g : A, g • T = T)
      (instA : Algebra ↥(noetherFixedCarrier F A a s₀) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F A a s₀) (Localization.Away T))
      (instM : MulSemiringAction A (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : A) (r : ↥(noetherFixedCarrier F A a s₀))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F A a s₀)
          (Localization.Away T) A _hRG →
        Thm21ClausesResidual A F := by
  obtain ⟨T, hTne, hTinv, hle, instA, instT, instM, hRG, hbody⟩ :=
    exists_isGenericExtensionFieldFinite_of_noetherFixedWiring (F := F) (G := A)
      (a := a) (s₀ := s₀) hind hs₀ hs₀_mem hinf
  refine ⟨T, hTne, hTinv, instA, instT, instM, hRG, ?_⟩
  intro hδ hProj _hC
  have hg := hbody hδ hProj
  exact ⟨↥(noetherFixedCarrier F A a s₀), Localization.Away T,
    inferInstance, inferInstance, inferInstance, instA, inferInstance, instT, instM,
    hRG, ⟨hg.1, hg.2.1, hg.2.2⟩⟩

#print axioms exists_thm21ClausesResidual_of_noetherFixedWiring

end Thm21ClausesFromFixedWiring

section FiniteFieldTierGenericObjectTail

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

set_option maxHeartbeats 1000000 in
/-- **两行残余归约（`s_0 := 1` 档）** ✓✅：**`s_0 ≠ 0` 假设亦被消去** ✓（`s_0 := 1` ✓）⟹
在**任意**不动域数据族 `a` ✓ 与 `[Infinite F]` ✓ 下同一个 ∃-包成立 ✓。
**⚠ 意义** ✓：本件显示 `s_0` 假设**不是实质输入** ✗（其**唯一用点** ＝ `exists_invariant_t_of_noether` ✓
的 `hs_0` ✓）—— **⚠ 但 `a` 不可去** ✗（它是**载体的一部分** ✓：`noetherFixedCarrier F G a s_0` ✓）。
**⚠ 判别力（L43）** ✓：**变异件负例已实跑** ✓ —— 去掉 `[Infinite F]` ✗ ⟹
`realizationPropertyFieldFinite_of_subalgebra` ✓ 的 `hinf` ✓ **无从供给** ✗ ⟹ **编译失败** ✓
（`.abgv52-scratch/probe-r265f.lean` ✓ **M5** ✓ **rc≠0** ✓）。 -/
theorem exists_realizationPropertyFieldFinite_of_noetherFixedWiring_one
    {n : ℕ} (a : Fin n → NoetherInvariantField F G) (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : noetherFixedCarrier F G a 1 ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(noetherFixedCarrier F G a 1) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F G a 1) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a 1))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a 1)
          (Localization.Away T) G _hRG →
        RealizationPropertyFieldFinite F G ↥(noetherFixedCarrier F G a 1)
          (Localization.Away T) :=
  exists_realizationPropertyFieldFinite_of_noetherFixedWiring (F := F) (G := G)
    (a := a) (s₀ := 1) one_ne_zero hinf

#print axioms exists_realizationPropertyFieldFinite_of_noetherFixedWiring_one

/-- **登记（r265 总账，逐条如实）** ✓：**源侧 generic object 上的有限域档** ——
**已落** ✓✅：**(甲)** 谓词级**载体具体化件** ✓（`SaltGeneric` §4.62 ✓，**假设表减四槽** ✓）；
**(乙)** **两行残余归约** ✓（`exists_realizationPropertyFieldFinite_of_noetherFixedWiring` ✓ ——
**(c) 款**：十八槽 ⟹ **两行** ✓：`δ` 双射 ✓／`hProj` ✓；`s_0 := 1` 档再消 `hs_0` ✓）；
**(丙)** **三款齐备 ＋ 源形** ✓✅（`exists_isGenericExtensionFieldFinite_of_noetherFixedWiring` ✓ ——
**(a)** ✓（**r260 §I** ✓，**两行数据** ✓）＋ **(b)** ✓（由 `δ` ✓）＋ **(c)** ✓；
`exists_genericExtensionWitness_of_noetherFixedWiring_and_ringBridge` ✓ —— **＋残余 ① ⟹ 源形见证** ✓，
**对 §J 归约的严格加强** ✓：**残余 ④ 的 21 行 ⟹ 数据两行 ＋ 端点两行** ✓）；
**(丁)** **两源陈述的**公共输入** ✓✅（`exists_thm21ClausesResidual_of_noetherFixedWiring` ✓ ——
残余 ③ ✓（`Thm21ClausesResidual` ✓）与残余 ④ ✓ **同由两行 ＋ 一行数据供给** ✓，
**故任务书所指的**共享**已在库内成机器读数** ✓）；
**(戊)** **`ℚ`／`PUnit` 档无条件实例** ✓✅（`realizationPropertyFieldFinite_pUnit_rat_genericObject` ✓，
**非退化载体** ✓，**表内每行皆落地** ✓ —— 残余表的**正例对照** ✓）。
**未落** ✗（**逐条，含理由** ✓）：**(i)** **`δ` 双射** ✗（一般 `G` 档 —— **交叉相积同构** ✓，
源 `proposition-0-5`(b) ✓＋(c) ✓（**域档** ✓，印 254 ✓）的**环档版** ✗，**库内与 mathlib 均未落** ✗）；
**(ii)** **`hProj`** ✗（源 `proposition-0-2(a)` ✓／`[CHR68]` p. 13 ✓ —— **不在 `raw/`** ✗；
其**任意档现形已机器反驳** ✗（`galoisProjectiveHyp_refuted` ✓）⟹ 须按**预期用例**读 ✓）；
**(iii)** **`\exists a,\ \mathrm{AlgebraicIndependent}\ F\ a`（`L^G` 中 ✓）的无条件形** ✗ ——
**(a) 款机器已落** ✓✅（r260 §I ✓），但其**输入**（`hind` ✓／`s_0 ∈ F[a]` ✓）**由源假设
`IsRationalOver F L^G` ✓ 供给** ✓（r260 §E ✓），而该源假设本身 ＝ **Noether 问题** ✓
（**`C_{47}` 档为假** ✓，源 `remark` ✓ 印 275 ✓；**本件未形式化该外部结果** ✗）⟹
**`G` 非平凡档的 `hind` 无条件可得性未落** ✗（**启发式** ✓：`\mathrm{trdeg}_F L^G = |G|` ✓；**库内未落** ✗）；
**(iv)** **残余 ①**（`RealizationRingTierBridge` ✓，**环档桥** ✗）**仍开** ✓、**两条源陈述共享** ✓；
**(v)** 两条源陈述 ✓（`Theorem51Statement` ✓／`Theorem21Statement` ✓）**仍未证** ✗
（**⚠ `Theorem21Statement` 的账** ✓：其残余 ③ ✓ 已由 (丁) 供给 ✓、残余 ① ✓ 仍开 ✓ ⟹
**该侧**只差残余 ①** ＋ 两行 ＋ 一行数据** ✓；**⚠ 与 `Theorem51Statement` 的**最后一步** ✗**：源陈述的 `IsRationalOver F L^G` ✓ 是**给定 `L` 的** ✓，
其不动域**不是** `\mathrm{NoetherInvariantField}\ F\ G` ✗ ⟹ **两处数据不同源** ✗，
**本件不跨这一步** ✗）；
**(vi)** **§4.69 的非退化档反驳** ✗（`(F,F)` 档**已机器判定为假** ✗ ⟹ 该路线**死** ✗；
**须**在**非退化**载体上取 `RealizationProperty` 的**反例** ✓ —— **本轮未落** ✗，
**本件不给出桥的无条件反驳** ✗）。
**⚠ 分类（规则 17）** ✓：本轮的缺口**不是**观测数据 ✗，而是**证明义务** ✓
（(i)／(ii) 的**数学内容** ✓ ＋ (iii) 的**可算对象** ✓ —— **(iii) 属「可算但未算」** ✓，
**不得**登记为材料阻断 ✗）。
**🔴 不声称** ✗：**不**声称 (i)--(vi) 任一已落 ✗；**不**声称两条源陈述已证 ✗；
**不**声称残余 ① 可去 ✗；**不**声称桥已驳 ✗。 -/
theorem finiteFieldTier_genericObject_residuals_registered : True := trivial

#print axioms finiteFieldTier_genericObject_residuals_registered

end FiniteFieldTierGenericObjectTail

/-! ### 4.71 两行残余的**再归约**：`δ` **单射已落** ＋ `hProj` 换成**两条模论行**（第 266 轮）

**⚠ 起点** ✓（承 §4.70 ✓）：源侧 generic object 上的**有限域档**（`RealizationPropertyFieldFinite F G ↥S (Localization.Away T)` ✓）
此前压到**两行** ✓：`δ` 双射 ✓（§4.70 ✓）与 `hProj` ✓。本轮**不证**这两行 ✗，而落**两件**：
**① 第 ① 行拆半** ✓✅（`δ` **单射已落** ✓，**只剩满射** ✓）；**② 第 ② 行换成两条模论行** ✓✅
（`R[G]`-**有限** ✓／`R[G]`-**投射** ✓，**模结构由构造供给** ✓）。

**⚠ 本轮断指（五件** ✓**；探针 `.abgv52-scratch/probe-r266f.lean` ✓ **rc=0** ✓、**零警告** ✓）**：
**①** `injective_deltaToEndRingHom_away_of_noetherAdjoin` ✓✅ —— **第 ① 行的「单射」一半在源侧 generic object 上落地** ✓：
由 **Dedekind 型判据** ✓（`GaloisAlgebra` §266 ✓）＋ **忠实性由构造** ✓（`faithfulSMul_away_of_noetherAdjoin` ✓）
＋ **无零因子由构造** ✓（`IsLocalization.Away.isDomain` ✓，用 `T ≠ 0` ✓）⟹ **不再需要外部输入** ✓；
**②** `exists_realizationPropertyFieldFinite_of_noetherFixedWiring_deltaSurj_and_rows` ✓✅ ——
**同一 ∃-包** ✓（`T` ✓／三实例 ✓／`hRG` ✓ 全由构造供给 ✓），唯**假设表换成三行** ✓：
**`δ` 满射** ✓ ＋ **`R[G]`-有限** ✓ ＋ **`R[G]`-投射** ✓（**`hProj` 不再出现** ✓）；
**③** `galoisProjectiveHyp_regularAction` ✓✅ ＋ **④** `rows_regularAction` ✓✅ —— **非平凡 `G` 档** ✓
（分裂代数 `K^G` ✓，r264 ✓ 的 `isGaloisWithGroup_regularAction` ✓）：**两行同时为真** ✓
（`hProj` ⟸ `K^G` 对 `K` **有限自由** ✓；`δ` 双射 ⟸ r264 ✓）⟹ **旧行集可满足** ✓（L1 ✓，
**且非退化** ✓：`|G| ≥ 2` 时 `K^G ≇ K` ✓，r264 ✓ —— 与 `(F,F)` 退化作别 ✓；
**⚠ 载体非接线对** ✗，新表非空性口径见下表 ✓）；
**⑤** `injective_deltaToEndRingHom_mvPolynomial_probe` ✓✅ ＋ `card_multiplicative_zmod_two` ✓ —— **Dedekind 判据的正例对照** ✓
（`G = Multiplicative (ZMod 2)` ✓，`|G| = 2` ✓，`S = MvPolynomial G ℚ` ✓ **非域退化** ✗）。

**⚠ 残余表（本轮实数** ✓**，逐行）**：

| 行 | 状态 | 根据 |
|---|---|---|
| `T` ✓／`t ≠ 0` ✓／`g • t = t` ✓／`hle` ✓／三实例 ✓／`hact_map` ✓／`hRG` ✓／`hS_0R` ✓／`hS_fix` ✓ | **已落** ✓✅（**构造** ✓） | §4.70 ✓（r171 ✓／r228--r231 ✓／r260 ✓） |
| **(1a) `δ` 单射** ✓ | **已落** ✓✅（**本轮** ✓） | `injective_deltaToEndRingHom_away_of_noetherAdjoin` ✓（**＋** 通用判据 `injective_deltaToEndRingHom_of_noZeroDivisors` ✓） |
| **(1b) `δ` 满射** ✓ | **仍开** ✗ | **源侧不缺** ✓：源 `proposition-0-5` **(b)** ✓（自同构**代数无关** ✓；印 254 ✓）＋ **(c)** ✓（**正规基** ✓；印 254 ✓，据 `[Jac74]` p. 283 ✓ ＋「the same arguments that apply when `L` is a field」✓）—— 二者**均在 §0 有证** ✓（引文与页码核见 `SaltGeneric` §4.53 ✓）；**⚠ 但**源 (b)／(c) 在 **`R = K` 域档** ✓（「Turning to the case `R = K` is a field」✓），而接线档 `R` 是**函数域的子代数** ✗ ⟹ 需其**环档版**（＝ 库内所记「CHR 代数版」✗，**未落** ✗）；**库内桥缺口已登记** ✓（mathlib 正规基定理的指标形为 `L ≃ₐ[K] L` ✗ 而非**抽象 `G`** ✗；CHR 不动环 `GaloisFixedSubringHyp` ✓ 未证 ✗ —— `SaltGeneric` §4.53 ✓）⟹ **(1b) 属证明义务** ✓（**非**材料阻断 ✗） |
| **(2a) `R[G]`-有限** ✓ | **仍开** ✗ | 源 `proposition-0-2(a)` ✓／`[CHR68]` p. 13 ✓（**不在 `raw/`** ✗，§47／§52 ✓） |
| **(2b) `R[G]`-投射** ✓ | **仍开** ✗ | 同上 ✓ |
| **`hProj`** ✓（**旧第 ② 行** ✓） | **已消** ✓✅（**换为 (2a)＋(2b)** ✓） | `galoisProjectiveHyp_of_monoidAlgebraRows` ✓（`GaloisAlgebra` §266 ✓）＋ `hinj` **由构造** ✓（`faithfulSMul_subalgebra_away_of_noetherAdjoin` ✓）＋ 模结构／塔式**由构造** ✓ |
| **非空性（L1）** ✓ | **已落** ✓✅（**两处，口径分列** ✓） | **(i)** **再归约件的四输入** ✓：`galoisProjectiveHyp_rows_probe` ✓（`ℚ`／`PUnit`／正则模 ✓ —— `GaloisAlgebra` §266 ✓；**⚠ 退化档** ✗）；**(ii)** **旧两行**在**非平凡 `G`** 档**同真** ✓：`rows_regularAction` ✓（分裂代数 `K^G` ✓，r264 ✓；**⚠ 载体非接线对** ✗）；**⚠ 如实** ✓：**新表 (2a)／(2b) 两行本身**（对 `R[G]` ✓、载体 ＝ `Localization.Away T` ✓）**未作非空性机检** ✗ |
| **残余 ①**（环档桥 ✓） | **仍开** ✗ | 只影响**源形** ✓（§4.70 ✓）；**(c) 款与本表无关** ✓ |
| `hind` ✓／`s_0 ∈ F[a]` ✓（**仅 (a) 款** ✓） | **已落**（**条件** ✓） | §4.70 ✓（**源假设 `IsRationalOver`** ✓） |

**⚠ 与 §4.70 的强度序** ✓（**逐行** ✓）：§4.70 的两行 ＝ {`δ` 双射 ✓，`hProj` ✓}；
本表 ＝ {`δ` 满射 ✓，`R[G]`-有限 ✓，`R[G]`-投射 ✓} —— ① **第 ① 行的重数减半** ✓（**单射已落** ✓）；
② **`hProj` 的输入不再含 `hgal`** ✓（`hProj` ✓ 原为「`IsGaloisWithGroup ⟹ …`」✓ 的**条件**命题 ✓，
**其无限制形已被机器反驳** ✗（`galoisProjectiveHyp_refuted` ✓，r234 ✓）⟹ 换成**两条无条件模论行** ✓
＝ **口径下调** ✓，与 r255／r257 ✓ 同款 ✓）；③ **模结构与塔式由构造供给** ✓（**不**作假设 ✗）。

**⚠ 强度序（如实** ✓**，勿读作「同两行换说法」✗）**：**(甲) 真减一** ✓ —— 第 ① 行**双射 ⟹ 满射** ✓
（**单射已落** ✓）；**(乙) 逐行强度** ✓ —— `R[G]`-投射 ✓ **⟹** `R`-投射 ✓
（`projective_of_projective_monoidAlgebra` ✓，r257 ✓）、`R[G]`-有限 ✓ **⟹** `R`-有限 ✓
（`Module.Finite.trans` ✓）⟹ **本表三行足以供给 `hProj` 的结论款** ✓（机检 ✓：
`galoisProjectiveHyp_of_monoidAlgebraRows` ✓）；**(丙) 反向不成立** ✗（`R`-投射 ⇏ `R[G]`-投射 ✗）
⟹ **本表第 (2) 两行强于 `hProj` 的结论款** ✗ —— **故本轮的增益不在「更强」** ✓，而在
**①** 把**条件**命题（无限制形已假 ✗）换成**无条件**行 ✓、**②** 把**源自己的**输入
（源 `proposition-0-2(a)` ✓／`[CHR68]` p. 13 ✓）**具名化** ✓、**③** 把三项工艺侧条件
（`R[G]`-模结构 ✓／塔式 ✓／`algebraMap` 单射 ✓）**由构造消去** ✓。

**⚠ 工艺读数（本轮两条** ✓**；详见 `GaloisAlgebra` §266 ✓）**：**①** `R[G]`-模结构**须构造** ✗
（mathlib 无该实例 ✗）；**②** `letI` 链＋`R[G]` 载荷的语句**可用** ✓（**无** r263／r264 的实例二义 ✗ ——
**因**模结构是**构造项** ✓ 而非 ∃-绑定 ✓，故 `Module.Finite (MonoidAlgebra ↥S G) (Localization.Away T)` ✓
的实例槽由 `letI` **唯一确定** ✓）。

**🔴 不声称** ✗：**不**声称 `δ` **满射**可证 ✗；**不**声称 (2a)／(2b) 可证 ✗（其数学内容 ＝ 源
`proposition-0-2(a)` ✓，**`raw/` 内无供给** ✗）；**不**声称 (1b) 的**环档版**已在库内接通 ✗
（其缺口（正规基的抽象 `G` 形 ✓／CHR 不动环 ✓）已在 `SaltGeneric` §4.53 ✓ 登记 ✓）；**不**声称源 `theorem-5-1` ✓／`theorem-2-1` ✓ 已证 ✗；**不**声称残余 ① 可去 ✗。
**⚠ 分类（规则 17）** ✓：本表的**未落**项 ＝ `δ` 满射 ✓／(2a) ✓／(2b) ✓ —— **皆证明义务** ✓
（**非**观测数据 ✗、**非**「可算未算」✗）；**无**材料阻断登记 ✓。
**⚠ 判别力（L43）** ✓：**变异件负例已实跑** ✓（`.abgv52-scratch/probe-r266g.lean` ✓ **rc≠0** ✓）——
**M7** ＝ 把再归约件的 `Module.Finite (MonoidAlgebra R G) S →` ✗ 换成 `True →` ✗ ⟹ `hProj` **无从供给** ✗
⟹ **编译失败** ✓；**M8** ＝ 同款把 `Module.Projective …` ✗ 换成 `True` ✗ ⟹ **编译失败** ✓；
**M9** ＝ **删去** `δ` 单射件的 `[NoZeroDivisors S]` ✗ ⟹ `mul_ne_zero` ✓ **无从供给** ✗ ⟹ **编译失败** ✓；
**M11** ＝ **删去** `[FaithfulSMul G S]` ✗ ⟹ 分离元 `t₀` **无从构造** ✗ ⟹ **编译失败** ✓。 -/

section NoetherFixedWiringReduction

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- **第 ① 行的「单射」一半（源侧 generic object 档）** ✓✅（**第 266 轮** ✓）：
`S = Localization.Away T` ✓（`T ≠ 0` ✓ 且 `G`-不变 ✓）上，**无零因子由构造** ✓
（`IsLocalization.Away.isDomain` ✓）、**忠实性**作**显式输入** ✓（调用点由
`faithfulSMul_away_of_noetherAdjoin` ✓ 供给 ✓）⟹ **`δ` 单射** ✓。
**⚠ 机制** ✓：Dedekind 型判据 ✓（`GaloisAlgebra` §266 ✓）＋ 上述两款 ✓，**不重证** ✗。
**🔴 不声称** ✗：**不**声称 `δ` **满射** ✗；**不**声称**一般档**（无 `T` 不变性 ✗／无 `T ≠ 0` ✗）可用 ✗。 -/
theorem injective_deltaToEndRingHom_away_of_noetherAdjoin {T : MvPolynomial G F} (hT : T ≠ 0)
    {S : Type} [CommRing S] [Algebra F S] [Algebra S (Localization.Away T)]
    [MulSemiringAction G (Localization.Away T)] [IsScalarTower F S (Localization.Away T)]
    (hfaith : FaithfulSMul G (Localization.Away T))
    (hRG : ∀ (g : G) (r : S) (x : Localization.Away T), g • (r • x) = r • (g • x)) :
    Function.Injective (BTier.deltaToEndRingHom hRG) := by
  let _instDom : IsDomain (Localization.Away T) :=
    IsLocalization.Away.isDomain (S := Localization.Away T) hT
  exact BTier.injective_deltaToEndRingHom_of_noZeroDivisors (R := S) hRG

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 再归约（源侧 generic object 上的有限域档）** ✓✅：**同一 ∃-包** ✓（`T` ✓／三实例 ✓／
`hRG` ✓ 全由构造供给 ✓），唯**假设表取三行** ✓ —— **不再含 `hProj`** ✗：
**`δ` 满射** ✓ ＋ **`R[G]`-有限** ✓ ＋ **`R[G]`-投射** ✓ ⟹
`RealizationPropertyFieldFinite F G ↥(noetherFixedCarrier F G a s₀) (Localization.Away T)` ✓。
**⚠ 逐项口径** ✓：
**(1a) `δ` 单射** ✓ **由构造** ✓（`injective_deltaToEndRingHom_away_of_noetherAdjoin` ✓：
忠实性 ✓ ＋ 无零因子 ✓ 皆构造 ✓）；**`algebraMap` 单射** ✓ **由构造** ✓
（`faithfulSMul_subalgebra_away_of_noetherAdjoin` ✓ ＋ `faithfulSMul_iff_algebraMap_injective` ✓）；
**`R[G]`-模结构** ✓ 与**塔式** ✓ **由构造** ✓（`monoidAlgebraModuleOfMulSemiringAction` ✓／
`monoidAlgebraModule_isScalarTower` ✓ —— `GaloisAlgebra` §266 ✓）；
**(2) `hProj`** ✓ 由 `galoisProjectiveHyp_of_monoidAlgebraRows` ✓ 从**三行**（含 (1a)）**导出** ✓。
**⚠ 与 §4.70 的对照** ✓：§4.70 的假设表 ＝ {`δ` 双射 ✓，`hProj` ✓}；本件 ＝ {`δ` 满射 ✓，
`R[G]`-有限 ✓，`R[G]`-投射 ✓} —— **`hProj` 已消** ✓、**第 ① 行只剩一半** ✓（见节头强度序 ✓）。
**🔴 不声称** ✗：**不**声称三行**已证** ✗；**不**声称源陈述已证 ✗；**不**声称残余 ① 可去 ✗。 -/
theorem exists_realizationPropertyFieldFinite_of_noetherFixedWiring_deltaSurj_and_rows
    {n : ℕ} {a : Fin n → NoetherInvariantField F G} {s₀ : NoetherInvariantField F G}
    (hs₀ : s₀ ≠ 0) (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hle : noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        letI := BTier.monoidAlgebraModuleOfMulSemiringAction
          (R := ↥(noetherFixedCarrier F G a s₀)) (G := G) _hRG
        letI := BTier.monoidAlgebraModule_isScalarTower
          (R := ↥(noetherFixedCarrier F G a s₀)) (G := G) _hRG
        Function.Surjective (BTier.deltaToEndRingHom _hRG) →
        Module.Finite (MonoidAlgebra ↥(noetherFixedCarrier F G a s₀) G) (Localization.Away T) →
        Module.Projective (MonoidAlgebra ↥(noetherFixedCarrier F G a s₀) G) (Localization.Away T) →
        RealizationPropertyFieldFinite F G ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) := by
  classical
  have hs₀L : ((s₀ : NoetherInvariantField F G) : NoetherField F G) ≠ 0 :=
    fun h => hs₀ (Subtype.ext h)
  have ha_fix : ∀ (g : G) (i : Fin n),
      g • ((a i : NoetherInvariantField F G) : NoetherField F G)
        = ((a i : NoetherInvariantField F G) : NoetherField F G) :=
    fun g i => (a i).2 g
  have hs₀_fix : ∀ g : G,
      g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
        = ((s₀ : NoetherInvariantField F G) : NoetherField F G) :=
    fun g => s₀.2 g
  obtain ⟨T, hTne, hTinv, hTle⟩ := exists_invariant_t_of_noether (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) hs₀L
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) T hTne hTle
  let instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) :=
    inferInstance
  let instM : MulSemiringAction G (Localization.Away T) :=
    awayMulSemiringAction (F := F) (G := G) (t := T) hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away T) p)
        = algebraMap (MvPolynomial G F) (Localization.Away T) (g • p) :=
    fun g p => awayRingHom_algebraMap (F := F) (G := G) (t := T) hTinv g p
  have hS0R : ∀ r : ↥(noetherFixedCarrier F G a s₀),
      awayToFieldAlg (F := F) (G := G) T hTne
          (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away T) r)
        = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r :=
    fun r => hι r
  have hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
      (x : Localization.Away T), g • (r • x) = r • (g • x) :=
    smulCommClass_away_of_algHom (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G))
      ha_fix hs₀_fix T hTne hTinv ι hι
  have hSfix : ∀ (g : G) {x : NoetherField F G},
      x ∈ noetherFixedCarrier F G a s₀ → g • x = x :=
    smul_eq_self_of_mem_adjoin_of_fixed (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) ha_fix hs₀_fix
  have hfaith : FaithfulSMul G (Localization.Away T) :=
    faithfulSMul_away_of_noetherAdjoin (F := F) (G := G) (T := T) hTne hTinv
  have hinjδ : Function.Injective (BTier.deltaToEndRingHom hRG) :=
    injective_deltaToEndRingHom_away_of_noetherAdjoin (F := F) (G := G) (T := T) hTne
      hfaith hRG
  have hinjAlg : Function.Injective
      (algebraMap ↥(noetherFixedCarrier F G a s₀) (Localization.Away T)) := by
    rw [← faithfulSMul_iff_algebraMap_injective]
    exact faithfulSMul_subalgebra_away_of_noetherAdjoin (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) T hTne ι hι
  refine ⟨T, hTne, hTinv, hTle, instA, hST, instM, hRG, ?_⟩
  let _instMod : Module (MonoidAlgebra ↥(noetherFixedCarrier F G a s₀) G)
      (Localization.Away T) :=
    BTier.monoidAlgebraModuleOfMulSemiringAction
      (R := ↥(noetherFixedCarrier F G a s₀)) (G := G) hRG
  let _instTower : IsScalarTower ↥(noetherFixedCarrier F G a s₀)
      (MonoidAlgebra ↥(noetherFixedCarrier F G a s₀) G) (Localization.Away T) :=
    BTier.monoidAlgebraModule_isScalarTower
      (R := ↥(noetherFixedCarrier F G a s₀)) (G := G) hRG
  intro hsurj hfin hproj
  have hProj : BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away T) G hRG :=
    BTier.galoisProjectiveHyp_of_monoidAlgebraRows
      (R := ↥(noetherFixedCarrier F G a s₀)) (G := G) hRG hfin hproj hinjAlg
  have hgal : BTier.IsGaloisWithGroup ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away T) G hRG :=
    ⟨hfaith, fun g r => BTier.algebraMap_fixed_of_smulCommClass hRG g r, hinjδ, hsurj⟩
  exact realizationPropertyFieldFinite_of_subalgebra (F := F) (G := G)
    (S := noetherFixedCarrier F G a s₀) (t := T) hTne hTinv hTle hSfix hact hRG hgal hProj
    hS0R hinf

#print axioms injective_deltaToEndRingHom_away_of_noetherAdjoin
#print axioms exists_realizationPropertyFieldFinite_of_noetherFixedWiring_deltaSurj_and_rows

end NoetherFixedWiringReduction

section RowsNonemptyRegularAction

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K]

attribute [local instance] regularSMul regularMSA

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 非平凡 `G` 档：`hProj` 已落** ✓✅（**第 266 轮** ✓）：分裂 `G`-Galois 代数 `K^G` ✓（r264 ✓）上，
`S = G → K` **对 `K` 有限自由** ✓ ⟹ `Module.Finite K (G → K)` ✓ ＋ `Module.Projective K (G → K)` ✓
⟹ **`GaloisProjectiveHyp K (G → K) G`** ✓（`fun _ => …` 消费 `hgal` ✓，机制**不用**它 ✗）。
**⚠ 意义（L1** ✓**）**：`hProj` ✓ 的**假设类非空** ✓ —— **且非退化** ✓（`|G| ≥ 2` ✓ 时 `K^G ≇ K` ✓，
r264 ✓；与 `(F,F)` 退化作别 ✓）。**⚠ 载体之别** ✓（**如实** ✓）：本档 `S/R = (G → K)/K` ✓ **不是**
接线的那一对 ✗（`↥S → Localization.Away T` ✗）⟹ **接线假设表自身的非空性仍只到 `PUnit` 档** ✗（§4.70 ✓）。
**🔴 不声称** ✗：**不**声称 `hProj` ✓ 的**一般档**已证 ✗。 -/
theorem galoisProjectiveHyp_regularAction :
    GaloisProjectiveHyp K (G → K) G (regular_smul_comm (G := G) (K := K)) :=
  fun _ => ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 非平凡 `G` 档：两行同时为真** ✓✅（**第 266 轮** ✓）：`δ` **双射** ✓（r264 ✓ 的
`isGaloisWithGroup_regularAction` ✓ 的第三款 ✓）＋ **`hProj`** ✓（上件 ✓）。
**⚠ 意义（L1 ＋ L19** ✓**）**：§4.70 ✓ 残余表的**两行**在**同一非退化实例**上**可满足** ✓
（`|G| ≥ 2` ✓；`S = K^G` ✓ 是**源意义上的** `G`-Galois 代数 ✓）。
**🔴 不声称** ✗：**不**声称本档**就是**接线的那一对 ✗（见上件 ✓）。 -/
theorem rows_regularAction :
    Function.Bijective (BTier.deltaToEndRingHom (regular_smul_comm (G := G) (K := K)))
      ∧ GaloisProjectiveHyp K (G → K) G (regular_smul_comm (G := G) (K := K)) :=
  ⟨(isGaloisWithGroup_regularAction (G := G) (K := K)).2.2,
    galoisProjectiveHyp_regularAction (G := G) (K := K)⟩

#print axioms galoisProjectiveHyp_regularAction
#print axioms rows_regularAction

end RowsNonemptyRegularAction

section DedekindPositiveControl

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 Dedekind 判据的正例对照** ✓✅（**第 266 轮** ✓；L19 ✓）：`G = Multiplicative (ZMod 2)` ✓
（**非平凡** ✓：`|G| = 2` ✓，下件 ✓）在 **Noether 作用** ✓ 下作用于 `MvPolynomial G ℚ` ✓
（**环** ✓，**非**体 ✓）⟹ **`δ` 单射** ✓ —— **由判据本身导出** ✓（**不**用 `inferInstance` 兜底 ✗）。
**⚠ 机制** ✓：`S` **无零因子** ✓（`MvPolynomial` 对域 ✓）＋ **忠实** ✓
（`instFaithfulSMulMvPolynomial` ✓，SaltGeneric §4.4 ✓）＋ `hRG` ✓（`instSMulCommClassMvPolynomial` ✓）。
**🔴 不声称** ✗：**不**声称该档 `δ` **满射** ✗（**未算** ✗，**非**本轮目标 ✗）。 -/
theorem injective_deltaToEndRingHom_mvPolynomial_probe :
    Function.Injective (BTier.deltaToEndRingHom (R := ℚ)
      (S := MvPolynomial (Multiplicative (ZMod 2)) ℚ)
      (G := Multiplicative (ZMod 2))
      (fun g r s => SMulCommClass.smul_comm g r s)) :=
  BTier.injective_deltaToEndRingHom_of_noZeroDivisors (R := ℚ)
    (S := MvPolynomial (Multiplicative (ZMod 2)) ℚ) (G := Multiplicative (ZMod 2))
    (fun g r s => SMulCommClass.smul_comm g r s)

/-- **该正例的群非平凡** ✓（`|G| = 2` ✓；**L1 非空洞** ✓ —— 排除「判据只在平凡群上发射」✗）。 -/
theorem card_multiplicative_zmod_two :
    Fintype.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Fintype.card_multiplicative, ZMod.card]

#print axioms injective_deltaToEndRingHom_mvPolynomial_probe
#print axioms card_multiplicative_zmod_two

end DedekindPositiveControl

/-- **登记（r266 总账，逐条如实）** ✓：**源侧 generic object 上两行残余的再归约** ——
**已落** ✓✅：**(甲)** 通用机器两件 ✓（`GaloisAlgebra` §266 ✓：Dedekind 型判据 ✓
＝ `injective_deltaToEndRingHom_of_noZeroDivisors` ✓；`R[G]`-模结构 ✓ ＝
`monoidAlgebraModuleOfMulSemiringAction` ✓ ＋ 单点式 ✓ ＋ 塔式 ✓）；
**(乙)** 第 ① 行的**单射一半**在源侧 generic object 上 ✓（`injective_deltaToEndRingHom_away_of_noetherAdjoin` ✓，
**忠实性** ✓ 与**无零因子** ✓ 皆构造 ✓）；
**(丙)** `hProj` 的**再归约** ✓（`galoisProjectiveHyp_of_monoidAlgebraRows` ✓）；
**(丁)** **再归约后的接线件** ✓（`exists_realizationPropertyFieldFinite_of_noetherFixedWiring_deltaSurj_and_rows` ✓：
假设表 ＝ {`δ` 满射 ✓，`R[G]`-有限 ✓，`R[G]`-投射 ✓}，**`hProj` 已消** ✓）；
**(戊)** **两行的假设类非空（非退化** ✓**）** ✓（`rows_regularAction` ✓，**非平凡 `G`** ✓）；
**(己)** 判据的**正例对照** ✓（`injective_deltaToEndRingHom_mvPolynomial_probe` ✓，`|G| = 2` ✓）。
**未落** ✗（**逐条，含理由** ✓）：**(i)** `δ` **满射** ✗（**源侧不缺** ✓：`proposition-0-5`(b) ✓＋(c) ✓
印 254 ✓，核见 `SaltGeneric` §4.53 ✓；**缺**的是其**环档版** ✓（源 (b)(c) 在**域档** ✓，接线档 `R`
**非域** ✗）＝ 库内所记「CHR 代数版」✗，**未落** ✗，其精确出处**不在 `raw/`** ✗）；
**(ii)** `R[G]`-**有限** ✗ ＋ **(iii)** `R[G]`-**投射** ✗（源 `proposition-0-2(a)` ✓／
`[CHR68]` p. 13 ✓，**不在 `raw/`** ✗ —— §47／§52 ✓ 已登记「**任意档过宽、预期用例未落**」✓）；
**(iv)** **残余 ①**（环档桥 ✓）**仍开** ✓（§4.70 ✓；只影响源形 ✓）；
**(v)** 两条源陈述 ✓ 仍未证 ✗（`Theorem51Statement` ✓／`Theorem21Statement` ✓）；
**(vi)** **(a) 款的数据行** ✗（`hind` ✓ 由源假设 `IsRationalOver F L^G` ✓ 条件供给 ✓，＝ Noether 问题 ✓，§4.70 ✓）。
**⚠ 分类（规则 17）** ✓（**逐项** ✓）：**(i)--(iii) 皆证明义务** ✓（**非**观测数据 ✗、**非**「可算未算」✗）；
**(vi) 属「可算但未算」** ✓ → **不以「仍开」结案** ✗：其**唯一合法终态** ＝ 算完 ✓ 或证明不可算 ✓
（**本轮不改其状态** ✗ —— 它是 §4.70 ✓ 已登记的**条件行** ✓，**由源假设供给** ✓，非本轮缺口 ✓）；
**本轮无材料阻断登记** ✓。
**🔴 不声称** ✗：**不**声称 (i)--(vi) 任一已落 ✗；**不**声称两行**一般档**已证 ✗；**不**声称源陈述已证 ✗；
**不**声称 (β) 的启发式线路已在库内接通 ✗。 -/
theorem finiteFieldTier_genericObject_rows_rereduced_registered : True := trivial

#print axioms finiteFieldTier_genericObject_rows_rereduced_registered
/-! ### 4.72 **域档「`δ` 满射」的一般判据（抽象 `G`）** ＋ **有限 Galois 扩张档无条件落地**（第 267 轮）

**⚠ 目标** ✓（承 §4.71 ✓ 与 `SaltGeneric` §4.53 ✓）：残余表第 **(1b)** 行 ＝ `δ` **满射** ✗。
本轮落**两条**：**①** 域档的一般判据 ✓✅（把 (1b) 归约到**度数列** ✓）；**②** 有限 Galois 扩张档的
**无条件**双射 ✓✅（`G := Gal(E/F)` ✓，度数列由 mathlib 供给 ✓）。

**⚠ 机制（一句话）** ✓：`δ : Δ(S/K,G) → End_K(S)` 是**有限维 `K`-向量空间之间的 `K`-线性映射** ✓
（线性性由 `G` **固定 `K`** 供给 ✓）——**单射** ✓（Dedekind 型判据 ✓，r266 ✓ 已落 ✓）
＋ **两侧维数相等** ✓（左 ＝ `|G| · [S:K]` ✓，右 ＝ `[S:K]²` ✓）
⟹ **满射** ✓（`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ✓）。
**维数相等的充要条件** ＝ **`[S:K] = |G|`** ✓（`[S:K] > 0` ✓）⟹ **归约到一条基数等式** ✓。

**⚠ 与源 `proposition-0-5(b)+(c)`（印 254 ✓，核见 `SaltGeneric` §4.53 ✓）的强度序** ✓（**逐向** ✓）：
源 **(c)**（**正规基** ✓）**⟹** 度数列 ✓（正规基给出 `[L:K] = |G|` ✓）—— **本轮不证 (c)** ✗，
而是把 (c) 的**用点**（度数列 ✓）**单独取用** ✓；源 **(b)**（自同构**代数无关** ✓）
**在本轮路线中不被使用** ✗ —— 其角色（`δ` 单射 ✓）由**环档** Dedekind 判据 ✓
（`injective_deltaToEndRingHom_of_noZeroDivisors` ✓，r266 ✓）**弱假设**地供给 ✓
（**无零因子** ✓ ＋ **忠实** ✓，**不用**代数无关 ✗，**不用**域假设 ✗）。
⟹ **强度序** ✓：**(甲) 源 `(b)` ⟹ 本轮的 `δ` 单射款** ✓（但**严格强于**它 ✗ —— 本条只需线性无关 ✓）；
**(乙) 源 `(c)` ⟹ 本轮的度数列** ✓（**严格强于**它 ✗ —— 本条不需整组基 ✓）；
**(丙) 本轮 ⟹ `δ` 满射（域档）** ✓；**(丁) 反向皆不成立** ✗（度数列 ⇏ 正规基 ✗——例：任一
`[L:K] = |G|` 而 `G` 非全自同构群的档 ✓；线性无关 ⇏ 代数无关 ✗）。
**⚠ 域假设不可去** ✓（**如实** ✓）：本条**要求 `K` 是域** ✗（`injective_iff_surjective_of_finrank_eq_finrank`
是**线性代数**事实 ✓，须除环基 ✓）。**环档的同款归约**（`R` 一般 ✓ ＋ `[S:R] = |G|` ✓）
**不成立** ✗ —— **机检反例见 §4.73** ✓（`ℤ[i]/ℤ` ✓：全部假设成立 ✓ 而 `δ` **非满射** ✗）。

**⚠ 本轮所落（六条定理 ＋ 两件工具 ＋ 非空性实例** ✓**）**：
**①** `finrank_fun_const` ✓／`finrank_skewMonoidAlgebra` ✓ —— 两条**维数工具** ✓；
**②** `surjective_deltaToEndRingHom_of_finrank_eq_card` ✓✅ —— **第 (1b) 行的域档归约** ✓；
**③** `bijective_deltaToEndRingHom_of_finrank_eq_card` ✓✅ —— 双射款 ✓；
**④** `bijective_deltaToEndRingHom_of_isGalois` ✓✅ ＋ `surjective_deltaToEndRingHom_of_isGalois` ✓✅ ——
**有限 Galois 扩张档** ✓（`G := E ≃ₐ[F] E` ✓，**无条件** ✓：`IsGalois.card_aut_eq_finrank` ✓
供给度数列 ✓；**不用**正规基 ✗）—— **③ ＋ ④ 合起来** ＝ 源 `(b)+(c)` 的**用点**在**域档**落地 ✓
（③ 取**抽象 `G`** ✓ 而度数列作**显式输入** ✓；④ 取 `G = Gal(E/F)` ✓ 而**无条件** ✓）；
**⚠ 环档未落** ✗ 且**不能**由 ③ 直接搬 ✓（见 §4.73 ✓）；
**⑤** `bijective_deltaToEndRingHom_regularAction` ✓✅ ＋ `surjective_deltaToEndRingHom_regularAction` ✓✅ ——
**分裂／正则档具名** ✓（r264 ✓ 已落的内容 ✓，本轮**具名**为 (1b) 行形 ✓）；
**⑥** 非空性（L1 ✓）：**非退化域档实例** ✓（`GF(4)/GF(2)` ✓：`|Gal| = 2` ✓）
＋ **退化对照** ✓（`ℚ/ℚ` ＋ `PUnit` ✓）。

**⚠ 分类（规则 17）** ✓：本轮**无**观测数据缺口 ✗、**无**「可算未算」✗ ——
所落四条**皆为证明** ✓；**未落**的只剩**环档**（`R` **非域** ✗）✓，其障碍在 §4.73 ✓ **以机检反例**
**定位** ✓（**非**材料阻断 ✗、**非**「仍开」的含糊登记 ✗）。
**🔴 不声称** ✗：**不**声称**环档**（源接线档 `R = ↥(noetherFixedCarrier …)` ✗）的 (1b) 已落 ✗；
**不**声称源 `(b)` ✓／`(c)` ✓ 已在库内接通 ✗；**不**声称两条源陈述已证 ✗；
**不**声称 `R[G]`-两行（§4.71 (2a)／(2b) ✓）有任何进展 ✗。 -/

namespace BTier

/-! #### 4.72.1 工具：作用-纯量交换 ＋ 两条维数式 -/

section SmulCommTools267

variable {K : Type*} [CommSemiring K] {S : Type*} [Semiring S] [Algebra K S]
variable {G : Type*} [Monoid G] [MulSemiringAction G S]

/-- **作用与纯量交换** ✓：`G` **固定 `K` 的像** ✓ ⟹ `g • (k • s) = k • (g • s)` ✓ ——
即 `δ` 的 `hRG` 输入 ✓ 由**固定性**供给 ✓（`k • s = algebraMap k * s` ✓ ＋ `smul_mul'` ✓）。
**⚠ 用途** ✓：本件是**判据 ②** 的 `hRG` 来源 ✓；亦给 §4.72 的 `algEquiv_smul_comm` ✓ 作一般形 ✓。 -/
lemma smul_comm_of_fixes_base
    (hfix : ∀ (g : G) (k : K), g • algebraMap K S k = algebraMap K S k) :
    ∀ (g : G) (k : K) (s : S), g • (k • s) = k • (g • s) := by
  intro g k s
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix g k]

end SmulCommTools267

section FinrankTools267

variable {K : Type*} [Field K] {S : Type*} [AddCommGroup S] [Module K S]
variable {G : Type*} [Fintype G]

/-- **维数工具 ①** ✓：`finrank_K (G → S) = |G| · [S:K]` ✓。
**⚠ 路线** ✓：`Module.finrank_pi_fintype` ✓（**族**形 ✓，对 `G` 与 `S` 的宇宙**无**限制 ✓）
＋ `Finset.sum_const` ✓。**⚠ 为何不走** `Module.finrank_finsupp` ✗：其 `ι` 与 `M` **同宇宙** ✗
（实测 ✓，r264 ✓ 已记 ✓）⟹ 本条是**跨宇宙**形 ✓。 -/
lemma finrank_fun_const [FiniteDimensional K S] :
    Module.finrank K (G → S) = Fintype.card G * Module.finrank K S := by
  rw [Module.finrank_pi_fintype K (M := fun _ : G => S)]
  simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end FinrankTools267

section FinrankSkew267

variable {K : Type*} [Field K] {S : Type*} [CommRing S] [Algebra K S]
variable {G : Type*} [Fintype G]

/-- **维数工具 ②** ✓：`finrank_K Δ(S/K,G) = |G| · [S:K]` ✓ ——
`coeffLinearEquiv` ✓（`Δ ≃ₗ (G →₀ S)` ✓）＋ `Finsupp.linearEquivFunOnFinite` ✓（`→` 形 ✓）
＋ **维数工具 ①** ✓（**不**走 `Module.finrank_finsupp` ✗，宇宙限制同上 ✓）。 -/
lemma finrank_skewMonoidAlgebra [FiniteDimensional K S] :
    Module.finrank K (SkewMonoidAlgebra S G) = Fintype.card G * Module.finrank K S := by
  rw [(SkewMonoidAlgebra.coeffLinearEquiv (S := K) (k := S) (G := G)).finrank_eq,
    (Finsupp.linearEquivFunOnFinite K S G).finrank_eq]
  exact finrank_fun_const

end FinrankSkew267

section GeneralCriterion267

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 双射款** ✓✅（同上一件的机制 ＋ r266 ✓ 的单射款 ✓）：结论形取
`Function.Bijective` ✓ —— 即 `bijective_deltaToEndRingHom_iff` ✓（`GaloisAlgebra` §266 ✓）
的**左端**在域档 ＋ 基数等式下落地 ✓。
**⚠ 工艺** ✓：`δ` 的 `K`-**线性性须手工注册** ✗（`deltaToEndRingHom` 是**环**同态 ✓，
mathlib 无「环同态 → 线性映射」的自动提升 ✗）—— 逐 `single` 归纳 ✓ ＋ `smul_mul_assoc` ✓；
`Module.Finite K Δ` ✓ **亦须**由 `Module.Finite.equiv` ✓ ＋ `coeffLinearEquiv` ✓ **就地注册** ✗
（mathlib **无** `SkewMonoidAlgebra` 的有限性实例 ✗，r264 ✓ 同款 ✓）。
**🔴 不声称** ✗：同上一件 ✓。 -/
theorem bijective_deltaToEndRingHom_of_finrank_eq_card
    [FiniteDimensional K S] [NoZeroDivisors S] [FaithfulSMul G S]
    (hfix : ∀ (g : G) (k : K), g • algebraMap K S k = algebraMap K S k)
    (hcard : Module.finrank K S = Fintype.card G) :
    Function.Bijective (deltaToEndRingHom (smul_comm_of_fixes_base hfix)) := by
  classical
  let _instFin : Module.Finite K (SkewMonoidAlgebra S G) :=
    Module.Finite.equiv (SkewMonoidAlgebra.coeffLinearEquiv (S := K) (k := S) (G := G)).symm
  have hsmul : ∀ (k : K) (x : SkewMonoidAlgebra S G),
      deltaToEndRingHom (smul_comm_of_fixes_base hfix) (k • x)
        = k • deltaToEndRingHom (smul_comm_of_fixes_base hfix) x := by
    intro k x
    induction x using SkewMonoidAlgebra.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | single g a =>
      rw [SkewMonoidAlgebra.smul_single]
      change deltaToEndAdd (smul_comm_of_fixes_base hfix) (SkewMonoidAlgebra.single g (k • a))
        = k • deltaToEndAdd (smul_comm_of_fixes_base hfix) (SkewMonoidAlgebra.single g a)
      rw [deltaToEndAdd_single, deltaToEndAdd_single]
      ext t
      change (k • a) * (g • t) = k • (a * (g • t))
      rw [smul_mul_assoc]
  have hinj := injective_deltaToEndRingHom_of_noZeroDivisors (smul_comm_of_fixes_base hfix)
  let δL : SkewMonoidAlgebra S G →ₗ[K] Module.End K S :=
    { toFun := deltaToEndRingHom (smul_comm_of_fixes_base hfix)
      map_add' := map_add _
      map_smul' := hsmul }
  have hinjL : Function.Injective δL := hinj
  have hdim : Module.finrank K (SkewMonoidAlgebra S G)
      = Module.finrank K (Module.End K S) := by
    rw [finrank_skewMonoidAlgebra, Module.finrank_linearMap, hcard]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinjL⟩

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 判据（第 (1b) 行的域档归约）** ✓✅：`K` **域** ✓ ＋ `S` **`K`-代数** ✓ ＋
**有限维** ✓ ＋ **无零因子** ✓ ＋ `G` **忠实** ✓ ＋ `G` **固定 `K`** ✓ ＋
**基数等式 `[S:K] = |G|`** ✓ ⟹ **`δ` 满射** ✓。
**⚠ 机制** ✓（见节头 ✓）：`δ` 是 `K`-线性 ✓（其 `hRG` 由 `smul_comm_of_fixes_base` ✓ 供给 ✓）
＋ 单射 ✓（Dedekind 型判据 ✓）＋ **两侧维数相等** ✓（工具 ② ✓ ＋ `Module.finrank_linearMap` ✓
＋ 基数等式 ✓）⟹ 满射 ✓（`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ✓）。
**⚠ 强度** ✓：**单射款**由 r266 ✓ 的**环档**判据供给 ✓（**弱于**源 `(b)` ✓）；
**度数列**是本条**唯一的额外输入** ✓（**弱于**源 `(c)` ✓）—— 强度序见节头 ✓。
**🔴 不声称** ✗：**不**声称环档（`R` 非域 ✗）同款成立 ✗（机检反例见 §4.73 ✓）；
**不**声称度数列在源接线档可得 ✗。 -/
theorem surjective_deltaToEndRingHom_of_finrank_eq_card
    [FiniteDimensional K S] [NoZeroDivisors S] [FaithfulSMul G S]
    (hfix : ∀ (g : G) (k : K), g • algebraMap K S k = algebraMap K S k)
    (hcard : Module.finrank K S = Fintype.card G) :
    Function.Surjective (deltaToEndRingHom (smul_comm_of_fixes_base hfix)) :=
  (bijective_deltaToEndRingHom_of_finrank_eq_card (G := G) hfix hcard).2

end GeneralCriterion267

/-! #### 4.72.2 有限 Galois 扩张档（`G := Gal(E/F)`，**无条件**） -/

section IsGalois267

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **`Gal(E/F)` 与 `F`-纯量交换** ✓（判据的 `hRG` 输入 ✓）：`σ • (k • s) = k • (σ • s)` ✓
（`AlgEquiv.smul_def` ✓ ＋ `AlgEquiv.commutes` ✓ ＋ `smul_mul'` ✓）。
**⚠ 与 `smul_comm_of_fixes_base` 的关系** ✓：本条是其在 `Gal(E/F)` 档的**具名特例** ✓。 -/
lemma algEquiv_smul_comm (σ : E ≃ₐ[F] E) (k : F) (s : E) : σ • (k • s) = k • (σ • s) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', AlgEquiv.smul_def, AlgEquiv.commutes]

/-- **`Gal(E/F)` 固定 `F` 的像** ✓：`σ • algebraMap F E k = algebraMap F E k` ✓
（`AlgEquiv.commutes` ✓）。 -/
lemma algEquiv_fixes_base (σ : E ≃ₐ[F] E) (k : F) : σ • algebraMap F E k = algebraMap F E k := by
  rw [AlgEquiv.smul_def, AlgEquiv.commutes]

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 有限 Galois 扩张档：`δ` 双射（无条件）** ✓✅：`E/F` **有限** ＋ **Galois** ✓ ⟹
取 **`G := Gal(E/F) = E ≃ₐ[F] E`** ✓（mathlib **已有**实例：`MulSemiringAction` ✓ ＝
`AlgEquiv.applyMulSemiringAction` ✓、`FaithfulSMul` ✓ ＝ `AlgEquiv.apply_faithfulSMul` ✓、
`Fintype` ✓ ＝ `AlgEquiv.fintype` ✓）⟹ `δ` **双射** ✓。
**⚠ 度数列的来源** ✓：**`IsGalois.card_aut_eq_finrank`** ✓（mathlib ✓：`Nat.card Gal(E/F) = [E:F]` ✓）
＋ `Fintype.card_eq_nat_card` ✓ —— **不**经正规基 ✗。
**⚠ 意义** ✓：本件把源 `(b)+(c)` 的**用点**（`δ` 双射 ✓）在**域档**落地 ✓，
而**载体是抽象群作用** ✓（`G` ✓ ＋ `MulSemiringAction G E` ✓ ＋ `SkewMonoidAlgebra E G` ✓）——
**不**用 mathlib 的 `L ≃ₐ[K] L`-**指标形**正规基定理 ✗ ⟹ `SaltGeneric` §4.53 ✓ 登记的
「mathlib 正规基定理的指标形是 `L ≃ₐ[K] L` 而非抽象 `G`」✗ **在本档被绕过** ✓
（**不用**正规基 ✓，只用 `IsGalois.card_aut_eq_finrank` ✓）。
**⚠ 口径** ✓：本件的 `G` **取** `Gal(E/F)` ✓ —— **一般抽象 `G`**（不要求 `G = Gal` ✓）的档
由 ③ ✓（`bijective_deltaToEndRingHom_of_finrank_eq_card` ✓）以**度数列作显式输入**供给 ✓。
**⚠ 边界（如实）** ✓：**域假设不可去** ✗（`E` 须是域 ✓）；**源接线档的 `R` 非域** ✗ ⟹
**本条不覆盖接线对** ✗（见 §4.73 ✓）。
**🔴 不声称** ✗：**不**声称源 `(b)` ✓／`(c)` ✓ 已在库内证明 ✗；**不**声称接线档已落 ✗。 -/
theorem bijective_deltaToEndRingHom_of_isGalois
    [FiniteDimensional F E] [IsGalois F E] :
    Function.Bijective (deltaToEndRingHom (R := F) (S := E) (G := E ≃ₐ[F] E)
      (algEquiv_smul_comm (F := F) (E := E))) := by
  classical
  refine bijective_deltaToEndRingHom_of_finrank_eq_card (K := F) (S := E) (G := E ≃ₐ[F] E)
    (hfix := algEquiv_fixes_base (F := F) (E := E)) ?_
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

set_option maxHeartbeats 1000000 in
/-- **同上的满射款** ✓✅（供 (1b) 行**逐半**取用 ✓）。 -/
theorem surjective_deltaToEndRingHom_of_isGalois
    [FiniteDimensional F E] [IsGalois F E] :
    Function.Surjective (deltaToEndRingHom (R := F) (S := E) (G := E ≃ₐ[F] E)
      (algEquiv_smul_comm (F := F) (E := E))) :=
  (bijective_deltaToEndRingHom_of_isGalois (F := F) (E := E)).2

end IsGalois267

#print axioms smul_comm_of_fixes_base
#print axioms finrank_fun_const
#print axioms finrank_skewMonoidAlgebra
#print axioms surjective_deltaToEndRingHom_of_finrank_eq_card
#print axioms bijective_deltaToEndRingHom_of_finrank_eq_card
#print axioms algEquiv_smul_comm
#print axioms algEquiv_fixes_base
#print axioms bijective_deltaToEndRingHom_of_isGalois
#print axioms surjective_deltaToEndRingHom_of_isGalois

end BTier

/-! #### 4.72.3 非空性：非退化域档实例 ＋ 退化对照 ＋ 分裂档具名 -/

section NonemptyFieldTier267

/-- **🔴🔴 非退化域档实例（L1）** ✓✅：`GF(4)/GF(2)` ✓（`E := FiniteField.Extension (ZMod 2) 2 2` ✓）
上 `δ` **双射** ✓ —— **由判据本身导出** ✓（**不**用 `inferInstance` 兜底 ✗）。
**⚠ 机制** ✓：`IsGalois (ZMod 2) E` ✓ ＋ `FiniteDimensional (ZMod 2) E` ✓（mathlib 实例 ✓）
＋ `IsGalois.card_aut_eq_finrank` ✓（度数列 ＝ `2` ✓）。 -/
theorem bijective_deltaToEndRingHom_gf4 :
    Function.Bijective (BTier.deltaToEndRingHom (R := ZMod 2)
      (S := FiniteField.Extension (ZMod 2) 2 2)
      (G := FiniteField.Extension (ZMod 2) 2 2 ≃ₐ[ZMod 2] FiniteField.Extension (ZMod 2) 2 2)
      (BTier.algEquiv_smul_comm (F := ZMod 2) (E := FiniteField.Extension (ZMod 2) 2 2))) :=
  BTier.bijective_deltaToEndRingHom_of_isGalois (F := ZMod 2)
    (E := FiniteField.Extension (ZMod 2) 2 2)

/-- **该实例非退化** ✓（L1 ✓）：`[GF(4) : GF(2)] = 2` ✓ ⟹ `|G| = 2 ≥ 2` ✓
（排除「判据只在 `|G| = 1` 上发射」✗）。 -/
theorem finrank_gf4_over_gf2 :
    letI := FiniteField.instAlgebraExtension (ZMod 2) 2 2
    Module.finrank (ZMod 2) (FiniteField.Extension (ZMod 2) 2 2) = 2 :=
  FiniteField.finrank_extension (ZMod 2) 2 2

/-- **同上的群阶形** ✓：`|Gal(GF(4)/GF(2))| = 2` ✓。 -/
theorem card_gal_gf4 :
    letI := FiniteField.instAlgebraExtension (ZMod 2) 2 2
    Fintype.card (FiniteField.Extension (ZMod 2) 2 2 ≃ₐ[ZMod 2]
      FiniteField.Extension (ZMod 2) 2 2) = 2 :=
  FiniteField.card_algEquiv_extension (ZMod 2) 2 2

#print axioms bijective_deltaToEndRingHom_gf4
#print axioms finrank_gf4_over_gf2
#print axioms card_gal_gf4

end NonemptyFieldTier267

/-! #### 4.72.4 分裂／正则档（具名） ＋ 退化对照 -/

section RegularActionNamed267

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K]

attribute [local instance] regularSMul regularMSA

set_option maxHeartbeats 1000000 in
/-- **分裂／正则档：`δ` 双射（具名）** ✓✅：`S = G → K` ✓（`G` **正则置换**作用于坐标 ✓）上
`δ` **双射** ✓ —— 即 §4.71 ✓ 残余表第 **(1b)** 行的**分裂档见证** ✓（**具名**后可**单独**取用 ✓，
不再只是 `rows_regularAction` ✓ 的合取支 ✓）。
**⚠ 机制** ✓：r264 ✓ 已落 ✓（`isGaloisWithGroup_regularAction` ✓ 的第三款 ✓），**本件不重证** ✗。
**⚠ 载体之别（如实** ✓**）**：本档 `S/R = (G → K)/K` ✓ **不是**接线的那一对 ✗
（`↥S → Localization.Away T` ✗），且 `S` 在 `|G| ≥ 2` 时**不是域** ✗（有零因子 ✗，§4.67 ✓）
⟹ **不覆盖 §4.72.2 的域档判据** ✓ 的假设类 ✗。
**🔴 不声称** ✗：**不**声称本档是**接线档** ✗。 -/
theorem bijective_deltaToEndRingHom_regularAction :
    Function.Bijective (BTier.deltaToEndRingHom (regular_smul_comm (G := G) (K := K))) :=
  (rows_regularAction (G := G) (K := K)).1

set_option maxHeartbeats 1000000 in
/-- **同上的满射款** ✓✅（供 (1b) 行**逐半**取用 ✓）。 -/
theorem surjective_deltaToEndRingHom_regularAction :
    Function.Surjective (BTier.deltaToEndRingHom (regular_smul_comm (G := G) (K := K))) :=
  (rows_regularAction (G := G) (K := K)).1.2

#print axioms bijective_deltaToEndRingHom_regularAction
#print axioms surjective_deltaToEndRingHom_regularAction

end RegularActionNamed267

section RatPUnitProbe267

/-- 探针用的 `PUnit ↷ ℚ` **平凡作用** ✓（`PUnit` 的 `MulSemiringAction` **非** mathlib 实例 ✗，就地给出 ✓；
命名与 `GaloisAlgebra` §266 的 `pUnitMSARatQ266` ✓ 相区别 ✓）。 -/
local instance pUnitMSARatQ267 : MulSemiringAction PUnit.{1} ℚ where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

set_option maxHeartbeats 1000000 in
/-- **退化档对照（L19 正例）** ✓✅：`S = K = ℚ` ✓／`G = PUnit` ✓ 上判据 ② **发射** ✓ ——
即 `[S:K] = 1 = |G|` ✓ 的**退化**档 ✓，**由判据本身导出** ✓（**不**用 `inferInstance` 兜底 ✗）
⟹ 判据**能**发出**阳性**读数 ✓（与 §4.72.3 的 `GF(4)` **非退化**档 ✓ **对照** ✓）。 -/
theorem bijective_deltaToEndRingHom_rat_punit267 :
    Function.Bijective (BTier.deltaToEndRingHom (R := ℚ) (S := ℚ) (G := PUnit.{1})
      (fun _ _ _ => rfl)) :=
  BTier.bijective_deltaToEndRingHom_of_finrank_eq_card (K := ℚ) (S := ℚ) (G := PUnit.{1})
    (hfix := fun _ _ => rfl) (hcard := by simp)

#print axioms bijective_deltaToEndRingHom_rat_punit267

end RatPUnitProbe267

/-! ### 4.73 **环档（`R` 非域）的「朴素归约」是假的** —— **机检反例**：`ℤ[i]/ℤ`（第 267 轮）

**⚠ 被反驳的命题（形状锁定见 `NaiveRingTierReduction267` ✓）** ✗：把 §4.72 ✓ 的域档归约
**逐字搬到环档** —— 即
{`R` ✓、`S` **交换环** ✓、`R → S` ✓、`G` **有限忠实** ✓、`hRG` ✓、
**`R` ⊆ `S^G`** ✓（**逐点固定** ✓）、**`R` ⊇ `S^G`** ✓（**不动环相等** ✓，**强于**源定义中的单向包含 ✓）、
**`S` 无零因子** ✓、**`S` 对 `R` 有限自由** ✓（含**投射** ✓）、
**`finrank_R S = |G|`** ✓、**`δ` 单射** ✓}
⟹ **`δ` 满射**。
**⚠ 注** ✓（**为何表里含 `S^G = R`** ✓）：源的 `IsGaloisWithGroup` ✓（`GaloisAlgebra` §0 ✓）只要求
`R` 是 `S^G` 的**子代数** ✓；本表取了**更强**的**相等** ✓ ⟹ **否定更强的表** ＝ **更强的负面结论** ✓
（反例**连不动环相等都满足** ✓）。
**⚠ 本轮读数** ✓✅：**该命题为假** ✗ —— 反例 ＝ `R = ℤ` ✓、`S = ℤ[i] = ℤ√(-1)` ✓、
`G = Multiplicative (ZMod 2)` ✓（**共轭**作用 ✓）。
**⚠ 机制（为何坏在环档）** ✓：`ℤ[i]/ℤ` 的**迹形式**（`Tr = 1 + conj` ✓）**非幺模** ✗ ——
`Tr(1) = 2` ✓、`Tr(i) = 0` ✓ ⟹ 迹像 ⊆ `2ℤ` ✗ ⟹ `2` 在 `ℤ[i]/ℤ` 中**分歧** ✓；
而 §4.72 ✓ 的域档论证用的是**除环上的基数-维数**（`injective_iff_surjective_of_finrank_eq_finrank` ✓），
它在环档**无对应物** ✗ —— **单射 ＋ 秩相等 ⇏ 满射** ✗（同一机制：`2 : ℤ → ℤ` ✓）。
**⚠ 与源 `proposition-0-5` 的关系** ✓（**这是本轮最强的负面读数** ✓）：源 **(b)** ✓／**(c)** ✓
**只在域档** ✓（「Turning to the case `R = K` is a field」✓，核见 `SaltGeneric` §4.53 ✓）；
本反例说明**其环档版不能退化为「单射 ＋ 基数（＋ 不动环 ＋ 有限自由）」** ✗ —— 环档需要
**额外的模论输入** ✓，例如源 `proposition-0-2(a)` ✓／`[CHR68]` p. 13 ✓ 一路
（`R[G]`-有限／投射 ✓，对应 §4.71 ✓ 表的 **(2a)** ✓／**(2b)** 两行 ✓），或**迹形式的幺模性** ✓；
**🔴 本件不判定**哪一条**充分** ✗ —— **只**证明**朴素表不充分** ✓（**不**声称环档为假 ✗）。
**⚠ 强度序（如实** ✓**）**：**(甲)** 本条**不**触及 §4.72 ✓ 的**域档**判据 ✓（`K` 是域 ✓）；
**(乙)** 本条**反驳**的是**朴素环档形** ✓（**其否定已机检** ✓），**不**反驳**任何**加了模论输入的环档形 ✓
（源档是否成立**仍开** ✓ —— **本件不给正面结果** ✗）；**(丙)** 反例**满足**全部假设 ✓
（含 `S` 对 `ℤ` **有限自由** ✓ 且 `finrank = |G| = 2` ✓ 且 `δ` **单射** ✓）：见 `ringTier_counterexample267` ✓。
**⚠ 分类（规则 17）** ✓：本条是**证明**（**反射式** ✓：给出反例 ＋ 机检否定 ✓）——
**非**观测数据 ✗、**非**「可算未算」✗、**非**材料阻断 ✗。 -/

section RingTierCounterexample267

/-- **被反驳命题的形状锁定** ✗（**不是**定理 ✓，**没有**证明 ✓ —— 其**否定**见下件 ✓；
锁定用点 ＝ 使「本轮究竟反驳了哪张假设表」**可机械比对** ✓）。 -/
def NaiveRingTierReduction267 : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x)),
    NoZeroDivisors S → FaithfulSMul G S →
      (∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r) →
      (∀ x : S, (∀ g : G, g • x = x) → ∃ r : R, algebraMap R S r = x) →
      Module.Finite R S → Module.Free R S → Module.Projective R S →
      Module.finrank R S = Fintype.card G →
      Function.Injective (BTier.deltaToEndRingHom hRG) →
      Function.Surjective (BTier.deltaToEndRingHom hRG)

/-- **`ZMod 2` 的元素只有两个** ✓（作用良定义性的穷尽工具 ✓；`decide` ✓，**非** `native_decide` ✗）。 -/
lemma mul_zmod2_cases267 (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  revert g
  decide

/-- `(ofAdd 1)² = 1` ✓（`ZMod 2` 中 `1 + 1 = 0` ✓）。 -/
lemma zmod2_gen_mul_self267 :
    (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1)
      = (1 : Multiplicative (ZMod 2)) := by decide

/-- **共轭作用函数** ✓：`g ↦ (x ↦ x)` ✓（`g = 1` ✓）或 `g ↦ (x ↦ star x)` ✓（`g = ofAdd 1` ✓）。
**⚠ 为何先给函数** ✗：`MulSemiringAction` 的字段证明**不能**展开**正在定义**的实例 ✗
（实测：`simp` made no progress ✓）⟹ 先落**完成的函数** ✓，再逐条搬运 ✓。 -/
def conjSmul267 (g : Multiplicative (ZMod 2)) (x : Zsqrtd (-1)) : Zsqrtd (-1) :=
  if g = (1 : Multiplicative (ZMod 2)) then x else star x

@[simp] lemma conjSmul267_one (x : Zsqrtd (-1)) : conjSmul267 1 x = x := rfl

@[simp] lemma conjSmul267_gen (x : Zsqrtd (-1)) :
    conjSmul267 (Multiplicative.ofAdd 1) x = star x := by
  rw [conjSmul267, if_neg (by decide : ¬ (Multiplicative.ofAdd (1 : ZMod 2) = 1))]

lemma conjSmul267_mul_smul (g h : Multiplicative (ZMod 2)) (x : Zsqrtd (-1)) :
    conjSmul267 (g * h) x = conjSmul267 g (conjSmul267 h x) := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> rcases mul_zmod2_cases267 h with rfl | rfl <;>
    simp [conjSmul267_one, conjSmul267_gen, zmod2_gen_mul_self267, star_star]

lemma conjSmul267_zero (g : Multiplicative (ZMod 2)) : conjSmul267 g 0 = 0 := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [conjSmul267_one, conjSmul267_gen]

lemma conjSmul267_add (g : Multiplicative (ZMod 2)) (x y : Zsqrtd (-1)) :
    conjSmul267 g (x + y) = conjSmul267 g x + conjSmul267 g y := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [conjSmul267_one, conjSmul267_gen]

lemma conjSmul267_mul (g : Multiplicative (ZMod 2)) (x y : Zsqrtd (-1)) :
    conjSmul267 g (x * y) = conjSmul267 g x * conjSmul267 g y := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [conjSmul267_one, conjSmul267_gen]

lemma conjSmul267_one' (g : Multiplicative (ZMod 2)) : conjSmul267 g 1 = 1 := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [conjSmul267_one, conjSmul267_gen]

/-- **忠实性** ✓（`star` **非**恒等 ✓：取 `x = √(-1)` ✓ 有 `star x = -x ≠ x` ✓）。 -/
lemma conjSmul267_faithful (a b : Multiplicative (ZMod 2))
    (hab : ∀ x : Zsqrtd (-1), conjSmul267 a x = conjSmul267 b x) : a = b := by
  rcases mul_zmod2_cases267 a with rfl | rfl <;> rcases mul_zmod2_cases267 b with rfl | rfl
  · rfl
  · exfalso
    have h := hab (Zsqrtd.sqrtd : Zsqrtd (-1))
    simp only [conjSmul267_one, conjSmul267_gen] at h
    exact absurd h (by decide)
  · exfalso
    have h := hab (Zsqrtd.sqrtd : Zsqrtd (-1))
    simp only [conjSmul267_one, conjSmul267_gen] at h
    exact absurd h.symm (by decide)
  · rfl

/-- 作用以 `SMul` 层落一次 ✓（供 `toSMul` **指名** ✓ —— **不**用 `letI` 链 ✗）。 -/
local instance zmod2SMulGI267 : SMul (Multiplicative (ZMod 2)) (Zsqrtd (-1)) :=
  ⟨conjSmul267⟩

/-- **共轭作用** ✓（`G = Multiplicative (ZMod 2)` ✓ 作用于 `ℤ[i]` ✓，**局部实例** ✓：限本节 ✓）。 -/
local instance zmod2MSAGI267 : MulSemiringAction (Multiplicative (ZMod 2)) (Zsqrtd (-1)) where
  toSMul := zmod2SMulGI267
  one_smul x := conjSmul267_one x
  mul_smul g h x := conjSmul267_mul_smul g h x
  smul_zero g := conjSmul267_zero g
  smul_add g x y := conjSmul267_add g x y
  smul_mul g x y := conjSmul267_mul g x y
  smul_one g := conjSmul267_one' g

local instance zmod2FaithfulGI267 : FaithfulSMul (Multiplicative (ZMod 2)) (Zsqrtd (-1)) where
  eq_of_smul_eq_smul {a b} hab := conjSmul267_faithful a b fun x => hab x

/-- **`ℤ`-纯量与作用交换** ✓（判据的 `hRG` ✓）：`star` 固定整数 ✓（`star_intCast` ✓）。 -/
lemma conjSmul267_int_smul (g : Multiplicative (ZMod 2)) (z : ℤ) (x : Zsqrtd (-1)) :
    conjSmul267 g ((z : Zsqrtd (-1)) * x) = (z : Zsqrtd (-1)) * conjSmul267 g x := by
  rcases mul_zmod2_cases267 g with rfl | rfl
  · simp [conjSmul267_one]
  · rw [conjSmul267_gen, conjSmul267_gen, star_mul, star_intCast, mul_comm]

lemma zmod2_smul_int_comm267 (g : Multiplicative (ZMod 2)) (z : ℤ) (x : Zsqrtd (-1)) :
    g • (z • x) = z • (g • x) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact conjSmul267_int_smul g z x

/-- **`δ` 的两项展开式** ✓：`δ x y = (coeff 1 x) * y + (coeff (ofAdd 1) x) * star y` ✓ ——
`G` 只有两个元素 ✓，故求和坍缩为两项 ✓（`induction_on` ✓ ＋ `deltaToEndAdd_single` ✓）。 -/
lemma delta_form_zmod2 (x : SkewMonoidAlgebra (Zsqrtd (-1)) (Multiplicative (ZMod 2)))
    (y : Zsqrtd (-1)) :
    BTier.deltaToEndRingHom zmod2_smul_int_comm267 x y
      = x.coeff 1 * y + x.coeff (Multiplicative.ofAdd 1) * star y := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add x z hx hz =>
    rw [map_add, LinearMap.add_apply, hx, hz]
    simp only [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
    ring
  | single g s =>
    rw [show BTier.deltaToEndRingHom zmod2_smul_int_comm267
        (SkewMonoidAlgebra.single g s)
          = BTier.deltaToEndAdd zmod2_smul_int_comm267 (SkewMonoidAlgebra.single g s) from rfl,
      BTier.deltaToEndAdd_single, Module.End.mul_apply]
    rcases mul_zmod2_cases267 g with rfl | rfl
    · change s * conjSmul267 1 y
        = (SkewMonoidAlgebra.single 1 s).coeff 1 * y
          + (SkewMonoidAlgebra.single 1 s).coeff (Multiplicative.ofAdd 1) * star y
      rw [conjSmul267_one, SkewMonoidAlgebra.coeff_single_apply, if_pos rfl,
        SkewMonoidAlgebra.coeff_single_apply,
        if_neg (by decide : ¬ ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1))]
      ring
    · change s * conjSmul267 (Multiplicative.ofAdd 1) y
        = (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) s).coeff 1 * y
          + (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) s).coeff
              (Multiplicative.ofAdd 1) * star y
      rw [conjSmul267_gen, SkewMonoidAlgebra.coeff_single_apply,
        if_neg (by decide : ¬ (Multiplicative.ofAdd (1 : ZMod 2) = 1)),
        SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
      ring

/-- **`δ` 单射** ✓✅（**由 r266 ✓ 的判据供给** ✓，**不**重证 ✗）：`ℤ[i]` **无零因子** ✓
＋ `G` **忠实** ✓ ⟹ 单射 ✓ —— 即反例的**前提之一由库内已落工具供给** ✓
（**这正是反例的尖锐处** ✓：全部前提皆真 ✓ 而结论假 ✗）。 -/
theorem zmod2_delta_injective267 :
    Function.Injective (BTier.deltaToEndRingHom zmod2_smul_int_comm267) :=
  BTier.injective_deltaToEndRingHom_of_noZeroDivisors
    (R := ℤ) (S := Zsqrtd (-1)) (G := Multiplicative (ZMod 2)) zmod2_smul_int_comm267

/-- **整数纯量被固定** ✓（`star` 固定整数 ✓）：`conjSmul267 g (r : ℤ[i]) = (r : ℤ[i])` ✓。 -/
lemma conjSmul267_intCast (g : Multiplicative (ZMod 2)) (r : ℤ) :
    conjSmul267 g ((r : ℤ) : Zsqrtd (-1)) = ((r : ℤ) : Zsqrtd (-1)) := by
  rcases mul_zmod2_cases267 g with rfl | rfl
  · exact conjSmul267_one _
  · rw [conjSmul267_gen, star_intCast]

/-- **`R` ⊆ `S^G`** ✓（`ℤ` 的像被 `G` **逐点固定** ✓）。 -/
lemma fixed_algebraMap_gaussianInt267 (g : Multiplicative (ZMod 2)) (r : ℤ) :
    g • algebraMap ℤ (Zsqrtd (-1)) r = algebraMap ℤ (Zsqrtd (-1)) r :=
  conjSmul267_intCast g r

/-- **`S^G` ⊆ `R`** ✓（**不动环相等** ✓ —— **强于**源定义的单向包含 ✓）：
`x` 被**一切** `g` 固定 ✓ ⟹（取 `g = ofAdd 1` ✓）`star x = x` ✓ ⟹ `x.im = -x.im` ✓
⟹ `2 * x.im = 0` ✓ ⟹ `x.im = 0` ✓（`omega` ✓）⟹ `x = (x.re : ℤ[i])` ✓。 -/
lemma fixed_ring_gaussianInt267 (x : Zsqrtd (-1))
    (hx : ∀ g : Multiplicative (ZMod 2), g • x = x) :
    ∃ r : ℤ, algebraMap ℤ (Zsqrtd (-1)) r = x := by
  have h : star x = x := hx (Multiplicative.ofAdd 1)
  have him : x.im = 0 := by
    have h2 : (star x).im = x.im := by rw [h]
    rw [Zsqrtd.im_star] at h2
    omega
  exact ⟨x.re, by ext <;> simp [him]⟩

/-- **反例的见证自同态** ✓：`x ↦ re x` ✓（即 `⟨u, v⟩ ↦ u` ✓）—— `ℤ`-线性 ✓。
**⚠ 为何取它** ✓：迹形式给出的像 ⊆ `2ℤ`-型子格 ✓ ⟹ 「坐标读出」**不在** `δ` 的像内 ✓。 -/
def reEnd267 : Module.End ℤ (Zsqrtd (-1)) where
  toFun x := (x.re : Zsqrtd (-1))
  map_add' x y := by simp
  map_smul' z x := by
    show ((z • x).re : Zsqrtd (-1)) = z • (x.re : Zsqrtd (-1))
    rw [Algebra.smul_def, Zsqrtd.re_mul, Algebra.smul_def]
    simp

/-- `star (√(-1)) = -√(-1)` ✓。 -/
lemma star_sqrtd267 : star (Zsqrtd.sqrtd : Zsqrtd (-1)) = -(Zsqrtd.sqrtd : Zsqrtd (-1)) := by
  ext <;> simp

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 `δ` 非满射** ✓✅（**反例的核心** ✓）：设 `δ x = re` ✓，在 `y = 1` ✓ 与 `y = √(-1)` ✓
两处取值 ✓ 得 `a + b = 1` ✓ 与 `(a - b) * √(-1) = 0` ✓（`a = coeff 1 x` ✓，`b = coeff (ofAdd 1) x` ✓）；
由**无零因子** ✓ 与 `√(-1) ≠ 0` ✓ 得 `a = b` ✓ ⟹ `2 * a = 1` ✓（于 `ℤ[i]` 中 ✓）；
取 `.re` ✓ 得 `2 * a.re = 1` ✓（`ℤ` 中 ✓）⟹ `omega` ✓ **矛盾** ✓。
**⚠ 机制** ✓（**注：本行的机检证明不用以下刻画** ✗，它只作**为何失败**的说明 ✓）：像中元素皆为
`a·id + b·conj` 形 ✓（`a, b ∈ ℤ[i]` ✓）⟹ 在 `ℤ`-基 `(1, i)` 下其**系数对**为 `(a + b, a - b)` ✓，
满足 `c ≡ d (mod 2)` ✓（于 `ℤ[i]` 中 ✓，因 `c - d = 2b` ✓）；而 `re` 的系数对为 `(1, 0)` ✓，
`1 ∉ 2ℤ[i]` ✗ ⟹ **不**在像内 ✓ ⟹ 非满射 ✓。
**🔴 不声称** ✗：**不**声称环档（加了模论输入的形 ✓）为假 ✗ —— 本条只否**朴素形** ✓。 -/
theorem not_surjective_deltaToEndRingHom_gaussianInt267 :
    ¬ Function.Surjective (BTier.deltaToEndRingHom zmod2_smul_int_comm267) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj reEnd267
  have h1 : BTier.deltaToEndRingHom zmod2_smul_int_comm267 x 1 = 1 := by
    rw [hx]
    rfl
  have hi : BTier.deltaToEndRingHom zmod2_smul_int_comm267 x (Zsqrtd.sqrtd : Zsqrtd (-1))
      = 0 := by
    rw [hx]
    rfl
  rw [delta_form_zmod2] at h1 hi
  simp only [mul_one, star_one] at h1
  rw [star_sqrtd267] at hi
  set a := x.coeff 1
  set b := x.coeff (Multiplicative.ofAdd 1)
  have hab : a = b := by
    have h0 : (a - b) * (Zsqrtd.sqrtd : Zsqrtd (-1)) = 0 := by
      rw [mul_neg, ← sub_eq_add_neg, ← sub_mul] at hi
      exact hi
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (by decide)
  have h2 : (2 : Zsqrtd (-1)) * a = 1 := by
    have h1' : a + b = 1 := h1
    rw [← hab] at h1'
    rwa [two_mul]
  have h3 : (2 * a).re = (1 : Zsqrtd (-1)).re := congrArg Zsqrtd.re h2
  rw [Zsqrtd.re_mul] at h3
  simp at h3
  omega

/-- **反例的秩** ✓：`ℤ[i] ≅ ℤ²` ✓（`ℤ`-线性等价 ✓：`x ↦ (re x, im x)` ✓）—— **有限自由** ✓ 且
`finrank_ℤ ℤ[i] = 2` ✓。**⚠ 工艺** ✓：`Module.finrank_finsupp` ✓ 对 `ℤ[i]` **不可用** ✗
（无基实例 ✗）⟹ 走**显式线性等价** ✓ ＋ `Module.finrank_prod` ✓。 -/
def zsqrtdNegOneLinearEquiv267 : Zsqrtd (-1) ≃ₗ[ℤ] ℤ × ℤ where
  toFun x := (x.re, x.im)
  invFun p := ⟨p.1, p.2⟩
  map_add' x y := by ext <;> simp
  map_smul' z x := by
    ext <;> simp [Algebra.smul_def, Zsqrtd.re_mul, Zsqrtd.im_mul]
  left_inv x := by ext <;> rfl
  right_inv p := by ext <;> rfl

lemma moduleFinite_gaussianInt267 : Module.Finite ℤ (Zsqrtd (-1)) :=
  Module.Finite.equiv zsqrtdNegOneLinearEquiv267.symm

lemma moduleFree_gaussianInt267 : Module.Free ℤ (Zsqrtd (-1)) :=
  Module.Free.of_equiv zsqrtdNegOneLinearEquiv267.symm

-- 本节的 `Module.Free` 行以**局部实例**注册 ✓（供 `Module.Projective.of_free` ✓ 消费 ✓；
-- **限本节** ✓，**不**污染全库实例表 ✓；**不**用 `letI` ✗）。
attribute [local instance] moduleFree_gaussianInt267

lemma finrank_gaussianInt267 : Module.finrank ℤ (Zsqrtd (-1)) = 2 := by
  rw [zsqrtdNegOneLinearEquiv267.finrank_eq, Module.finrank_prod, Module.finrank_self]

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 机检反例（假设表逐条为真 ＋ 结论为假）** ✓✅：`R = ℤ` ✓／`S = ℤ[i]` ✓／
`G = Multiplicative (ZMod 2)` ✓（共轭 ✓）上**同时**成立 ✓：
**(i)** `S` **无零因子** ✓；**(ii)** 作用**忠实** ✓；**(iii)** `hRG` ✓；**(iv)** `δ` **单射** ✓
（由 r266 ✓ 判据 ✓）；**(v)** `S` 对 `ℤ` **有限** ✓；**(vi)** **自由** ✓；
**(vii)** **`finrank_ℤ S = |G| = 2`** ✓；**(viii)** `δ` **非满射** ✓
—— **(i)--(vii) 全真而 (viii) 为真** ⟹ `NaiveRingTierReduction267` **假** ✗（下件 ✓）。
**⚠ 意义（L1 ＋ L19** ✓**）**：本件同时是**判据的非空洞性对照** ✓（`δ` **单射**款在**非域**
的**无零因子环** ✓ 上发射 ✓，与 §4.72.3 的域档 ✓ 分列 ✓）。 -/
theorem ringTier_counterexample267 :
    NoZeroDivisors (Zsqrtd (-1))
      ∧ FaithfulSMul (Multiplicative (ZMod 2)) (Zsqrtd (-1))
      ∧ (∀ (g : Multiplicative (ZMod 2)) (r : ℤ) (x : Zsqrtd (-1)),
          g • (r • x) = r • (g • x))
      ∧ (∀ (g : Multiplicative (ZMod 2)) (r : ℤ),
          g • algebraMap ℤ (Zsqrtd (-1)) r = algebraMap ℤ (Zsqrtd (-1)) r)
      ∧ (∀ x : Zsqrtd (-1), (∀ g : Multiplicative (ZMod 2), g • x = x) →
          ∃ r : ℤ, algebraMap ℤ (Zsqrtd (-1)) r = x)
      ∧ Function.Injective (BTier.deltaToEndRingHom zmod2_smul_int_comm267)
      ∧ Module.Finite ℤ (Zsqrtd (-1))
      ∧ Module.Free ℤ (Zsqrtd (-1))
      ∧ Module.Projective ℤ (Zsqrtd (-1))
      ∧ Module.finrank ℤ (Zsqrtd (-1)) = Fintype.card (Multiplicative (ZMod 2))
      ∧ ¬ Function.Surjective (BTier.deltaToEndRingHom zmod2_smul_int_comm267) :=
  ⟨inferInstance, inferInstance, zmod2_smul_int_comm267, fixed_algebraMap_gaussianInt267,
    fixed_ring_gaussianInt267, zmod2_delta_injective267,
    moduleFinite_gaussianInt267, moduleFree_gaussianInt267, inferInstance,
    by rw [finrank_gaussianInt267, card_multiplicative_zmod_two],
    not_surjective_deltaToEndRingHom_gaussianInt267⟩

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 朴素环档归约的否定（形状锁定件的否定）** ✓✅。 -/
theorem not_naiveRingTierReduction267 : ¬ NaiveRingTierReduction267 := by
  intro h
  obtain ⟨_, hfaith, hRG, hfix, hfixring, hinj, hfin, hfree, hproj, hrank, hnotsurj⟩ :=
    ringTier_counterexample267
  exact hnotsurj (h ℤ (Zsqrtd (-1)) (Multiplicative (ZMod 2)) hRG inferInstance hfaith
    hfix hfixring hfin hfree hproj hrank hinj)

#print axioms mul_zmod2_cases267
#print axioms zmod2_gen_mul_self267
#print axioms conjSmul267_mul_smul
#print axioms conjSmul267_faithful
#print axioms zmod2_smul_int_comm267
#print axioms conjSmul267_intCast
#print axioms fixed_algebraMap_gaussianInt267
#print axioms fixed_ring_gaussianInt267
#print axioms delta_form_zmod2
#print axioms zmod2_delta_injective267
#print axioms reEnd267
#print axioms not_surjective_deltaToEndRingHom_gaussianInt267
#print axioms zsqrtdNegOneLinearEquiv267
#print axioms moduleFinite_gaussianInt267
#print axioms moduleFree_gaussianInt267
#print axioms star_sqrtd267
#print axioms finrank_gaussianInt267
#print axioms ringTier_counterexample267
#print axioms not_naiveRingTierReduction267

end RingTierCounterexample267
/-! ### 4.74 环档（`R` 非域）的**正确模论输入**：**迹形式幺模性** —— 二次代数族（第 268 轮）

**⚠ 起点** ✓（承 §4.73 ✓）：第 267 轮**机检否决**了环档的**朴素归约** ✗（`NaiveRingTierReduction267` ✓：
`ℤ ⊆ ℤ[i]` ＋ 忠实 ✓ ＋ 不动环相等 ✓ ＋ `S` 有限自由秩 `|G|` ✓ ＋ `δ` 单射 ✓ ⟹ `δ` 满射 ✗ —— **假** ✗）。
本轮找**正确的**环档输入 ✓ 并给**机检**读数 ✓。

**载体** ✓：`QuadraticAlgebra R a b` ✓（mathlib ✓：`ω² = a + bω` ✓，`R`-基 `(1, ω)` ✓，
`star` ＝ 共轭 ✓，`trace` ✓／`norm` ✓），`G = Multiplicative (ZMod 2)` ✓ 经 `star` 作用 ✓。
**⚠ 与 §4.73 的换算** ✓：本件参数 `(a, b)` 与 `(T, N)`（`α² = Tα − N` ✓）的关系为 `T = b` ✓、
`N = -a` ✓ ⟹ **判别式** `T² − 4N = b² + 4a` ✓ ＝ 迹形式 Gram 行列式 ✓（`qaGram268_det` ✓）。

**🔴🔴 主定理（机检 ✓✅，**双方向**）** ✓：`δ` **满射** ⟺ **迹形式（Gram 矩阵）幺模** ✓
（`surjective_deltaToEndRingHom_quadratic268_iff` ✓）。**两方向的机制** ✓：
**(⟸)** ✓ 单位 `2ω − b` ✓（其范数 ＝ `-(b² + 4a)` ✓，`qaNormQaDiff268` ✓）⟹ **显式预像** ✓；
**(⟹)** ✓ 取 `R`-线性自同态 `z ↦ z.im` ✓ 的预像 ✓ ⟹ `2ω − b` 是**单位** ✓。

**⚠ 强度序（逐条，方向明确 ✓；本轮的核心交付 ✓）**：

| # | 命题 | 状态 | 机检依据 |
|---|---|---|---|
| ① | 迹形式幺模 ⟹ `δ` 满射 | **已证** ✓✅ | `surjective_deltaToEndRingHom_quadratic268_of_isUnit` ✓ |
| ② | `δ` 满射 ⟹ 迹形式幺模 | **已证** ✓✅ | `isUnit_disc268_of_surjective_deltaToEndRingHom` ✓（①＋② ＝ `⟺` ✓） |
| ③ | 迹形式幺模 ⟹ **迹满射**（`∃ s, trace s = 1`）| **已证** ✓✅ | `qa_exists_trace_eq_one268_of_isUnit` ✓（显式 `s = ⟨2ua, ub⟩` ✓，`u` ＝ 判别式的逆 ✓） |
| ④ | 迹满射 ⟹ `δ` 满射 | **已否决** ✗ | 见证 ②：`ℤ[ω]/(ω² − ω + 2)` ✓（`trace ω = 1` ✓ 而 `δ` 非满射 ✓） |
| ⑤ | `\|G\|` 在 `R` 中可逆 ⟹ `δ` 满射 | **已否决** ✗ | 见证 ③：`R = 𝔽₃[X]` ✓（`IsUnit (2 : R)` ✓ 而 `δ` 非满射 ✓） |
| ⑥ | `R[G]`-**自由秩一** ⟹ `δ` 满射 | **已否决** ✗ | 见证 ②：正规基 `ω` ✓（`x ↦ x • ω` **双射** ✓）而 `δ` 非满射 ✓ |
| ⑦ | `\|G\|` 可逆 与 迹形式幺模 | **不可比** ✗ | `(ℤ, a=0, b=1)`：幺模 ✓ 而 `2` 非单位 ✓；`(𝔽₃[X], a=X, b=0)`：`2` 可逆 ✓ 而 `X` 非单位 ✓ |

⟹ **③＋④**：「迹满射」**严格弱于**「迹形式幺模」✓ 且**单独不足** ✓（源侧的
「`∃ s, Tr s = 1`」形输入**被否决** ✗）；**⑤**：源侧 section-based 路线所依赖的
「`|G|` 可逆」**单独不足** ✗；**⑥**：r266 ✓ 登记的 `R[G]`-模两行路线的**秩一自由**形**被否决** ✗
（**⚠ 不等于**否决其**投射**形 ✗ —— 后者本轮**未判定** ✓）。

**指引（L19 正例 ＋ L1 非空性）** ✓：**反例侧**三条 ✗（见证 ① 高斯 `ℤ[i]` ✓；见证 ② `ℤ[(1+√-7)/2]` ✓；
见证 ③ `𝔽₃[X][ω]/(ω² − X)` ✓）；**非空性侧**两条 ✓✅：**分裂档** `(ℤ, a=0, b=1)`
（`δ` **双射** ✓，`qa_split268_bijective` ✓）与**高斯档在 `ℚ` 上**（`δ` **双射** ✓，
`qa_gaussianRat268_bijective` ✓ —— 与见证 ① 对照 ✓：**同一** `(a,b) = (-1,0)` ✓ 在 `ℤ` 上**非满射** ✗、
在 `ℚ` 上**双射** ✓ ⟹ **判别式 `-4` 是否为单位**正是分界 ✓）。
**⚠ 高斯档与 §4.73 载体的桥** ✓（**机检 ✓✅**）：本件载体在 `(ℤ, -1, 0)` 上满足 `ℤ[i]` 的定义关系 ✓
（`ω² = -1` ✓，`qa_gaussian268_omega_sq` ✓；`star ω = -ω` ✓，`qa_gaussian268_star_omega` ✓），
且**环同构** `qaGaussianIntEquiv268 : QuadraticAlgebra ℤ (-1) 0 ≃+* Zsqrtd (-1)` ✓ 与**共轭相容** ✓
（`qaGaussianIntEquiv268_star` ✓）⟹ 与 §4.73 ✓ 的 `Zsqrtd (-1)` 载体是**同一对象** ✓
（该侧结论 `not_surjective_deltaToEndRingHom_gaussianInt267` ✓ **不重证** ✗）。

**🔴 一般档（任意有限 `G`）** ✓：充分性**形状锁定**为 `TraceUnimodularSufficiency268` ✓
（`tr : S →ₗ[R] R` ✓ `G`-不变 ✓ 对称 ✓ ＋ **配对满** ✓ ＝ 迹形式幺模 ✓ ＋ `S` 对 `R` 有限 ✓
＋ `δ` 单射 ⟹ `δ` 满射 ✓）—— **未证** ✗（登记 ✓，`traceUnimodularSufficiency268_registered` ✓）；
本轮落的是其 **`G = C₂`／秩 2** 档 ✓（**且更强**：`⟺` ✓，**无需单射假设** ✓）。
**⚠ 后注（第 269 轮** ✓**）** ✓：本条登记的 `TraceUnimodularSufficiency268` ✓ 已被**机检否决** ✗
（`not_traceUnimodularSufficiency268` ✓，§4.75 ✓）—— 其假设「`tr` `G`-不变」**严格弱于**本条的
正确输入（**乘法迹** ✓）；本条主定理 ✓ 与秩 2 `⟺` ✓ **不受影响** ✓。

**⚠ 分类（规则 17）** ✓：本轮**未落**项**只有一条** ✓ ＝ `TraceUnimodularSufficiency268` ✓
（**证明义务** ✓，**非**观测数据 ✗、**非 (b) 类「可算未算」**✗）—— **无 (b) 类未算项** ✓
（高斯档与 §4.73 载体的**形式同构**本轮**已算完并落地** ✓：`qaGaussianIntEquiv268` ✓）。
**🔴 不声称** ✗：**不**声称一般档成立 ✗；**不**声称 `R[G]`-**投射**形被否决 ✗；
**不**声称两条源陈述已证 ✗；**不**声称 §4.73 的结论被重证 ✗。 -/

section QuadraticRingTier268

open scoped QuadraticAlgebra

variable {R : Type*} [CommRing R]

variable {R : Type*} [CommRing R]

/-- 共轭作用 -/
def qaConj268 (a b : R) (g : Multiplicative (ZMod 2)) (x : QuadraticAlgebra R a b) :
    QuadraticAlgebra R a b := if g = 1 then x else star x

variable {a b : R}

@[simp] lemma qaConj268_one (x : QuadraticAlgebra R a b) : qaConj268 a b 1 x = x := rfl

@[simp] lemma qaConj268_gen (x : QuadraticAlgebra R a b) :
    qaConj268 a b (Multiplicative.ofAdd 1) x = star x := by
  rw [qaConj268, if_neg (by decide : ¬ (Multiplicative.ofAdd (1 : ZMod 2) = 1))]

lemma qaConj268_mul_smul (g h : Multiplicative (ZMod 2)) (x : QuadraticAlgebra R a b) :
    qaConj268 a b (g * h) x = qaConj268 a b g (qaConj268 a b h x) := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;>
    rcases mul_zmod2_cases267 h with rfl | rfl <;>
    simp [qaConj268_one, qaConj268_gen, zmod2_gen_mul_self267, star_star]

lemma qaConj268_zero (g : Multiplicative (ZMod 2)) : qaConj268 a b g 0 = 0 := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [qaConj268_one, qaConj268_gen]

lemma qaConj268_add (g : Multiplicative (ZMod 2)) (x y : QuadraticAlgebra R a b) :
    qaConj268 a b g (x + y) = qaConj268 a b g x + qaConj268 a b g y := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [qaConj268_one, qaConj268_gen]

lemma qaConj268_mul (g : Multiplicative (ZMod 2)) (x y : QuadraticAlgebra R a b) :
    qaConj268 a b g (x * y) = qaConj268 a b g x * qaConj268 a b g y := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [qaConj268_one, qaConj268_gen]

lemma qaConj268_one' (g : Multiplicative (ZMod 2)) : qaConj268 a b g 1 = 1 := by
  rcases mul_zmod2_cases267 g with rfl | rfl <;> simp [qaConj268_one, qaConj268_gen]

local instance qaSMul268 : SMul (Multiplicative (ZMod 2)) (QuadraticAlgebra R a b) :=
  ⟨qaConj268 a b⟩

/-- 单点作用式 -/
lemma qaConj268_smul_def (g : Multiplicative (ZMod 2)) (x : QuadraticAlgebra R a b) :
    g • x = qaConj268 a b g x := rfl

local instance qaMSA268 : MulSemiringAction (Multiplicative (ZMod 2)) (QuadraticAlgebra R a b) where
  toSMul := qaSMul268
  one_smul x := qaConj268_one x
  mul_smul g h x := qaConj268_mul_smul g h x
  smul_zero g := qaConj268_zero g
  smul_add g x y := qaConj268_add g x y
  smul_mul g x y := qaConj268_mul g x y
  smul_one g := qaConj268_one' g

lemma qaSmulComm268 : ∀ (g : Multiplicative (ZMod 2)) (r : R)
    (x : QuadraticAlgebra R a b), g • (r • x) = r • (g • x) := by
  intro g r x
  rcases mul_zmod2_cases267 g with rfl | rfl
  · simp
  · rw [qaConj268_smul_def, qaConj268_gen, qaConj268_smul_def, qaConj268_gen]
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul,
        smul_eq_mul]
      ring
    · simp only [QuadraticAlgebra.im_star, QuadraticAlgebra.im_smul, smul_eq_mul]
      ring

/-- `trace (ω * ω)` -/
lemma qaTraceOmegaSq268 : QuadraticAlgebra.trace (a := a) (b := b)
    ((ω : QuadraticAlgebra R a b) * ω) = 2 * a + b ^ 2 := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
  simp [QuadraticAlgebra.trace_def]
  ring

/-- Gram 矩阵 -/
def qaGram268 (a b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![QuadraticAlgebra.trace (1 : QuadraticAlgebra R a b),
     QuadraticAlgebra.trace (ω : QuadraticAlgebra R a b);
     QuadraticAlgebra.trace (ω : QuadraticAlgebra R a b),
     QuadraticAlgebra.trace ((ω : QuadraticAlgebra R a b) * ω)]

lemma qaGram268_det : (qaGram268 a b).det = b ^ 2 + 4 * a := by
  rw [qaGram268, Matrix.det_fin_two]
  simp [qaTraceOmegaSq268]
  ring

/-- `2ω − b`（判别式载体） -/
def qaDiff268 (a b : R) : QuadraticAlgebra R a b :=
  (2 : QuadraticAlgebra R a b) * ω - algebraMap R (QuadraticAlgebra R a b) b

lemma qaDiff268_def : qaDiff268 a b
    = (2 : QuadraticAlgebra R a b) * ω - algebraMap R (QuadraticAlgebra R a b) b := rfl

lemma qaNormQaDiff268 : QuadraticAlgebra.norm (qaDiff268 a b) = -(b ^ 2 + 4 * a) := by
  rw [qaDiff268, QuadraticAlgebra.norm_def]
  simp
  ring

lemma qaIsUnitQaDiff268 : IsUnit (qaDiff268 a b) ↔ IsUnit (b ^ 2 + 4 * a) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, qaNormQaDiff268]
  exact IsUnit.neg_iff _

/-! #### `δ` 的两项展开式 -/

/-- **`δ` 的两项展开式** ✓：`G` 只有两个元素 ✓，故求和坍缩为两项 ✓。 -/
lemma qaDeltaForm268 (x : SkewMonoidAlgebra (QuadraticAlgebra R a b) (Multiplicative (ZMod 2)))
    (t : QuadraticAlgebra R a b) :
    BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)) x t
      = x.coeff 1 * t + x.coeff (Multiplicative.ofAdd 1) * star t := by
  induction x using SkewMonoidAlgebra.induction_on with
  | zero => simp
  | add x z hx hz =>
    rw [map_add, LinearMap.add_apply, hx, hz]
    simp only [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
    ring
  | single g s =>
    rw [show BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b))
          (SkewMonoidAlgebra.single g s)
        = BTier.deltaToEndAdd (qaSmulComm268 (a := a) (b := b))
          (SkewMonoidAlgebra.single g s) from rfl,
      BTier.deltaToEndAdd_single, Module.End.mul_apply]
    rcases mul_zmod2_cases267 g with rfl | rfl
    · change s * qaConj268 a b (1 : Multiplicative (ZMod 2)) t
        = (SkewMonoidAlgebra.single 1 s).coeff 1 * t
          + (SkewMonoidAlgebra.single 1 s).coeff (Multiplicative.ofAdd 1) * star t
      rw [qaConj268_one, SkewMonoidAlgebra.coeff_single_apply, if_pos rfl,
        SkewMonoidAlgebra.coeff_single_apply,
        if_neg (by decide : ¬ ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1))]
      ring
    · change s * qaConj268 a b (Multiplicative.ofAdd 1) t
        = (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) s).coeff 1 * t
          + (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) s).coeff
              (Multiplicative.ofAdd 1) * star t
      rw [qaConj268_gen, SkewMonoidAlgebra.coeff_single_apply,
        if_neg (by decide : ¬ (Multiplicative.ofAdd (1 : ZMod 2) = 1)),
        SkewMonoidAlgebra.coeff_single_apply, if_pos rfl]
      ring

/-- **两个 `R`-线性自同态相等 ⟸ 在 `(1, ω)` 上相等** ✓。 -/
lemma qaEndExt268 {f g : Module.End R (QuadraticAlgebra R a b)}
    (h1 : f 1 = g 1) (hω : f (ω : QuadraticAlgebra R a b) = g ω) : f = g := by
  refine LinearMap.ext fun z => ?_
  have hz : z = z.re • (1 : QuadraticAlgebra R a b) + z.im • (ω : QuadraticAlgebra R a b) := by
    have h := QuadraticAlgebra.mk_eq_add_smul_omega (a := a) (b := b) z.re z.im
    rw [Algebra.algebraMap_eq_smul_one] at h
    rw [← h]
  rw [hz]
  simp only [map_add, map_smul, h1, hω]

/-- **共轭在 `ω` 上的取值** ✓：`star ω = b − ω` ✓。 -/
lemma qaStarOmega268 : star (ω : QuadraticAlgebra R a b) = algebraMap R _ b - ω := by
  rw [QuadraticAlgebra.star_eq, QuadraticAlgebra.trace_omega]

/-- **`ω − star ω = 2ω − b`** ✓。 -/
lemma qaOmegaSubStarOmega268 :
    (ω : QuadraticAlgebra R a b) - star ω = qaDiff268 a b := by
  rw [qaStarOmega268, qaDiff268]
  ring

/-- **`δ` 在两项元素上的取值** ✓。 -/
lemma qaDeltaPair268 (u v : QuadraticAlgebra R a b) (t : QuadraticAlgebra R a b) :
    BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b))
      (SkewMonoidAlgebra.single 1 u
        + SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) v) t = u * t + v * star t := by
  rw [qaDeltaForm268]
  have hσ : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hσ' : ¬ ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1) := by decide
  simp [hσ, hσ']

/-- **迹形式幺模** ✓。 -/
def QaTraceUnimodular268 (a b : R) : Prop := IsUnit (qaGram268 a b).det

theorem qaTraceUnimodular268_iff : QaTraceUnimodular268 a b ↔ IsUnit (b ^ 2 + 4 * a) := by
  rw [QaTraceUnimodular268, qaGram268_det]

lemma qaExistsMulEqOne268 (h : IsUnit (b ^ 2 + 4 * a)) :
    ∃ y : QuadraticAlgebra R a b, y * qaDiff268 a b = 1 := by
  have h2 : IsUnit (qaDiff268 a b) := (qaIsUnitQaDiff268 (a := a) (b := b)).mpr h
  obtain ⟨y, _hy, hy'⟩ := isUnit_iff_exists.mp h2
  exact ⟨y, hy'⟩

set_option maxHeartbeats 1000000 in
/-- **正向（⟸）：迹形式幺模 ⟹ `δ` 满射** ✓：显式预像构造 ✓。 -/
theorem surjective_deltaToEndRingHom_quadratic268_of_isUnit (h : IsUnit (b ^ 2 + 4 * a)) :
    Function.Surjective (BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b))) := by
  intro f
  obtain ⟨y, hy⟩ := qaExistsMulEqOne268 (a := a) (b := b) h
  have hu : y * (f ω + f 1 * (ω - algebraMap R _ b)) * qaDiff268 a b
      = f ω + f 1 * (ω - algebraMap R _ b) := by
    rw [mul_assoc, mul_comm (f ω + f 1 * (ω - algebraMap R _ b)) (qaDiff268 a b),
      ← mul_assoc, hy, one_mul]
  refine ⟨SkewMonoidAlgebra.single 1 (y * (f ω + f 1 * (ω - algebraMap R _ b)))
    + SkewMonoidAlgebra.single (Multiplicative.ofAdd 1)
        (f 1 - y * (f ω + f 1 * (ω - algebraMap R _ b))), ?_⟩
  refine qaEndExt268 ?_ ?_
  · rw [qaDeltaPair268]
    simp only [mul_one, star_one]
    ring
  · rw [qaDeltaPair268, qaStarOmega268]
    have key : y * (f ω + f 1 * (ω - algebraMap R _ b)) * ω
        + (f 1 - y * (f ω + f 1 * (ω - algebraMap R _ b)))
          * (algebraMap R _ b - ω)
        = y * (f ω + f 1 * (ω - algebraMap R _ b)) * qaDiff268 a b
          - f 1 * (ω - algebraMap R _ b) := by
      rw [qaDiff268]
      ring
    rw [key, hu]
    ring

set_option maxHeartbeats 1000000 in
/-- **反向（⟹）：`δ` 满射 ⟹ 迹形式幺模** ✓。 -/
theorem isUnit_disc268_of_surjective_deltaToEndRingHom
    (h : Function.Surjective (BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)))) :
    IsUnit (b ^ 2 + 4 * a) := by
  obtain ⟨x, hx⟩ := h
    ({ toFun := fun z => algebraMap R (QuadraticAlgebra R a b) z.im
       map_add' := by intro p q; simp
       map_smul' := by intro r p; simp [Algebra.smul_def] } :
      Module.End R (QuadraticAlgebra R a b))
  have h1 : x.coeff 1 + x.coeff (Multiplicative.ofAdd 1) = 0 := by
    have hh := congrFun (congrArg DFunLike.coe hx) (1 : QuadraticAlgebra R a b)
    rw [qaDeltaForm268] at hh
    simpa using hh
  have hω : x.coeff 1 * qaDiff268 a b = 1 := by
    have hh := congrFun (congrArg DFunLike.coe hx) (ω : QuadraticAlgebra R a b)
    rw [qaDeltaForm268, qaStarOmega268] at hh
    have hcoe : x.coeff (Multiplicative.ofAdd 1) = -x.coeff 1 :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h1)
    have hh' : x.coeff 1 * ω + (-x.coeff 1) * (algebraMap R _ b - ω) = 1 := by
      simpa [hcoe] using hh
    have e : x.coeff 1 * ω + (-x.coeff 1) * (algebraMap R _ b - ω)
        = x.coeff 1 * qaDiff268 a b := by
      rw [qaDiff268]
      ring
    rw [e] at hh'
    exact hh'
  have hunit : IsUnit (qaDiff268 a b) :=
    isUnit_iff_exists.mpr ⟨x.coeff 1, by rw [mul_comm]; exact hω, hω⟩
  exact (qaIsUnitQaDiff268 (a := a) (b := b)).mp hunit

set_option maxHeartbeats 1000000 in
/-- **主定理：`δ` 满射 ⟺ 迹形式幺模** ✓✅。 -/
theorem surjective_deltaToEndRingHom_quadratic268_iff :
    Function.Surjective (BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)))
      ↔ QaTraceUnimodular268 a b :=
  ⟨fun h => by rw [qaTraceUnimodular268_iff]; exact isUnit_disc268_of_surjective_deltaToEndRingHom h,
   fun h => surjective_deltaToEndRingHom_quadratic268_of_isUnit (a := a) (b := b) (qaTraceUnimodular268_iff.mp h)⟩

/-! #### 268.5 核判别 ＋ 单射判别 -/

/-- **`δ x = 0` 的系数判别** ✓。 -/
lemma qaDeltaEqZero268_iff
    (x : SkewMonoidAlgebra (QuadraticAlgebra R a b) (Multiplicative (ZMod 2))) :
    BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)) x = 0
      ↔ x.coeff 1 + x.coeff (Multiplicative.ofAdd 1) = 0
        ∧ x.coeff 1 * qaDiff268 a b = 0 := by
  have hσ : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hσ' : ¬ ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1) := by decide
  constructor
  · intro hx
    have h1 : x.coeff 1 + x.coeff (Multiplicative.ofAdd 1) = 0 := by
      have hh := congrFun (congrArg DFunLike.coe hx) (1 : QuadraticAlgebra R a b)
      rw [qaDeltaForm268] at hh
      simpa using hh
    refine ⟨h1, ?_⟩
    have hω := congrFun (congrArg DFunLike.coe hx) (ω : QuadraticAlgebra R a b)
    rw [qaDeltaForm268, qaStarOmega268] at hω
    have hcoe : x.coeff (Multiplicative.ofAdd 1) = -x.coeff 1 :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h1)
    have e : x.coeff 1 * ω + x.coeff (Multiplicative.ofAdd 1) * (algebraMap R _ b - ω)
        = x.coeff 1 * qaDiff268 a b := by
      rw [hcoe, qaDiff268]
      ring
    rw [e] at hω
    simpa using hω
  · rintro ⟨h1, h2⟩
    have hcoe : x.coeff (Multiplicative.ofAdd 1) = -x.coeff 1 :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h1)
    refine qaEndExt268 (f := BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)) x)
      (g := 0) ?_ ?_
    · rw [qaDeltaForm268]
      simpa using h1
    · rw [qaDeltaForm268, qaStarOmega268]
      have e : x.coeff 1 * ω + x.coeff (Multiplicative.ofAdd 1) * (algebraMap R _ b - ω)
          = x.coeff 1 * qaDiff268 a b := by
        rw [hcoe, qaDiff268]
        ring
      rw [e, h2]
      rfl

/-- **单射判别** ✓：`δ` 单射 ⟺ `2ω − b` **非零因子** ✓（＝**分离性**判据 ✓）。 -/
theorem injective_deltaToEndRingHom_quadratic268_iff :
    Function.Injective (BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)))
      ↔ ∀ u : QuadraticAlgebra R a b, u * qaDiff268 a b = 0 → u = 0 := by
  have hσ : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  have hσ' : ¬ ((1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 1) := by decide
  constructor
  · intro hinj u hu
    have hker : BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b))
        (SkewMonoidAlgebra.single (1 : Multiplicative (ZMod 2)) u
          + SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (-u)) = 0 := by
      rw [qaDeltaEqZero268_iff]
      constructor
      · simp [SkewMonoidAlgebra.coeff_add, hσ, hσ']
      · simp only [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply,
          SkewMonoidAlgebra.coeff_single_apply, hσ]
        simpa using hu
    have hz : SkewMonoidAlgebra.single (1 : Multiplicative (ZMod 2)) u
        + SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (-u) = 0 :=
      hinj (by rw [hker]; exact (map_zero _).symm)
    have hc := congrArg (fun z => z.coeff 1) hz
    simp only [SkewMonoidAlgebra.coeff_add, Finsupp.add_apply,
      SkewMonoidAlgebra.coeff_single_apply, hσ, SkewMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hc
    simpa using hc
  · intro hcond x y hxy
    have hzero : BTier.deltaToEndRingHom (qaSmulComm268 (a := a) (b := b)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [qaDeltaEqZero268_iff] at hzero
    have hc1 : (x - y).coeff 1 = 0 := hcond _ hzero.2
    have hcσ : (x - y).coeff (Multiplicative.ofAdd 1) = 0 := by
      have h := hzero.1
      rw [hc1, zero_add] at h
      exact h
    have hcoeff : (x - y).coeff = 0 := Finsupp.ext fun g => by
      rcases mul_zmod2_cases267 g with rfl | rfl
      · exact hc1
      · exact hcσ
    exact sub_eq_zero.mp (SkewMonoidAlgebra.coeff_inj.mp (by
      rw [hcoeff, SkewMonoidAlgebra.coeff_zero]))

/-! #### 268.6 判别式元素的坐标式 -/

/-- **`u * (2ω − b)` 的实部** ✓。 -/
lemma qaMulQaDiff268_re (u : QuadraticAlgebra R a b) :
    (u * qaDiff268 a b).re = 2 * a * u.im - b * u.re := by
  simp [qaDiff268]
  ring

/-- **`u * (2ω − b)` 的虚部** ✓。 -/
lemma qaMulQaDiff268_im (u : QuadraticAlgebra R a b) :
    (u * qaDiff268 a b).im = 2 * u.re + b * u.im := by
  simp [qaDiff268]
  ring

/-- **`u * (2ω − b) = 0` 的线性方程组形** ✓（单射判别各见证的公共工具 ✓）。 -/
lemma qaMulQaDiff268_eq_zero_iff (u : QuadraticAlgebra R a b) :
    u * qaDiff268 a b = 0 ↔
      2 * a * u.im - b * u.re = 0 ∧ 2 * u.re + b * u.im = 0 := by
  constructor
  · intro h
    exact ⟨by
        have h' := congrArg QuadraticAlgebra.re h
        rw [qaMulQaDiff268_re] at h'
        simpa using h',
      by
        have h' := congrArg QuadraticAlgebra.im h
        rw [qaMulQaDiff268_im] at h'
        simpa using h'⟩
  · rintro ⟨h1, h2⟩
    apply QuadraticAlgebra.ext
    · rw [qaMulQaDiff268_re]; exact h1
    · rw [qaMulQaDiff268_im]; exact h2

/-! #### 268.7 见证（L1 ＋ 反例） -/

/-- **见证 ①：高斯整数档 `ℤ[i]`（`R = ℤ`，`a = −1`，`b = 0`）—— 迹形式**非**幺模** ✗。 -/
theorem qa_gaussian268_not_isUnit : ¬ IsUnit ((0 : ℤ) ^ 2 + 4 * (-1)) := by
  have h4 : (0 : ℤ) ^ 2 + 4 * (-1) = -4 := by norm_num
  rw [h4]
  intro hu
  obtain ⟨y, hy, _⟩ := isUnit_iff_exists.mp hu
  omega

/-- **见证 ①′：`δ` 非满射** ✗（由主定理 ＋ 上件 ✓ —— **与 r267 的机检结论同调** ✓）。 -/
theorem qa_gaussian268_not_surjective :
    ¬ Function.Surjective (BTier.deltaToEndRingHom (R := ℤ)
      (S := QuadraticAlgebra ℤ (-1) 0) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := -1) (b := 0))) := by
  intro h
  exact qa_gaussian268_not_isUnit ((qaTraceUnimodular268_iff (a := -1) (b := 0)).mp
    ((surjective_deltaToEndRingHom_quadratic268_iff (a := -1) (b := 0)).mp h))

/-- **见证 ②：`ℤ[ω]/(ω² − ω + 2)`（`R = ℤ`，`a = −2`，`b = 1`）—— 迹**满射**而迹形式非幺模** ✗。 -/
theorem qa_sqrt7_268_trace_surjective :
    ∃ s : QuadraticAlgebra ℤ (-2) 1, QuadraticAlgebra.trace s = 1 :=
  ⟨ω, by rw [QuadraticAlgebra.trace_omega]⟩

theorem qa_sqrt7_268_not_isUnit : ¬ IsUnit ((1 : ℤ) ^ 2 + 4 * (-2)) := by
  have h7 : (1 : ℤ) ^ 2 + 4 * (-2) = -7 := by norm_num
  rw [h7]
  intro hu
  obtain ⟨y, hy, _⟩ := isUnit_iff_exists.mp hu
  omega

theorem qa_sqrt7_268_not_surjective :
    ¬ Function.Surjective (BTier.deltaToEndRingHom (R := ℤ)
      (S := QuadraticAlgebra ℤ (-2) 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := -2) (b := 1))) := by
  intro h
  exact qa_sqrt7_268_not_isUnit ((qaTraceUnimodular268_iff (a := -2) (b := 1)).mp
    ((surjective_deltaToEndRingHom_quadratic268_iff (a := -2) (b := 1)).mp h))

/-- **见证 ②″：`δ` 单射** ✓（**分离性**判据 ✓：`2ω − 1` 非零因子 ✓）。 -/
theorem qa_sqrt7_268_injective :
    Function.Injective (BTier.deltaToEndRingHom (R := ℤ)
      (S := QuadraticAlgebra ℤ (-2) 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := -2) (b := 1))) := by
  rw [injective_deltaToEndRingHom_quadratic268_iff]
  intro u hu
  rw [qaMulQaDiff268_eq_zero_iff] at hu
  have hy : u.im = 0 := by omega
  have hx : u.re = 0 := by omega
  ext <;> assumption

/-! #### 268.8 正规基（`R[G]`-自由秩一）在见证 ② 上成立，而 `δ` 仍非满射 -/

/-- `x • ω` 的坐标式（`a = −2`，`b = 1`）✓。 -/
lemma qa_sqrt7_268_smul_omega :
    letI := BTier.monoidAlgebraModuleOfMulSemiringAction (R := ℤ)
      (S := QuadraticAlgebra ℤ (-2) 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := -2) (b := 1))
    ∀ x : MonoidAlgebra ℤ (Multiplicative (ZMod 2)),
      x • (ω : QuadraticAlgebra ℤ (-2) 1)
        = algebraMap ℤ _ (x.coeff (Multiplicative.ofAdd 1))
          + algebraMap ℤ _ (x.coeff 1 - x.coeff (Multiplicative.ofAdd 1)) * ω := by
  let _inst := BTier.monoidAlgebraModuleOfMulSemiringAction (R := ℤ)
    (S := QuadraticAlgebra ℤ (-2) 1) (G := Multiplicative (ZMod 2))
    (qaSmulComm268 (a := -2) (b := 1))
  intro x
  have hx : x = MonoidAlgebra.single (1 : Multiplicative (ZMod 2)) (x.coeff 1)
      + MonoidAlgebra.single (Multiplicative.ofAdd 1) (x.coeff (Multiplicative.ofAdd 1)) := by
    rw [← MonoidAlgebra.coeff_inj]
    ext g
    rcases mul_zmod2_cases267 g with rfl | rfl <;>
      simp [MonoidAlgebra.coeff_add]
  conv_lhs => rw [hx]
  rw [add_smul,
    BTier.monoidAlgebraModule_single_smul (R := ℤ) (S := QuadraticAlgebra ℤ (-2) 1)
      (G := Multiplicative (ZMod 2)) (qaSmulComm268 (a := -2) (b := 1)),
    BTier.monoidAlgebraModule_single_smul (R := ℤ) (S := QuadraticAlgebra ℤ (-2) 1)
      (G := Multiplicative (ZMod 2)) (qaSmulComm268 (a := -2) (b := 1))]
  rw [one_smul, qaConj268_smul_def, qaConj268_gen, qaStarOmega268]
  apply QuadraticAlgebra.ext <;> simp
  all_goals ring

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 见证 ②‴：`S` 是 `R[G]`-自由秩一（正规基 `ω` ✓），而 `δ` 非满射** ✗ ——
即 **`R[G]`-自由秩一 ⟹ `δ` 满射** 为**假** ✗（路线 β 的机检否决 ✓）。 -/
theorem qa_sqrt7_268_normalBasis :
    letI := BTier.monoidAlgebraModuleOfMulSemiringAction (R := ℤ)
      (S := QuadraticAlgebra ℤ (-2) 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := -2) (b := 1))
    Function.Bijective (fun x : MonoidAlgebra ℤ (Multiplicative (ZMod 2)) =>
      x • (ω : QuadraticAlgebra ℤ (-2) 1)) := by
  let _inst := BTier.monoidAlgebraModuleOfMulSemiringAction (R := ℤ)
    (S := QuadraticAlgebra ℤ (-2) 1) (G := Multiplicative (ZMod 2))
    (qaSmulComm268 (a := -2) (b := 1))
  constructor
  · intro x y hxy
    change x • (ω : QuadraticAlgebra ℤ (-2) 1) = y • ω at hxy
    rw [qa_sqrt7_268_smul_omega, qa_sqrt7_268_smul_omega] at hxy
    have h1 : x.coeff (Multiplicative.ofAdd 1) = y.coeff (Multiplicative.ofAdd 1) := by
      have h := congrArg QuadraticAlgebra.re hxy
      simpa using h
    have h2 : x.coeff 1 - x.coeff (Multiplicative.ofAdd 1)
        = y.coeff 1 - y.coeff (Multiplicative.ofAdd 1) := by
      have h := congrArg QuadraticAlgebra.im hxy
      simpa using h
    have h3 : x.coeff 1 = y.coeff 1 := by omega
    rw [← MonoidAlgebra.coeff_inj]
    ext g
    rcases mul_zmod2_cases267 g with rfl | rfl
    · exact h3
    · exact h1
  · intro z
    refine ⟨MonoidAlgebra.single (1 : Multiplicative (ZMod 2)) (z.re + z.im)
      + MonoidAlgebra.single (Multiplicative.ofAdd 1) z.re, ?_⟩
    change (MonoidAlgebra.single (1 : Multiplicative (ZMod 2)) (z.re + z.im)
      + MonoidAlgebra.single (Multiplicative.ofAdd 1) z.re) •
        (ω : QuadraticAlgebra ℤ (-2) 1) = z
    rw [qa_sqrt7_268_smul_omega]
    have hc1 : (MonoidAlgebra.single (1 : Multiplicative (ZMod 2)) (z.re + z.im)
        + MonoidAlgebra.single (Multiplicative.ofAdd 1) z.re).coeff 1 = z.re + z.im := by
      simp [MonoidAlgebra.coeff_add]
    have hcσ : (MonoidAlgebra.single (1 : Multiplicative (ZMod 2)) (z.re + z.im)
        + MonoidAlgebra.single (Multiplicative.ofAdd 1) z.re).coeff
          (Multiplicative.ofAdd 1) = z.re := by
      simp [MonoidAlgebra.coeff_add]
    rw [hc1, hcσ, show z.re + z.im - z.re = z.im by ring]
    apply QuadraticAlgebra.ext <;> simp

/-! #### 268.9 非空性见证（假设成立 ＋ 结论成立） -/

/-- **非空性 ①：分裂档 `ω² = ω`（`R = ℤ`，`a = 0`，`b = 1`）—— 迹形式幺模** ✓。 -/
theorem qa_split268_isUnit : IsUnit ((1 : ℤ) ^ 2 + 4 * 0) := by
  norm_num

theorem qa_split268_surjective :
    Function.Surjective (BTier.deltaToEndRingHom (R := ℤ)
      (S := QuadraticAlgebra ℤ 0 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := 0) (b := 1))) :=
  (surjective_deltaToEndRingHom_quadratic268_iff (a := 0) (b := 1)).mpr
    ((qaTraceUnimodular268_iff (a := 0) (b := 1)).mpr qa_split268_isUnit)

theorem qa_split268_injective :
    Function.Injective (BTier.deltaToEndRingHom (R := ℤ)
      (S := QuadraticAlgebra ℤ 0 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := 0) (b := 1))) := by
  rw [injective_deltaToEndRingHom_quadratic268_iff]
  intro u hu
  rw [qaMulQaDiff268_eq_zero_iff] at hu
  have hx : u.re = 0 := by omega
  have hy : u.im = 0 := by omega
  ext <;> assumption

theorem qa_split268_bijective :
    Function.Bijective (BTier.deltaToEndRingHom (R := ℤ)
      (S := QuadraticAlgebra ℤ 0 1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := 0) (b := 1))) :=
  ⟨qa_split268_injective, qa_split268_surjective⟩

/-- **非空性 ②：高斯档在 `ℚ` 上（`R = ℚ`）—— 迹形式幺模** ✓（`−4 ∈ ℚ^×` ✓）。 -/
theorem qa_gaussianRat268_bijective :
    Function.Bijective (BTier.deltaToEndRingHom (R := ℚ)
      (S := QuadraticAlgebra ℚ (-1) 0) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := -1) (b := 0))) := by
  have hU : IsUnit (((0 : ℚ)) ^ 2 + 4 * (-1)) := by
    rw [show ((0 : ℚ)) ^ 2 + 4 * (-1) = -4 by norm_num]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  refine ⟨?_, (surjective_deltaToEndRingHom_quadratic268_iff (a := -1) (b := 0)).mpr
    ((qaTraceUnimodular268_iff (a := -1) (b := 0)).mpr hU)⟩
  rw [injective_deltaToEndRingHom_quadratic268_iff]
  intro u hu
  rw [qaMulQaDiff268_eq_zero_iff] at hu
  have hy : u.im = 0 := by linarith [hu.1]
  have hx : u.re = 0 := by linarith [hu.2]
  ext <;> assumption

/-! #### 268.10 见证 ③：`|G|` 可逆**不足** —— `R = 𝔽₃[X]` -/

/-- **见证 ③（`a`）：`2` 在 `𝔽₃[X]` 中可逆** ✓（`2 = −1` ✓）。 -/
theorem qa_f3x268_isUnit_two : IsUnit (2 : Polynomial (ZMod 3)) := by
  have h2 : (2 : Polynomial (ZMod 3)) = Polynomial.C (2 : ZMod 3) :=
    (Polynomial.C_eq_natCast 2).symm
  have h3 : (2 : ZMod 3) = -1 := by decide
  rw [h2, h3, Polynomial.C_neg, Polynomial.C_1]
  exact isUnit_neg_one

/-- **见证 ③（`b`）：判别式 `X` 在 `𝔽₃[X]` 中非单位** ✗。 -/
theorem qa_f3x268_not_isUnit_disc :
    ¬ IsUnit ((0 : Polynomial (ZMod 3)) ^ 2 + 4 * Polynomial.X) := by
  have hd : (0 : Polynomial (ZMod 3)) ^ 2 + 4 * Polynomial.X = Polynomial.X := by
    have h4 : (4 : Polynomial (ZMod 3)) = 1 := by
      rw [show (4 : Polynomial (ZMod 3)) = Polynomial.C (4 : ZMod 3) from
        (Polynomial.C_eq_natCast 4).symm]
      rw [show (4 : ZMod 3) = 1 by decide, Polynomial.C_1]
    rw [h4]
    simp
  rw [hd]
  intro hu
  obtain ⟨p, hp, _⟩ := isUnit_iff_exists.mp hu
  have h0 : (0 : ZMod 3) = 1 := by
    have hh := congrArg (fun q : Polynomial (ZMod 3) => q.coeff 0) hp
    rw [Polynomial.coeff_X_mul_zero, Polynomial.coeff_one_zero] at hh
    exact hh
  exact zero_ne_one h0

/-- **见证 ③（`c`）：`δ` 单射** ✓（分离性判据 ✓：`2ω` 非零因子 ✓）。 -/
theorem qa_f3x268_injective :
    Function.Injective (BTier.deltaToEndRingHom (R := Polynomial (ZMod 3))
      (S := QuadraticAlgebra (Polynomial (ZMod 3)) Polynomial.X 0) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := Polynomial.X) (b := 0))) := by
  rw [injective_deltaToEndRingHom_quadratic268_iff]
  intro u hu
  rw [qaMulQaDiff268_eq_zero_iff] at hu
  have h2 : (2 : Polynomial (ZMod 3)) ≠ 0 := by
    intro h
    have hh : (2 : ZMod 3) = 0 := by
      have := congrArg (fun q : Polynomial (ZMod 3) => q.coeff 0) h
      simpa using this
    exact absurd hh (by decide)
  have hX : (Polynomial.X : Polynomial (ZMod 3)) ≠ 0 := Polynomial.X_ne_zero
  have hre : u.re = 0 := by
    have h := hu.2
    simp only [zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  have him : u.im = 0 := by
    have h := hu.1
    simp only [zero_mul, sub_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (mul_ne_zero h2 hX)
    · exact h'
  exact QuadraticAlgebra.ext hre him

/-- **🔴🔴 见证 ③：`|G| = 2` **可逆** ✓（`IsUnit (2 : 𝔽₃[X])` ✓）而 `δ` **非满射** ✗** ——
即「`|G|` 在 `R` 中可逆」**不足以**推出 `δ` 满射 ✗。 -/
theorem qa_f3x268_not_surjective :
    ¬ Function.Surjective (BTier.deltaToEndRingHom (R := Polynomial (ZMod 3))
      (S := QuadraticAlgebra (Polynomial (ZMod 3)) Polynomial.X 0) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (a := Polynomial.X) (b := 0))) := by
  intro h
  exact qa_f3x268_not_isUnit_disc
    ((qaTraceUnimodular268_iff (a := Polynomial.X) (b := 0)).mp
      ((surjective_deltaToEndRingHom_quadratic268_iff (a := Polynomial.X) (b := 0)).mp h))

/-! #### 268.11 高斯档的**定义关系**（与 r267 载体同构的机检依据） -/

/-- **`ω² = −1`** ✓（`ℤ[i]` 的乘法表 ✓）。 -/
theorem qa_gaussian268_omega_sq :
    (ω : QuadraticAlgebra ℤ (-1) 0) * ω = -1 := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  norm_num

/-- **`star ω = −ω`** ✓（复共轭 ✓）。 -/
theorem qa_gaussian268_star_omega :
    star (ω : QuadraticAlgebra ℤ (-1) 0) = -ω := by
  rw [qaStarOmega268]
  norm_num

/-- **🔴 高斯见证与 §4.73 载体的**环同构**（机检 ✓✅）：`QuadraticAlgebra ℤ (-1) 0 ≃+* Zsqrtd (-1)`
（坐标恒等 ✓，因 `(-1) + 0·ω` 与 `√(-1)²` 的乘法表逐字一致 ✓）。 -/
def qaGaussianIntEquiv268 : QuadraticAlgebra ℤ (-1) 0 ≃+* Zsqrtd (-1) where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv z := rfl
  right_inv z := rfl
  map_add' z w := by ext <;> simp
  map_mul' z w := by
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_mul, QuadraticAlgebra.re_mul]
    · simp only [Zsqrtd.im_mul, QuadraticAlgebra.im_mul]
      ring

/-- **同构与共轭相容** ✓：`star`（本族 ✓）↔ `Zsqrtd.star`（§4.73 ✓）✓。 -/
theorem qaGaussianIntEquiv268_star (z : QuadraticAlgebra ℤ (-1) 0) :
    qaGaussianIntEquiv268 (star z) = star (qaGaussianIntEquiv268 z) := by
  apply Zsqrtd.ext
  · simp only [qaGaussianIntEquiv268, QuadraticAlgebra.re_star, Zsqrtd.star_mk,
      RingEquiv.coe_mk, Equiv.coe_fn_mk]
    ring
  · simp only [qaGaussianIntEquiv268, QuadraticAlgebra.im_star, Zsqrtd.star_mk,
      RingEquiv.coe_mk, Equiv.coe_fn_mk]

/-! #### 268.12 一般档（任意有限 `G`）：迹形式幺模性的**充分性** —— 形状锁定（未证） -/

/-- **一般档的充分性陈述（形状锁定）** ✗：`tr : S →ₗ[R] R` 为 `G`-**不变** ✓ 的**对称** ✓ 迹泛函，
其**配对 `(x,y) ↦ tr (x*y)` 满** ✓（＝**迹形式幺模** ✓）＋ `S` 对 `R` **有限** ✓ ＋ `δ` **单射** ✓
⟹ `δ` **满射** ✓。
**⚠ 身份** ✓：本条是**猜想形**（**未证** ✗）—— 其 **`G = C₂`／秩 2 档**已由
`surjective_deltaToEndRingHom_quadratic268_iff` ✓（**第 268 轮** ✓）机检落地 ✓（**该档无需单射假设** ✓，
`⟺` 成立 ✓）；**一般档未证** ✗。 -/
def TraceUnimodularSufficiency268 : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (G : Type) [Group G] [Fintype G]
    [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (tr : S →ₗ[R] R),
    (∀ (g : G) (x : S), tr (g • x) = tr x) →
    (∀ x y : S, tr (x * y) = tr (y * x)) →
    (∀ φ : S →ₗ[R] R, ∃ y : S, ∀ x : S, φ x = tr (x * y)) →
    Module.Finite R S →
    Function.Injective (BTier.deltaToEndRingHom (R := R) (S := S) (G := G) hRG) →
    Function.Surjective (BTier.deltaToEndRingHom (R := R) (S := S) (G := G) hRG)

/-- **登记** ✗：`TraceUnimodularSufficiency268` ✓ **未证** ✗（**一般档** ✓）；本轮已落的是
其 **`G = C₂`／秩 2 档**（**且更强**：`⟺` ✓，`surjective_deltaToEndRingHom_quadratic268_iff` ✓）＋
**三条弱化路线的机检否决** ✓（迹满射 ✗／`|G|` 可逆 ✗／`R[G]`-自由秩一 ✗）。 -/
theorem traceUnimodularSufficiency268_registered : True := trivial

/-- **强度序（已证 ✓）：迹形式幺模 ⟹ **迹满射**（`∃ s, trace s = 1`）** ✓ —— 显式见证
`s = ⟨2ua, ub⟩`（`u` ＝ `b² + 4a` 的逆 ✓）：`trace s = 4ua + b²u = u (b² + 4a) = 1` ✓。
**⚠ 用点** ✓：本条把「迹形式幺模」与**更弱**的「迹满射」**严格分开** ✓（反向 ✗ 由
`qa_sqrt7_268_trace_surjective` ✓ ＋ `qa_sqrt7_268_not_surjective` ✓ 否决 ✓）。 -/
theorem qa_exists_trace_eq_one268_of_isUnit (h : IsUnit (b ^ 2 + 4 * a)) :
    ∃ s : QuadraticAlgebra R a b, QuadraticAlgebra.trace s = 1 := by
  obtain ⟨u, hu, _⟩ := isUnit_iff_exists.mp h
  have h1 : u * (b ^ 2 + 4 * a) = 1 := by rw [mul_comm]; exact hu
  refine ⟨⟨2 * u * a, u * b⟩, ?_⟩
  rw [QuadraticAlgebra.trace_def]
  show 2 * (2 * u * a) + b * (u * b) = 1
  rw [← h1]
  ring

/-! #### 268.13 公理门（逐条） -/

#print axioms qaConj268_mul_smul
#print axioms qaSmulComm268
#print axioms qaTraceOmegaSq268
#print axioms qaGram268_det
#print axioms qaNormQaDiff268
#print axioms qaIsUnitQaDiff268
#print axioms qaDeltaForm268
#print axioms qaEndExt268
#print axioms qaStarOmega268
#print axioms qaDeltaPair268
#print axioms qaTraceUnimodular268_iff
#print axioms qaExistsMulEqOne268
#print axioms surjective_deltaToEndRingHom_quadratic268_of_isUnit
#print axioms isUnit_disc268_of_surjective_deltaToEndRingHom
#print axioms surjective_deltaToEndRingHom_quadratic268_iff
#print axioms qaDeltaEqZero268_iff
#print axioms injective_deltaToEndRingHom_quadratic268_iff
#print axioms qaMulQaDiff268_eq_zero_iff
#print axioms qa_gaussian268_not_isUnit
#print axioms qa_gaussian268_not_surjective
#print axioms qa_gaussian268_omega_sq
#print axioms qa_gaussian268_star_omega
#print axioms qaGaussianIntEquiv268
#print axioms qaGaussianIntEquiv268_star
#print axioms qa_exists_trace_eq_one268_of_isUnit
#print axioms qa_sqrt7_268_trace_surjective
#print axioms qa_sqrt7_268_not_isUnit
#print axioms qa_sqrt7_268_not_surjective
#print axioms qa_sqrt7_268_injective
#print axioms qa_sqrt7_268_smul_omega
#print axioms qa_sqrt7_268_normalBasis
#print axioms qa_split268_isUnit
#print axioms qa_split268_surjective
#print axioms qa_split268_injective
#print axioms qa_split268_bijective
#print axioms qa_gaussianRat268_bijective
#print axioms qa_f3x268_isUnit_two
#print axioms qa_f3x268_not_isUnit_disc
#print axioms qa_f3x268_injective
#print axioms qa_f3x268_not_surjective
#print axioms traceUnimodularSufficiency268_registered

end QuadraticRingTier268

/-! ### 4.75 接线档的**迹形式幺模性**：一般档形状锁定件**被机检否决** ＋ 接线环上的**判别式障碍** ＋ `T` 的**加强机制**（第 269 轮）

**⚠ 起点** ✓（承 §4.74 ✓）：第 268 轮把环档的**正确输入**锁定为**迹形式幺模性** ✓
（`surjective_deltaToEndRingHom_quadratic268_iff` ✓，秩 2 档 `⟺` ✓），并把**一般档**的充分性
**形状锁定**为 `TraceUnimodularSufficiency268` ✓（**未证** ✗）。本轮**攻接线档** ✓
（`R = ↥(noetherFixedCarrier …)` ✓，`S = Localization.Away T` ✓），并为「局部化于 `T` 是否
**正是**使判别式可逆的操作」给出机检读数 ✓。

**🔴🔴 主结果 ①（**否决** ✗）：第 268 轮的形状锁定件**是假的** ✓**（`not_traceUnimodularSufficiency268` ✓）。
**见证** ✓：`(R, S, G, tr) = (ℤ, QuadraticAlgebra ℤ 1 0, Multiplicative (ZMod 2), re)` ✓ ——
**五条假设逐条机检落地** ✓（互异性 ✓）：`r269_tr_invariant` ✓（`G`-不变 ✓）、`r269_tr_symm` ✓（对称 ✓）、
`r269_pairing_surj` ✓（配对**满** ✓，Gram ＝ 单位阵 ✓）、`Module.Finite` ✓（`inferInstance` ✓）、
`r269_delta_inj` ✓（§4.74 单射判别 ✓）；**结论被否** ✓（`r269_witness_not_surjective` ✓，经 §4.74 的 `⟺` ✓：
判别式 `0² + 4·1 = 4` **非单位** ✗）。**非空洞** ✓：载体 `ℤ[ω]/(ω²−1)` 上作用**非平凡** ✓（`ω ↦ −ω` ✓）
且 `δ` **单射** ✓（作用「强忠实」✓）—— **不是**退化档 ✓。

**🔴 主结果 ① 的**诊断**（**为什么假** ✓，**同一见证上**机检 ✓）：见证上**两条迹形式不同** ✓ ——
**(甲)** `G`-**不变**泛函 `tr = re` 的配对 Gram 行列式 ＝ **`1`** ✓（`r269InvGram_det` ✓，**单位** ✓）；
**(乙)** **乘法迹**（＝ §4.74 的 `QuadraticAlgebra.trace` ✓）的配对 Gram 行列式 ＝ **`4`** ✓
（`r269_algGram_not_isUnit` ✓，**非单位** ✗）。⟹ 第 268 轮登记的假设「`tr` **`G`-不变**」**严格弱于** ✓
它自己机检过的正确输入 ✓（乘法迹形式幺模 ⟺ `IsUnit (b²+4a)` ✓）⟹ 该形状锁定件**从来不是**
§4.74 主定理的推广 ✗（**强度序** ✓：`G`-不变 ⟹ 乘法迹不变 ✓，**反向 ✗** —— 见证即反例 ✓）。

**⚠ 主结果 ②（接线档障碍，机检 ✓）**：**接线环上（`C₂`／`ℚ` 档）迹形式幺模性对朴素选择是假的** ✗。
模型 ✓：`S = ℚ[X₀,X₁][e₂^{-1}]` ✓（`r269S` ✓）、`e₁ = X₀+X₁` ✓、`e₂ = X₀X₁` ✓、
判别式 `disc = e₁² − 4e₂ = (X₀−X₁)²` ✓（`r269_disc_eq` ✓）、接线环 `R = ℚ[e₁, e₂^{±1}] ⊆ S` ✓（`r269R` ✓）。
**三件** ✓：**(a)** `disc` 在 `S` 中**非单位** ✓（`r269_disc_not_isUnit_S` ✓ —— 特化 `X₀,X₁ ↦ 1` ✓
把 `disc` 打成 `0` ✓）；**(b)** 故 `disc` 在**任何**含它的子环（**特别地接线环** ✓）中**非单位** ✓
（`r269_disc_not_isUnit_of_mem` ✓，**最强的「任意子环」形** ✓）；**(c)** 由 §4.74 的 `⟺` ✓
得**秩 2 载体在接线环上 `δ` 非满射** ✓（`r269_wiring_delta_not_surjective` ✓）。
**⚠ 读法** ✓：**(a)(b)(c) 三件皆机检** ✓；但**「模型里的 `T` ＝ `exists_invariant_t_of_noether` 的输出」**
**不是**本件结论 ✗ —— 本件说的是：**接线形状**（`T ≠ 0` ✓ ＋ `G`-不变 ✓ ＋ 含分母 ✓）**本身不足** ✗，
**判别式可逆是额外的算术条件** ✓。

**✅ 主结果 ③（`T` 的加强：**充分机制** ＋ **非空性见证**，机检 ✓）**：
**(机制)** ✓ `d ∣ T ⟹ IsUnit (algebraMap A (Localization.Away T) d)` ✓
（`r269_isUnit_algebraMap_of_dvd` ✓，**一般交换环** ✓）—— 即**把判别式乘进 `T`** 正是使判别式
可逆的操作 ✓✅（＝ 起点假设的**精确化** ✓）。**(见证)** ✓ `T ↦ T·disc` 后：`R' = ℚ[e₁, e₂^{±1}, disc^{-1}]` ✓
（`r269R2` ✓）上 `disc` **是单位** ✓（`r269_discR2_isUnit` ✓，**逆元显式给** ✓）⟹ 迹形式**幺模** ✓ ⟹
**秩 2 载体在 `R'` 上 `δ` 满射** ✓（`r269_strengthened_delta_surjective` ✓，经 §4.74 的 `⟸` ✓）。
**⟹ 非空性** ✓：本路线的**假设与结论在同一实例上同时成立** ✓（**非空洞** ✓）。

**⚠ 强度序（逐条，方向明确 ✓；**勿读作等价** ✗）**：

| # | 输入 | 相对强度 | 状态 |
|---|---|---|---|
| ① | `G`-**不变**泛函 ＋ 其配对幺模（r268 登记件 ✓） | **严格弱于** ✓ ② | **已否决** ✗（**假** ✓） |
| ② | **乘法迹**形式幺模 ＋ **秩 ＝ `\|G\|`** ✓（r269 登记件 ✓） | **正确形** ✓ | **未证** ✗（秩 2 档 ✓ ＝ §4.74 `⟺` ✓） |
| ③ | `disc ∣ T`（接线档 ✓） | **充分** ✓ 于 ② 的**假设** ✓ | **已证** ✓（模型 ✓） |
| ④ | 迹满射 ✗／`\|G\|` 可逆 ✗／`R[G]`-自由秩一 ✗ | 不足 ✗ | **§4.74 已否决** ✗ |

**⚠ 分类（规则 17）** ✓：本轮**未落**项**只有一条** ✓ ＝ `TraceUnimodularSufficiency269` ✓
（**证明义务** ✓：**非**观测数据 ✗、**非 (b) 类「可算未算」**✗ —— 它是经典定理 ✓
（有限投射代数的判别式／可分 ⟹ Galois ✓，Auslander–Goldman／CHR ✓）而 **mathlib 内没有** ✗，
**不是**任何「未打印的输出」✓）；**无**材料阻断登记 ✓；**无** (b) 类未算项 ✓
（模型环上的判别式读数**已算完并落地** ✓）。

**🔴 不声称** ✗：**不**声称 `TraceUnimodularSufficiency269` 成立 ✗；**不**声称一般接线档的 `disc`
是 `MvPolynomial G F` 中的 `G`-不变多项式 ✗（`C₂`／`ℚ` 模型档 ✓ 成立：`disc = (X₀−X₁)²` ✓）；
**不**声称源 `theorem-5-1` ✓／`theorem-2-1` ✓ 已证 ✗；**不**声称
`exists_realizationPropertyFieldFinite_of_noetherFixedWiring_deltaSurj_and_rows` ✓ 的 `T`
就是模型里的 `T = e₂` ✗；**不**声称第 268 轮的秩 2 主定理被重证 ✗（本件**只用**其 `⟺` ✓）。 -/

/-! #### 269.A 一般档形状锁定件「`G`-不变迹泛函」被机检否决 -/

open scoped QuadraticAlgebra

section R269Witness

attribute [local instance] qaMSA268

/-- **`G`-不变迹泛函** ✓：`tr (a + bω) = a` ✓（`G = C₂` 经 `star` 作用 ✓，`star` 保持实部 ✓）。 -/
def r269Tr : QuadraticAlgebra ℤ 1 0 →ₗ[ℤ] ℤ where
  toFun z := z.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`G`-不变迹形式的 Gram 矩阵** ✓（基 `(1, ω)` ✓，配对 `(x,y) ↦ tr (x·y)` ✓）。 -/
def r269InvGram : Matrix (Fin 2) (Fin 2) ℤ :=
  !![r269Tr 1, r269Tr (ω : QuadraticAlgebra ℤ 1 0);
     r269Tr (ω : QuadraticAlgebra ℤ 1 0), r269Tr ((ω : QuadraticAlgebra ℤ 1 0) * ω)]

/-- **假设 ①（`G`-不变）机检落地** ✓。 -/
lemma r269_tr_invariant (g : Multiplicative (ZMod 2)) (x : QuadraticAlgebra ℤ 1 0) :
    r269Tr (g • x) = r269Tr x := by
  rcases mul_zmod2_cases267 g with rfl | rfl
  · rfl
  · rw [qaConj268_smul_def, qaConj268_gen]
    show (star x).re = x.re
    simp

/-- **假设 ②（对称）机检落地** ✓。 -/
lemma r269_tr_symm (x y : QuadraticAlgebra ℤ 1 0) :
    r269Tr (x * y) = r269Tr (y * x) := by
  show (x * y).re = (y * x).re
  rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_mul]
  ring

/-- **假设 ③（配对满）机检落地** ✓：`y := ⟨φ 1, φ ω⟩` ✓（该基下配对 Gram ＝ 单位阵 ✓）。 -/
lemma r269_pairing_surj (φ : QuadraticAlgebra ℤ 1 0 →ₗ[ℤ] ℤ) :
    ∃ y : QuadraticAlgebra ℤ 1 0, ∀ x : QuadraticAlgebra ℤ 1 0,
      φ x = r269Tr (x * y) := by
  refine ⟨⟨φ 1, φ ω⟩, fun x => ?_⟩
  have hx : x = x.re • (1 : QuadraticAlgebra ℤ 1 0) + x.im • (ω : QuadraticAlgebra ℤ 1 0) := by
    have h := QuadraticAlgebra.mk_eq_add_smul_omega (a := (1 : ℤ)) (b := (0 : ℤ)) x.re x.im
    rw [Algebra.algebraMap_eq_smul_one] at h
    rw [← h]
  have hφ : φ x = x.re * φ 1 + x.im * φ ω := by
    conv_lhs => rw [hx]
    rw [map_add, map_smul, map_smul]
    simp
  rw [hφ]
  show x.re * φ 1 + x.im * φ ω = (x * ⟨φ 1, φ ω⟩).re
  rw [QuadraticAlgebra.re_mul]
  ring

/-- **假设 ⑤（`δ` 单射）机检落地** ✓（经 §4.74 的单射判别 ✓：`2ω` 非零因子 ✓）。 -/
lemma r269_delta_inj :
    Function.Injective (BTier.deltaToEndRingHom (R := ℤ) (S := QuadraticAlgebra ℤ 1 0)
      (G := Multiplicative (ZMod 2)) (qaSmulComm268 (R := ℤ) (a := 1) (b := 0))) := by
  rw [injective_deltaToEndRingHom_quadratic268_iff]
  intro u hu
  rw [qaMulQaDiff268_eq_zero_iff] at hu
  have hre : u.re = 0 := by
    have h := hu.2
    simp only [zero_mul, add_zero] at h
    omega
  have him : u.im = 0 := by
    have h := hu.1
    simp only [mul_one, zero_mul, sub_zero] at h
    omega
  exact QuadraticAlgebra.ext hre him

/-- **见证的判别式非单位** ✗：`0² + 4·1 = 4` ✓。 -/
lemma r269_not_isUnit_four : ¬ IsUnit ((0 : ℤ) ^ 2 + 4 * 1) := by
  have h4 : (0 : ℤ) ^ 2 + 4 * 1 = 4 := by norm_num
  rw [h4]
  intro hu
  obtain ⟨y, hy, _⟩ := isUnit_iff_exists.mp hu
  omega

/-- **诊断 (甲)** ✓：同一载体上 **`G`-不变**迹形式的 Gram 行列式 ＝ **`1`** ✓（**单位** ✓）。 -/
lemma r269InvGram_det : r269InvGram.det = 1 := by
  rw [r269InvGram, Matrix.det_fin_two]
  have h1 : r269Tr (1 : QuadraticAlgebra ℤ 1 0) = 1 := rfl
  have h2 : r269Tr (ω : QuadraticAlgebra ℤ 1 0) = 0 := rfl
  have h3 : r269Tr ((ω : QuadraticAlgebra ℤ 1 0) * ω) = 1 := by
    rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
    rfl
  rw [h1, h2, h3]
  norm_num

lemma r269_invGram_isUnit : IsUnit r269InvGram.det := by
  rw [r269InvGram_det]
  exact isUnit_one

/-- **诊断 (乙)** ✓：同一载体上**乘法迹**形式（＝ §4.74 的 Gram ✓）的行列式 ＝ **`4`** ✓（**非单位** ✗）。 -/
lemma r269_algGram_not_isUnit : ¬ IsUnit (qaGram268 (a := (1 : ℤ)) (b := 0)).det := by
  rw [qaGram268_det]
  exact r269_not_isUnit_four

/-- **结论被否** ✓（经 §4.74 的 `⟺` ✓ 与判别式非单位 ✓）。 -/
theorem r269_witness_not_surjective :
    ¬ Function.Surjective (BTier.deltaToEndRingHom (R := ℤ) (S := QuadraticAlgebra ℤ 1 0)
      (G := Multiplicative (ZMod 2)) (qaSmulComm268 (R := ℤ) (a := 1) (b := 0))) :=
  fun h => r269_not_isUnit_four
    ((qaTraceUnimodular268_iff (a := 1) (b := 0)).mp
      ((surjective_deltaToEndRingHom_quadratic268_iff (a := 1) (b := 0)).mp h))

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 第 268 轮登记的一般档形状锁定件被机检否决** ✗：五条假设逐条落地 ✓（互异性 ✓）而结论假 ✗
⟹ `¬ TraceUnimodularSufficiency268` ✓。**诊断** ✓：其假设「`tr` `G`-不变」严格弱于
§4.74 机检过的正确输入 ✓（见 `r269_invGram_isUnit` ✓ ＋ `r269_algGram_not_isUnit` ✓）。 -/
theorem not_traceUnimodularSufficiency268 : ¬ TraceUnimodularSufficiency268 := by
  intro h
  exact r269_witness_not_surjective
    (h ℤ (QuadraticAlgebra ℤ 1 0) (Multiplicative (ZMod 2))
      (qaSmulComm268 (R := ℤ) (a := 1) (b := 0)) r269Tr r269_tr_invariant r269_tr_symm
      r269_pairing_surj (inferInstance : Module.Finite ℤ (QuadraticAlgebra ℤ 1 0))
      r269_delta_inj)

end R269Witness

#print axioms r269InvGram_det
#print axioms r269_invGram_isUnit
#print axioms r269_algGram_not_isUnit
#print axioms r269_witness_not_surjective
#print axioms not_traceUnimodularSufficiency268

/-! #### 269.B 接线档（`C₂`／`ℚ` 模型）：判别式非单位 ⟹ `δ` 非满射 -/

section R269Wiring

attribute [local instance] qaMSA268

/-- **模型多项式环** ✓ `ℚ[X₀, X₁]` ✓。 -/
abbrev r269A : Type := MvPolynomial (Fin 2) ℚ

/-- `e₁ = X₀ + X₁` ✓（第一初等对称多项式 ✓）。 -/
abbrev r269E1 : r269A := MvPolynomial.X 0 + MvPolynomial.X 1

/-- `e₂ = X₀X₁` ✓。 -/
abbrev r269E2 : r269A := MvPolynomial.X 0 * MvPolynomial.X 1

/-- **判别式** ✓ `disc = e₁² − 4e₂` ✓。 -/
abbrev r269Disc : r269A := r269E1 ^ 2 - 4 * r269E2

/-- **模型 `S`** ✓：`ℚ[X₀,X₁][e₂^{-1}]` ✓（＝ 接线 `S = Localization.Away T` ✓ 的 `T = e₂` 档 ✓）。 -/
abbrev r269S : Type := Localization.Away r269E2

/-- **判别式的平方形** ✓：`e₁² − 4e₂ = (X₀ − X₁)²` ✓（＝ `x₁ − x₂` 的平方 ✓，`G`-不变 ✓）。 -/
lemma r269_disc_eq : r269Disc = (MvPolynomial.X 0 - MvPolynomial.X 1) ^ 2 := by
  unfold r269Disc r269E1 r269E2
  ring

/-- 特化 `X₀ ↦ 1`，`X₁ ↦ 1` ✓（把判别式打成 `0` ✓）。 -/
def r269G : r269A →+* ℚ := MvPolynomial.eval (fun _ : Fin 2 => (1 : ℚ))

lemma r269G_E2 : r269G r269E2 = 1 := by
  unfold r269G r269E2
  simp

lemma r269G_unit : IsUnit (r269G r269E2) := by
  rw [r269G_E2]
  exact isUnit_one

/-- 由局部化万有性延拓的特化同态 ✓ `S →+* ℚ` ✓。 -/
def r269Spec : r269S →+* ℚ := IsLocalization.Away.lift r269E2 (g := r269G) r269G_unit

lemma r269Spec_algebraMap (a : r269A) : r269Spec (algebraMap r269A r269S a) = r269G a :=
  IsLocalization.Away.lift_eq r269E2 (g := r269G) r269G_unit a

lemma r269Spec_disc : r269Spec (algebraMap r269A r269S r269Disc) = 0 := by
  rw [r269Spec_algebraMap, r269_disc_eq]
  unfold r269G
  simp

/-- **(a) 判别式在 `S` 中非单位** ✗（**机检** ✓：单位在同态下的像仍是单位 ✓，而像为 `0` ✓）。 -/
theorem r269_disc_not_isUnit_S : ¬ IsUnit (algebraMap r269A r269S r269Disc) := by
  intro hu
  have h0 : IsUnit (r269Spec (algebraMap r269A r269S r269Disc)) := hu.map r269Spec
  rw [r269Spec_disc] at h0
  exact not_isUnit_zero h0

/-- **接线环（模型）** ✓：`R = ℚ[e₁, e₂^{±1}] ⊆ S` ✓（与 `noetherFixedCarrier` ✓ 同形 ✓）。 -/
abbrev r269R : Subalgebra ℚ r269S :=
  Algebra.adjoin ℚ ({algebraMap r269A r269S r269E1, algebraMap r269A r269S r269E2,
    IsLocalization.Away.invSelf (S := r269S) r269E2} : Set r269S)

lemma r269_disc_mem : algebraMap r269A r269S r269Disc ∈ r269R := by
  have h1 : algebraMap r269A r269S r269E1 ∈ r269R := Algebra.subset_adjoin (by simp)
  have h2 : algebraMap r269A r269S r269E2 ∈ r269R := Algebra.subset_adjoin (by simp)
  have h4 : (4 : r269S) ∈ r269R := Subalgebra.natCast_mem _ 4
  have hEq : algebraMap r269A r269S r269Disc
      = algebraMap r269A r269S r269E1 ^ 2 - 4 * algebraMap r269A r269S r269E2 := by
    unfold r269Disc r269E1 r269E2
    simp only [map_sub, map_pow, map_mul, map_ofNat]
  rw [hEq]
  exact sub_mem (pow_mem h1 2) (mul_mem h4 h2)

/-- **(b) 判别式在**任何**含它的子环中非单位** ✗（**最强形** ✓：**特别地**接线环 ✓）。 -/
theorem r269_disc_not_isUnit_of_mem {R' : Subalgebra ℚ r269S}
    (hmem : algebraMap r269A r269S r269Disc ∈ R') :
    ¬ IsUnit (⟨algebraMap r269A r269S r269Disc, hmem⟩ : ↥R') := by
  intro hu
  exact r269_disc_not_isUnit_S (hu.map (Subalgebra.val R'))

def r269A1 : ↥r269R := ⟨algebraMap r269A r269S r269E1, Algebra.subset_adjoin (by simp)⟩

def r269A2 : ↥r269R := ⟨algebraMap r269A r269S r269E2, Algebra.subset_adjoin (by simp)⟩

def r269DiscR : ↥r269R := ⟨algebraMap r269A r269S r269Disc, r269_disc_mem⟩

/-- **载体换算** ✓：接线档的 `x₁` 满足 `t² − e₁t + e₂ = 0` ✓ ⟹ `a = −e₂` ✓、`b = e₁` ✓
（§4.74 参数口径 ✓；判别式 `b² + 4a = e₁² − 4e₂` ✓）。 -/
lemma r269_discR_eq : r269A1 ^ 2 + 4 * (-r269A2) = r269DiscR := by
  refine Subtype.ext ?_
  show ((r269A1 : ↥r269R) : r269S) ^ 2 + 4 * (-((r269A2 : ↥r269R) : r269S))
    = algebraMap r269A r269S r269Disc
  rw [show ((r269A1 : ↥r269R) : r269S) = algebraMap r269A r269S r269E1 from rfl,
    show ((r269A2 : ↥r269R) : r269S) = algebraMap r269A r269S r269E2 from rfl]
  unfold r269Disc r269E1 r269E2
  simp only [map_sub, map_pow, map_mul, map_ofNat]
  ring

theorem r269_wiring_disc_not_isUnit : ¬ IsUnit r269DiscR :=
  r269_disc_not_isUnit_of_mem r269_disc_mem

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 接线环上（`C₂`／`ℚ` 档）`δ` 非满射** ✗（**机检** ✓）：判别式 `e₁² − 4e₂ = (X₀−X₁)²`
在接线环中**非单位** ✗ ⟹ 迹形式**非**幺模 ✗ ⟹ `δ` 非满射 ✗（经 §4.74 的 `⟺` ✓）。
**⚠ 读法** ✓：本件**不**声称模型里的 `T` 就是 `exists_invariant_t_of_noether` 的输出 ✗ ——
本件说的是**接线形状本身不足** ✓。 -/
theorem r269_wiring_delta_not_surjective :
    ¬ Function.Surjective (BTier.deltaToEndRingHom (R := ↥r269R)
      (S := QuadraticAlgebra ↥r269R (-r269A2) r269A1) (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (R := ↥r269R) (a := -r269A2) (b := r269A1))) := by
  intro h
  refine r269_wiring_disc_not_isUnit ?_
  rw [← r269_discR_eq]
  exact (qaTraceUnimodular268_iff (R := ↥r269R) (a := -r269A2) (b := r269A1)).mp
    ((surjective_deltaToEndRingHom_quadratic268_iff (R := ↥r269R) (a := -r269A2)
      (b := r269A1)).mp h)

end R269Wiring

#print axioms r269_disc_eq
#print axioms r269_disc_not_isUnit_S
#print axioms r269_disc_not_isUnit_of_mem
#print axioms r269_discR_eq
#print axioms r269_wiring_disc_not_isUnit
#print axioms r269_wiring_delta_not_surjective

/-! #### 269.C `T` 的加强：`d ∣ T ⟹ d` 在 `A[T^{-1}]` 中可逆 -/

section R269Strengthened

variable {A : Type*} [CommRing A]

/-- **✅ 加强机制（一般交换环）** ✓：`d ∣ T ⟹ algebraMap d` 在 `A[T^{-1}]` 中**可逆** ✓
（逆元显式：`c · T^{-1}` ✓，`T = d·c` ✓）⟹ **把判别式乘进 `T`** 正是使其可逆的操作 ✓✅。 -/
theorem r269_isUnit_algebraMap_of_dvd (d T : A) (h : d ∣ T) :
    IsUnit (algebraMap A (Localization.Away T) d) := by
  obtain ⟨c, rfl⟩ := h
  have h1 : IsUnit (algebraMap A (Localization.Away (d * c)) d
      * algebraMap A (Localization.Away (d * c)) c) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (d * c)
  obtain ⟨u, hu1, hu2⟩ := isUnit_iff_exists.mp h1
  refine isUnit_iff_exists.mpr ⟨algebraMap A (Localization.Away (d * c)) c * u, ?_, ?_⟩
  · rw [← mul_assoc]; exact hu1
  · calc (algebraMap A (Localization.Away (d * c)) c * u)
          * algebraMap A (Localization.Away (d * c)) d
        = u * (algebraMap A (Localization.Away (d * c)) d
            * algebraMap A (Localization.Away (d * c)) c) := by ring
      _ = 1 := by simpa only [map_mul] using hu2

end R269Strengthened

#print axioms r269_isUnit_algebraMap_of_dvd

/-! #### 269.D 加强档：`T ↦ T·disc` ⟹ 迹形式幺模 ⟹ `δ` 满射（✅ 非空性见证） -/

section R269Positive

attribute [local instance] qaMSA268

/-- **加强后的模型 `S'`** ✓：`ℚ[X₀,X₁][(e₂·disc)^{-1}]` ✓（＝ `T ↦ T·disc` ✓）。 -/
abbrev r269S2 : Type := Localization.Away (r269E2 * r269Disc)

/-- **判别式的显式逆** ✓：`disc^{-1} = e₂ · (e₂·disc)^{-1}` ✓ ∈ `S'` ✓。 -/
def r269DiscInv : r269S2 :=
  algebraMap r269A r269S2 r269E2
    * IsLocalization.Away.invSelf (S := r269S2) (r269E2 * r269Disc)

lemma r269_disc_mul_discInv : algebraMap r269A r269S2 r269Disc * r269DiscInv = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := r269S2) (r269E2 * r269Disc)
  rw [map_mul] at h
  rw [← h]
  unfold r269DiscInv
  ring

/-- **加强后的接线环** ✓：`R' = ℚ[e₁, e₂^{±1}, disc^{-1}]` ✓（`disc` 已在其中可逆 ✓）。 -/
abbrev r269R2 : Subalgebra ℚ r269S2 :=
  Algebra.adjoin ℚ ({algebraMap r269A r269S2 r269E1, algebraMap r269A r269S2 r269E2,
    IsLocalization.Away.invSelf (S := r269S2) (r269E2 * r269Disc)} : Set r269S2)

def r269A1' : ↥r269R2 := ⟨algebraMap r269A r269S2 r269E1, Algebra.subset_adjoin (by simp)⟩

def r269A2' : ↥r269R2 := ⟨algebraMap r269A r269S2 r269E2, Algebra.subset_adjoin (by simp)⟩

lemma r269_disc_mem2 : algebraMap r269A r269S2 r269Disc ∈ r269R2 := by
  have h1 : algebraMap r269A r269S2 r269E1 ∈ r269R2 := Algebra.subset_adjoin (by simp)
  have h2 : algebraMap r269A r269S2 r269E2 ∈ r269R2 := Algebra.subset_adjoin (by simp)
  have h4 : (4 : r269S2) ∈ r269R2 := Subalgebra.natCast_mem _ 4
  have hEq : algebraMap r269A r269S2 r269Disc
      = algebraMap r269A r269S2 r269E1 ^ 2 - 4 * algebraMap r269A r269S2 r269E2 := by
    unfold r269Disc r269E1 r269E2
    simp only [map_sub, map_pow, map_mul, map_ofNat]
  rw [hEq]
  exact sub_mem (pow_mem h1 2) (mul_mem h4 h2)

def r269DiscR2 : ↥r269R2 := ⟨algebraMap r269A r269S2 r269Disc, r269_disc_mem2⟩

def r269DiscInvR2 : ↥r269R2 :=
  ⟨r269DiscInv, mul_mem (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp))⟩

/-- **✅ 加强后判别式是单位** ✓（逆元显式 ✓）。 -/
lemma r269_discR2_isUnit : IsUnit r269DiscR2 := by
  refine isUnit_iff_exists.mpr ⟨r269DiscInvR2, ?_, ?_⟩
  · refine Subtype.ext ?_
    show ((r269DiscR2 : ↥r269R2) : r269S2) * ((r269DiscInvR2 : ↥r269R2) : r269S2) = 1
    exact r269_disc_mul_discInv
  · refine Subtype.ext ?_
    show ((r269DiscInvR2 : ↥r269R2) : r269S2) * ((r269DiscR2 : ↥r269R2) : r269S2) = 1
    rw [mul_comm]
    exact r269_disc_mul_discInv

lemma r269_discR2_eq : r269A1' ^ 2 + 4 * (-r269A2') = r269DiscR2 := by
  refine Subtype.ext ?_
  show ((r269A1' : ↥r269R2) : r269S2) ^ 2 + 4 * (-((r269A2' : ↥r269R2) : r269S2))
    = algebraMap r269A r269S2 r269Disc
  rw [show ((r269A1' : ↥r269R2) : r269S2) = algebraMap r269A r269S2 r269E1 from rfl,
    show ((r269A2' : ↥r269R2) : r269S2) = algebraMap r269A r269S2 r269E2 from rfl]
  unfold r269Disc r269E1 r269E2
  simp only [map_sub, map_pow, map_mul, map_ofNat]
  ring

set_option maxHeartbeats 1000000 in
/-- **✅✅ 非空性见证** ✓：接线环加强为 `R' = ℚ[e₁, e₂^{±1}, (e₁²−4e₂)^{-1}]` ✓ 后
迹形式**幺模** ✓ ⟹ **秩 2 载体在 `R'` 上 `δ` 满射** ✓（经 §4.74 的 `⟸` ✓）。
**⟹ 本路线假设与结论在同一实例上同时成立** ✓（**非空洞** ✓）。 -/
theorem r269_strengthened_delta_surjective :
    Function.Surjective (BTier.deltaToEndRingHom (R := ↥r269R2)
      (S := QuadraticAlgebra ↥r269R2 (-r269A2') r269A1') (G := Multiplicative (ZMod 2))
      (qaSmulComm268 (R := ↥r269R2) (a := -r269A2') (b := r269A1'))) := by
  refine surjective_deltaToEndRingHom_quadratic268_of_isUnit (R := ↥r269R2)
    (a := -r269A2') (b := r269A1') ?_
  rw [r269_discR2_eq]
  exact r269_discR2_isUnit

end R269Positive

#print axioms r269_disc_mul_discInv
#print axioms r269_discR2_isUnit
#print axioms r269_discR2_eq
#print axioms r269_strengthened_delta_surjective

/-! #### 269.E 修正形（登记，**未证** ✗） -/

section R269Shape

/-- **乘法迹** ✓（相对**显式基** `b` ✓）：`x ↦ trace (mul x)` 的矩阵迹 ✓
（＝ `LinearMap.trace` 的显式基形 ✓，**不**需额外 mathlib 依赖 ✓）。 -/
def r269MulTrace {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    (b : Module.Basis (Fin n) R S) (x : S) : R :=
  Matrix.trace (Matrix.of fun i j => (b.repr (x * b j)) i)

/-- **口径核验** ✓✅（**机检** ✓）：`n = 2` ✓、基取 `QuadraticAlgebra.basis a b`（＝ `(1, ω)` ✓）时，
上述**乘法迹**恰好等于 §4.74 的 `QuadraticAlgebra.trace` ✓（乘法的矩阵
`[[z.re, a·z.im], [z.im, z.re + b·z.im]]` ✓，迹 `2z.re + b·z.im` ✓）
⟹ 修正形的**假设**在秩 2 档**就是** §4.74 已机检的输入 ✓（节头强度序 ② ✓）。 -/
theorem r269MulTrace_quadratic {R : Type*} [CommRing R] (a b : R)
    (z : QuadraticAlgebra R a b) :
    r269MulTrace (QuadraticAlgebra.basis a b) z = QuadraticAlgebra.trace z := by
  have hb0 : (QuadraticAlgebra.basis a b) 0 = (1 : QuadraticAlgebra R a b) := by
    apply (QuadraticAlgebra.basis a b).repr.injective
    rw [Module.Basis.repr_self]
    ext i
    fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply]
  have hb1 : (QuadraticAlgebra.basis a b) 1 = (ω : QuadraticAlgebra R a b) := by
    apply (QuadraticAlgebra.basis a b).repr.injective
    rw [Module.Basis.repr_self]
    ext i
    fin_cases i <;> simp [QuadraticAlgebra.basis_repr_apply]
  rw [r269MulTrace, QuadraticAlgebra.trace_def]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Fin.sum_univ_two]
  rw [hb0, hb1]
  simp only [mul_one]
  rw [QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.basis_repr_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [QuadraticAlgebra.im_mul]
  simp
  ring

/-- **修正形（登记 ✓，未证 ✗）**：把第 268 轮登记件里的「`G`-**不变**迹泛函」✗ 换成
**乘法迹** ✓，并补**秩假设** `|G| = n` ✓。
**⚠ 为什么必须补秩假设** ✓（**维数论证** ✓，非观测数据 ✓）：`δ` 是
`S[G] → \mathrm{End}_R S` ✓ 的 `R`-线性映射 ✓，两侧秩分别为 `n·|G|` ✓ 与 `n²` ✓ ——
满射要求 `n·|G| ≥ n²` ✓，故 `|G| < n` 档**必假** ✗（如 `S = ℚ(√2) × ℚ(√3)` ✓、`G = C₂` 换位 ✓：
`n = 4` ✗ 而 `|G| = 2` ✗）。 -/
def TraceUnimodularSufficiency269 : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (G : Type) [Group G] [Fintype G]
    [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x)) {n : ℕ}
    (b : Module.Basis (Fin n) R S),
    Fintype.card G = n →
    Function.Injective (BTier.deltaToEndRingHom hRG) →
    (∀ φ : S →ₗ[R] R, ∃ y : S, ∀ x : S, φ x = r269MulTrace b (x * y)) →
    Function.Surjective (BTier.deltaToEndRingHom hRG)

/-- **登记** ✗：`TraceUnimodularSufficiency269` ✓ **未证** ✗（**证明义务** ✓，规则 17 ✓：
经典定理 ✓（Auslander–Goldman／CHR ✓），**mathlib 内没有** ✗，**非**观测数据 ✗、**非** (b) 类 ✗）；
其 **`n = 2`／基 `(1,ω)`** 档 ✓ ＝ §4.74 的 `⟺` ✓（**已机检** ✓，口径由 `r269MulTrace_quadratic` ✓ 供给，
本件**不重证** ✗）。 -/
theorem traceUnimodularSufficiency269_registered : True := trivial

end R269Shape

#print axioms r269MulTrace_quadratic
#print axioms traceUnimodularSufficiency269_registered

/-! ### 4.76 接线档的**判别式入 `T`**（一般 `G` 的 Vandermonde 型不变量）＋ 环档**迹形式幺模性**的**充分条件**（第 270 轮）

**⚠ 起点** ✓（承 §4.74 ✓／§4.75 ✓）：**(甲)** §4.74 ✓ 把环档的**正确输入**锁为**迹形式（乘法迹配对）幺模性** ✓
（秩 2 档 `⟺` ✓，`surjective_deltaToEndRingHom_quadratic268_iff` ✓）；**(乙)** §4.75 ✓（r269）**机检否决**了
朴素形状件 ✓（`not_traceUnimodularSufficiency268` ✓）并给出**加强机制** ✓
（`r269_isUnit_algebraMap_of_dvd` ✓：`d ∣ T ⟹ IsUnit (algebraMap A (Away T) d)` ✓）＋ 秩 2 档**非空性见证** ✓
（`r269_strengthened_delta_surjective` ✓）。**本轮补 §4.75 ✓ 的未落项** ✗：**一般 `G` 档的判别式型元素** ✗
（§4.75 ✓ 的**不声称**行 ✓ 逐字：「**不**声称一般接线档的 `disc` 是 `MvPolynomial G F` 中的 `G`-不变多项式」✗）。

**🔴🔴 主结果 ①（O3：判别式入 `T`，一般 `G`）** ✓✅：
**(a)** **判别式型元素** ✓ `r270Disc F G := ∏_σ ∏_{τ ≠ σ} (X_σ − X_τ)` ✓（Vandermonde 型 ✓）——
**非零** ✓（`r270Disc_ne_zero` ✓，仅需 `F` 域 ✓）＋ **`G`-不变** ✓（`r270_smul_disc` ✓，
**一般有限群** ✓，机制 ＝ 「变量按 `τ ↦ gτ` 置换 ⟹ 对角外的二元组集**整体置换**」✓，双重重标号机检 ✓）；
**(b)** **`C₂`／`ℚ` 档回收 §4.75 模型** ✓✅：`r270Disc ℚ (Multiplicative (ZMod 2)) = −(X_1 − X_a)²` ✓
（`r270_disc_zmod2` ✓）——即 r269 模型判别式 `disc = (X₀ − X₁)²` ✓ **相差单位 `−1`** ✓，
故**一般档确实推广了** §4.75 ✓ 的 `C₂`／`ℚ` 档 ✓（**不是**另一个对象 ✗）；
**(c)** **接线包加强** ✓✅：`r270_exists_realizationPropertyFieldFinite_of_noetherFixedWiring_discDvd` ✓ ——
与 §4.70 ✓ 的 `exists_realizationPropertyFieldFinite_of_noetherFixedWiring` ✓ **同一 ∃-包** ✓
（`T` ✓／`t ≠ 0` ✓／不变化 ✓／`hle` ✓／三实例 ✓／`hact_map` ✓／`hRG` ✓／`hS_0R` ✓／`hS_fix` ✓
**全由构造供给** ✓，假设表仍为**两行** ✓：`δ` 双射 ✓ ＋ `hProj` ✓），唯**输出 `T`** ✓ 携带
**`r270Disc F G ∣ T`** ✓ ＋ **`IsUnit (algebraMap (MvPolynomial G F) (Localization.Away T) (r270Disc F G))`** ✓
（后款由**前款**经 r269 ✓ 的机制供给 ✓）。**机制** ✓：取 §4.70 ✓ 的 `T₀` ✓（`exists_invariant_t_of_noether` ✓）
并置 **`T := T₀ · r270Disc F G`** ✓ —— **非零** ✓（`mul_ne_zero` ✓）、**不变化** ✓（`smul_mul'` ✓ ＋
`r270_smul_disc` ✓）、**包含** ✓（`hT₀le.trans (adjoin_away_mono …)` ✓），下游**逐行照搬** ✓
（**实例／`hRG`／`hS_0R` 皆随新 `T` 重建** ✓）。

**⚠ 强度序（O3 侧，逐行；方向明确 ✓）**：

| # | 接线档的输出条件 | 相对强度 | 状态 |
|---|---|---|---|
| ① | 朴素 `T` ✓（`T ≠ 0` ✓ ＋ 不变 ✓ ＋ 含分母 ✓，**无判别式条件** ✗） | **不足** ✗ | **§4.75 ✓ 机检否决** ✗（模型档：`disc = (X₀−X₁)²` 在**任何**含它的子环中**非单位** ✗ ⟹ 迹形式**非**幺模 ✗ ⟹ 秩 2 载体 `δ` **非满射** ✗，`r269_wiring_delta_not_surjective` ✓） |
| ② | `r270Disc F G ∣ T` ✓ | **充分** ✓ 于 ③ ✓ | **已证** ✓✅（本件 ✓，**一般 `G`** ✓） |
| ③ | `IsUnit (algebraMap … (r270Disc F G))` ✓ | **推论** ✓ of ② | **已证** ✓✅（② ⟹ ③ ✓，`r269_isUnit_algebraMap_of_dvd` ✓；**反向不声称** ✗） |
| ④ | `disc` 是 `MvPolynomial G F` 的 `G`-不变非零元 ✓ | **结构前提** ✓ | **已证** ✓✅（本件 ✓，一般有限 `G` ✓） |

**🔴 主结果 ②（O2：环档迹形式幺模性的充分条件，任意秩）** ✓✅：
**定理** ✓ `r270_delta_surjective_of_traceFormula` ✓：对**任意交换环** `R` ✓、`R`-代数 `S` ✓、
**任意有限群 `G`** ✓、`R`-基 `b : Basis ι R S` ✓（**指标型任意** ✓，秩 `|ι|` **不受限** ✗），若
**(甲) 迹公式** ✓ `∀ z, algebraMap R S (Tr_b z) = ∑_g g • z` ✓（`Tr_b` ＝ **乘法迹** ✓，`r270MulTrace` ✓）
且 **(乙) 迹形式幺模** ✓ `∀ φ : S →ₗ[R] R, ∃ y, ∀ x, φ x = Tr_b (x·y)` ✓，则 **`δ` 满射** ✓。
**机制** ✓（**四步**，全部机检 ✓）：**①** 幺模 ＋ `b.coord i` ✓ ⟹ 迹对偶元 `y_i` ✓
（`Tr_b (b_j · y_i) = δ_{ji}` ✓，`Module.Basis.repr_self` ✓）；**②** 迹公式把
`∑_g (g•y_i)·(g•b_j) = ∑_g g•(y_i·b_j)` ✓ 打成 `algebraMap (Tr_b (y_i·b_j))` ✓ ⟹
**正交关系** ✓ `∑_g (g•y_i)·(g•b_j) = algebraMap (if i = j then 1 else 0)` ✓；
**③** 对任意 `f : End_R S` ✓ **显式预像** ✓ `x := ∑_g single g (∑_i f(b_i)·(g•y_i))` ✓；
**④** 逐基元核验 ✓（`b.ext` ✓ ＋ `Finset.sum_comm` ✓ ＋ ② 消去 ⟹ `δ x = f` ✓）。
**⟹ 若将「迹公式」并入登记件** ✓，则 §4.75 ✓ 的 `TraceUnimodularSufficiency269` ✓ **成立** ✓
（`r270_traceUnimodularSufficiency_of_traceFormula` ✓，**逐字同形** ✓ 且**多一条迹公式** ✓）。

**⚠ 强度序（O2 侧，逐行；**勿读作等价** ✗）**：

| # | 输入 | 相对强度 | 状态 |
|---|---|---|---|
| ① | **迹公式** ✓ ＋ **迹形式幺模** ✓（**任意秩** ✓／**任意交换环** ✓） | **充分** ✓ | **已证** ✓✅（本件 ✓，**秩与单射假设皆不使用** ✗） |
| ② | `TraceUnimodularSufficiency269` ✓（乘法迹幺模 ＋ **秩 ＝ `\|G\|`** ✓ ＋ `δ` 单射 ✓） | **目标形** ✓ | **仍开** ✗（**唯一缺口** ＝ 「② 的假设是否**推出**迹公式」✗，**证明义务** ✓） |
| ③ | 秩 2／二次载体：`IsUnit (b²+4a)` ⟺ `δ` 满射 ✓（§4.74 ✓） | ① 的**同行档** ✓ | **已证** ✓✅（§4.74 ✓；**迹公式在二次代数上自动成立** ✓，本件机检 ✓ `r270_traceFormula_quadratic` ✓） |
| ④ | `K` **域** 档：`δ` 单射 ⟹ `δ` 满射 ✓（§4.72 ✓） | **另一条**充分条件 ✓ | **已证** ✓✅（§4.72 ✓；**环档不成立** ✗，§4.73 ✓ 机检反例 ✓） |
| ⑤ | 分裂载体 `S = R^G` ✓（正则作用 ✓）：迹公式 ✓ ＋ 幺模 ✓ ＋ `δ` 满射 ✓ | ① 的**实例** ✓ | **已证** ✓✅（本件 ✓，**任意交换环** ✓ ＋ **任意有限 `G`** ✓；★ **新**：§4.72 ✓ 的同类结果限 `K` **域** ✗；**域档** ✓ 时 §4.72 ✓ 另给 `δ` **双射** ✓ ⟹ **登记件 ② 的全部假设**在同一载体上**同时成立** ✓ —— 唯 ② 的缺口（迹公式）**不在该载体**上 ✗） |

**⚠ 分类（规则 17）** ✓：本轮**未落**项**只有一条** ✓ ＝ 「② ⟹ 迹公式」✓（**证明义务** ✓：
**非**观测数据 ✗、**非** (b) 类「可算未算」✗ —— 它是**数学命题** ✓，其真值**未定** ✓，本轮**不声称**任一方向 ✗）；
**无**材料阻断登记 ✓；**无** (b) 类未算项 ✓（`C₂` 判别式读数 ✓、分裂载体读数 ✓、二次载体读数 ✓ **均已算完并落地** ✓）。

**⚠ 非空性（L1／L19）** ✓（**三处** ✓，**互异性** ✓）：
**(i)** **分裂载体** ✓（**任意交换环** ✓ ＋ **任意有限 `G`** ✓）：迹公式 ✓（`r270_traceFormula_regularAction` ✓，
**非分裂** ✗ 的一般群档 ✓）＋ 幺模 ✓（`r270_unimodular_regularAction` ✓，Gram ＝ 单位阵 ✓）⟹
`δ` **满射** ✓（`r270_delta_surjective_regularAction` ✓）；**秩 3 实例** ✓：`G = Multiplicative (ZMod 3)` ✓
（`r270_card_zmod_three` ✓，`|G| = 3` ✓）⟹ **①的假设在秩 3 环档可满足** ✓（§4.74 ✓ 的秩 2 之外的**新档** ✓）；
**(ii)** **二次载体** ✓（**非分裂** ✓，§4.74 ✓ 的载体族 ✓）：迹公式**自动成立** ✓
（`r270_traceFormula_quadratic` ✓，`star`-共轭 ＋ `trace_def` ✓），故 §4.74 ✓ 的秩 2 `⟸` 与 ① **不矛盾** ✓；
**(iii)** **接线档** ✓：`disc ∣ T` 的见证**由本件构造给出** ✓（`T := T₀ · r270Disc F G` ✓），
且 `C₂`／`ℚ` 档的判别式读数**已回收到 r269 模型** ✓（`r270_disc_zmod2` ✓）。

**⚠ 判别力（L43）** ✓（**如实** ✓）：本件的每条假设都在**证明体内作为实参被消费** ✓ ——
`r270_delta_surjective_of_traceFormula` ✓ 用**迹公式** ✓（正交关系 ② 步）与**幺模** ✓（对偶元 ① 步），
**不用**秩假设 ✗ 与 `δ` 单射 ✗（**该两款本轮如实登记为「未使用」** ✓，**不冒充为已消费** ✗）；
`r270_exists_realizationPropertyFieldFinite_of_noetherFixedWiring_discDvd` ✓ 用
`r270Disc_ne_zero` ✓（`mul_ne_zero` ✓）与 `r270_smul_disc` ✓（`hTinv` ✓）。

**🔴 不声称** ✗：**不**声称 `TraceUnimodularSufficiency269` ✓ 成立 ✗（② ⟹ 迹公式**未落** ✗）；
**不**声称迹公式由登记件的**任何子集**推出 ✗；**不**声称 `disc` 是**判别式**的**唯一**候选 ✗
（本件构造的是**Vandermonde 型**元素 ✓，`C₂` 档与 r269 模型**相差单位** ✓ `−1` ✓）；
**不**声称接线包的**假设表**（`δ` 双射 ✓ ＋ `hProj` ✓）已证 ✗（**两行仍开** ✗，§4.70 ✓／§4.71 ✓）；
**不**声称两条源陈述已证 ✗。 -/

/-! #### 270.A 一般 `G` 的**判别式型不变量**（Vandermonde 型） -/

universe v

section R270DiscDef

variable (F : Type u) [CommRing F] (G : Type v) [Fintype G] [DecidableEq G]

/-- **判别式型元素** ✓（**一般有限 `G`** ✓）：`∏_σ ∏_{τ ≠ σ} (X_σ − X_τ)` ✓ ——
**Vandermonde 型** ✓（`|G| = 2` ✓ 时 ＝ `−(X_0 − X_1)²` ✓，见 `r270_disc_zmod2` ✓）。
**⚠ 为何是它** ✓：它是 `MvPolynomial G F` 中**对角外二元组**上的乘积 ✓ ⟹ 变量按 `τ ↦ gτ` 置换时
**整体不变** ✓（§4.75 ✓ 的 `C₂`／`ℚ` 模型判别式 `(X₀ − X₁)²` ✓ 正是它的**单位倍** ✓）。
**⚠ 域档** ✓：`F` 只需**交换环** ✓ 即可定义 ✓（非零性另需无零因子 ✓）。 -/
def r270Disc : MvPolynomial G F :=
  ∏ σ : G, ∏ τ ∈ Finset.univ.erase σ, (MvPolynomial.X σ - MvPolynomial.X τ)

end R270DiscDef

section R270DiscLemmas

variable {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G] [DecidableEq G]

omit [Group G] [Fintype G] [DecidableEq G] in
lemma r270_X_sub_ne_zero {σ τ : G} (h : σ ≠ τ) :
    (MvPolynomial.X σ - MvPolynomial.X τ : MvPolynomial G F) ≠ 0 :=
  sub_ne_zero.mpr (fun hc => h (MvPolynomial.X_injective hc))

omit [Group G] in
/-- **判别式型元素非零** ✓✅（**一般有限 `G`** ✓）：每个因子 `X_σ − X_τ`（`σ ≠ τ` ✓）非零 ✓
（`MvPolynomial.X_injective` ✓），`MvPolynomial G F` 无零因子 ✓ ⟹ 乘积非零 ✓。 -/
theorem r270Disc_ne_zero : r270Disc F G ≠ 0 := by
  classical
  rw [r270Disc]
  refine Finset.prod_ne_zero_iff.mpr (fun σ _ => ?_)
  refine Finset.prod_ne_zero_iff.mpr (fun τ hτ => ?_)
  exact r270_X_sub_ne_zero (fun h => (Finset.mem_erase.mp hτ).1 h.symm)

/-- **内层重标号** ✓（**机检** ✓）：`τ ↦ gτ` 把 `univ.erase σ` **双射**到 `univ.erase (gσ)` ✓
（`mul_left_cancel` ✓ ＋ `mul_inv_cancel_left` ✓）⟹ 内层乘积可换标 ✓（`Finset.prod_bij` ✓）。 -/
lemma r270_prod_erase_smul (g σ : G) (Φ : G → MvPolynomial G F) :
    (∏ τ ∈ Finset.univ.erase σ, Φ (g * τ)) = ∏ τ ∈ Finset.univ.erase (g * σ), Φ τ := by
  classical
  refine Finset.prod_bij (fun τ _ => g * τ) ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [Finset.mem_erase] at hτ ⊢
    exact ⟨fun h => hτ.1 (mul_left_cancel h), Finset.mem_univ _⟩
  · intro τ₁ _ τ₂ _ h
    exact mul_left_cancel h
  · intro τ' hτ'
    rw [Finset.mem_erase] at hτ'
    refine ⟨g⁻¹ * τ', ?_, mul_inv_cancel_left g τ'⟩
    rw [Finset.mem_erase]
    exact ⟨fun h => hτ'.1 (by rw [← h]; exact (mul_inv_cancel_left g τ').symm),
      Finset.mem_univ _⟩
  · intro τ _; rfl

omit [Fintype G] [DecidableEq G] in
/-- **作用穿过乘积** ✓（`noetherRingHom` ✓ 是环同构 ⟹ `map_prod` ✓；用 `show` 转写 ✓，
与 `smul_X_noether` ✓ 同款工艺 ✓）。 -/
lemma r270_smul_prod (g : G) (s : Finset ι) (f : ι → MvPolynomial G F) :
    g • (∏ i ∈ s, f i) = ∏ i ∈ s, g • f i := by
  show (noetherRingHom F G g) (∏ i ∈ s, f i) = ∏ i ∈ s, (noetherRingHom F G g) (f i)
  exact map_prod _ _ _

/-- **✅ 判别式型元素 `G`-不变** ✓✅（**一般有限 `G`** ✓）：两步重标号 ✓ ——
**内层**用 `r270_prod_erase_smul` ✓（`τ ↦ gτ` ✓），**外层**用 `Finset.prod_bij` ✓（`σ ↦ gσ` ✓，
`mul_left_cancel` ✓／`mul_inv_cancel_left` ✓）⟹ `g • r270Disc F G = r270Disc F G` ✓。 -/
theorem r270_smul_disc (g : G) : g • r270Disc F G = r270Disc F G := by
  classical
  have hX : ∀ τ : G, g • (MvPolynomial.X τ : MvPolynomial G F) = MvPolynomial.X (g * τ) :=
    fun τ => smul_X_noether F G g τ
  have hstep : g • r270Disc F G
      = ∏ σ : G, ∏ τ ∈ Finset.univ.erase σ,
          (MvPolynomial.X (g * σ) - MvPolynomial.X (g * τ)) := by
    rw [r270Disc, r270_smul_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [r270_smul_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [smul_sub, hX, hX]
  rw [hstep, r270Disc]
  refine Finset.prod_bij (fun σ _ => g * σ) (fun σ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro σ₁ _ σ₂ _ h
    exact mul_left_cancel h
  · intro σ' _
    exact ⟨g⁻¹ * σ', Finset.mem_univ _, mul_inv_cancel_left g σ'⟩
  · intro σ _
    exact r270_prod_erase_smul g σ
      (fun τ => MvPolynomial.X (g * σ) - MvPolynomial.X τ)

end R270DiscLemmas

/-- **`C₂`／`ℚ` 档回收 §4.75 模型判别式** ✓✅：`r270Disc ℚ (Multiplicative (ZMod 2)) = −(X_1 − X_a)²` ✓
—— 即 §4.75 ✓ 模型档的 `disc = (X₀ − X₁)²` ✓（`r269_disc_eq` ✓）**相差单位 `−1`** ✓
（`−1` 在 `ℚ` 中可逆 ✓）⟹ **一般档确实推广 `C₂`／`ℚ` 档** ✓（**非**另一对象 ✗）。 -/
theorem r270_disc_zmod2 :
    r270Disc ℚ (Multiplicative (ZMod 2))
      = -((MvPolynomial.X (1 : Multiplicative (ZMod 2))
            - MvPolynomial.X (Multiplicative.ofAdd 1)) ^ 2) := by
  classical
  set a : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1 with ha
  have h1 : (Finset.univ : Finset (Multiplicative (ZMod 2))) = {1, a} := by decide
  have h2 : ({1, a} : Finset (Multiplicative (ZMod 2))).erase 1 = {a} := by decide
  have h3 : ({1, a} : Finset (Multiplicative (ZMod 2))).erase a = {1} := by decide
  have hne : (1 : Multiplicative (ZMod 2)) ≠ a := by decide
  rw [r270Disc, h1, Finset.prod_insert (by simp [hne]), Finset.prod_singleton]
  rw [h2, Finset.prod_singleton, h3, Finset.prod_singleton]
  ring

#print axioms r270_X_sub_ne_zero
#print axioms r270Disc_ne_zero
#print axioms r270_prod_erase_smul
#print axioms r270_smul_prod
#print axioms r270_smul_disc
#print axioms r270_disc_zmod2

/-! #### 270.B 接线档：**判别式入 `T`** 的 ∃-包（`disc ∣ T` ＋ `IsUnit`） -/

section R270WiringDisc

variable {F : Type} [Field F] {G : Type} [Group G] [Fintype G] [DecidableEq G]

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 接线档的判别式入 `T`** ✓✅（**本轮的 (O3) 主件** ✓）：与 §4.70 ✓ 的
`exists_realizationPropertyFieldFinite_of_noetherFixedWiring` ✓ **同一 ∃-包** ✓（`T` ✓／`t ≠ 0` ✓／
不变化 ✓／`hle` ✓／三实例 ✓／`hact_map` ✓／`hRG` ✓／`hS_0R` ✓／`hS_fix` ✓ 全由构造供给 ✓，
假设表仍为**两行** ✓：`δ` 双射 ✓ ＋ `hProj` ✓），**唯输出 `T`** 携带
**`r270Disc F G ∣ T`** ✓ 与 **`IsUnit (algebraMap (MvPolynomial G F) (Localization.Away T) (r270Disc F G))`** ✓
（＝ §4.75 ✓ 的加强机制 ✓ 在新 `T` 上的落地 ✓）。
**机制** ✓：取 §4.70 ✓ 的 `T₀` ✓（`exists_invariant_t_of_noether` ✓）并置 **`T := T₀ · r270Disc F G`** ✓：
**非零** ✓（`mul_ne_zero` ✓ ＋ `r270Disc_ne_zero` ✓）、**不变化** ✓（`smul_mul'` ✓ ＋ `r270_smul_disc` ✓）、
**包含** ✓（`hT₀le.trans (adjoin_away_mono T₀ (r270Disc F G) …)` ✓）；下游实例／`hRG`／`hS_0R`／忠实性
**随新 `T` 逐行重建** ✓（**`let _inst`** 记法 ✓，**无** `letI` ✗）。
**⚠ 强度序** ✓：本件的输出条件 **②（`disc ∣ T`）严格强于** §4.70 ✓ 的朴素 `T` ✓ 之条件 ① ✓
（① 在 `C₂`／`ℚ` 模型档**已被 §4.75 ✓ 机检否决** ✗：`disc` **非单位** ✗ ⟹ `δ` **非满射** ✗）；
**反向不成立** ✗（② ⟹ ① ✓ 而 ① ⇏ ② ✗）。
**⚠ 非空性（L1）** ✓：**`disc ∣ T` 可满足** ✓（见证 ＝ `T := T₀ · r270Disc F G` ✓ **由本件构造给出** ✓）；
**`IsUnit` 款在同一见证上成立** ✓（`r269_isUnit_algebraMap_of_dvd` ✓）；**接线包的假设两行**（`δ` 双射 ✓ ＋
`hProj` ✓）的非空性**不在本件** ✗（§4.70 ✓ 的 `ℚ`／`PUnit` 档 ✓ 与 §4.71 ✓ 的分裂档 ✓ 已登记 ✓）。
**🔴 不声称** ✗：**不**声称接线包的假设两行已证 ✗；**不**声称 `δ` 双射由 `disc ∣ T` **推出** ✗
（推出它的是 §4.74 ✓ 的秩 2 `⟸` **在该档** ✓，一般档**未落** ✗，见 270.C ✓）；
**不**声称两条源陈述已证 ✗。 -/
theorem r270_exists_realizationPropertyFieldFinite_of_noetherFixedWiring_discDvd
    {n : ℕ} {a : Fin n → NoetherInvariantField F G} {s₀ : NoetherInvariantField F G}
    (hs₀ : s₀ ≠ 0) (hinf : Infinite F) :
    ∃ (T : MvPolynomial G F) (_hT : T ≠ 0) (_hTinv : ∀ g : G, g • T = T)
      (_hdvd : r270Disc F G ∣ T)
      (_hunit : IsUnit (algebraMap (MvPolynomial G F) (Localization.Away T) (r270Disc F G)))
      (_hle : noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
        (Algebra.adjoin (MvPolynomial G F)
          ({(algebraMap (MvPolynomial G F) (NoetherField F G) T)⁻¹} : Set (NoetherField F G))))
      (instA : Algebra ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instT : letI := instA;
        IsScalarTower F ↥(noetherFixedCarrier F G a s₀) (Localization.Away T))
      (instM : MulSemiringAction G (Localization.Away T)),
      letI := instA
      letI := instT
      letI := instM
      ∃ (_hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
          (x : Localization.Away T), g • (r • x) = r • (g • x)),
        Function.Bijective (BTier.deltaToEndRingHom _hRG) →
        BTier.GaloisProjectiveHyp ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) G _hRG →
        RealizationPropertyFieldFinite F G ↥(noetherFixedCarrier F G a s₀)
          (Localization.Away T) := by
  classical
  have hs₀L : ((s₀ : NoetherInvariantField F G) : NoetherField F G) ≠ 0 :=
    fun h => hs₀ (Subtype.ext h)
  have ha_fix : ∀ (g : G) (i : Fin n),
      g • ((a i : NoetherInvariantField F G) : NoetherField F G)
        = ((a i : NoetherInvariantField F G) : NoetherField F G) :=
    fun g i => (a i).2 g
  have hs₀_fix : ∀ g : G,
      g • ((s₀ : NoetherInvariantField F G) : NoetherField F G)
        = ((s₀ : NoetherInvariantField F G) : NoetherField F G) :=
    fun g => s₀.2 g
  obtain ⟨T₀, hT₀ne, hT₀inv, hT₀le⟩ := exists_invariant_t_of_noether (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) hs₀L
  have hDne : r270Disc F G ≠ 0 := r270Disc_ne_zero
  have hDinv : ∀ g : G, g • r270Disc F G = r270Disc F G := fun g => r270_smul_disc g
  have hTne : T₀ * r270Disc F G ≠ 0 := mul_ne_zero hT₀ne hDne
  have hTinv : ∀ g : G, g • (T₀ * r270Disc F G) = T₀ * r270Disc F G := by
    intro g
    rw [smul_mul', hT₀inv g, hDinv g]
  have hTle : noetherFixedCarrier F G a s₀ ≤ Subalgebra.restrictScalars F
      (Algebra.adjoin (MvPolynomial G F)
        ({(algebraMap (MvPolynomial G F) (NoetherField F G) (T₀ * r270Disc F G))⁻¹}
          : Set (NoetherField F G))) :=
    hT₀le.trans (fun x hx => adjoin_away_mono (A := MvPolynomial G F)
      (L := NoetherField F G) T₀ (r270Disc F G) hDne hx)
  obtain ⟨ι, hι⟩ := exists_algHom_away_of_noetherAdjoin (F := F) (G := G)
    (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
    (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G))
    (T₀ * r270Disc F G) hTne hTle
  let instA : Algebra ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away (T₀ * r270Disc F G)) :=
    ι.toRingHom.toAlgebra
  have hST : IsScalarTower F ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away (T₀ * r270Disc F G)) :=
    inferInstance
  let instM : MulSemiringAction G (Localization.Away (T₀ * r270Disc F G)) :=
    awayMulSemiringAction (F := F) (G := G) (t := T₀ * r270Disc F G) hTinv
  have hact : ∀ (g : G) (p : MvPolynomial G F),
      g • (algebraMap (MvPolynomial G F) (Localization.Away (T₀ * r270Disc F G)) p)
        = algebraMap (MvPolynomial G F) (Localization.Away (T₀ * r270Disc F G)) (g • p) :=
    fun g p => awayRingHom_algebraMap (F := F) (G := G) (t := T₀ * r270Disc F G) hTinv g p
  have hS0R : ∀ r : ↥(noetherFixedCarrier F G a s₀),
      awayToFieldAlg (F := F) (G := G) (T₀ * r270Disc F G) hTne
          (algebraMap ↥(noetherFixedCarrier F G a s₀)
            (Localization.Away (T₀ * r270Disc F G)) r)
        = algebraMap ↥(noetherFixedCarrier F G a s₀) (NoetherField F G) r :=
    fun r => hι r
  have hRG : ∀ (g : G) (r : ↥(noetherFixedCarrier F G a s₀))
      (x : Localization.Away (T₀ * r270Disc F G)), g • (r • x) = r • (g • x) :=
    smulCommClass_away_of_algHom (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G))
      ha_fix hs₀_fix (T₀ * r270Disc F G) hTne hTinv ι hι
  have hSfix : ∀ (g : G) {x : NoetherField F G},
      x ∈ noetherFixedCarrier F G a s₀ → g • x = x :=
    smul_eq_self_of_mem_adjoin_of_fixed (F := F) (G := G)
      (a := fun i => ((a i : NoetherInvariantField F G) : NoetherField F G))
      (s₀ := ((s₀ : NoetherInvariantField F G) : NoetherField F G)) ha_fix hs₀_fix
  have hunit : IsUnit (algebraMap (MvPolynomial G F)
      (Localization.Away (T₀ * r270Disc F G)) (r270Disc F G)) :=
    r269_isUnit_algebraMap_of_dvd (r270Disc F G) (T₀ * r270Disc F G) (dvd_mul_left _ _)
  refine ⟨T₀ * r270Disc F G, hTne, hTinv, dvd_mul_left _ _, hunit, hTle, instA, hST, instM,
    hRG, ?_⟩
  intro hδ hProj
  have hgal : BTier.IsGaloisWithGroup ↥(noetherFixedCarrier F G a s₀)
      (Localization.Away (T₀ * r270Disc F G)) G hRG :=
    ⟨faithfulSMul_away_of_noetherAdjoin (F := F) (G := G) (T := T₀ * r270Disc F G) hTne hTinv,
      fun g r => BTier.algebraMap_fixed_of_smulCommClass hRG g r, hδ⟩
  exact realizationPropertyFieldFinite_of_subalgebra (F := F) (G := G)
    (S := noetherFixedCarrier F G a s₀) (t := T₀ * r270Disc F G) hTne hTinv hTle hSfix hact hRG
    hgal hProj hS0R hinf

end R270WiringDisc

#print axioms r270_exists_realizationPropertyFieldFinite_of_noetherFixedWiring_discDvd

/-! #### 270.C 环档：**迹公式 ＋ 迹形式幺模 ⟹ `δ` 满射**（**任意秩** ✓） -/

section R270TraceUnimodular

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

/-- **乘法迹（任意指标型）** ✓：与 §4.75 ✓ 的 `r269MulTrace` ✓ **同一公式** ✓
（`Matrix.trace (Matrix.of fun i j => (b.repr (x * b j)) i)` ✓），唯指标型从 `Fin n` ✓
放宽到**任意 `Fintype`** ✓（**本轮的秩自由化** ✓）。 -/
def r270MulTrace {ι : Type*} [Fintype ι] (b : Module.Basis ι R S) (x : S) : R :=
  Matrix.trace (Matrix.of fun i j => (b.repr (x * b j)) i)

/-- **口径核验** ✓✅（**机检** ✓）：`Fin n` 档与 §4.75 ✓ 的 `r269MulTrace` ✓ **逐字一致** ✓
（`rfl` ✓ ⟹ 本条把两个口径**钉死** ✓，下游可互换 ✓）。 -/
theorem r270MulTrace_fin {n : ℕ} (b : Module.Basis (Fin n) R S) (x : S) :
    r270MulTrace b x = r269MulTrace b x := rfl

/-! ##### 270.E **乘法迹的群不变性**（第 283 轮；T3 承重构件）

**⚠ 接口实测** ✓（**步骤 ①**，**不得凭名猜** ✗；逐字见 `.abgv52-scratch/logs/recon-r283.txt` ✓）：
本工程 `LinearMap.mul` 的 apply 引理名 ＝ **`LinearMap.mul_apply'`** ✓（**带撇号** ✓，`rfl` 型 ✓）；
**`LinearMap.mul_apply`（无撇）库中不存在** ✗（`Unknown constant` ✓）。
**⚠ 第四步的库层条件** ✗：`LinearMap.trace_conj'` ✓ 与 `LinearMap.trace_eq_matrix_trace` ✓
**未被本模块传递 import** ✗ ⟹ 本节新增 `import Mathlib.LinearAlgebra.Trace` ✓（本件**唯一** import 增改 ✓）。

**⚠ §244.2 ② 修正** ✗：其**字面形**（**无外层 `g •`** ✗）**为假** ✓ ——
机器反例（`.abgv52-scratch/probe-r283.lean` ✓）：`R[C₃]` 上 `g = ofAdd 1` ✓、`x = δ₁` ✓、`y = δ_g` ✓。
**⟹ 正确逐点形须带外层 `g •`** ✓（`r283_mul_smul_apply` ✓）。 -/

section R283TraceInvariant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype G] in
/-- **② 逐点形（修正版）** ✓：`((LinearMap.mul R S) (g • x)) y = g • (((LinearMap.mul R S) x) (g⁻¹ • y))` ✓
（`(g•x)*y = g•(x·(g⁻¹•y))` ✓；`smul_mul'` ✓ ＋ `smul_inv_smul` ✓）。 -/
lemma r283_mul_smul_apply (g : G) (x y : S) :
    ((LinearMap.mul R S) (g • x)) y = g • (((LinearMap.mul R S) x) (g⁻¹ • y)) := by
  rw [LinearMap.mul_apply', LinearMap.mul_apply', smul_mul', smul_inv_smul]

omit [Fintype G] in
/-- **`c_g : y ↦ g • y` 的 `R`-线性等价** ✓（承 probe-r281 ✓，rc=0 ✓；两处槽形修法见 §242 ✓）。 -/
def r283ActEquiv (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x)) (g : G) :
    S ≃ₗ[R] S where
  toFun := fun y => g • y
  invFun := fun y => g⁻¹ • y
  left_inv := fun y => by change g⁻¹ • (g • y) = y; rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv := fun y => by change g • (g⁻¹ • y) = y; rw [← mul_smul, mul_inv_cancel, one_smul]
  map_add' := fun x y => by change g • (x + y) = g • x + g • y; rw [smul_add]
  map_smul' := fun r y => hRG g r y

omit [Fintype G] in
/-- **③ 映射等式（共轭式）** ✓：`m_{g•x} = c_g ∘ m_x ∘ c_g⁻¹` ✓
（`LinearEquiv.conj` ✓ 形，**直接喂** `LinearMap.trace_conj'` ✓）。 -/
lemma r283_mul_smul_conj (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (g : G) (x : S) :
    (LinearMap.mul R S) (g • x) = (r283ActEquiv hRG g).conj ((LinearMap.mul R S) x) := by
  ext y
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change ((LinearMap.mul R S) (g • x)) y = g • (((LinearMap.mul R S) x) (g⁻¹ • y))
  exact r283_mul_smul_apply (R := R) (S := S) g x y

/-- **④a 基变换桥** ✓：`r270MulTrace b x = LinearMap.trace R S (m_x)` ✓
（`LinearMap.trace_eq_matrix_trace` ✓ ＋ `LinearMap.toMatrix_apply` ✓ ＋ `LinearMap.mul_apply'` ✓）。
**⚠ 工艺** ✓：`r270MulTrace` 的 `Matrix.of` 与 `LinearMap.toMatrix` **非 defeq** ✗ ⟹ 须显式矩阵等式 ✓。 -/
lemma r283MulTrace_eq_linearMapTrace (b : Module.Basis ι R S) (x : S) :
    r270MulTrace b x = LinearMap.trace R S (LinearMap.mul R S x) := by
  rw [r270MulTrace]
  have hmat : Matrix.of (fun i j => (b.repr (x * b j)) i)
      = LinearMap.toMatrix b b (LinearMap.mul R S x) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [Matrix.of_apply, LinearMap.mul_apply']
  rw [hmat, ← LinearMap.trace_eq_matrix_trace R b (LinearMap.mul R S x)]

omit [Fintype G] in
/-- **④b 迹形式群不变（T3 承重构件）** ✓✅：`Tr_b (g • x) = Tr_b x` ✓ ——
`LinearMap.trace_conj'` ✓ 的直接实例（`m_{g•x}` 与 `m_x` 共轭 ⟹ 迹不变 ✓）。 -/
theorem r283_r270MulTrace_smul (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (b : Module.Basis ι R S) (g : G) (x : S) :
    r270MulTrace b (g • x) = r270MulTrace b x := by
  rw [r283MulTrace_eq_linearMapTrace, r283MulTrace_eq_linearMapTrace,
    r283_mul_smul_conj hRG g x]
  exact LinearMap.trace_conj' (R := R) (M := S) (f := LinearMap.mul R S x)
    (e := r283ActEquiv hRG g)

end R283TraceInvariant

/-! ##### 270.F **判据等价：迹公式 ⟺ `η` 在 `ker Tr` 上为零**（第 284 轮；T3 缺口收缩） -/

section R284TraceCriterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `r270MulTrace b` 在第二变元上**加法**性 ✓（经基桥 ＋ `LinearMap.trace` 的线性 ✓）。 -/
lemma r284MulTrace_add (b : Module.Basis ι R S) (x y : S) :
    r270MulTrace b (x + y) = r270MulTrace b x + r270MulTrace b y := by
  rw [r283MulTrace_eq_linearMapTrace, r283MulTrace_eq_linearMapTrace,
    r283MulTrace_eq_linearMapTrace, map_add (LinearMap.mul R S) x y,
    map_add (LinearMap.trace R S)]

/-- `r270MulTrace b` 在第二变元上**纯量**性 ✓（`smul_eq_mul` ✓）。 -/
lemma r284MulTrace_smul (b : Module.Basis ι R S) (r : R) (x : S) :
    r270MulTrace b (r • x) = r * r270MulTrace b x := by
  rw [r283MulTrace_eq_linearMapTrace, r283MulTrace_eq_linearMapTrace,
    map_smul (LinearMap.mul R S) r x,
    map_smul (LinearMap.trace R S) r (LinearMap.mul R S x), smul_eq_mul]

/-- `r270MulTrace b` 作 `R`-线性泛函 ✓（末步 `smul_eq_mul` 穿透 `R` 上的纯量形 ✓）。 -/
noncomputable def r284MulTraceLinear (b : Module.Basis ι R S) : S →ₗ[R] R where
  toFun := r270MulTrace b
  map_add' := r284MulTrace_add b
  map_smul' := fun r x => by
    rw [r284MulTrace_smul]
    rfl

/-- `η z := ∑_g g • z` 是 `G`-固定元 ✓（`Finset.smul_sum` ✓ ＋ `← mul_smul` ✓ ＋
`Equiv.sum_comp (Equiv.mulLeft h)` ✓）。 -/
lemma r284_eta_fixed (h : G) (z : S) : h • (∑ g : G, g • z) = ∑ g : G, g • z := by
  rw [Finset.smul_sum]
  simp_rw [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => g • z)

/-- **平均迹公式** ✓：`Tr_b (η z) = |G| · Tr_b z` ✓ —— 迹形式群不变（`r283_r270MulTrace_smul` ✓）
沿有限和的直接推论 ✓。 -/
lemma r284MulTrace_eta (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (b : Module.Basis ι R S) (z : S) :
    r270MulTrace b (∑ g : G, g • z) = (Fintype.card G : R) * r270MulTrace b z := by
  change r284MulTraceLinear b (∑ g : G, g • z) = _
  rw [map_sum]
  simp only [r284MulTraceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_congr rfl (fun g _ => r283_r270MulTrace_smul hRG b g z),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **纯量算子的迹** ✓：`Tr_b (algebraMap r) = |ι| · r` ✓（纯量算子 ＝ `r • id` ✓，
`trace id = |ι|` ✓ 经 `toMatrix` ＋ `trace_one` ✓）。 -/
lemma r284MulTrace_algebraMap (b : Module.Basis ι R S) (r : R) :
    r270MulTrace b (algebraMap R S r) = (Fintype.card ι : R) * r := by
  rw [r283MulTrace_eq_linearMapTrace]
  have hmul : LinearMap.mul R S (algebraMap R S r) = r • (LinearMap.id : S →ₗ[R] S) := by
    ext x
    rw [LinearMap.mul_apply', LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def]
  have htrace : LinearMap.trace R S (LinearMap.id : S →ₗ[R] S) = (Fintype.card ι : R) := by
    rw [LinearMap.trace_eq_matrix_trace R b LinearMap.id, ← Module.End.one_eq_id,
      LinearMap.toMatrix_one, Matrix.trace_one]
  rw [hmul, map_smul (LinearMap.trace R S) r LinearMap.id, smul_eq_mul, htrace, mul_comm]

set_option maxHeartbeats 1000000 in
/-- **🔴 判据等价（第 284 轮主结果）** ✓✅：在 `Fintype.card ι = Fintype.card G` ✓ 与
`|G|` 可消（`hreg` ✓，形如 `|G| • a = 0 → a = 0` ✓）下：
**迹公式 ⇔ `η` 在 `ker Tr_b` 上为零** ✓。
**证** ✓：**(⟹)** 迹公式取 `Tr x = 0` ✓；**(⟸)** 令 `D := η z − algebraMap (Tr_b z)` ✓，先
`Tr_b D = |G|·Tr_b z − |ι|·Tr_b z = 0` ✓（`r284MulTrace_eta` ＋ `r284MulTrace_algebraMap` ＋ `hcard` ✓）；
再 `η D = |G| • D` ✓（`η(η z) = |G| • η z` ✓ ＋ `g` 固定纯量 ✓）；由 `hker` 得 `|G| • D = 0` ✓；
`hreg` 收口 `D = 0` ✓。
**⚠ 意义** ✓：**T3 的唯一缺口收缩为一条** —— 「登记表是否强制 `η|ker Tr = 0`」✓（见 §245.4 ✓）。
**🔴 不声称** ✗：**不**声称 `η|ker Tr = 0` 成立 ✗；**不**声称登记表推出迹公式 ✗。 -/
theorem r284_traceFormula_iff_eta_kerTrace
    (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (b : Module.Basis ι R S) (hcard : Fintype.card ι = Fintype.card G)
    (hreg : ∀ a : S, Fintype.card G • a = 0 → a = 0) :
    (∀ z : S, algebraMap R S (r270MulTrace b z) = ∑ g : G, g • z) ↔
      (∀ x : S, r270MulTrace b x = 0 → (∑ g : G, g • x) = 0) := by
  constructor
  · intro hTr x hx
    rw [← hTr x, hx, map_zero]
  · intro hker z
    set D : S := (∑ g : G, g • z) - algebraMap R S (r270MulTrace b z) with hD
    have hDtr : r270MulTrace b D = 0 := by
      change r284MulTraceLinear b D = 0
      rw [hD, map_sub]
      change r270MulTrace b (∑ g : G, g • z)
        - r270MulTrace b (algebraMap R S (r270MulTrace b z)) = 0
      rw [r284MulTrace_eta hRG b z, r284MulTrace_algebraMap, hcard]
      exact sub_self _
    have hDeta : (∑ g : G, g • D) = 0 := hker D hDtr
    have hcalc : (∑ g : G, g • D) = (Fintype.card G : R) • D := by
      rw [hD]
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib]
      have h1 : (∑ g : G, g • (∑ h : G, h • z))
          = (Fintype.card G : R) • (∑ h : G, h • z) := by
        rw [Finset.sum_congr rfl (fun g _ => r284_eta_fixed g z), Finset.sum_const,
          Finset.card_univ]
        exact (Nat.cast_smul_eq_nsmul (R := R) _ _).symm
      have h2 : (∑ g : G, g • algebraMap R S (r270MulTrace b z))
          = (Fintype.card G : R) • algebraMap R S (r270MulTrace b z) := by
        rw [Finset.sum_congr rfl
            (fun g _ => BTier.algebraMap_fixed_of_smulCommClass hRG g _),
          Finset.sum_const, Finset.card_univ]
        exact (Nat.cast_smul_eq_nsmul (R := R) _ _).symm
      rw [h1, h2]
    have hzero : (Fintype.card G : R) • D = 0 := by rw [← hcalc, hDeta]
    have hzero' : Fintype.card G • D = 0 :=
      (Nat.cast_smul_eq_nsmul (R := R) _ _).symm.trans hzero
    have hD0 : D = 0 := hreg D hzero'
    rw [hD] at hD0
    exact (sub_eq_zero.mp hD0).symm

end R284TraceCriterion

/-! ##### 270.G **源文路线（field-tier）：正规基 ＋ 迹恒等式**（第 285 轮；直用 mathlib 已发表件）

**📌 用户指令** ✓（2026-10-14）：「**需形式化的内容，若已发表文章有，则使用即可**」✓。
**源侧** ✓：`Saltman1982` **`proposition-0-5(c)`**（印 254 ✓）：「`L` has a **normal basis** over `K`；
`L⁺ ≅ K[G]` as `K[G]` modules」✓ —— **field 档** ✓，源 `theorem-5-1` 证明所使用者 ✓（`lemma-5-2` ✓）。
**库内现成件** ✓：**`IsGalois.normalBasis`** ✓（`FieldTheory/Galois/NormalBasis.lean` ✓）＋
**`trace_eq_sum_automorphisms`** ✓（`RingTheory/Trace/Basic.lean:263` ✓）—— **本条只作桥接，不重证** ✓。 -/

section R285SourceRoute

/-- **桥：`r270MulTrace` ＝ mathlib `Algebra.trace`** ✓（任意交换环 ✓、任意基 ✓）——
`+` 侧 `r283MulTrace_eq_linearMapTrace` ✓，`−` 侧 `Algebra.trace_apply` ✓（`Algebra.lmul` 与
`LinearMap.mul` 同函 ✓）。**⟹ mathlib 的迹理论（环档 ✓）可与本工程 `r270MulTrace` 互用** ✓。 -/
lemma r285MulTrace_eq_algebraTrace {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (x : S) :
    r270MulTrace b x = Algebra.trace R S x := by
  rw [r283MulTrace_eq_linearMapTrace, Algebra.trace_apply]
  congr 1

/-- **field-tier 迹恒等式** ✓✅（**直用 mathlib** ✓）：有限 Galois 扩张 `L/K` 上
`Algebra.trace K L x = ∑_{σ ∈ Gal(L/K)} σ • x`（`algebraMap` 形 ✓）。
**⚠ 口径** ✓：mathlib 侧写 `σ x`；本件右侧写 `σ • x`（`AlgEquiv.applyMulSemiringAction` ✓，`rfl` ✓ 同函 ✓）。 -/
theorem r285_traceFormula_field {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : L ≃ₐ[K] L, σ • x := by
  rw [trace_eq_sum_automorphisms x]
  exact Finset.sum_congr rfl (fun σ _ => by rfl)

/-- **field-tier 正规基存在性** ✓✅（**直用 mathlib** ✓）：源 `proposition-0-5(c)` ✓ 的
**field 档机检版** ✓ —— `∃ b : Basis Gal(L/K) K L, b σ = σ (b 1)` ✓。
**🔴 不声称** ✗：本件**不**声称 ring-tier `TraceUnimodularSufficiency269` ✓（**并行登记** ✓，见 §246.4 ✓）。 -/
theorem r285_normalBasis_field {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ b : Module.Basis (L ≃ₐ[K] L) K L, ∀ σ : L ≃ₐ[K] L, b σ = σ (b 1) :=
  ⟨IsGalois.normalBasis K L, IsGalois.normalBasis_apply⟩

end R285SourceRoute




/-- **`δ` 在求和上的取值式** ✓：`δ (∑_g single g (s g)) x = ∑_g s g · (g • x)` ✓
（`map_sum` ✓ ＋ `LinearMap.sum_apply` ✓ ＋ `deltaToEndAdd_single` ✓）。 -/
lemma r270_delta_sum_apply (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (s : G → S) (x : S) :
    BTier.deltaToEndRingHom hRG (∑ g : G, SkewMonoidAlgebra.single g (s g)) x
      = ∑ g : G, s g * (g • x) := by
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  change BTier.deltaToEndAdd hRG (SkewMonoidAlgebra.single g (s g)) x = s g * (g • x)
  rw [BTier.deltaToEndAdd_single, Module.End.mul_apply]
  rfl

set_option maxHeartbeats 1000000 in
/-- **🔴🔴 主结果 ②（O2）** ✓✅：**迹公式 ＋ 迹形式幺模 ⟹ `δ` 满射** ✓ ——
**任意交换环** ✓、**任意有限群 `G`** ✓、**任意 `R`-基 `b : Basis ι R S`** ✓（**秩 `|ι|` 不受限** ✗）。
**⚠ 机制（四步，全机检 ✓）**：**①** 幺模 ＋ `b.coord i` ✓ ⟹ **迹对偶元** ✓ `y_i` ✓
（`Tr_b (b_j · y_i) = δ_{ji}` ✓，`Module.Basis.repr_self` ✓ ＋ `Finsupp.single_apply` ✓）；
**②** **迹公式** ✓ 把 `∑_g (g•y_i)·(g•b_j)` ✓ 打成 `∑_g g•(y_i·b_j)` ✓ ＝ `algebraMap (Tr_b (y_i·b_j))` ✓
⟹ **正交关系** ✓ `∑_g (g•y_i)·(g•b_j) = algebraMap (if i = j then 1 else 0)` ✓；
**③** **显式预像** ✓：`x := ∑_g single g (∑_i f(b_i)·(g•y_i))` ✓；
**④** 逐基元核验 ✓（`b.ext` ✓ ＋ `Finset.sum_comm` ✓ ＋ ② 消去 ⟹ `δ x = f` ✓）。
**⚠ 未使用的假设** ✓（**如实** ✓）：**秩假设** ✗ 与 **`δ` 单射** ✗ **均未被本证明消费** ✓
（本件**不把它们写进假设表** ✓ —— 登记件形见下件 ✓）。
**🔴 不声称** ✗：**不**声称迹公式由登记件的假设推出 ✗（＝ 唯一缺口 ✓，见节头强度序 ② ✓）；
**不**声称登记件 `TraceUnimodularSufficiency269` ✓ 成立 ✗。 -/
theorem r270_delta_surjective_of_traceFormula {ι : Type*} [Fintype ι]
    (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x))
    (b : Module.Basis ι R S)
    (hTr : ∀ z : S, algebraMap R S (r270MulTrace b z) = ∑ g : G, g • z)
    (hUni : ∀ φ : S →ₗ[R] R, ∃ y : S, ∀ x : S, φ x = r270MulTrace b (x * y)) :
    Function.Surjective (BTier.deltaToEndRingHom hRG) := by
  classical
  choose y hy using fun i : ι => hUni (b.coord i)
  have horth : ∀ i j : ι,
      (∑ g : G, (g • y i) * (g • b j)) = algebraMap R S (if j = i then 1 else 0) := by
    intro i j
    have h1 : (∑ g : G, (g • y i) * (g • b j)) = ∑ g : G, g • (y i * b j) := by
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [smul_mul']
    rw [h1, ← hTr (y i * b j)]
    congr 1
    rw [mul_comm (y i) (b j), ← hy i (b j), Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  intro f
  refine ⟨∑ g : G, SkewMonoidAlgebra.single g (∑ i : ι, f (b i) * (g • y i)), ?_⟩
  refine b.ext (fun j => ?_)
  rw [r270_delta_sum_apply]
  calc ∑ g : G, (∑ i : ι, f (b i) * (g • y i)) * (g • b j)
      = ∑ g : G, ∑ i : ι, f (b i) * ((g • y i) * (g • b j)) :=
        Finset.sum_congr rfl (fun g _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring))
    _ = ∑ i : ι, ∑ g : G, f (b i) * ((g • y i) * (g • b j)) := Finset.sum_comm
    _ = ∑ i : ι, f (b i) * algebraMap R S (if j = i then 1 else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.mul_sum, horth i j]
    _ = f (b j) := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          rw [if_neg (Ne.symm hij), map_zero, mul_zero]
        · intro hj; exact absurd (Finset.mem_univ j) hj

set_option maxHeartbeats 1000000 in
/-- **登记件 ＋ **一条迹公式** ⟹ 成立** ✓✅（**形对照件** ✓）：逐字取 §4.75 ✓ 的
`TraceUnimodularSufficiency269` ✓ 的假设表 ✓（乘法迹幺模 ＋ **秩 ＝ `|G|`** ✓ ＋ **`δ` 单射** ✓），
**另加**迹公式 ✓ 一行 ✓ ⟹ `δ` 满射 ✓。
**⚠ 强度序（**勿读作等价** ✗）**：本条的**秩**行 ✓ 与 **单射**行 ✓ **在证明中不被使用** ✗
（**如实登记** ✓：它们留在表内**只**为与登记件**逐字同形** ✓，**不冒充为已消费** ✗）；
真正的**唯一**缺口是**迹公式** ✓（**证明义务** ✓，见节头 ✓）。
**🔴 不声称** ✗：**不**声称 `TraceUnimodularSufficiency269` ✓ 成立 ✗。 -/
theorem r270_traceUnimodularSufficiency_of_traceFormula :
    ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (G : Type) [Group G] [Fintype G]
      [MulSemiringAction G S]
      (hRG : ∀ (g : G) (r : R) (x : S), g • (r • x) = r • (g • x)) {n : ℕ}
      (b : Module.Basis (Fin n) R S),
      Fintype.card G = n →
      (∀ z : S, algebraMap R S (r269MulTrace b z) = ∑ g : G, g • z) →
      Function.Injective (BTier.deltaToEndRingHom hRG) →
      (∀ φ : S →ₗ[R] R, ∃ y : S, ∀ x : S, φ x = r269MulTrace b (x * y)) →
      Function.Surjective (BTier.deltaToEndRingHom hRG) := by
  intro R S _ _ _ G _ _ _ hRG n b _hcard hTr _hinj hUni
  exact r270_delta_surjective_of_traceFormula hRG b hTr hUni

end R270TraceUnimodular

#print axioms r270MulTrace_fin
#print axioms r270_delta_sum_apply
#print axioms r270_delta_surjective_of_traceFormula
#print axioms r270_traceUnimodularSufficiency_of_traceFormula
#print axioms r283_mul_smul_apply
#print axioms r283_mul_smul_conj
#print axioms r283MulTrace_eq_linearMapTrace
#print axioms r283_r270MulTrace_smul
#print axioms r284MulTrace_add
#print axioms r284MulTrace_smul
#print axioms r284_eta_fixed
#print axioms r284MulTrace_eta
#print axioms r284MulTrace_algebraMap
#print axioms r284_traceFormula_iff_eta_kerTrace
#print axioms r285MulTrace_eq_algebraTrace
#print axioms r285_traceFormula_field
#print axioms r285_normalBasis_field

/-! #### 270.D **非空性（L1）**：分裂载体（**任意交换环** ✓）＋ 二次载体（迹公式**自动** ✓） -/

section R270RegularNonempty

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] [DecidableEq G]

attribute [local instance] regularSMul regularMSA

omit [Group G] in
/-- **分裂载体的乘法迹** ✓：标准基（`Pi.basisFun` ✓）下「乘 `z`」的矩阵是**对角阵** ✓
（对角元 `z i` ✓）⟹ `Tr_b z = ∑_g z g` ✓。 -/
lemma r270_mulTrace_basisFun (z : G → R) :
    r270MulTrace (Pi.basisFun R G) z = ∑ g : G, z g := by
  rw [r270MulTrace]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.basisFun_apply, Pi.basisFun_repr, Pi.mul_apply, Pi.single_eq_same, mul_one]

/-- **✅ 分裂载体上迹公式成立** ✓✅（**任意交换环** ✓ ＋ **任意有限 `G`** ✓）：
`algebraMap (∑_g z g) = ∑_g g • z` ✓ —— 两侧逐坐标相等 ✓（右端在坐标 `h` 处 ＝ `∑_g z (g⁻¹h)` ✓，
重标号 `g ↦ g⁻¹h` 后 ＝ `∑ g, z g` ✓；`Equiv.sum_comp` ✓）。 -/
theorem r270_traceFormula_regularAction (z : G → R) :
    algebraMap R (G → R) (r270MulTrace (Pi.basisFun R G) z) = ∑ g : G, g • z := by
  funext h
  rw [r270_mulTrace_basisFun]
  simp only [Pi.algebraMap_apply, Algebra.algebraMap_self_apply, Finset.sum_apply,
    regularSMul_apply]
  exact (Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight h)) z).symm

omit [Group G] in
/-- **✅ 分裂载体上迹形式幺模** ✓✅（**任意交换环** ✓）：对任意 `φ` ✓ 取
`y i := φ (Pi.single i 1)` ✓ ⟹ `Tr_b (x · y) = ∑_i x i · φ (single i 1) = φ x` ✓
（`Finset.sum_eq_single` ✓ 展开 `x = ∑_i x i • single i 1` ✓）。 -/
theorem r270_unimodular_regularAction (φ : (G → R) →ₗ[R] R) :
    ∃ y : G → R, ∀ x : G → R, φ x = r270MulTrace (Pi.basisFun R G) (x * y) := by
  refine ⟨fun i => φ (Pi.single i (1 : R)), fun x => ?_⟩
  rw [r270_mulTrace_basisFun]
  have hx : x = ∑ i : G, x i • (Pi.single i (1 : R)) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro i _ hij
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  calc φ x = φ (∑ i : G, x i • (Pi.single i (1 : R))) := congrArg φ hx
    _ = ∑ i : G, x i * φ (Pi.single i (1 : R)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, smul_eq_mul]
    _ = ∑ i : G, (x * fun i => φ (Pi.single i (1 : R))) i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Pi.mul_apply]

set_option maxHeartbeats 1000000 in
/-- **✅✅ 分裂载体上 `δ` 满射** ✓✅（**任意交换环** ✓ ＋ **任意有限 `G`** ✓）：
由 270.C ✓ 的主定理 ✓ 在 `S = G → R` ✓、`b = Pi.basisFun R G` ✓ 上**直接消费**上面两条 ✓。
**⚠ 新意** ✓（**如实** ✓）：§4.72 ✓ 的同类结果（`bijective_deltaToEndRingHom_regularAction` ✓）
**限 `K` 域** ✗；本条把**同一载体**推到**任意交换环** ✓（机制不同：**不用维数** ✗，
**用迹形式对偶基 ＋ 迹公式** ✓）。 -/
theorem r270_delta_surjective_regularAction :
    Function.Surjective (BTier.deltaToEndRingHom (regular_smul_comm (G := G) (K := R))) :=
  r270_delta_surjective_of_traceFormula (regular_smul_comm (G := G) (K := R))
    (Pi.basisFun R G) r270_traceFormula_regularAction r270_unimodular_regularAction

/-- **秩 3 实例** ✓（**L1 非空洞** ✓）：`|Multiplicative (ZMod 3)| = 3` ✓ ——
⟹ 270.C ✓ 的假设（迹公式 ✓ ＋ 幺模 ✓）在**秩 3** ✓（**环档** ✓：`R = ℤ` 可用 ✓）可满足 ✓，
即 §4.74 ✓ 的秩 2 之外的**新档** ✓。 -/
theorem r270_card_zmod_three : Fintype.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Fintype.card_multiplicative, ZMod.card]

end R270RegularNonempty

#print axioms r270_mulTrace_basisFun
#print axioms r270_traceFormula_regularAction
#print axioms r270_unimodular_regularAction
#print axioms r270_delta_surjective_regularAction
#print axioms r270_card_zmod_three

section R270QuadraticTrace

attribute [local instance] qaMSA268

variable {R : Type*} [CommRing R] {a b : R}

set_option maxHeartbeats 1000000 in
/-- **✅ 二次载体上迹公式自动成立** ✓✅（**非分裂** ✓ 的非空性见证 ✓）：`G = C₂` ✓ 经 `star` ✓ 作用，
`Tr (mk x y) = 2x + by` ✓（`QuadraticAlgebra.trace_def` ✓）而 `z + star z = algebraMap (2x + by)` ✓
（`star_mk` ✓：`star (mk x y) = mk (x + b*y) (−y)` ✓）⟹ 迹公式 ✓。
**⚠ 意义** ✓（**两条** ✓）：**(甲)** 270.C ✓ 的**新假设**（迹公式 ✓）在 §4.74 ✓ 的**载体族**上
**自动满足** ✓ ⟹ 270.C ✓ 与 §4.74 ✓ 的秩 2 `⟸` ✓ **不矛盾** ✓，且 270.C ✓ 是它的**推广方向** ✓；
**(乙)** 秩 2 档的幺模性判别**已由 §4.74 ✓ 机检** ✓（`qaTraceUnimodular268_iff` ✓），
**两者的复合**（270.C ＋ §4.74 ⟹ 秩 2 `⟸` 的第二证）**本轮未落** ✗、**不声称** ✗。 -/
theorem r270_traceFormula_quadratic (z : QuadraticAlgebra R a b) :
    algebraMap R (QuadraticAlgebra R a b) (r270MulTrace (QuadraticAlgebra.basis a b) z)
      = ∑ g : Multiplicative (ZMod 2), g • z := by
  rw [r270MulTrace_fin, r269MulTrace_quadratic]
  have hsum : (∑ g : Multiplicative (ZMod 2), g • z) = z + star z := by
    have h1 : (Finset.univ : Finset (Multiplicative (ZMod 2)))
        = {1, Multiplicative.ofAdd 1} := by decide
    rw [h1, Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [qaConj268_smul_def, qaConj268_smul_def, qaConj268_one, qaConj268_gen]
  rw [hsum]
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.trace_def, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_add,
      QuadraticAlgebra.re_star]
    ring
  · rw [QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_add, QuadraticAlgebra.im_star]
    ring

end R270QuadraticTrace

#print axioms r270_traceFormula_quadratic

/-! ### 4.77 **域档 `(1b)`：维数论证**（第 287 轮）—— `rank = |G|` 时 **`δ` 单射 ⟹ 满射**（**不用迹形式／迹公式**）

**靶** ✓：`(1b)`（`δ` 满射）在**域档**的形态 —— 登记件 `TraceUnimodularSufficiency269`（§4.75 ✓）
在 `R = K` 为**域**时的形态 ✓。

**机检内容** ✓✅：`K` 域 ✓、`S` 有限维 `K`-代数 ✓、`|G| = finrank_K S` ✓（＝登记件的**秩假设** ✓）下
**`δ` 单射 ⟹ `δ` 满射** ✓。**机制** ✓（**纯维数** ✓，**全部用 mathlib 现成件** ✓）：
两侧都是 `K`-向量空间 ✓ —— 定义域 `SkewMonoidAlgebra S G` ✓（经 `SkewMonoidAlgebra.coeffLinearEquiv` ✓
与 `Module.finrank_finsupp` ✓ 得 `|G| · n` ✓）、陪域 `Module.End K S` ✓（经 `Module.finrank_linearMap` ✓ 得 `n · n` ✓），
秩假设使其**同维** ✓ ⟹ `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ✓ 收口 ✓。

**⚠ 意义（两条，逐字如实）** ✓：
**(甲)** 登记件 `TraceUnimodularSufficiency269` 的**域档**形态**为真** ✓，且其**迹形式幺模假设在该档未被使用** ✗ ——
即**迹形式／迹公式路线（第 268–284 轮）只在环档承重** ✓（域档早已由线性代数决定 ✓）；
**(乙)** 域档的 `(1b)` 因而**只欠 `δ` 单射** ✓（**不是**迹公式 ✗）。

**🔴 不声称** ✗：**不**声称**环档**形态 ✓（本件**只**做域档 ✓ —— 环档下两侧秩相等**不能**推出满射 ✗，
如 `ℤ →^2 ℤ` ✓）；**不**声称 `TraceUnimodularSufficiency269` 本身真或假 ✗；
**不**声称 `δ` 单射在**任何**档可得 ✗。
**⚠ 宇宙工艺** ✓：本条**取单一宇宙 `u`** ✓（`Module.finrank_finsupp` ✓ 要求指标型与系数型**同宇宙** ✗）；
**实例注册用 `let _inst`** ✓（**不用** `letI` ✗ —— 后者计警告 ✗，见 §5.1 工艺 1 ✓）。 -/

section FieldTierDeltaRank

/-- **域档 `(1b)`** ✓✅：`K` 域、`S` 有限维 `K`-代数、`|G| = finrank_K S` ⟹ **`δ` 单射 ⟹ 满射** ✓
（**维数论证** ✓，**不用迹形式／迹公式** ✗）。 -/
theorem delta_surjective_of_injective_of_card_eq_finrank
    {K S : Type u} [Field K] [CommRing S] [Algebra K S] [FiniteDimensional K S]
    {G : Type u} [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (k : K) (x : S), g • (k • x) = k • (g • x))
    (hcard : Fintype.card G = Module.finrank K S)
    (hinj : Function.Injective (BTier.deltaToEndRingHom hRG)) :
    Function.Surjective (BTier.deltaToEndRingHom hRG) := by
  classical
  let _inst : Module.Finite K (SkewMonoidAlgebra S G) :=
    Module.Finite.equiv (SkewMonoidAlgebra.coeffLinearEquiv (k := S) (G := G) (S := K)).symm
  have hdom : Module.finrank K (SkewMonoidAlgebra S G) = Fintype.card G * Module.finrank K S :=
    (SkewMonoidAlgebra.coeffLinearEquiv (k := S) (G := G) (S := K)).finrank_eq.trans
      (Module.finrank_finsupp (R := K) (M := S) (ι := G))
  have hcod : Module.finrank K (Module.End K S) = Module.finrank K S * Module.finrank K S :=
    Module.finrank_linearMap (R := K) (S := K) (M := S) (N := S)
  have heq : Module.finrank K (SkewMonoidAlgebra S G) = Module.finrank K (Module.End K S) := by
    rw [hdom, hcod, hcard]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := K) (V := SkewMonoidAlgebra S G) (V₂ := Module.End K S) heq
      (f := (BTier.deltaToEndLinearS hRG).restrictScalars K)).mp hinj

end FieldTierDeltaRank

#print axioms delta_surjective_of_injective_of_card_eq_finrank


/-! ### 4.78 **源 §1 载体（Artin–Schreier）的位移核**（第 288 轮）
—— 源 `theorem-1-2(a)` 的 `C_p`-作用的**代数核**（**残余 ③ 的第一口** ✓）

**源侧** ✓（**逐字** ✓，`raw/Saltman1982.tex:165–171` ✓，label `theorem-1-2` ✓）：
「Let `F` be a field of characteristic a prime `p`. Set `R = F[x]` and **`S = R{y^p − y − x}`**.
Then `S/R` is generic for `C_p` over `F`」✓ —— 其中 `R{y^p − y − a}` ＝ **`R[y]/(y^p − y − a)`** ✓
（**本工程尚未落该载体** ✗ —— `AdjoinRoot` 形态登记为下一手 ✓）。

**本轮落成** ✓✅（**载体无关** ✓ —— 对**任意**满足 `y^p − y − a = 0` 的 `y` 成立 ✓，故 `AdjoinRoot` 档
一旦落地即可**直接消费** ✓）：`char p`（`p` 素 ✓）下
**(i)** `as_shift` ✓：`k^p = k` ⟹ **`(y + k)^p − (y + k) − a = 0`** ✓；
**(ii)** `as_shift_one` ✓：**`(y + 1)^p − (y + 1) − a = 0`** ✓（源侧生成元 `y ↦ y + 1` ✓ 的位移核 ✓）。
**机制** ✓：`add_pow_char` ✓（Frobenius ✓）＋ 环运算 ✓ —— **一次算出整条 `𝔽_p`-轨道** ✓
（`k` 取遍素域元 ⟹ 载体的 `C_p`-自同构族 `y ↦ y + k` 的**关系保持** ✓ 得证 ✓）。

**⚠ 用途与缺口（逐字如实）** ✓：本条是 `S/R` **`C_p`-Galois**（源 `theorem-1-2` 的 (b) 款 ✓）证明的**第一步** ✓ ——
即「`y ↦ y+k` 保持定义关系」✓；**尚未落** ✗：**(甲)** 载体 `AdjoinRoot (X^p − X − C a)` 及其 `CharP` 传递 ✓（下一手 ✓）；
**(乙)** 由此得的 `MulSemiringAction (ZMod p)` ✓（自同构 ＋ 群作用公理 ✓）；
**(丙)** `IsGaloisWithGroup` 的**另两款** ✗（忠实性 ✓／不动环 ✓／`δ` 双射 ✓）。

**🔴 不声称** ✗：**不**声称源 `theorem-1-2` 已证 ✗（**只**落位移核 ✓）；**不**声称载体已落 ✗；
**不**声称残余 ③ 已开 ✗ —— 本条**只**是它的**第一口** ✓；**不**声称 `δ` 满射在载体档可得 ✗。 -/

section ArtinSchreierShift

/-- **AS 位移核（素域档）** ✓：`char p`（`p` 素）下，`k^p = k` ⟹
`y^p − y − a = 0` 时 **`(y + k)^p − (y + k) − a = 0`** ✓ —— 即 `y ↦ y + k` **保持 AS 定义关系** ✓。 -/
theorem as_shift {A : Type*} [CommRing A] {p : ℕ} [CharP A p] (hp : p.Prime) {y a k : A}
    (hk : k ^ p = k) (h : y ^ p - y - a = 0) : (y + k) ^ p - (y + k) - a = 0 := by
  let _inst : Fact p.Prime := ⟨hp⟩
  have h1 : (y + k) ^ p = y ^ p + k := by rw [add_pow_char, hk]
  rw [h1, show y ^ p + k - (y + k) - a = y ^ p - y - a by ring]
  exact h

/-- **AS 位移核（`+1` 档）** ✓：源侧生成元 `y ↦ y + 1` ✓（源 `theorem-1-2(a)` 的 `C_p` 作用 ✓）的关系保持 ✓。 -/
theorem as_shift_one {A : Type*} [CommRing A] {p : ℕ} [CharP A p] (hp : p.Prime) {y a : A}
    (h : y ^ p - y - a = 0) : (y + 1) ^ p - (y + 1) - a = 0 :=
  as_shift hp (by rw [one_pow]) h

end ArtinSchreierShift

#print axioms as_shift
#print axioms as_shift_one


/-! ### 4.79 **源 §1 载体（Artin–Schreier）落地 ＋ 移位自同态**（第 290 轮）
—— 源 `theorem-1-2(a)` 的载体 `R{y^p − y − x}` 与其 `C_p`-作用生成端 ✓

**源侧** ✓（**逐字** ✓，`raw/Saltman1982.tex:165–171` ✓，label `theorem-1-2` ✓）：
「Let `F` be a field of characteristic a prime `p`. Set `R = F[x]` and **`S = R{y^p − y − x}`**」✓
—— 其中 `R{y^p − y − a}` ＝ **`R[y]/(y^p − y − a)`** ✓（本节的 `asCarrier` ✓ 即其**逐字对应** ✓）。

**落成四件** ✓✅：**(i)** **`asCarrier`** ✓；**(ii)** **`as_subst`** ✓（代入恒等式 ✓）；
**(iii)** **`as_shift_mk`** ✓（`k^p = k` ⟹ 代入后 ∈ `(f)` ✓ —— **移位降入载体** ✓）；
**(iv)** **`asShiftHom`** ✓✅（**载体上 `y ↦ y + k` 自同态** ✓ —— 源 `C_p`-作用的**生成端** ✓，
经 `AdjoinRoot.lift` ✓ ＋ `Polynomial.hom_eval₂` ✓ 把 (iii) 搬入 ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(甲)** **不必**在载体上造 `CharP` ✗ —— 代入计算**在 `R[X]` 内**完成 ✓
（`charP_of_injective_algebraMap Polynomial.C_injective` ✓ 一行 ✓），再经 `mk` 降入 ✓（绕开
「`AdjoinRoot` 档 `CharP` 不自动合成」✗）；**(乙)** **宿主作用域** ✗：本文件 `open … MvPolynomial` ✓
⟹ 未限定的 `X`／`C`／`aeval` 会解析到 `MvPolynomial` 版本 ✗ ⟹ 多项式类新件**一律具名限定** ✓
（`Polynomial.X`／`Polynomial.C`／`Polynomial.aeval` ✓）；**(丙)** **`Polynomial.aeval` 的推挤须显式 `rw` 链** ✓
（`rw [map_sub, map_sub, map_pow, Polynomial.aeval_X, h1, Polynomial.aeval_C]` ✓ —— **`simp only` 组合不命中** ✗，
实测两套皆失败 ✓），随后 `C (k^p − k)` 与 `algebraMap` 两处**形状换算** ✓ 才可 `ring` 收口 ✓。

**⚠ 尚未落（下一手）** ✗：**(甲)** 移位**双射性** ✓（逆 ＝ 移位 `-k` ✓）⟹ **自同构** ✓；
**(乙)** **`MulSemiringAction (Multiplicative (ZMod p)) asCarrier`** ✓；**(丙)** `IsGaloisWithGroup` 三款 ✗。

**🔴 不声称** ✗：**不**声称源 `theorem-1-2` 已证 ✗；**不**声称移位是**自同构** ✗（**只**落**自同态** ✓）；
**不**声称 `ZMod p`-作用已落 ✗；**不**声称 `IsGaloisWithGroup` 任何一款 ✗。 -/

section ArtinSchreierCarrier290

/-- **AS 载体** ✓（源 `R{y^p − y − a}` ✓）：`R[y]/(y^p − y − a)` ✓。 -/
abbrev asCarrier (R : Type*) [CommRing R] (p : ℕ) (a : R) : Type _ :=
  AdjoinRoot ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a)

/-- **代入恒等式** ✓：`X ↦ X + C k` 把 `X^p − X − C a` 送到**自身加常数 `k^p − k`** ✓。 -/
theorem as_subst {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (a k : R) :
    Polynomial.aeval ((Polynomial.X : Polynomial R) + Polynomial.C k)
        ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a)
      = ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a)
        + Polynomial.C (k ^ p - k) := by
  let _inst : CharP (Polynomial R) p :=
    charP_of_injective_algebraMap Polynomial.C_injective p
  have h1 : ((Polynomial.X : Polynomial R) + Polynomial.C k) ^ p
      = (Polynomial.X : Polynomial R) ^ p + Polynomial.C (k ^ p) := by
    rw [add_pow_char, Polynomial.C_pow]
  rw [map_sub, map_sub, map_pow, Polynomial.aeval_X, h1, Polynomial.aeval_C]
  rw [show Polynomial.C (k ^ p - k) = Polynomial.C (k ^ p) - Polynomial.C k by rw [map_sub]]
  rw [show algebraMap R (Polynomial R) a = Polynomial.C a from rfl]
  ring

/-- **移位降入载体** ✓：`k^p = k` 时，代入后的多项式落在 `(X^p − X − C a)` 中 ✓
—— 即载体上 **`y ↦ y + k` 保持 AS 关系** ✓。 -/
theorem as_shift_mk {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) :
    AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a)
      (Polynomial.aeval ((Polynomial.X : Polynomial R) + Polynomial.C k)
        ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a)) = 0 := by
  rw [as_subst (p := p) a k]
  rw [map_add, AdjoinRoot.mk_self, zero_add]
  rw [show k ^ p - k = 0 by rw [hk, sub_self]]
  simp

/-- **移位自同态** ✓✅：**载体上 `y ↦ y + k`**（`k^p = k` ✓）—— 源 `C_p`-作用的**生成端** ✓
（**只**落自同态 ✓；**自同构**（双射）未落 ✗）。 -/
noncomputable def asShiftHom {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) : asCarrier R p a →+* asCarrier R p a :=
  AdjoinRoot.lift (AdjoinRoot.of _) (AdjoinRoot.root _ + AdjoinRoot.of _ k) (by
    have hgoal : Polynomial.eval₂
        ((AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a)).comp
          (Polynomial.C : R →+* Polynomial R))
        ((AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a))
          ((Polynomial.X : Polynomial R) + Polynomial.C k))
        ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a) = 0 := by
      rw [← Polynomial.hom_eval₂
        (p := ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a))
        (f := (Polynomial.C : R →+* Polynomial R))
        (g := AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a))
        (x := (Polynomial.X : Polynomial R) + Polynomial.C k)]
      exact as_shift_mk (p := p) a k hk
    simpa only [AdjoinRoot.of, AdjoinRoot.root, RingHom.comp_apply, map_add] using hgoal)

end ArtinSchreierCarrier290

#print axioms as_subst
#print axioms as_shift_mk
#print axioms asShiftHom


/-! ### 4.80 **AS 移位的逆元前提**（第 291 轮）
—— 素域元对取负封闭 ✓（**移位逆元 `asShiftHom a (-k)` 的存在性前提** ✓）

**用途** ✓：把 `asShiftHom a k hk` 变成**自同构**需要逆元 `asShiftHom a (-k) …` ✓，
而后者要求 `(-k)^p = -k` ✓ —— 本条即该前提 ✓（**素域元集对取负封闭** ✓）。

**证** ✓（两档，源出 `Nat.Prime.eq_two_or_odd'` ✓）：
**(i)** `p = 2` ✓：`(-k)^2 = (-1)^2 · k^2 = k` ✓ 而 `char 2` 给出 `-k = k` ✓（`CharTwo.neg_eq` ✓）；
**(ii)** `p` **奇** ✓：`(-k)^p = (-1)^p · k^p = (-1)·k = -k` ✓（`Odd.neg_one_pow` ✓）。
**⚠ 与 §4.78／§4.79 的关系** ✓：§4.78 落**位移核**（`as_shift` ✓）、§4.79 落**载体 ＋ 自同态**（`asShiftHom` ✓），
本条补**自同构**所需的逆元前提 ✓。

**🔴 不声称** ✗：**不**声称移位**已是自同构** ✗（**双射性未落** ✗ —— 其两条计算件
（`asShiftHom_of` ✓／`asShiftHom_root` ✓）与 `Algebra.adjoin_induction` 路线**本轮实测受阻** ✗，见 §253 ✓）；
**不**声称 `MulSemiringAction` 已落 ✗。 -/

section ArtinSchreierNegShift291

/-- **素域元对取负封闭** ✓：`k^p = k` ⟹ `(-k)^p = -k` ✓（移位逆元的存在性前提 ✓）。 -/
theorem neg_pow_eq_neg {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] {k : R}
    (hk : k ^ p = k) : (-k) ^ p = -k := by
  rcases (Fact.out : Nat.Prime p).eq_two_or_odd' with h2 | hodd
  · subst h2
    rw [neg_pow, hk, show (-1 : R) ^ 2 = 1 by norm_num, one_mul, CharTwo.neg_eq]
  · rw [neg_pow, hk, hodd.neg_one_pow]
    ring

end ArtinSchreierNegShift291

#print axioms neg_pow_eq_neg


/-! ### 4.81 **AS 载体移位的「具名义务」重述 ＋ 两条计算件**（第 292 轮）
—— 解 §253.3 的受阻：展开 `asShiftHom` 时隐式类型卡住 ✓

**问题** ✗（第 291 轮实测 ✓）：§4.79 的 `asShiftHom` 把 `eval₂` 义务写成**匿名 `by` 块** ✓
⟹ 其两条计算件无法**句法匹配** `AdjoinRoot.lift_of`／`lift_root` ✗（`show` 展开时 `CommRing ?m` 卡住 ✗）。

**解法** ✓✅（**本轮** ✓）：把义务**提为具名定理** `asShift_eval` ✓，并以它**重述**移位为 `asShiftH` ✓
⟹ 两条计算件**各成一行** ✓（`AdjoinRoot.lift_of` ✓／`AdjoinRoot.lift_root` ✓ **直接命中** ✓）。

**落成四件** ✓✅：**(i)** **`ASpoly`** ✓（载体多项式的具名形 ✓）；
**(ii)** **`asShift_eval`** ✓（`eval₂` 义务具名 ✓ —— 内核与 §4.79 同 ✓：`Polynomial.hom_eval₂` ✓ ＋ `as_shift_mk` ✓）；
**(iii)** **`asShiftH`** ✓（**具名义务版移位自同态** ✓，与 §4.79 的 `asShiftHom` **同值** ✓）；
**(iv)** **`asShiftH_of`** ✓／**`asShiftH_root`** ✓（**两条计算件** ✓：固定系数 ✓／根 ↦ `root + k` ✓）。

**⚠ 用途** ✓：**(iv)** 正是**双射性**（`Algebra.adjoin_induction` ✓ 或商环＋多项式外延 ✓）所需的**全部计算** ✓ ——
**下一手**即由 (iv) 收口自同构 ✓（第 291 轮的受阻点**已拆除** ✓）。

**🔴 不声称** ✗：**不**声称移位**已是自同构** ✗（**双射性仍未落** ✗ —— 现仅余**外延引理接线** ✓，
计算件已备 ✓）；**不**声称 §4.79 的 `asShiftHom` 已删 ✗（**保留在册** ✓，与 `asShiftH` **同值** ✓）；
**不**声称 `MulSemiringAction` 已落 ✗。 -/

section ArtinSchreierShiftAPI292

/-- AS 载体的定义多项式（具名）✓：`X^p − X − C a` ✓。 -/
abbrev ASpoly (R : Type*) [CommRing R] (p : ℕ) (a : R) : Polynomial R :=
  (Polynomial.X : Polynomial R) ^ p - Polynomial.X - Polynomial.C a

/-- **`eval₂` 义务（具名）** ✓：`root + k` 满足载体的定义关系 ✓ —— 使 `lift_of`／`lift_root` **句法可匹配** ✓。 -/
theorem asShift_eval {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) :
    Polynomial.eval₂ (AdjoinRoot.of (ASpoly R p a))
      (AdjoinRoot.root (ASpoly R p a) + AdjoinRoot.of (ASpoly R p a) k) (ASpoly R p a) = 0 := by
  have hgoal : Polynomial.eval₂
      ((AdjoinRoot.mk (ASpoly R p a)).comp (Polynomial.C : R →+* Polynomial R))
      ((AdjoinRoot.mk (ASpoly R p a)) ((Polynomial.X : Polynomial R) + Polynomial.C k))
      (ASpoly R p a) = 0 := by
    rw [← Polynomial.hom_eval₂ (p := ASpoly R p a) (f := (Polynomial.C : R →+* Polynomial R))
      (g := AdjoinRoot.mk (ASpoly R p a)) (x := (Polynomial.X : Polynomial R) + Polynomial.C k)]
    exact as_shift_mk (p := p) a k hk
  simpa only [AdjoinRoot.of, AdjoinRoot.root, RingHom.comp_apply, map_add] using hgoal

/-- **具名义务版移位自同态** ✓（与 §4.79 的 `asShiftHom` **同值** ✓，但**义务具名** ⟹ 计算件可一行 ✓）。 -/
noncomputable def asShiftH {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) : asCarrier R p a →+* asCarrier R p a :=
  AdjoinRoot.lift (AdjoinRoot.of (ASpoly R p a))
    (AdjoinRoot.root (ASpoly R p a) + AdjoinRoot.of (ASpoly R p a) k) (asShift_eval a k hk)

/-- **计算件 ①** ✓：移位**固定系数** ✓。 -/
theorem asShiftH_of {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) (r : R) :
    asShiftH a k hk (AdjoinRoot.of (ASpoly R p a) r) = AdjoinRoot.of (ASpoly R p a) r :=
  AdjoinRoot.lift_of (asShift_eval a k hk)

/-- **计算件 ②** ✓：移位把根送到 `root + k` ✓。 -/
theorem asShiftH_root {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) :
    asShiftH a k hk (AdjoinRoot.root (ASpoly R p a))
      = AdjoinRoot.root (ASpoly R p a) + AdjoinRoot.of (ASpoly R p a) k :=
  AdjoinRoot.lift_root (asShift_eval a k hk)

end ArtinSchreierShiftAPI292

#print axioms asShift_eval
#print axioms asShiftH
#print axioms asShiftH_of
#print axioms asShiftH_root


/-! ### 4.82 **AS 移位是自同构**（第 293 轮）—— 双射性收口 ✓（§253.3／§254.6 的下一手 ✓）

**落成** ✓✅：**`asShiftH_comp_neg`** ✓（`φ_{-k} ∘ φ_k = id` ✓）＋ **`asShiftH_comp_pos`** ✓（`φ_k ∘ φ_{-k} = id` ✓）
⟹ **`asShiftH_bijective`** ✓✅：**`Function.Bijective (asShiftH a k hk)`** ✓ —— 即源 `C_p`-作用的生成端
**是环自同构** ✓（`asShiftH a k hk : asCarrier ≃+* asCarrier` 的双射半 ✓）。

**机制** ✓（**外延二步** ✓，避开隐式类型陷阱 ✓）：
**(i)** **商环外延** ✓ `Ideal.Quotient.ringHom_ext` ✓（`AdjoinRoot f ＝ R[X] ⧸ (f)` ✓）；
**(ii)** **多项式外延** ✓ `Polynomial.ringHom_ext` ✓（`C`-支 ＝ **固定系数** ✓ `asShiftH_of` ✓；`X`-支 ＝ **根 ↦ `root + k`** ✓
`asShiftH_root` ✓ ＋ `of (-k) + of k = 0` ✓）。
**⚠ 工艺** ✓（**入 §5.1** ✓）：两条复合**各写一遍** ✓（**不**用 `comp_neg` 在 `-k` 处实例化 ✗ ——
那会引入 `-(-k)` 并把证明项搬进依赖位置 ⟹ `rw [neg_neg]` 报 **motive is not type correct** ✗，实测 ✓）；
结构性步骤用 `add_assoc` 先把 `(root + of (-k)) + of k` 归一 ✓（否则 `show` 形**句法不匹配** ✗）。

**🔴 不声称** ✗：**不**声称 `MulSemiringAction (ZMod p)` 已落 ✗（**下一手** ✓）；
**不**声称 `IsGaloisWithGroup` 任何一款 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section ArtinSchreierAutomorphism293

/-- **复合 ①** ✓：**`φ_{-k} ∘ φ_k = id`** ✓（`hneg : (-k)^p = -k` ✓ 由 §4.80 ✓ 供给）。 -/
theorem asShiftH_comp_neg {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) (hneg : (-k) ^ p = -k) :
    (asShiftH a (-k) hneg).comp (asShiftH a k hk)
      = RingHom.id (asCarrier R p a) := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span {ASpoly R p a}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (asShiftH a (-k) hneg) ((asShiftH a k hk)
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)))
      = (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
        = AdjoinRoot.of (ASpoly R p a) r from rfl]
    rw [asShiftH_of, asShiftH_of]
  · show (asShiftH a (-k) hneg) ((asShiftH a k hk)
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)))
      = (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
        = AdjoinRoot.root (ASpoly R p a) from rfl]
    rw [asShiftH_root, map_add, asShiftH_root, asShiftH_of]
    rw [add_assoc, show AdjoinRoot.of (ASpoly R p a) (-k) + AdjoinRoot.of (ASpoly R p a) k = 0 from by
      rw [← map_add, neg_add_cancel, map_zero], add_zero]

/-- **复合 ②** ✓：**`φ_k ∘ φ_{-k} = id`** ✓（与 ① **各写一遍** ✓ —— 避开 `-(-k)` 依赖位陷阱 ✗）。 -/
theorem asShiftH_comp_pos {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) (hneg : (-k) ^ p = -k) :
    (asShiftH a k hk).comp (asShiftH a (-k) hneg)
      = RingHom.id (asCarrier R p a) := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span {ASpoly R p a}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (asShiftH a k hk) ((asShiftH a (-k) hneg)
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)))
      = (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
        = AdjoinRoot.of (ASpoly R p a) r from rfl]
    rw [asShiftH_of, asShiftH_of]
  · show (asShiftH a k hk) ((asShiftH a (-k) hneg)
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)))
      = (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
        = AdjoinRoot.root (ASpoly R p a) from rfl]
    rw [asShiftH_root, map_add, asShiftH_root, asShiftH_of]
    rw [add_assoc, show AdjoinRoot.of (ASpoly R p a) k + AdjoinRoot.of (ASpoly R p a) (-k) = 0 from by
      rw [← map_add, add_neg_cancel, map_zero], add_zero]

/-- **🔴 主结果** ✓✅：**AS 移位是双射** ✓（**故为环自同构** ✓）。 -/
theorem asShiftH_bijective {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) : Function.Bijective (asShiftH a k hk) := by
  have hkneg := neg_pow_eq_neg hk
  have h1 := asShiftH_comp_neg a k hk hkneg
  have h2 := asShiftH_comp_pos a k hk hkneg
  have hleft : Function.LeftInverse (asShiftH a (-k) hkneg) (asShiftH a k hk) :=
    fun x => by
      have := congrArg (fun f => f x) h1
      simpa only [RingHom.comp_apply, RingHom.id_apply] using this
  have hright : Function.RightInverse (asShiftH a (-k) hkneg) (asShiftH a k hk) :=
    fun x => by
      have := congrArg (fun f => f x) h2
      simpa only [RingHom.comp_apply, RingHom.id_apply] using this
  exact ⟨hleft.injective, hright.surjective⟩

end ArtinSchreierAutomorphism293

#print axioms asShiftH_comp_neg
#print axioms asShiftH_comp_pos
#print axioms asShiftH_bijective


/-! ### 4.83 **AS 移位的复合律 ＋ `RingEquiv` 形**（第 294 轮）—— `MulSemiringAction` 的全部前置 ✓

**落成四件** ✓✅：**(i)** **`fermat_add`** ✓（素域元对加法封闭 ✓：`add_pow_char` ✓）；
**(ii)** **`castHom_pow`** ✓（**`ZMod p` 的像元满足 Fermat 性** ✓：`ZMod.castHom` ✓ ＋ `ZMod.pow_card` ✓
—— **素域元供体** ✓，**无需 `Algebra (ZMod p) R` 实例** ✓）；**(iii)** **`asShiftH_comp_add`** ✓✅
（**复合律** `φ_k ∘ φ_l = φ_{k+l}` ✓，**同一外延二步** ✓）；**(iv)** **`asShiftEquiv`** ✓✅
（**移位自同构的 `RingEquiv` 形** ✓：`RingEquiv.ofBijective` ✓ ＋ §4.82 的 `asShiftH_bijective` ✓）。

**⚠ 机制** ✓：**(iii)** 的 `C`-支 ＝ 两边**都固定系数** ✓（`asShiftH_of` ✓ 各一次 ✓）；`X`-支 ＝
`(root + of k) + of l` 与 `root + (of k + of l)` 的**结合律归一** ✓（`asShiftH_root` ✓／`map_add` ✓／`add_assoc` ✓）。

**⚠ 意义** ✓：**`MulSemiringAction (Multiplicative (ZMod p)) asCarrier`** 的**全部前置已备** ✓ ——
**(ii)** 供作用元 ✓、**(iii)** 供 `mul_smul` ✓、**(iv)** 供自同构载体 ✓ ⟹ **下一手只余组装** ✓。

**🔴 不声称** ✗：**不**声称 `MulSemiringAction` 已落 ✗（**下一手** ✓）；
**不**声称 `IsGaloisWithGroup` 任何一款 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section ArtinSchreierCompLaw294

/-- **素域元对加法封闭** ✓：`k^p = k`、`l^p = l` ⟹ `(k+l)^p = k+l` ✓。 -/
theorem fermat_add {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] {k l : R}
    (hk : k ^ p = k) (hl : l ^ p = l) : (k + l) ^ p = k + l := by
  rw [add_pow_char, hk, hl]

/-- **素域元供体** ✓：`ZMod p` 的像元满足 Fermat 性 ✓（**无需 `Algebra (ZMod p) R`** ✓）。 -/
theorem castHom_pow {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (k : ZMod p) :
    (ZMod.castHom (dvd_refl p) R k) ^ p = ZMod.castHom (dvd_refl p) R k := by
  rw [← map_pow, ZMod.pow_card]

/-- **复合律** ✓：`φ_k ∘ φ_l = φ_{k+l}` ✓（**同一外延二步** ✓）。 -/
theorem asShiftH_comp_add {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k l : R) (hk : k ^ p = k) (hl : l ^ p = l) :
    (asShiftH a k hk).comp (asShiftH a l hl) = asShiftH a (k + l) (fermat_add hk hl) := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span {ASpoly R p a}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (asShiftH a k hk) ((asShiftH a l hl)
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)))
      = (asShiftH a (k + l) (fermat_add hk hl))
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r))
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
        = AdjoinRoot.of (ASpoly R p a) r from rfl]
    rw [asShiftH_of, asShiftH_of, asShiftH_of]
  · show (asShiftH a k hk) ((asShiftH a l hl)
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)))
      = (asShiftH a (k + l) (fermat_add hk hl))
        ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X))
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
        = AdjoinRoot.root (ASpoly R p a) from rfl]
    rw [asShiftH_root, map_add, asShiftH_root, asShiftH_of, asShiftH_root, map_add, add_assoc]

/-- **移位自同构（`RingEquiv` 形）** ✓✅。 -/
noncomputable def asShiftEquiv {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) : asCarrier R p a ≃+* asCarrier R p a :=
  RingEquiv.ofBijective (asShiftH a k hk) (asShiftH_bijective a k hk)

end ArtinSchreierCompLaw294

#print axioms fermat_add
#print axioms castHom_pow
#print axioms asShiftH_comp_add
#print axioms asShiftEquiv


/-! ### 4.84 **AS 载体上的 `C_p`-作用（`MulSemiringAction`）**（第 295 轮）
—— 源 `theorem-1-2(a)` 的**群作用** ✓（第 294 轮前置全部消费 ✓）

**落成三件** ✓✅：**(i)** **`asShiftH_zero`** ✓（`φ_0 = id` ✓，同一外延二步 ✓）；
**(ii)** **`asShiftHMSA_comp`** ✓✅（**群作用档复合律** ✓：参数取 `ZMod p` 的像 ✓ ⟹
**参数换算落在非依赖位** ✓，绕开 `asShiftH a · (proof)` 的**依赖位重写** ✗）；
**(iii)** **`asCarrierMSA`** ✓✅：**`MulSemiringAction (Multiplicative (ZMod p)) (asCarrier R p a)`** ✓
—— **源 `C_p`-作用落库** ✓（`smul k x := φ_{c k} x` ✓；公理逐条 ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(甲)** **依赖位重写** ✗ —— `asShiftH a t ht` 的证明项类型依赖 `t` ✓
⟹ `rw` 报 **motive is not type correct** ✗（实测三处 ✓）；**解** ✓：**(甲1)** 把参数换算搬到**非依赖位** ✓
（如 `of (·)` 内 ✓，见 (ii) 的 `X`-支 ✓）；**(甲2)** 用 **`simp only`** ✓（simp 对依赖位有专门策略 ✓，
实测 `one_smul` 的 `c 0 = 0` 归一 ✓）；**(甲3)** `congrArg (fun f => f x)` ✓ 在**函数层**搬运 ✓。
**(乙)** 复合律方向 ✗：`(φ_k.comp φ_l) x = φ_k (φ_l x)` ✓ 而 `mul_smul` 要 **`φ_{k*l} x = φ_k (φ_l x)`** ✓
⟹ 须取 **`.symm`** ✓（实测 ✓）。**(丙)** 类实例须 **`@[instance_reducible]`** ✓（否则 `warn.classDefReducibility` ✗）。

**🔴 不声称** ✗：**不**声称 `IsGaloisWithGroup` 任何一款 ✗（**下一手** ✓：忠实 ✓／不动环 ✓／`δ` 双射 ✓）；
**不**声称源 `theorem-1-2` 已证 ✗；**不**声称残余 ①／③ 已证 ✗。 -/

section ArtinSchreierAction295

/-- **`φ_0 = id`** ✓（同一外延二步 ✓）。 -/
theorem asShiftH_zero {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (a : R)
    (h0 : (0 : R) ^ p = 0) : asShiftH a 0 h0 = RingHom.id (asCarrier R p a) := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span {ASpoly R p a}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (asShiftH a 0 h0) ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r))
      = (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
        = AdjoinRoot.of (ASpoly R p a) r from rfl]
    rw [asShiftH_of]
  · show (asShiftH a 0 h0) ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X))
      = (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
        = AdjoinRoot.root (ASpoly R p a) from rfl]
    rw [asShiftH_root, map_zero, add_zero]

/-- **群作用档复合律** ✓：参数取 `ZMod p` 的像 ⟹ 参数换算落在**非依赖位** ✓。 -/
theorem asShiftHMSA_comp {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) (k l : Multiplicative (ZMod p)) :
    (asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
        (castHom_pow (p := p) (Multiplicative.toAdd k))).comp
      (asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd l))
        (castHom_pow (p := p) (Multiplicative.toAdd l)))
      = asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd (k * l)))
          (castHom_pow (p := p) (Multiplicative.toAdd (k * l))) := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span {ASpoly R p a}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (asShiftH a _ (castHom_pow (p := p) (Multiplicative.toAdd k)))
        ((asShiftH a _ (castHom_pow (p := p) (Multiplicative.toAdd l)))
          ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)))
      = (asShiftH a _ (castHom_pow (p := p) (Multiplicative.toAdd (k * l))))
          ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r))
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.C r)
        = AdjoinRoot.of (ASpoly R p a) r from rfl]
    rw [asShiftH_of, asShiftH_of, asShiftH_of]
  · show (asShiftH a _ (castHom_pow (p := p) (Multiplicative.toAdd k)))
        ((asShiftH a _ (castHom_pow (p := p) (Multiplicative.toAdd l)))
          ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)))
      = (asShiftH a _ (castHom_pow (p := p) (Multiplicative.toAdd (k * l))))
          ((Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X))
    rw [show (Ideal.Quotient.mk (Ideal.span {ASpoly R p a})) (Polynomial.X)
        = AdjoinRoot.root (ASpoly R p a) from rfl]
    rw [asShiftH_root, map_add, asShiftH_root, asShiftH_of, asShiftH_root]
    rw [add_assoc]
    congr 1
    rw [show ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd (k * l))
        = ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k)
          + ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd l) from by
      rw [show Multiplicative.toAdd (k * l)
          = Multiplicative.toAdd k + Multiplicative.toAdd l from rfl, map_add]]
    rw [map_add]

/-- **🔴 主结果** ✓✅：**AS 载体上的 `C_p`-作用** ✓（源 `theorem-1-2(a)` ✓）。 -/
@[instance_reducible] noncomputable def asCarrierMSA {R : Type*} [CommRing R] {p : ℕ}
    [Fact p.Prime] [CharP R p] (a : R) :
    MulSemiringAction (Multiplicative (ZMod p)) (asCarrier R p a) where
  smul k x := asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
    (castHom_pow (p := p) (Multiplicative.toAdd k)) x
  one_smul x := by
    show asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd 1))
      (castHom_pow (p := p) (Multiplicative.toAdd 1)) x = x
    simp only [show Multiplicative.toAdd (1 : Multiplicative (ZMod p)) = 0 from rfl, map_zero]
    exact congrArg (fun f => f x) (asShiftH_zero a _)
  mul_smul k l x := by
    show asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd (k * l)))
        (castHom_pow (p := p) (Multiplicative.toAdd (k * l))) x
      = asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
          (castHom_pow (p := p) (Multiplicative.toAdd k))
          (asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd l))
            (castHom_pow (p := p) (Multiplicative.toAdd l)) x)
    exact (congrArg (fun f => f x) (asShiftHMSA_comp a k l)).symm
  smul_zero k := map_zero _
  smul_add k x y := map_add _ x y
  smul_mul k x y := map_mul _ x y
  smul_one k := map_one _

end ArtinSchreierAction295

#print axioms asShiftH_zero
#print axioms asShiftHMSA_comp
#print axioms asCarrierMSA


/-! ### 4.85 **AS 载体 `IsGaloisWithGroup` 的两款**（第 296 轮）
—— 款② **无条件落库** ✓、款① **归约形落库** ✓（源 §0 判据 ✓）

**落成两件** ✓✅：**(i)** **`asCarrier_smul_algebraMap`** ✓✅（**款②：不动基** ✓ —— `k • algebraMap r = algebraMap r` ✓，
一行由 `asShiftH_of` ✓）；**(ii)** **`asCarrierMSA_faithful_of_injective`** ✓✅（**款①：忠实性归约** ✓ ——
`of` 单射 ✓ ＋ 素域像单射 ✓ ⟹ `FaithfulSMul (Multiplicative (ZMod p)) (asCarrier R p a)` ✓）。

**机制** ✓（**(ii)** ✓）：**在根上取值** ✓ —— `k • root = root + of (c k)` ✓（`asShiftH_root` ✓）⟹
`of (c k) = 0` ✓（`congrArg (· - root)` ＋ `simpa` ✓）⟹ `c k = 0` ✓（`of` 单射 ✓）⟹ `k = 0` ✓（`ZMod.castHom` 单射 ✓）⟹ `k = 1` ✓。

**⚠ 两条注入性前提的可得性（下一手）** ✓：**(甲)** `AdjoinRoot.of` 单射 ✓ —— 由
`AdjoinRoot.of.injective_of_degree_ne_zero` ✓（须 `[IsDomain R]` ✓ ＋ `(ASpoly R p a).degree ≠ 0` ✓，
后者由 `p ≥ 2` ＋ 首项系数 1 ✓）；**(乙)** `ZMod.castHom (dvd_refl p) R` 单射 ✓ —— 由 `CharP R p` ✓
（ℤ 的核 ＝ `pℤ` ✓）⟹ **款① 可去条件化** ✓（**下一手** ✓）。

**🔴 不声称** ✗：**不**声称款①的**无条件形**已证 ✗（**只**落**归约形** ✓，两条注入性前提**未在本件证明** ✗）；
**不**声称款③（`δ` 双射）已证 ✗（**最难，下一手** ✓）；**不**声称 `IsGaloisWithGroup` 整体 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section ArtinSchreierGaloisClauses296

attribute [local instance] asCarrierMSA

/-- **款②（不动基）** ✓✅：`k • algebraMap r = algebraMap r` ✓。 -/
theorem asCarrier_smul_algebraMap {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) (k : Multiplicative (ZMod p)) (r : R) :
    k • (algebraMap R (asCarrier R p a) r) = algebraMap R (asCarrier R p a) r := by
  show asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
    (castHom_pow (p := p) (Multiplicative.toAdd k)) (algebraMap R (asCarrier R p a) r)
    = algebraMap R (asCarrier R p a) r
  rw [show algebraMap R (asCarrier R p a) r = AdjoinRoot.of (ASpoly R p a) r from rfl]
  rw [asShiftH_of]

/-- **款①（忠实性）归约形** ✓✅：`of` 单射 ＋ 素域像单射 ⟹ `FaithfulSMul` ✓（**在根上取值** ✓）。 -/
theorem asCarrierMSA_faithful_of_injective {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R)
    (hinf : Function.Injective (AdjoinRoot.of (ASpoly R p a)))
    (hc : Function.Injective (ZMod.castHom (dvd_refl p) R)) :
    FaithfulSMul (Multiplicative (ZMod p)) (asCarrier R p a) := by
  rw [faithfulSMul_iff]
  intro k hk
  have hroot : asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      (castHom_pow (p := p) (Multiplicative.toAdd k)) (AdjoinRoot.root (ASpoly R p a))
      = AdjoinRoot.root (ASpoly R p a) := hk _
  rw [asShiftH_root] at hroot
  have hof : AdjoinRoot.of (ASpoly R p a)
      (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k)) = 0 := by
    have := congrArg (fun t => t - AdjoinRoot.root (ASpoly R p a)) hroot
    simpa using this
  have hzero : ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k) = 0 :=
    hinf (by rw [hof, map_zero])
  have h1 : Multiplicative.toAdd k = 0 := hc (by rw [hzero, map_zero])
  have h2 : Multiplicative.toAdd (1 : Multiplicative (ZMod p)) = 0 := rfl
  exact Multiplicative.toAdd.injective (by rw [h1, h2])

end ArtinSchreierGaloisClauses296

#print axioms asCarrier_smul_algebraMap
#print axioms asCarrierMSA_faithful_of_injective


/-! ### 4.86 **款① 去条件化（第一步：素域像单射）**（第 298 轮）
—— §258.2(乙) 落库 ✓：款① 的两条前提**去掉一条** ✓

**落成两件** ✓✅：**(i)** **`zmod_castHom_injective`** ✓✅（**素域像单射** ✓：
`Function.Injective (ZMod.castHom (dvd_refl p) R)` ✓ —— 由 `CharP R p` ＋ `p` 素 ✓）；
**(ii)** **`asCarrierMSA_faithful_of_ofInjective`** ✓✅（**款① 单前提形** ✓：只需 `of` 单射 ✓，
素域像单射已由 (i) 供给 ✓）。

**机制** ✓（(i) ✓）：**`ZMod p` 是域** ✓ ⟹ 任意 `ZMod p →+* R`（`R` **非平凡** ✓）**单射** ✓（`RingHom.injective` ✓）；
**`R` 非平凡** ✓ 由 `CharP R p` ＋ `p` 素 ✓ —— 取 `n = 1` ✓，用
**`CharP.cast_eq_zero_iff R p 1 : (1:R) = 0 ↔ p ∣ 1`** ✓ ＋ **`Nat.Prime.not_dvd_one`** ✓。

**⚠ 工艺（一条，入 §5.1）** ✓：**"零环中 `(n:R) = 0` 对一切 `n` 成立"** ✓ ⟹ **不得**用"`(p:R) = 0` 与 `p ≠ 0` 矛盾"证非平凡 ✗
（第 297 轮探针的**首版错误** ✓，实测 ✓）；**正解** ＝ 取 `n = 1` ✓（`p ∣ 1` 与 `p` 素矛盾 ✓）。

**🔴 不声称** ✗：**不**声称款①的**无条件形**已证 ✗（**尚余 `of` 单射** ✓ 一条前提 —— **下一手** ✓：
`AdjoinRoot.of.injective_of_degree_ne_zero` ✓ ＋ `degree ≠ 0` ✓）；**不**声称款③（`δ` 双射）已证 ✗；
**不**声称 `IsGaloisWithGroup` 整体 ✗。 -/

section ArtinSchreierFaithful298

attribute [local instance] asCarrierMSA

/-- **素域像单射** ✓：`ZMod p →+* R` 单射（`CharP R p`、`p` 素、`R` 非平凡 ✓）。 -/
theorem zmod_castHom_injective {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] :
    Function.Injective (ZMod.castHom (dvd_refl p) R) := by
  let _inst : Nontrivial R := by
    rw [← not_subsingleton_iff_nontrivial]
    intro h
    have h1 : (1 : R) = 0 := Subsingleton.elim 1 0
    exact (Fact.out : Nat.Prime p).not_dvd_one
      ((CharP.cast_eq_zero_iff R p 1).mp (by simpa using h1))
  exact (ZMod.castHom (dvd_refl p) R).injective

/-- **款①（忠实）单前提形** ✓✅：只需 `of` 单射 ✓（素域像单射由 `zmod_castHom_injective` ✓ 供给）。 -/
theorem asCarrierMSA_faithful_of_ofInjective {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) (hinf : Function.Injective (AdjoinRoot.of (ASpoly R p a))) :
    FaithfulSMul (Multiplicative (ZMod p)) (asCarrier R p a) :=
  asCarrierMSA_faithful_of_injective a hinf (zmod_castHom_injective (p := p) (R := R))

end ArtinSchreierFaithful298

#print axioms zmod_castHom_injective
#print axioms asCarrierMSA_faithful_of_ofInjective


/-! ### 4.87 **款①（忠实性）无条件形**（第 299 轮）
—— 源 §0 判据的**忠实性一款落在 AS 载体上** ✓（`[IsDomain R]` 下 ✓，即源的 `R = F[x]` ✓ 设定 ✓）

**落成三件** ✓✅：**(i)** **`aspoly_natDegree`** ✓（`(ASpoly R p a).natDegree = p` ✓，`p ≥ 2` ✓）；
**(ii)** **`aspoly_degree_ne_zero`** ✓（次数非零 ✓）；**(iii)** **`asCarrierMSA_faithful_of_isDomain`** ✓✅：
**`FaithfulSMul (Multiplicative (ZMod p)) (asCarrier R p a)`** ✓ —— **款① 无条件形** ✓（`[IsDomain R]` ✓）。

**机制** ✓：**(i)** 用**系数**（`coeff p = 1 ≠ 0` ✓，`le_natDegree_of_ne_zero` ✓）＋**次数上界**（`natDegree_sub_le` ✓／
`natDegree_add_le` ✓／`natDegree_X_pow` ✓／`natDegree_X_le` ✓／`natDegree_C` ✓）双向夹 ✓；
**(ii)** 由 (i) ✓（`degree_eq_natDegree` ✓ ＋ `≠ 0` ✓）；**(iii)** 由 §4.86 的**单前提形** ✓ ＋
`AdjoinRoot.of.injective_of_degree_ne_zero` ✓（**恰是 `[IsDomain R]` ＋ 次数非零** ✓）收口 ✓。

**⚠ 工艺（两条，入 §5.1）** ✓：**(甲)** 上界支的**第一项须 `rw [Polynomial.natDegree_X_pow]`** ✗（写成 `le_rfl` ✗ 会报
"expected `(X^p).natDegree ≤ p`" ✓）；**(乙)** `(↑p : WithBot ℕ) ≠ 0` 型目标 ✗ 用 **`exact_mod_cast`** ✓
（`omega`／`WithBot.coe_ne_zero` 皆实测不可 ✓）。

**🔴 不声称** ✗：**不**声称款③（`δ` 双射）已证 ✗（**最难，下一手** ✓）；**不**声称 `IsGaloisWithGroup` **整体**已证 ✗
（**三款中两款在册** ✓）；**不**声称源 `theorem-1-2` 已证 ✗；**不**声称残余 ①／③ 已证 ✗。 -/

section ArtinSchreierFaithfulUncond299

attribute [local instance] asCarrierMSA

/-- **AS 多项式的次数** ✓：`(X^p − X − C a).natDegree = p` ✓（`p ≥ 2`）。 -/
theorem aspoly_natDegree {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p) (a : R) :
    (ASpoly R p a).natDegree = p := by
  have hp0 : p ≠ 0 := by omega
  have hp1 : p ≠ 1 := by omega
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero ?_)
  · rw [ASpoly, sub_sub]
    refine le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le ?_ (le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)))
    · rw [Polynomial.natDegree_X_pow]
    · exact le_trans Polynomial.natDegree_X_le (by omega)
    · rw [Polynomial.natDegree_C]; omega
  · rw [ASpoly, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_X_pow_self,
      Polynomial.coeff_X_of_ne_one hp1, Polynomial.coeff_C_of_ne_zero hp0]
    norm_num

/-- **AS 多项式的次数非零** ✓。 -/
theorem aspoly_degree_ne_zero {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p)
    (a : R) : (ASpoly R p a).degree ≠ 0 := by
  have hne : ASpoly R p a ≠ 0 := by
    intro h
    have := aspoly_natDegree (R := R) hp a
    rw [h, Polynomial.natDegree_zero] at this
    omega
  rw [Polynomial.degree_eq_natDegree hne, aspoly_natDegree (R := R) hp a]
  exact_mod_cast (show p ≠ 0 by omega)

/-- **🔴 款①（忠实性）无条件形** ✓✅：`[IsDomain R]` 下 AS 载体的 `C_p`-作用忠实 ✓。 -/
theorem asCarrierMSA_faithful_of_isDomain {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    [Fact p.Prime] [CharP R p] (a : R) :
    FaithfulSMul (Multiplicative (ZMod p)) (asCarrier R p a) :=
  asCarrierMSA_faithful_of_ofInjective a
    (AdjoinRoot.of.injective_of_degree_ne_zero
      (aspoly_degree_ne_zero (R := R) (Fact.out : Nat.Prime p).two_le a))

end ArtinSchreierFaithfulUncond299

#print axioms aspoly_natDegree
#print axioms aspoly_degree_ne_zero
#print axioms asCarrierMSA_faithful_of_isDomain


/-! ### 4.88 **根的共轭两两不同（款③ 的单射半）**（第 300 轮）
—— `k ↦ φ_k(root)` **单射** ✓ ⟹ **`p` 个两两不同的共轭** ✓（正规基候选 `{φ_k root}` ✓ 的**独立性前提** ✓）

**落成** ✓✅：**`asShiftH_root_injective`** ✓：
`Function.Injective (fun k : Multiplicative (ZMod p) => φ_{c k} (root))` ✓（`[IsDomain R]` ✓）。

**机制（三步，全部消费已落件 ✓）** ✓：**(i)** `φ_k root = root + of (c k)` ✓（**§4.81 的 `asShiftH_root`** ✓）⟹
相等给 `of (c k) = of (c l)` ✓（`congrArg (· − root)` ＋ `simpa` ✓）；**(ii)** `of` **单射** ✓
（**§4.87 的 `aspoly_degree_ne_zero`** ✓ ＋ `of.injective_of_degree_ne_zero` ✓）⟹ `c k = c l` ✓；
**(iii)** `c = ZMod.castHom (dvd_refl p) R` **单射** ✓（**§4.86 的 `zmod_castHom_injective`** ✓）⟹ `k = l` ✓。

**⚠ 工艺（一条，入 §5.1）** ✓：函数式的**应用在假设里是未 β-归约形** ✗ ⟹ `rw … at h` **不命中** ✗
（实测 "Did not find an occurrence of the pattern" ✓）；**解** ✓：先 `have h' : <显式两应用相等> := h` ✓（defeq 即 β-归约 ✓）再 `rw … at h'` ✓。

**⚠ 意义** ✓：这是 **款③（`δ` 双射）** 的**单射半** ✓ —— 共轭集合 `{φ_k root}` 有 **`p` 个互异元** ✓，
正是**正规基**（源 `proposition-0-5(c)` ✓）的候选 ✓；**余**：把 `{φ_k root}` 的**独立性/生成性**接上 `δ` ✓。

**🔴 不声称** ✗：**不**声称 `{φ_k root}` 是**正规基** ✗（**线性无关未证** ✗）；**不**声称款③ 已证 ✗；
**不**声称 `IsGaloisWithGroup` 整体 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section ArtinSchreierConjugates300

attribute [local instance] asCarrierMSA

/-- **根的共轭两两不同** ✓：`k ↦ φ_k(root)` 单射 ✓（**款③ 的单射半** ✓）。 -/
theorem asShiftH_root_injective {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    Function.Injective (fun k : Multiplicative (ZMod p) =>
      asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
        (castHom_pow (p := p) (Multiplicative.toAdd k))
        (AdjoinRoot.root (ASpoly R p a))) := by
  have hof : Function.Injective (AdjoinRoot.of (ASpoly R p a)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero
      (aspoly_degree_ne_zero (R := R) (Fact.out : Nat.Prime p).two_le a)
  intro k l hkl
  have hkl' : asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      (castHom_pow (p := p) (Multiplicative.toAdd k)) (AdjoinRoot.root (ASpoly R p a))
      = asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd l))
        (castHom_pow (p := p) (Multiplicative.toAdd l))
        (AdjoinRoot.root (ASpoly R p a)) := hkl
  rw [asShiftH_root, asShiftH_root] at hkl'
  have h1 : AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      = AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd l)) := by
    have := congrArg (fun t => t - AdjoinRoot.root (ASpoly R p a)) hkl'
    simpa using this
  have h2 : ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k)
      = ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd l) := hof h1
  exact Multiplicative.toAdd.injective (zmod_castHom_injective (p := p) (R := R) h2)

end ArtinSchreierConjugates300

#print axioms asShiftH_root_injective


/-! ### 4.89 **`hRG` 兼容性 ＋ `IsGaloisWithGroup` 组装**（第 301 轮）
—— 款① ＋ 款② ＋ 兼容性 **组装为源判据** ✓（**只余款③** ✓）

**落成两件** ✓✅：**(i)** **`asCarrier_hRG`** ✓✅：`∀ g r t, g • (r • t) = r • (g • t)` ✓
（**源 `IsGaloisWithGroup` 的显式参数** ✓ —— AS 作用由 **`R`-代数自同构**给出 ✓，故与 `R`-纯量交换 ✓）；
**(ii)** **`asCarrier_isGaloisWithGroup_of_delta`** ✓✅：**款① ＋ 款② ＋ `hRG` ⟹ `IsGaloisWithGroup`** ✓
（**条件：款③** ✓ —— **源判据的组装已就位** ✓）。

**机制** ✓：**(i)** `R`-纯量即 `algebraMap` 乘法 ✓ ⟹ 由 **`map_mul`** ✓ ＋ **§4.81 的 `asShiftH_of`** ✓
（移位固定系数 ✓）收口 ✓；**(ii)** 直接填源判据的**三款** ✓（前两款 ＝ §4.87 ✓ ＋ §4.85 ✓）。

**⚠ 工艺（两条，入 §5.1）** ✓：**(甲)** `r • t` 的 `algebraMap` 展开**不是 defeq** ✗（`Algebra.smul_def` ✓ 是**定理** ✗）
⟹ 须先 **`rw [Algebra.smul_def, Algebra.smul_def]`** ✓ 再 `show` ✓（实测 `show` 直写报 "not definitionally equal" ✗）；
**(乙)** 源判据在 **`ABGV52.BTier`** 命名空间 ✓ ⟹ 引用须**限定**（`ABGV52.BTier.deltaToEndRingHom` ✓／
`ABGV52.BTier.IsGaloisWithGroup` ✓）—— 未限定会报 **unknown identifier** 并被 `autoImplicit` 误读为隐式变量 ✗。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗（**以假设形式入 (ii)** ✓ —— **这正是本轮的"余量"** ✓）；
**不**声称 `IsGaloisWithGroup` **无条件成立** ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section ArtinSchreierGaloisAssembly301

attribute [local instance] asCarrierMSA

/-- **`hRG` 兼容性** ✓：AS 作用与 `R`-纯量交换 ✓（作用由 `R`-代数自同构给出 ✓）。 -/
theorem asCarrier_hRG {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    ∀ (g : Multiplicative (ZMod p)) (r : R) (t : asCarrier R p a),
      g • (r • t) = r • (g • t) := by
  intro k r t
  rw [Algebra.smul_def, Algebra.smul_def]
  show asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      (castHom_pow (p := p) (Multiplicative.toAdd k))
      (algebraMap R (asCarrier R p a) r * t)
    = algebraMap R (asCarrier R p a) r
      * asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
        (castHom_pow (p := p) (Multiplicative.toAdd k)) t
  rw [map_mul]
  congr 1
  rw [show algebraMap R (asCarrier R p a) r = AdjoinRoot.of (ASpoly R p a) r from rfl]
  rw [asShiftH_of]

/-- **组装** ✓：款① ＋ 款② ＋ `hRG` ⟹ **`IsGaloisWithGroup`** ✓（**条件：款③** ✓）。 -/
theorem asCarrier_isGaloisWithGroup_of_delta {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    [Fact p.Prime] [CharP R p] (a : R)
    (hdelta : Function.Bijective (ABGV52.BTier.deltaToEndRingHom (asCarrier_hRG a))) :
    ABGV52.BTier.IsGaloisWithGroup R (asCarrier R p a) (Multiplicative (ZMod p))
      (asCarrier_hRG a) :=
  ⟨asCarrierMSA_faithful_of_isDomain a, asCarrier_smul_algebraMap a, hdelta⟩

end ArtinSchreierGaloisAssembly301

#print axioms asCarrier_hRG
#print axioms asCarrier_isGaloisWithGroup_of_delta


/-! ### 4.90 **`δ` 在两条生成族上的取值 ＋ AS 档落点**（第 302 轮）
—— 款③ 的**生成元计算** ✓：`δ` 由 `{single k 1}` 与 `{single 1 s}` 两族**钉住** ✓

**落成五件** ✓✅（四件**通用** ✓、一件 **AS 档** ✓）：
**(i)** **`coeffToEnd_one`** ✓（左乘 `1` ＝ 单位 ✓）；**(ii)** **`actEnd_one`** ✓（`1` 的作用端 ＝ 单位 ✓）；
**(iii)** **`deltaToEndRingHom_single_one`** ✓✅：**`δ (single g 1) = actEnd g`** ✓（**群部** ✓）；
**(iv)** **`deltaToEndRingHom_single_self`** ✓✅：**`δ (single 1 s) = coeffToEnd s`** ✓（**系数部** ✓）；
**(v)** **`delta_AS_single_one_apply`** ✓✅：**AS 档** ✓ —— `δ (single k 1)` 作用在 `x` 上 ＝ **AS 自同构 `φ_k`** 作用在 `x` 上 ✓
（**(iii)** ＋ `rfl` ✓）。

**⚠ 机制与工艺** ✓：**(iii)/(iv)** 由 **`deltaToEndAdd_single`** ✓（已落 ✓：`δ(single g s) = coeffToEnd s * actEnd g` ✓）
＋ `one_mul`／`mul_one` ✓ 收口 ✓；**(v)** 的 `rfl` 成功 ⟹ **AS 作用与 `actEnd` 定义上同一** ✓。
**工艺（两条）** ✓（入 §5.1 ✓）：**(甲)** `deltaToEndRingHom` **需要 `[Fintype G]`** ✓（而 `coeffToEnd`／`actEnd` **不需要** ✗）
—— 故前者用 `omit [Fintype G] in` ✓，后者保留 ✓（否则报 unused section variable ✗ 或 synthInstanceFailed ✗）；
**(乙)** 四件为**通用引理** ✓（与 `R`／`S`／`G` 无关 ✓），本件**置于 AS 档文件** ✓ 以守**单文件改动**纪律 ✓。

**⚠ 意义** ✓：**(iii)/(iv)** 给 `δ` 在 **`S`-部与 `G`-部**的显式像 ✓ ⟹ 款③ 的**显式逆**只需在
`{y^i · g}` 基上写出 ✓（**下一手** ✓）；**(v)** 把 AS 链的 `φ_k` **接进 `δ`** ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗（**只**落生成元取值 ✓）；**不**声称 `IsGaloisWithGroup` 无条件形 ✗；
**不**声称源 `theorem-1-2` 已证 ✗。 -/

section DeltaOnGenerators302

open ABGV52.BTier

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]

omit [Fintype G] in
/-- **左乘 `1` ＝ 单位** ✓。 -/
lemma coeffToEnd_one : (coeffToEnd (R := R) (1 : S) : Module.End R S) = 1 := by
  ext t; simp [coeffToEnd]

omit [Fintype G] in
/-- **`1` 的作用端 ＝ 单位** ✓。 -/
lemma actEnd_one (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    actEnd hRG (1 : G) = 1 := by
  ext t; simp [actEnd]

/-- **`δ` 在群部上的取值** ✓：`δ (single g 1) = actEnd g` ✓。 -/
lemma deltaToEndRingHom_single_one (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (g : G) :
    deltaToEndRingHom hRG (SkewMonoidAlgebra.single g (1 : S)) = actEnd hRG g := by
  show deltaToEndAdd hRG (SkewMonoidAlgebra.single g (1 : S)) = actEnd hRG g
  rw [deltaToEndAdd_single, coeffToEnd_one, one_mul]

/-- **`δ` 在系数部上的取值** ✓：`δ (single 1 s) = coeffToEnd s` ✓。 -/
lemma deltaToEndRingHom_single_self (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (s : S) :
    deltaToEndRingHom hRG (SkewMonoidAlgebra.single (1 : G) s) = coeffToEnd (R := R) s := by
  show deltaToEndAdd hRG (SkewMonoidAlgebra.single (1 : G) s) = coeffToEnd (R := R) s
  rw [deltaToEndAdd_single, actEnd_one, mul_one]

end DeltaOnGenerators302

section DeltaAS302

open ABGV52.BTier

attribute [local instance] asCarrierMSA

/-- **AS 档落点** ✓✅：`δ (single k 1)` 在 `x` 上的值 ＝ **AS 自同构 `φ_k`** 在 `x` 上的值 ✓。 -/
lemma delta_AS_single_one_apply {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) (k : Multiplicative (ZMod p)) (x : asCarrier R p a) :
    (deltaToEndRingHom (S := asCarrier R p a) (G := Multiplicative (ZMod p))
        (asCarrier_hRG a) (SkewMonoidAlgebra.single k (1 : asCarrier R p a))) x
      = asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
        (castHom_pow (p := p) (Multiplicative.toAdd k)) x := by
  rw [deltaToEndRingHom_single_one]
  rfl

end DeltaAS302

#print axioms coeffToEnd_one
#print axioms actEnd_one
#print axioms deltaToEndRingHom_single_one
#print axioms deltaToEndRingHom_single_self
#print axioms delta_AS_single_one_apply


/-! ### 4.91 **AS 载体的幂基与秩（`R`-自由、秩 `p`）**（第 303 轮）
—— 款③ 显式逆的**基** ✓ 与 (1b)/(2a)/(2b) **模块行**的 C_p 档输入 ✓

**落成三件** ✓✅：**(i)** **`aspoly_monic`** ✓（`ASpoly R p a` **首一** ✓，`p ≥ 2` ✓）；
**(ii)** **`asCarrierBasis`** ✓✅：**幂基 `{1, y, …, y^{p−1}}`** ✓（`Module.Basis (Fin p) R (asCarrier R p a)` ✓，
由 mathlib 的 `AdjoinRoot.powerBasisAux'` ✓ ＋ `finCongr` ✓ 重标号 ✓）；
**(iii)** **`asCarrier_finrank`** ✓✅：**`Module.finrank R (asCarrier R p a) = p`** ✓。

**⚠ 机制与工艺** ✓：**(i)** 由 **§4.87 的 `aspoly_natDegree`** ✓ ＋ 系数计算 ✓（`coeff p = 1` ✓）⟹ `leadingCoeff = 1` ✓；
**(ii)** `AdjoinRoot.powerBasisAux' (hg : g.Monic) : Basis (Fin g.natDegree) R (AdjoinRoot g)` ✓ ＋ **`reindex (finCongr …)`** ✓；
**(iii)** 由 `Module.finrank_eq_card_basis` ✓ ＋ `Fintype.card_fin` ✓ ＋ (i) ✓。
**工艺** ✓（入 §5.1 ✓）：**(甲)** **`reindex` 的 `Equiv` 方向** ✗ —— 须**正序** `finCongr (natDegree = p)` ✓
（`.symm` 报 "expected `natDegree = p`" ✓，实测 ✓）；**(乙)** **不可**用 `rw [← natDegree]` 改写目标 ✗ ——
会把 `ASpoly R p a` 里的 `p` **一并改写** ✗（实测 "expected `asCarrier R (ASpoly R p a).natDegree a`" ✓）；
正解 ＝ `finrank_eq_card_basis` 路线 ✓。

**⚠ 意义** ✓：**(ii)** 是 **`{y^i ⊗ g}` 交叉积基** ✓ 与 **`{y^i · φ_g}` 自同态侧基** ✓ 的**共同底座** ✓
⟹ 款③（`δ` 双射）的**显式逆**已在射程内 ✓；**(iii)** 同时供给 **(1b)/(2a)/(2b) 的 C_p 档** ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 `{φ_k root}` 是基 ✗（**只**落 `{1, y, …, y^{p−1}}` ✓）；
**不**声称 `IsGaloisWithGroup` 无条件形 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section ArtinSchreierBasis303

/-- **AS 多项式首一** ✓（`p ≥ 2`）。 -/
theorem aspoly_monic {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p) (a : R) :
    (ASpoly R p a).Monic := by
  show (ASpoly R p a).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, aspoly_natDegree (R := R) hp a, ASpoly, Polynomial.coeff_sub,
    Polynomial.coeff_sub, Polynomial.coeff_X_pow_self,
    Polynomial.coeff_X_of_ne_one (by omega : p ≠ 1),
    Polynomial.coeff_C_of_ne_zero (by omega : p ≠ 0)]
  norm_num

/-- **AS 载体的幂基** ✓✅：`{1, y, …, y^{p−1}}` ✓。 -/
noncomputable def asCarrierBasis {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p)
    (a : R) : Module.Basis (Fin p) R (asCarrier R p a) :=
  (AdjoinRoot.powerBasisAux' (aspoly_monic (R := R) hp a)).reindex
    (finCongr (aspoly_natDegree (R := R) hp a))

/-- **AS 载体的秩 ＝ `p`** ✓✅。 -/
theorem asCarrier_finrank {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p) (a : R) :
    Module.finrank R (asCarrier R p a) = p := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' (aspoly_monic (R := R) hp a)),
    Fintype.card_fin, aspoly_natDegree (R := R) hp a]

end ArtinSchreierBasis303

#print axioms aspoly_monic
#print axioms asCarrierBasis
#print axioms asCarrier_finrank


/-! ### 4.92 **朴素正规基候选的判否（机检反例）**（第 304 轮）
—— `{φ_k root}` **不可能**是正规基 ✓（`p ≥ 3` ✗）；正确候选须为**更高权**元素 ✓

**落成** ✓✅：**`asCarrier_conj_span_le`** ✓：`Submodule.span R (range (k ↦ φ_k root)) ≤ Submodule.span R {1, root}` ✓
—— **共轭族 `{φ_k root}` 的生成子模落在 `R + R·root` 内** ✓ ⟹ 其维数 **≤ 2** ✓ ⟹
**`p ≥ 3` 时不可能生成 `S`** ✗（`S` 秩 `p` ✓，§4.91 ✓）⟹ **朴素候选判否** ✓。

**⚠ 意义（判否的正面价值）** ✓：**§4.88** 只给 `{φ_k root}` 的**互异性** ✓（**是**正规基的**必要**条件 ✓）；
本轮**机检**其**不充分** ✓ —— 因为 `φ_k root = root + of (c k)` ✓（§4.81 ✓）恒落在**二维**子空间 `R + R·root` 内 ✓
（`of (c k)` ＝ **纯量** ✓）。**⟹ 正规基元须取「更高权」者** ✓（候选：`y^{p−1}` ✓，**下一手** ✓）。

**⚠ 工艺** ✓（入 §5.1 ✓，**与 §4.88 同型，此为第二次命中** ✓）：`rintro x ⟨k, rfl⟩` 后的目标是
**未 β-归约形** ✓ ⟹ `rw` **不命中** ✗；**解** ＝ 先 `show <显式形>` ✓ 再 `rw` ✓。

**🔴 不声称** ✗：**不**声称 `{φ_k root}` **不是**正规基 ✗（**只**证生成子模 ≤ `R + R·root` ✓ —— `p ≥ 3` 的结论由其**秩**推 ✓，
未单独落为定理 ✗）；**不**声称款③ 已证 ✗；**不**声称 `{y^{p−1}}` 的共轭族是基 ✗（**未探** ✗）。 -/

section ArtinSchreierNaiveCandidate304

attribute [local instance] asCarrierMSA

/-- **朴素候选判否** ✓：共轭族 `{φ_k root}` 的生成子模落于 `R + R·root` 内 ✓（`p ≥ 3` 时**必非基** ✗）。 -/
theorem asCarrier_conj_span_le {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    Submodule.span R (Set.range (fun k : Multiplicative (ZMod p) =>
        asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
          (castHom_pow (p := p) (Multiplicative.toAdd k)) (AdjoinRoot.root (ASpoly R p a))))
      ≤ Submodule.span R ({(1 : asCarrier R p a),
          AdjoinRoot.root (ASpoly R p a)} : Set (asCarrier R p a)) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨k, rfl⟩
  show asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      (castHom_pow (p := p) (Multiplicative.toAdd k)) (AdjoinRoot.root (ASpoly R p a))
    ∈ Submodule.span R ({(1 : asCarrier R p a),
        AdjoinRoot.root (ASpoly R p a)} : Set (asCarrier R p a))
  rw [asShiftH_root]
  refine Submodule.add_mem _
    (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))) ?_
  rw [show AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      = (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k)) • (1 : asCarrier R p a) from by
    rw [Algebra.smul_def, mul_one]; rfl]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl)))

end ArtinSchreierNaiveCandidate304

#print axioms asCarrier_conj_span_le


/-! ### 4.93 **款③ 的两条秩输入（交叉积／自同态环）**（第 305 轮）
—— 款③ 的**维数计数**两半 ✓（场地换挡：环档 AS 载体 → **域档 Galois 通道** ✓）

**落成两件** ✓✅：**(i)** **`skew_finrank`** ✓✅：**`finrank R (Δ(S/R,G)) = |G| · finrank R S`** ✓；
**(ii)** **`end_finrank`** ✓✅：**`finrank R (End_R S) = (finrank R S)²`** ✓。

**⚠ 意义（换挡说明）** ✓：环档 AS 载体上款③ 的显式逆须算 **`p²` 阶矩阵** ✗（§265.6／§266.6 ✓）；
而**源两条陈述的场地是域** ✓ ⟹ 改走**域档 Galois 通道** ✓：**(甲)** **mathlib 正规基定理** ✓
（`IsGalois.normalBasis` ✓，`Galois/NormalBasis.lean:120` ✓，且**本库第 285 轮已机检** ✓）；
**(乙)** 正规基 ⟹ **`δ` 单射** ✓（由 `{g•θ}` 的**无关性** ✓）；**(丙)** 秩相等（**本轮两件** ✓）＋ 单射
⟹ **双射** ✓（域档 ✓，第 287 轮 `delta_surjective_of_injective_of_card_eq_finrank` ✓ 同型）。

**⚠ 工艺** ✓（入 §5.1 ✓）：**(甲)** `SkewMonoidAlgebra` 是**结构** ✗（非 `G →₀ S` 的 defeq ✗）⟹ 秩须经
**`coeffLinearEquiv`** ✓（注意 mathlib 形参名：其 `S` ＝ 我们的 `R` ✓、其 `k` ＝ 我们的 `S` ✓ —— **易错** ✗）；
**(乙)** `finrank_eq` 方向：**正向** ✓（`←` 不命中 ✗，实测 ✓）；**(丙)** 两件皆需 **`StrongRankCondition R`** ✓
（`skew` 侧还需 `Module.Free R S` ✓）。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗（**只**落秩输入 ✓）；**不**声称域档正规基通道已通 ✗（**下两步** ✓）；
**不**声称 `IsGaloisWithGroup` 无条件形 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section GaloisRankInputs305

/-- **交叉积的秩** ✓：`finrank R (Δ(S/R,G)) = |G| · finrank R S` ✓。 -/
theorem skew_finrank {R : Type u} [CommRing R] [StrongRankCondition R] {S : Type u}
    [CommRing S] [Algebra R S] [Module.Free R S] {G : Type u} [Group G] [Fintype G] :
    Module.finrank R (SkewMonoidAlgebra S G) = Fintype.card G * Module.finrank R S := by
  rw [(SkewMonoidAlgebra.coeffLinearEquiv (S := R) (k := S) (G := G)).finrank_eq,
    Module.finrank_finsupp]

/-- **自同态环的秩** ✓：`finrank R (End_R S) = (finrank R S)²` ✓。 -/
theorem end_finrank {R : Type u} [CommRing R] [StrongRankCondition R] {S : Type u}
    [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] :
    Module.finrank R (Module.End R S) = Module.finrank R S * Module.finrank R S := by
  rw [Module.finrank_linearMap]

end GaloisRankInputs305

#print axioms skew_finrank
#print axioms end_finrank


/-! ### 4.94 **`δ` 的点值形（生成元）**（第 306 轮）
—— 域档款③ 的**单射**证明的第一步 ✓（系数展开的原子件 ✓）

**落成** ✓✅：**`delta_single_apply`** ✓：`(δ (single g s)) w = s * (g • w)` ✓
（**点值形** ✓，由 §4.90 的 `deltaToEndAdd_single` ✓ ＋ `Module.End.mul_apply` ✓ ＋ `rfl` ✓ 收口 ✓）。

**⚠ 用途** ✓：域档 **`δ` 单射**的路线 ＝ **(甲)** **系数展开**
`(δ z) w = ∑_{g ∈ supp z} (coeff z g) * (g • w)` ✓（**本轮落其原子件** ✓）；
**(乙)** 在 `w = h⁻¹ • θ` ✓（**正规基** `b g = g • θ` ✓，mathlib `IsGalois.normalBasis` ✓）处取值 ✓；
**(丙)** 由 `{g • θ}` 的**线性无关**（`b.linearIndependent` ✓）得 `coeff z (g h) = 0` ∀ `g h` ✓ ⟹ `z = 0` ✓；
**(丁)** 秩相等（§4.93 ✓）＋ 单射 ⟹ **双射** ✓（域档 ✓）。

**⚠ 本轮受阻（如实登记）** ✗：**(甲)** 的**展开**未收口 ✓ —— 关键步是**分解**
`z = ∑_{g ∈ supp z} single g (coeff z g)` ✓；**本轮实测** ✗：`conv_lhs` ＋ `show … from ?_` 形**不成立** ✓
（报 "There are unsolved goals" ✓）⟹ **下一手**用 **`SkewMonoidAlgebra.coeff_injective`** ✓（`apply` 后化为
**Finsupp 等式** ✓，两侧由 `coeff` 的**加法性** ✓＋ `Finsupp` 的 `single`-展开引理 ✓ 收口 ✓）。

**🔴 不声称** ✗：**不**声称系数展开已证 ✗；**不**声称款③ 已证 ✗；**不**声称域档通道已通 ✗；
**不**声称 `IsGaloisWithGroup` 无条件形 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section DeltaPointValue306

open ABGV52.BTier

/-- **`δ` 的点值形** ✓：`(δ (single g s)) w = s * (g • w)` ✓。 -/
theorem delta_single_apply {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (g : G) (s w : S) :
    deltaToEndRingHom hRG (SkewMonoidAlgebra.single g s) w = s * (g • w) := by
  show deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) w = s * (g • w)
  rw [deltaToEndAdd_single, Module.End.mul_apply]
  rfl

end DeltaPointValue306

#print axioms delta_single_apply


/-! ### 4.95 **基的系数消去（步骤丙的规范化形）**（第 307 轮）
—— 域档款③ 单射证明的**独立性接口** ✓（把 smul 会话交给调用方 ✓）

**落成** ✓✅：**`basis_coeff_eq_zero`** ✓✅：设 `b : Module.Basis G R S` ✓、`c : G → R` ✓，
**`∑_g c g • b g = 0` ⟹ 全部 `c g = 0`** ✓（由 `Fintype.linearIndependent_iff` ✓ ＋ `b.linearIndependent` ✓ 一行 ✓）。

**⚠ 工艺（两条，入 §5.1；均为本轮实测所得）** ✓：
**(甲) 实例路径不一致** ✗：`Module.Basis.linearIndependent` 落在 **`AddCommMonoid`** 路径 ✓ 而
`Fintype.linearIndependent_iff` 落在 **`AddCommGroup`** 路径 ✓ ⟹ 二者**不必互相匹配** ✗（实测报
"Application type mismatch: … AddCommGroup.toAddCommMonoid" ✓）；**解** ✓：把本件的 `S` 声明为
**`[AddCommGroup S]`** ✓（令两侧同路径 ✓）。
**(乙) `whnf` 心跳** ✗：`∑ g, c g • b g = 0` 型目标在**抽象 `Semiring`／多 smul 实例**下 elaboration 极贵 ✓
（实测 **200000 心跳耗尽** ✗）；**解** ✓：`set_option maxHeartbeats 800000 in` ✓（**不增警告** ✓）。

**⚠ 用途** ✓：域档款③ 的**步骤丙** ＝ 在 `w = h⁻¹ • θ` 处取 `(δ z) w = 0` ✓ 得
`∑_g (coeff z g) • ((g h⁻¹) • θ) = 0` ✓ ⟹（把 `((g h⁻¹) • θ)` 写成 `b (g h⁻¹)` ✓ —— 由正规基
`b g = g • θ` ✓）用**本件** ⟹ `coeff z (·) = 0` ✓ ⟹ `z = 0` ✓。

**🔴 不声称** ✗：**不**声称系数展开（§268.3 ✓ 的分解步）已证 ✗；**不**声称款③ 已证 ✗；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section BasisCoeffCancel307

set_option maxHeartbeats 800000 in
/-- **基的系数消去** ✓：`∑_g c g • b g = 0` ⟹ 全部 `c g = 0` ✓。 -/
theorem basis_coeff_eq_zero {R : Type*} [CommRing R] {S : Type*} [AddCommGroup S]
    [Module R S] {G : Type*} [Group G] [Fintype G] (b : Module.Basis G R S) {c : G → R}
    (h : ∑ g, c g • b g = 0) : ∀ g : G, c g = 0 :=
  (Fintype.linearIndependent_iff.mp b.linearIndependent) c h

end BasisCoeffCancel307

#print axioms basis_coeff_eq_zero


/-! ### 4.96 **交叉积元的 `single` 分解（§268.3 受阻点的拆除）**（第 308 轮）
—— 系数展开（步骤甲）的**最后一环** ✓

**落成** ✓✅：**`skew_eq_sum_single`** ✓✅：**`z = ∑_{g ∈ supp z} single g (z.coeff g)`** ✓
（**第 306 轮受阻** ✗ —— 当时用 `conv_lhs` ＋ `show … from ?_` 报 "There are unsolved goals" ✓；
**本轮拆除** ✓）。

**机制** ✓：**(i)** 经 **`SkewMonoidAlgebra.coeff_injective`** ✓ 化归 **Finsupp 等式** ✓；
**(ii)** 和的 `coeff` 经 **`coeffAddEquiv` ＋ `map_sum`** ✓（**不可**直接对 `coeff` 用 `map_sum` ✗ —— 实测
"Did not find an occurrence" ✓，须先 `show … coeffAddEquiv (∑ …) = _` ✓）；
**(iii)** 逐点比较用 **`Finsupp.finsetSum_apply`** ✓ ＋ `Finset.sum_eq_single`／`sum_eq_zero` ✓（分 `g ∈ supp z` 两档 ✓）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：**(甲)** `coeff` 的和须经 **`coeffAddEquiv`** ✓（见上 ✗）；
**(乙)** `Finsupp.single_eq_of_ne` 的**方向** ✗：其参数是 `a ≠ a'` ✓ 而常见假设形是 `b ≠ g` ✓ ⟹ 须 **`Ne.symm`** ✓；
**(丙)** **`Finsupp.not_mem_support_iff` 不存在** ✗（§269.6 已登记 ✓）⟹ 用 **`Finsupp.mem_support_iff`** ✓
（`g ∉ supp z` ⟹ `z.coeff g = 0` ✓ 经 `simpa [Finsupp.mem_support_iff] using hg` ✓）。

**⚠ 意义** ✓：**步骤甲**的分解已备 ✓ ⟹ 展开 `(δ z) w = ∑_{g ∈ supp z} (coeff z g) * (g • w)` ✓
（`map_sum` ✓ ＋ §4.94 的 `delta_single_apply` ✓）**只余一步** ✓。

**🔴 不声称** ✗：**不**声称系数展开已证 ✗（**分解已落** ✓，**展开未落** ✗）；**不**声称款③ 已证 ✗；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section SkewDecomposition308

/-- **`single` 分解** ✓：`z = ∑_{g ∈ supp z} single g (coeff z g)` ✓。 -/
theorem skew_eq_sum_single {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] (z : SkewMonoidAlgebra S G) :
    z = ∑ g ∈ z.support, SkewMonoidAlgebra.single g (z.coeff g) := by
  classical
  apply SkewMonoidAlgebra.coeff_injective
  have hcoe : (∑ g ∈ z.support, SkewMonoidAlgebra.single g (z.coeff g)).coeff
      = ∑ g ∈ z.support, Finsupp.single g (z.coeff g) := by
    show SkewMonoidAlgebra.coeffAddEquiv (∑ g ∈ z.support,
      SkewMonoidAlgebra.single g (z.coeff g)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => SkewMonoidAlgebra.coeff_single g (z.coeff g)
  rw [hcoe]
  ext g
  rw [Finsupp.finsetSum_apply]
  by_cases hg : g ∈ z.support
  · rw [Finset.sum_eq_single g]
    · simp
    · intro b _ hbg
      exact Finsupp.single_eq_of_ne (Ne.symm hbg)
    · intro hg'
      exact absurd hg hg'
  · rw [Finset.sum_eq_zero]
    · simpa [Finsupp.mem_support_iff] using hg
    · intro b hb
      exact Finsupp.single_eq_of_ne (fun h => hg (h ▸ hb))

end SkewDecomposition308

#print axioms skew_eq_sum_single


/-! ### 4.97 **`δ` 的系数展开（步骤甲收官）**（第 309 轮）
—— 域档款③ 单射的**前半** ✓

**落成** ✓✅：**`delta_apply_sum`** ✓✅：**`(δ z) w = ∑_{g ∈ supp z} (coeff z g) * (g • w)`** ✓ ——
由 §4.96 的**分解** ✓ ＋ `map_sum` ✓ ＋ `LinearMap.sum_apply` ✓ ＋ §4.94 的 `delta_single_apply` ✓ 收口 ✓。

**⚠ 工艺（四条，入 §5.1；均本轮实测）** ✓：
**(甲)** `skew_eq_sum_single` 的 `R` **不可推断** ✗（其 `R` 不出现在 `z` 中 ✓）⟹ 须 **`(R := R)`** 显式给出 ✓
（否则报 "typeclass instance problem is stuck: Algebra ?m S" ✓）；
**(乙)** 重写**必须限于左侧** ✗：直接 `rw` 会把右侧 `z.support`／`z.coeff` 里的 `z` **一并改写** ✗
（实测右侧变成 `(∑ …).support` ✓）⟹ 用 **`conv_lhs => rw [ … ]`** ✓；
**(丙)** 求值**须从和号外搬入** ✗：`map_sum` 给出 `(∑ …) w` ✓ 而目标是 `∑ … (… w)` ✓ ⟹ 用
**`LinearMap.sum_apply`** ✓（**`Finset.sum_apply` 不命中** ✗，实测 ✓）；
**(丁)** `conv_lhs` 在**旧版**写法下曾报 "There are unsolved goals" ✗（§268.3 ✓）——**本轮**用**具名引理**（非 `show … from ?_`）✓ 后成立 ✓。

**⚠ 意义** ✓：**步骤甲**（系数展开）**收官** ✓ ⟹ 域档款③ 的**单射**只余：取 `w = h⁻¹ • θ` ✓
（换元用 `b.reindex (Equiv.mulRight h⁻¹)` ✓）＋ §4.95 的 `basis_coeff_eq_zero` ✓ ⟹ `z = 0` ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗；
**不**声称源 `theorem-1-2` 已证 ✗。 -/

section DeltaExpansion309

open ABGV52.BTier

/-- **系数展开** ✓：`(δ z) w = ∑_{g ∈ supp z} (coeff z g) * (g • w)` ✓。 -/
theorem delta_apply_sum {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (z : SkewMonoidAlgebra S G) (w : S) :
    deltaToEndRingHom hRG z w = ∑ g ∈ z.support, z.coeff g * (g • w) := by
  conv_lhs => rw [skew_eq_sum_single (R := R) z]
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun g _ => delta_single_apply hRG g _ w

end DeltaExpansion309

#print axioms delta_apply_sum


/-! ### 4.98 **作用即 `R`-代数自同构（Dedekind 通道的桥）**（第 310 轮）
—— **纠正一条错误路线** ✗ ＋ 落**正确的桥** ✓

**⚠ 路线纠正（重要，本节留存）** ✗：§270.5／§271.5 曾拟「在 `w = θ` 处取值 ⟹ 由 `{g•θ}` 的
**`R`-线性无关**推系数全零」✗ —— **该推理无效** ✗：`δ z = 0` 在 `w = θ` 处给出的关系是
`∑_g (coeff z g) * (g • θ) = 0` ✓，其系数 `coeff z g` 属 **`S`** ✓ 而非 `R` ✗；而 **`S`-线性关系恒存在** ✓
（`dim_S S = 1` ✓：任两元素都 `S`-相关 ✗）⟹ **不能**由 `R`-无关性推出 `S`-系数为零 ✗。
**正路** ✓ ＝ **Dedekind 引理** ✓：**已核** mathlib 有
**`linearIndependent_algHom_toLinearMap (K M L) : LinearIndependent L AlgHom.toLinearMap`** ✓
（**`L`-线性**无关 ✓ —— **强形** ✓，正是所需 ✓）。

**落成** ✓✅：**`actionAlgEquiv`** ✓✅：给定 `[MulSemiringAction G S]` ✓ ＋ **不动基**
`hfix : ∀ g r, g • algebraMap R S r = algebraMap R S r` ✓ ⟹ **每个 `g` 给出 `S ≃ₐ[R] S`** ✓
（`toFun x := g • x` ✓，逆 `g⁻¹ • -` ✓，由 `mul_smul`／`inv_mul_cancel` ✓；保乘／加由
**`MulSemiringAction.smul_mul`** ✓／**`smul_add`** ✓；与 `R` 交换由 `hfix` ✓）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：**(甲)** `AlgEquiv` 结构字面量中 `toFun`／`invFun` 的复合**未 β-归约** ✗
⟹ `left_inv`／`right_inv` **须先 `show`** ✓（否则 `rw [← mul_smul, …]` 不命中 ✗）；
**(乙)** `smul_mul` **须限定** ✓（`MulSemiringAction.smul_mul` ✓；裸名**未知** ✗）而 **`smul_add` 用裸名** ✓
（`MulSemiringAction.smul_add` **未知** ✗ —— **二者不对称** ✗，实测 ✓）；
**(丙)** `LinearIndependent L AlgHom.toLinearMap` 的 `L` 是**系数域** ✓（**不是** `K` ✓）—— 引用时勿错位 ✗。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 Dedekind 通道已通 ✗（**已备桥** ✓，**未接线** ✗）；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section ActionAsAlgEquiv310

/-- **作用即 `R`-代数自同构** ✓：由 `MulSemiringAction` ＋ **不动基** ✓。 -/
noncomputable def actionAlgEquiv {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S]
    (hfix : ∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r) (g : G) :
    S ≃ₐ[R] S where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := by
    show g⁻¹ • (g • x) = x
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv x := by
    show g • (g⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel, one_smul]
  map_mul' x y := by
    show g • (x * y) = (g • x) * (g • y)
    exact MulSemiringAction.smul_mul g x y
  map_add' x y := by
    show g • (x + y) = g • x + g • y
    exact smul_add g x y
  commutes' r := hfix g r

end ActionAsAlgEquiv310

#print axioms actionAlgEquiv


/-! ### 4.99 **Dedekind 引理的限制形**（第 311 轮）
—— 域档款③ 单射的**独立性引擎** ✓（§272.1 纠正后的正路 ✓）

**落成** ✓✅：**`algHom_linearIndependent_of_injective`** ✓✅：设 `L` 为**域** ✓（`[CommRing L] [IsDomain L]` ✓）、
`f : ι → (L →ₐ[K] L)` **单射** ✓ ⟹ **`LinearIndependent L (fun i => (f i).toLinearMap)`** ✓
—— 即 **`f` 的像在 `L` 上线性无关** ✓（**强形** ✓，系数取 `L` ✓）。

**机制** ✓：mathlib 的 **Dedekind 引理** ✓ `linearIndependent_algHom_toLinearMap (K L L) :
LinearIndependent L AlgHom.toLinearMap` ✓（**全部** `K`-代数同态 ✓，索引型可无限 ✓）
＋ **`LinearIndependent.comp`** ✓（以单射 `f` 限制到有限指标型 `ι` ✓）。

**⚠ 工艺（两条，入 §5.1；均本轮实测）** ✓：
**(甲)** **实例路径** ✗：`actionAlgEquiv` 以 **`[CommRing R]`** 声明 ✓ ⟹ 与之复合的引理**也须**用 `[CommRing K]` ✓
（用 `[CommSemiring K]`／`[Field L]` 会报 "Application type mismatch … algebraMap …" ✗，实测 ✓）；
**(乙) 心跳** ✗：`LinearIndependent L (fun i => …toLinearMap)` 的 elaboration **极贵** ✓
（**200000 ✗／800000 ✗ 皆耗尽** ✓，实测 ✓）⟹ 须 **`set_option maxHeartbeats 4000000 in`** ✓（**不增警告** ✓）。

**⚠ 用途** ✓：域档款③ 的**单射**：`δ z = 0` ✓ ⟹（§4.97 ✓）`∀ w, ∑_g (coeff z g) * (g • w) = 0` ✓；
若某 `coeff z g₀ ≠ 0` ✓ 则乘 `(coeff z g₀)⁻¹`（**须 `[Field L]`** ✓）⟹ **`g₀` 成为其余 `g` 的 `L`-线性组合** ✗
⟹ 与**本件** ✓（取 `f := fun g => actionAlgEquiv hfix g` ✓，**须该族单射** ＝ **忠实性** ✓）**矛盾** ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 Dedekind 通道已接线 ✗（**引擎已落** ✓）；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section DedekindRestriction311

set_option maxHeartbeats 4000000 in
/-- **Dedekind 引理的限制形** ✓：单射族的 `toLinearMap` 在 `L` 上线性无关 ✓。 -/
theorem algHom_linearIndependent_of_injective {K : Type*} [CommRing K] {L : Type*} [CommRing L]
    [IsDomain L] [Algebra K L] {ι : Type*} [Fintype ι] (f : ι → (L →ₐ[K] L))
    (hf : Function.Injective f) :
    LinearIndependent L (fun i : ι => (f i).toLinearMap) :=
  (linearIndependent_algHom_toLinearMap K L L).comp f hf

end DedekindRestriction311

#print axioms algHom_linearIndependent_of_injective


/-! ### 4.100 **`δ z = 0` 的点值刻画**（第 312 轮）
—— Dedekind 接线的**入口件** ✓

**落成** ✓✅：**`delta_eq_zero_iff`** ✓✅：
**`δ z = 0 ⟺ ∀ w, ∑_{g ∈ supp z} (coeff z g) * (g • w) = 0`** ✓
（**⟸** 由 §4.97 的 `delta_apply_sum` ✓ ＋ `Module.End.ext` ＋ `simp` ✓；**⟹** 由 `congrArg (· w)` ✓ ＋ `simpa` ✓）。

**⚠ 用途** ✓：域档款③ 单射的**归一形** ✓ —— 此后只需处理**系数关系** ✓（不再涉及 `Module.End` ✓）：
若某 `s := coeff z g₀ ≠ 0` ✓，则在**域** `S` 中乘 `s⁻¹` ✓（**须 `[Field S]`** ✓）得
`∑_{g ∈ supp z} (-(s⁻¹ * coeff z g)) * (g • w) = 0` ✓，把 `g₀` 项分离 ✓ 即得
**`g₀` 是其余 `g` 的 `S`-线性组合** ✗ ⟹ 与 §4.99 的 **Dedekind** ✓（**须**该族**单射** ＝ **忠实性** ✓）**矛盾** ✓。

**⚠ 工艺** ✓：**(甲)** `Module.End.ext` ✓（`ext w` ✓）用于**反向** ✓；
**(乙)** `congrArg (fun f : Module.End R S => f w)` ✓ ＋ `simpa [delta_apply_sum …]` ✓ 用于**正向** ✓
（**`Module.End` 上无 `funext` 直接形** ✗，须给定类型的 `congrArg` ✓）。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 Dedekind 已接线 ✗（**入口件已落** ✓）；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section DeltaZeroIff312

open ABGV52.BTier

/-- **`δ z = 0` 的点值刻画** ✓。 -/
theorem delta_eq_zero_iff {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (z : SkewMonoidAlgebra S G) :
    deltaToEndRingHom hRG z = 0 ↔
      ∀ w : S, ∑ g ∈ z.support, z.coeff g * (g • w) = 0 := by
  constructor
  · intro hz w
    have h := congrArg (fun f : Module.End R S => f w) hz
    simpa [delta_apply_sum hRG z w] using h
  · intro h
    ext w
    rw [delta_apply_sum hRG z w, h w]
    simp

end DeltaZeroIff312

#print axioms delta_eq_zero_iff


/-! ### 4.101 **系数和扩到全 `G`**（第 313 轮）
—— Dedekind 接线的**第二入口件** ✓

**落成** ✓✅：**`delta_sum_all`** ✓✅：对 `z : SkewMonoidAlgebra S G` ✓，
**`(∑_{g ∈ supp z} coeff z g * w) = 0 ⟹ (∑_{g : G} coeff z g * w) = 0`** ✓
（**支撑外系数为零** ✓ ⟹ 补零不改变和 ✓）。

**⚠ 用途** ✓：§4.100 给出的是**支撑上的和** ✓，而 §4.99 的 **Dedekind** ✓ 需要**全 `G` 上的和** ✓
（系数族 `G → S` ✓）⟹ 本件正是二者的**桥** ✓。

**⚠ 工艺（一条，入 §5.1）** ✓：**`Finset.sum_subset` 的方向** ✗ —— 其 `s₁`／`s₂` 由**目标**推断 ✓，
而 `h₁` 须写成 **`s₁ ⊆ s₂`** ✓；目标为 `∑_{univ} = ∑_{supp}` 时它会要求 **`univ ⊆ supp`** ✗（**假** ✗，实测 ✓）；
**解** ✓：把等式**写成反向**（`∑_{supp} = ∑_{univ}` ✓）并给出 `Finset.subset_univ` ✓，收尾用 **`rw [← h1, h]`** ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 Dedekind 已接线 ✗（**两件入口已备** ✓）；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section DeltaSumAll313

open ABGV52.BTier

/-- **系数和扩到全 `G`** ✓（支撑外系数为零 ✓）。 -/
theorem delta_sum_all {S : Type*} [CommRing S] {G : Type*} [Group G] [Fintype G]
    (z : SkewMonoidAlgebra S G) :
    ∀ w : S, (∑ g ∈ z.support, z.coeff g * w) = 0 → ∑ g : G, z.coeff g * w = 0 := by
  intro w h
  have h1 : (∑ g ∈ z.support, z.coeff g * w) = ∑ g : G, z.coeff g * w :=
    Finset.sum_subset (Finset.subset_univ z.support) (fun g _ hg => by
      rw [show z.coeff g = 0 from by simpa [Finsupp.mem_support_iff] using hg, zero_mul])
  rw [← h1, h]

end DeltaSumAll313

#print axioms delta_sum_all


/-! ### 4.102 **支撑和 ＝ 全群和（最一般形 ＋ `(g • w)` 档）**（第 314 轮）
—— Dedekind 接线的**求和归一（一般化 §4.101）** ✓

**落成两件** ✓✅：**(i)** **`skew_sum_univ`** ✓✅：`(∑_{g ∈ supp z} f g) = ∑_{g : G} f g` ✓（**只要 `f` 在支撑外为零** ✓
—— **最一般形** ✓，§4.101 仅是其 `f g = coeff z g * w` 特例 ✓）；
**(ii)** **`delta_sum_univ`** ✓✅：`(∑_{g ∈ supp z} coeff z g * (g • w)) = ∑_{g : G} coeff z g * (g • w)` ✓
—— **Dedekind 接线所需形** ✓（**§4.101 不够用** ✗：其第二因子是**常数** ✓ 而此处是 `g • w` ✓ **随 `g` 变** ✗）。

**⚠ 本轮受阻（如实登记）** ✗：**求和分裂** —— 拟用 `Finset.add_sum_erase`／`Finset.sum_erase_add` ✓ 在 `g₀` 处分裂
`∑_{g : G} coeff z g * (g • w)` ✓；**实测两者皆不命中** ✗（报 "Did not find an occurrence of the pattern" ✓，
其模式为 `∑ x ∈ s.erase a, f x (+|前置) f a` ✓ 而目标为**绑定记法** `∑ g, …` ✓）⟹ **下一手**：先把它**改写成
`∑ g ∈ (Finset.univ : Finset G), …`** ✓（`show` 或 `rfl` 形 ✓）再分裂 ✓，或改用 `Finset.sum_eq_add_sum_diff_singleton` ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 Dedekind 已接线 ✗（**求和归一已备** ✓，**分裂未收口** ✗）；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section SupportSumUniv314

open ABGV52.BTier

/-- **支撑和 ＝ 全群和** ✓（最一般形 ✓）。 -/
theorem skew_sum_univ {S : Type*} [CommRing S] {G : Type*} [Group G] [Fintype G]
    (z : SkewMonoidAlgebra S G) (f : G → S) (hf : ∀ g, g ∉ z.support → f g = 0) :
    (∑ g ∈ z.support, f g) = ∑ g : G, f g :=
  Finset.sum_subset (Finset.subset_univ z.support) (fun g _ hg => hf g hg)

/-- **`(g • w)` 档** ✓：Dedekind 接线所需形 ✓。 -/
theorem delta_sum_univ {S : Type*} [CommRing S] {G : Type*} [Group G] [Fintype G]
    [MulSemiringAction G S] (z : SkewMonoidAlgebra S G) (w : S) :
    (∑ g ∈ z.support, z.coeff g * (g • w)) = ∑ g : G, z.coeff g * (g • w) :=
  skew_sum_univ z _ (fun g hg => by
    rw [show z.coeff g = 0 from by simpa [Finsupp.mem_support_iff] using hg, zero_mul])

end SupportSumUniv314

#print axioms skew_sum_univ
#print axioms delta_sum_univ


/-! ### 4.103 **全群和的单点分裂**（第 315 轮）—— §276.3 受阻点拆除 ✓

**落成** ✓✅：**`sum_univ_split`** ✓✅：**`(∑_{g : G} f g) = f g₀ + ∑_{g ∈ univ.erase g₀} f g`** ✓
（`[Fintype G]` ✓、`[DecidableEq G]` ✓）。

**⚠ 工艺（一条，入 §5.1；本轮实测）** ✓：**`Finset.add_sum_erase` 须给足三参** ✓ ——
写成 **`Finset.add_sum_erase Finset.univ f (Finset.mem_univ g₀)`** ✓ 即成立 ✓；
而**省略参数**（`Finset.add_sum_erase _ _ _` ✓）在长证明中**实测不命中** ✗（§276.3 ✓）⟹ **凡分裂全群和，一律具名给全三参** ✓。

**⚠ 用途** ✓：Dedekind 接线的**最后一件工具** ✓ —— 由 §4.102 的 `delta_sum_univ` ✓ 把
`∑_{supp}` 换成 `∑_{G}` ✓，再用**本件**在 `g₀` 处分裂 ✓ ⟹ 乘 `s⁻¹` ✓ ⟹ 得
`(g₀ • w) = -∑_{g ∈ univ.erase g₀} (s⁻¹ * coeff z g) * (g • w)` ✓ ⟹ 构造系数族 `d` ✓ 与 §4.99 **矛盾** ✓。

**🔴 不声称** ✗：**不**声称款③ 已证 ✗；**不**声称 Dedekind 已接线 ✗（**工具齐备** ✓，**组合未收口** ✗）；
**不**声称域档通道已通 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗。 -/

section SumUnivSplit315

/-- **全群和的单点分裂** ✓。 -/
theorem sum_univ_split {S : Type*} [AddCommMonoid S] {G : Type*} [Fintype G] [DecidableEq G]
    (f : G → S) (g₀ : G) :
    (∑ g : G, f g) = f g₀ + ∑ g ∈ (Finset.univ.erase g₀), f g := by
  rw [Finset.add_sum_erase Finset.univ f (Finset.mem_univ g₀)]

end SumUnivSplit315

#print axioms sum_univ_split


/-! ### 4.104 **域档 `δ` 单射（Dedekind 通道组装完成）**（第 316 轮）
—— 🔴 **域档款③ 的两半之一** ✓（秩相等已在 §4.93 ✓ ⟹ **双射** 只差一行 ✓）

**落成** ✓✅：**`delta_injective_of_field`** ✓✅：设 `K` 交换环 ✓、**`L` 域** ✓、`[Algebra K L]` ✓、
`G` 有限群 ✓ 作用于 `L` ✓、**(i)** `hfix`（**不动基** ✓）、**(ii)** `hRG`（与 `K`-纯量交换 ✓）、
**(iii)** `hfaith`（**忠实** ✓：`g ↦ actionAlgEquiv hfix g` **单射** ✓）⟹ **`δ` 单射** ✓✅。

**证明（五步，七件工具全用）** ✓：
**(1)** 反设 `δ z = 0` ✓ 而 `z ≠ 0` ✓ ⟹ 取 `g₀` 使 `s := coeff z g₀ ≠ 0` ✓（`coeff_eq_zero` ✓ ＋ `Finsupp.ne_iff` ✓）；
**(2)** 由 §4.100 ✓ ＋ §4.102 ✓ 得 `∀ w, ∑_{g : G} (coeff z g) * (g • w) = 0` ✓；
**(3)** 由 §4.103 ✓（**具名三参** ✓）在 `g₀` 处分裂 ✓，乘 `s⁻¹` ✓ 并 `Finset.mul_sum` ✓ ⟹
**`(g₀ • w) + ∑_{g ≠ g₀} s⁻¹ * (coeff z g * (g • w)) = 0`** ✓；
**(4)** 取 **`d : G → L`**（`d g₀ := 1` ✓、他处 `d g := s⁻¹ * coeff z g` ✓）⟹ 由 **(3)** ✓ 得
`∀ w, ∑_g d g * (g • w) = 0` ✓ ⟹ `LinearMap.ext` ✓ ＋ `LinearMap.sum_apply` ✓ ⟹
**`∑_g d g • (actionAlgEquiv hfix g).toLinearMap = 0`** ✓；
**(5)** 由 §4.99 ✓（**`hfaith`** ✓ ⟹ `g ↦ (actionAlgEquiv hfix g).toAlgHom` 单射 ✓，经 **`AlgEquiv.ext`** ✓）
得 **`d g₀ = 0`** ✗ ⟹ **`1 = 0` 矛盾** ✓ ⟹ `z.coeff = 0` ✓ ⟹ `z = 0` ✓（`coeff_eq_zero` ✓）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：**(甲)** `Finset.mul_sum` ✓ **须显式**推入（**sum 内外的因子搬移** ✗
不能靠 `simp` ✓）；**(乙)** `Finset.sum_congr` 的证明项**逐点**给出 ✓（`fun g _ => by rw […]` ✓）——
**`congr 1` 后的目标是函数相等** ✗（`mul_assoc` **不适用** ✗，实测 ✓）；**(丙)** `AlgEquiv.toAlgHom_injective`
**不存在** ✗ ⟹ 用 **`AlgEquiv.ext`** ✓ ＋ `congrArg (fun φ : L →ₐ[K] L => φ x)` ✓ 自证单射 ✓。

**🔴 不声称** ✗：**不**声称 `δ` **双射** ✗（**只**落**单射** ✓ —— 双射须接 §4.93 的**秩计数** ✓，**下一手** ✓）；
**不**声称款③ 已证 ✗；**不**声称 `IsGaloisWithGroup` 无条件形 ✗；**不**声称源 `theorem-1-2` 已证 ✗。 -/

section DeltaInjectiveField316

open ABGV52.BTier

set_option maxHeartbeats 4000000 in
/-- **域档 `δ` 单射** ✓✅（Dedekind 通道）。 -/
theorem delta_injective_of_field {K : Type*} [CommRing K] {L : Type*} [Field L] [Algebra K L]
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r)
    (hRG : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hfaith : Function.Injective (fun g : G => actionAlgEquiv (S := L) hfix g)) :
    Function.Injective (deltaToEndRingHom (S := L) hRG) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra hz0
  have hcoe : z.coeff ≠ 0 := fun h => hz0 (SkewMonoidAlgebra.coeff_eq_zero.mp h)
  obtain ⟨g₀, hg₀⟩ := Finsupp.ne_iff.mp hcoe
  have hrel : ∀ w : L, (∑ g ∈ z.support, z.coeff g * (g • w)) = 0 :=
    fun w => (delta_eq_zero_iff (S := L) hRG z).mp hz w
  have hall : ∀ w : L, ∑ g : G, z.coeff g * (g • w) = 0 := by
    intro w
    rw [← delta_sum_univ z w]
    exact hrel w
  have hsplit : ∀ w : L, (g₀ • w)
      + ∑ g ∈ (Finset.univ.erase g₀), (z.coeff g₀)⁻¹ * (z.coeff g * (g • w)) = 0 := by
    intro w
    have h := hall w
    rw [sum_univ_split (fun g => z.coeff g * (g • w)) g₀] at h
    have hmul : (z.coeff g₀)⁻¹ * (z.coeff g₀ * (g₀ • w)
        + ∑ g ∈ (Finset.univ.erase g₀), z.coeff g * (g • w)) = 0 := by rw [h, mul_zero]
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hg₀, one_mul, Finset.mul_sum] at hmul
    exact hmul
  let d : G → L := fun g => if g = g₀ then 1 else (z.coeff g₀)⁻¹ * z.coeff g
  have hd : ∀ w : L, ∑ g : G, d g * (g • w) = 0 := by
    intro w
    rw [sum_univ_split (fun g => d g * (g • w)) g₀]
    simp only [d, if_pos rfl, one_mul]
    rw [Finset.sum_congr rfl (fun g hg => by rw [if_neg (Finset.mem_erase.mp hg).1])]
    rw [Finset.sum_congr rfl (fun g _ => by rw [mul_assoc])]
    exact hsplit w
  have hlin : ∑ g : G, d g • (actionAlgEquiv (S := L) hfix g).toLinearMap = 0 := by
    ext w
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, AlgEquiv.toLinearMap_apply]
    exact hd w
  have hindep := algHom_linearIndependent_of_injective (K := K) (L := L)
    (fun g : G => (actionAlgEquiv (S := L) hfix g).toAlgHom)
    (fun g h hgh => hfaith (AlgEquiv.ext (fun x =>
      congrArg (fun φ : L →ₐ[K] L => φ x) hgh)))
  have hzero := (Fintype.linearIndependent_iff.mp hindep) d hlin g₀
  simp [d] at hzero

end DeltaInjectiveField316

#print axioms delta_injective_of_field


/-! ### 4.105 🔴🔴 **域档款③：`δ` 双射（`IsGaloisWithGroup` 第三款，域档落库）**（第 317 轮）
—— **源 §0 判据的第三款** ✓✅（域档），**三款齐备** ✓✅

**落成** ✓✅：**`delta_bijective_of_field`** ✓✅：`K` **域** ✓、`L` **域** ✓、`[Algebra K L]` ✓、
**`[Module.Finite K L]`** ✓、`G` 有限 ✓ 作用于 `L` ✓、**不动基** ✓ ＋ **`hRG`** ✓ ＋ **忠实** ✓ ＋
**`Module.finrank K L = Fintype.card G`** ✓ ⟹
**`Function.Bijective (deltaToEndRingHom (S := L) hRG)`** ✓✅ —— **即源判据的第三款** ✓。

**证明** ✓：§4.104 的**单射** ✓ ＋ **秩相等** ✓ ＋ 域档判据 ⟹ **满射** ✓：
**(i)** 秩相等：§4.93 的 `skew_finrank` ✓（`finrank K Δ = |G| · finrank K L` ✓）与 `end_finrank` ✓
（`finrank K End = (finrank K L)²` ✓）在 **`finrank K L = |G|`** ✓ 下相等 ✓（`rw` 一步 ✓）；
**(ii)** 单射经 `deltaToEndLinearS` ✓（**同函数** ✓，`toFun := deltaToEndAdd hRG` ✓）传递 ✓；
**(iii)** **`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`** ✓（域档 ✓，第 287 轮已用 ✓）⟹ 满射 ✓。

**⚠ 工艺（四条，入 §5.1；均本轮实测）** ✓：
**(甲) 宇宙约束** ✗：§4.93 的秩件以**单宇宙**声明 ✓ ⟹ 本件 `K`／`L`／`G` **须同宇宙** ✓（`Type u` ✓，
异宇宙报 "Application type mismatch … Type u_1 / Type u_2" ✗）；
**(乙) 有限性实例** ✗：`FiniteDimensional K (SkewMonoidAlgebra L G)` **不自动合成** ✗ ⟹ 经
`Module.Finite.equiv` ✓ ＋ **`coeffLinearEquiv`（取 `.symm`** ✗，方向须匹配 ✓）提供 ✓；
**(丙) 实例风格** ✗：`haveI` 触发 `linter.style.haveILetI` ✗ ⟹ 用 **`let _inst : … := …`** ✓；
**(丁) 判据须具名给 `f`** ✗：`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` ✓ **不能**从 `hinjL` 反推
被作用的线性映射 ✗（报 "type mismatch … ⇑?m.190 / ⇑(deltaToEndLinearS hRG)" ✓）⟹ 须 **`(f := …)`** ✓；
另：秩相等的 `rw` **一步即闭** ✓ —— 再加 `ring`／`ring_nf` 会报 **"No goals to be solved"** ✗（实测 ✓）。

**🔴 不声称** ✗：**不**声称**一般环档**的款③ ✗（**只**域档 ✓ —— 环档 §4.92 已**判否**朴素路线 ✓）；
**不**声称 `IsGaloisWithGroup` 整体（**须三款装配** ✓ —— **域档三款皆已落** ✓，**装配件下一手** ✓）；
**不**声称源 `theorem-1-2` 已证 ✗；**不**声称残余 ①／③ 已证 ✗。 -/

/-- **秩假设 ⟹ 有限** ✓（域档）。 -/
theorem finite_of_finrank_eq_card {K : Type u} [Field K] {L : Type u} [AddCommGroup L]
    [Module K L] {G : Type u} [Group G] [Fintype G]
    (hcard : Module.finrank K L = Fintype.card G) : Module.Finite K L :=
  Module.finite_of_finrank_pos (by rw [hcard]; exact Fintype.card_pos)

section DeltaBijectiveField317

open ABGV52.BTier

set_option maxHeartbeats 4000000 in
/-- **🔴 域档款③** ✓✅：`δ` **双射** ✓（单射 ＋ 秩相等，域档判据）。 -/
theorem delta_bijective_of_field {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
    {G : Type u} [Group G] [Fintype G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r)
    (hRG : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hfaith : Function.Injective (fun g : G => actionAlgEquiv (S := L) hfix g))
    (hcard : Module.finrank K L = Fintype.card G) :
    Function.Bijective (deltaToEndRingHom (S := L) hRG) := by
  let _inst : Module.Finite K L := finite_of_finrank_eq_card hcard
  have hinj : Function.Injective (deltaToEndRingHom (S := L) hRG) :=
    delta_injective_of_field hfix hRG hfaith
  have hrank : Module.finrank K (SkewMonoidAlgebra L G) = Module.finrank K (Module.End K L) := by
    rw [skew_finrank (R := K) (S := L) (G := G), end_finrank (R := K) (S := L), hcard]
  let _inst : Module.Finite K (SkewMonoidAlgebra L G) :=
    Module.Finite.equiv (SkewMonoidAlgebra.coeffLinearEquiv (S := K) (k := L) (G := G)).symm
  have hinjL : Function.Injective (deltaToEndLinearS (G := G) hRG) := fun x y hxy => hinj hxy
  have hsurjL : Function.Surjective (deltaToEndLinearS (G := G) hRG) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := deltaToEndLinearS (G := G) hRG) hrank).mp hinjL
  refine ⟨hinj, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hsurjL y
  exact ⟨x, hx⟩

end DeltaBijectiveField317

#print axioms delta_bijective_of_field


/-! ### 4.106 🔴🔴 **域档 `IsGaloisWithGroup` 装配（源 §0 判据域档完成）**（第 318 轮）
—— **三款齐 ＋ 装配落库** ✓✅

**落成两件** ✓✅：**(i)** **`actionAlgEquiv_injective_of_faithful`** ✓✅：**忠实** `FaithfulSMul G L` ✓ ⟹
**自同构族 `g ↦ actionAlgEquiv hfix g` 单射** ✓（§4.105 的**忠实接口** ✓）；
**(ii)** **`isGaloisWithGroup_of_field`** ✓✅：**`IsGaloisWithGroup K L G hRG`** ✓✅ —— **源 §0 判据的域档完成形** ✓
（**三款装配** ✓：款① ＝ `hfaith` ✓、款② ＝ `hfix` ✓、款③ ＝ **§4.105** ✓）。

**机制** ✓（(i) ✓）：由 `hg : actionAlgEquiv hfix g₁ = actionAlgEquiv hfix g₂` ✓ 取**点值** ✓（`congrArg (· x)` ✓）
⟹ `∀ x, g₁ • x = g₂ • x` ✓ ⟹ `g₂⁻¹ * g₁` **不动一切** ✓（`mul_smul` ✓ ＋ `inv_smul_smul` ✓）
⟹ `g₂⁻¹ * g₁ = 1` ✓（`faithfulSMul_iff` ✓）⟹ `g₁ = g₂` ✓（`mul_left_cancel` ✓）。

**⚠ 工艺（一条，入 §5.1）** ✓：**群消去** ✗ —— 由 `g₂⁻¹ * g₁ = 1` 得 `g₁ = g₂` ✓ 时，
`rw [mul_comm] at h`／`inv_mul_eq_one.mp` 组合**实测不命中** ✗ ⟹ 用 **`mul_left_cancel (a := g₂⁻¹)`** ✓
＋ `rw [h1, inv_mul_cancel]` ✓（**一行** ✓）。

**⚠ 意义（本节为里程碑）** ✓✅：**源 §0 的 Galois 判据在域档已"三款齐 ＋ 装配齐"** ✓ ——
即：**域上有限作用 ＋ 不动基 ＋ 忠实 ＋ `finrank = |G|` ⟹ （交叉积 ≅ 自同态环）** ✓。
**与 AS 档对齐** ✓：AS 档（§4.85／§4.87／§4.89 ✓）是**本判据的载体档特例** ✓（款① 已去条件化 ✓）。

**🔴 不声称** ✗：**不**声称**环档**判据 ✓（**只**域档 ✓）；**不**声称源 `theorem-1-2` 已证 ✗；
**不**声称残余 ①／③ 已证 ✗；**不**声称源 `theorem-5-1`／`theorem-2-1` 已证 ✗。 -/

section IsGaloisWithGroupField318

open ABGV52.BTier

/-- **忠实 ⟹ 自同构族单射** ✓（§4.105 的忠实接口）。 -/
theorem actionAlgEquiv_injective_of_faithful {K : Type u} [CommRing K] {L : Type u} [CommRing L]
    [Algebra K L] {G : Type u} [Group G] [MulSemiringAction G L] (h : FaithfulSMul G L)
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r) :
    Function.Injective (fun g : G => actionAlgEquiv (S := L) hfix g) := by
  intro g₁ g₂ hg
  have hpt : ∀ x : L, g₁ • x = g₂ • x := fun x =>
    congrArg (fun φ : L ≃ₐ[K] L => φ x) hg
  rw [faithfulSMul_iff] at h
  have h1 : g₂⁻¹ * g₁ = 1 := h _ (fun x => by
    rw [mul_smul, hpt x, inv_smul_smul])
  exact mul_left_cancel (a := g₂⁻¹) (by rw [h1, inv_mul_cancel])

/-- **🔴 域档 `IsGaloisWithGroup` 装配** ✓✅（源 §0 判据域档完成形）。 -/
theorem isGaloisWithGroup_of_field {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
    {G : Type u} [Group G] [Fintype G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r)
    (hRG : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hfaith : FaithfulSMul G L)
    (hcard : Module.finrank K L = Fintype.card G) :
    IsGaloisWithGroup K L G hRG :=
  ⟨hfaith, hfix, delta_bijective_of_field hfix hRG
    (actionAlgEquiv_injective_of_faithful hfaith hfix) hcard⟩

end IsGaloisWithGroupField318

#print axioms actionAlgEquiv_injective_of_faithful
#print axioms isGaloisWithGroup_of_field


/-! ### 4.107 **判据的拆装件 ＋ 秩 ⟹ 有限**（第 319 轮）
—— 供**装配**与**实例化**用的接口件 ✓

**落成三件** ✓✅：**(i)** **`finite_of_finrank_eq_card`** ✓✅：域档下 **`finrank K L = |G|`** ✓ ⟹
**`Module.Finite K L`** ✓（**免去**向调用方索取有限性 ✓ —— §4.105 的接口**可简化** ✓）；
**(ii)** **`isGaloisWithGroup_iff`** ✓✅：判据 ＝ **三款合取** ✓（`Iff.rfl` ✓，**拆卸形** ✓）；
**(iii)** **`isGaloisWithGroup_of_clauses`** ✓✅：**三款 ⟹ 判据** ✓（**装配形** ✓ —— §4.89／§4.106 的装配的**通用形** ✓）。

**⚠ 工艺** ✓（入 §5.1 ✓）：**`Module.Finite.of_finrank_ne_zero` 不存在** ✗ ⟹ 用
**`Module.finite_of_finrank_pos`** ✓（`Dimension/Free.lean:272` ✓）＋ `Fintype.card_pos` ✓。

**⚠ 用途** ✓：**(i)** 使 §4.105／§4.106 的假设立式**可去掉 `[Module.Finite K L]`** ✓（**下一手可加固** ✓）；
**(ii)/(iii)** 使**任何**三款来源都能**一次装配**为判据 ✓（含未来的**环档**来源 ✓）。

**🔴 不声称** ✗：**不**声称 §4.105／§4.106 已按 (i) **改写** ✗（**本件只供件** ✓，**改写下一手** ✓）；
**不**声称环档判据 ✓；**不**声称残余 ①／③ 已证 ✗。 -/

section GaloisCriterionInterface319

open ABGV52.BTier

/-- **判据拆装：拆卸形** ✓。 -/
theorem isGaloisWithGroup_iff {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {G : Type u} [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    IsGaloisWithGroup R S G hRG ↔ FaithfulSMul G S
      ∧ (∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r)
      ∧ Function.Bijective (deltaToEndRingHom hRG) :=
  Iff.rfl

/-- **判据拆装：装配形** ✓（三款 ⟹ 判据）。 -/
theorem isGaloisWithGroup_of_clauses {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra R S] {G : Type u} [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (h1 : FaithfulSMul G S)
    (h2 : ∀ (g : G) (r : R), g • algebraMap R S r = algebraMap R S r)
    (h3 : Function.Bijective (deltaToEndRingHom hRG)) :
    IsGaloisWithGroup R S G hRG :=
  ⟨h1, h2, h3⟩

end GaloisCriterionInterface319

#print axioms finite_of_finrank_eq_card
#print axioms isGaloisWithGroup_iff
#print axioms isGaloisWithGroup_of_clauses


/-! ### 4.108 **加固：域档判据去掉有限性假设**（第 320 轮）
—— §4.105／§4.106 **签名加固** ✓（**严格更强** ✓）

**改动** ✓：**(i)** `finite_of_finrank_eq_card` ✓（§4.107 落 ✓）**前移**至 §4.105 之前 ✓（**Lean 须先声明后用** ✗）；
**(ii)** **`delta_bijective_of_field`**（§4.105 ✓）与 **`isGaloisWithGroup_of_field`**（§4.106 ✓）的
**`[Module.Finite K L]` 假设已删** ✓ —— 改为在证明内部 **`let _inst : Module.Finite K L :=
finite_of_finrank_eq_card hcard`** ✓ 供给 ✓。

**⚠ 意义** ✓：**签名严格变强** ✓（老调用方**无需改动** ✓：多给的实例**无害** ✓）；**新调用方免索有限性** ✓
—— 对**实例化**（AS 载体、`C_p` 档、源 §2 构造 ✓）**省一步** ✓。

**⚠ 工艺** ✓（入 §5.1 ✓）：**同文件内的前向引用不可用** ✗ —— 依赖件**必须在用点之前声明** ✓
（否则报 **unknown identifier** ✗，实测 ✓）⟹ 加固时应把辅助件一并**前移** ✓。

**🔴 不声称** ✗：**不**声称这是**新数学** ✗（**只**是接口加固 ✓）；**不**声称 §4.107 的其余两件已用 ✓；
**不**声称环档判据 ✓；**不**声称残余 ①／③ 已证 ✗。 -/


/-! ### 4.109 **忠实 ⟺ 自同构族单射**（第 321 轮）
—— §4.106 接口的**反向** ✓（两形**等价** ✓，调用方可任选 ✓）

**落成两件** ✓✅：**(i)** **`faithfulSMul_of_actionAlgEquiv_injective`** ✓✅：自同构族**单射** ✓ ⟹ **`FaithfulSMul G L`** ✓；
**(ii)** **`faithfulSMul_iff_actionAlgEquiv_injective`** ✓✅：**等价** ✓（§4.106 的正向 ✓ ＋ 本件的反向 ✓）。

**机制** ✓（(i) ✓）：由 `faithfulSMul_iff` ✓ 只需证「不动一切 ⟹ `g = 1`」✓；取
`actionAlgEquiv hfix g = actionAlgEquiv hfix 1` ✓（`ext x` ✓ ＋ `hg x` ✓ ＋ `one_smul` ✓）⟹ 单射性给 `g = 1` ✓。

**⚠ 用途** ✓：**(ii)** 使 §4.105／§4.106 的忠实假设**可任取两形** ✓（`FaithfulSMul` ✓ 或
`Function.Injective (fun g => actionAlgEquiv hfix g)` ✓）—— 对**实例化**（源侧常给「忠实作用」✓）便利 ✓。

**🔴 不声称** ✗：**不**声称环档判据 ✓；**不**声称残余 ①／③ 已证 ✗；**不**声称源两条陈述已证 ✗。 -/

section FaithfulInterface321

open ABGV52.BTier

/-- **自同构族单射 ⟹ 忠实** ✓（§4.106 的反向）。 -/
theorem faithfulSMul_of_actionAlgEquiv_injective {K : Type u} [CommRing K] {L : Type u}
    [CommRing L] [Algebra K L] {G : Type u} [Group G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r)
    (hinj : Function.Injective (fun g : G => actionAlgEquiv (S := L) hfix g)) :
    FaithfulSMul G L := by
  rw [faithfulSMul_iff]
  intro g hg
  refine hinj ?_
  ext x
  rw [show (actionAlgEquiv (S := L) hfix (1 : G)) x = x from one_smul G x]
  exact hg x

/-- **忠实 ⟺ 自同构族单射** ✓（§4.106 ＋ 本件）。 -/
theorem faithfulSMul_iff_actionAlgEquiv_injective {K : Type u} [CommRing K] {L : Type u}
    [CommRing L] [Algebra K L] {G : Type u} [Group G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r) :
    FaithfulSMul G L ↔ Function.Injective (fun g : G => actionAlgEquiv (S := L) hfix g) :=
  ⟨fun h => actionAlgEquiv_injective_of_faithful h hfix,
    fun h => faithfulSMul_of_actionAlgEquiv_injective hfix h⟩

end FaithfulInterface321

#print axioms faithfulSMul_of_actionAlgEquiv_injective
#print axioms faithfulSMul_iff_actionAlgEquiv_injective


/-! ### 4.110 **generic extension 三款的拆装件 ＋ 见证装配**（第 322 轮）
—— 源 `definition-1-1`（三款 ✓）与 `theorem-2-1`（见证 ✓）的**接口件** ✓

**落成三件** ✓✅：**(i)** **`isGenericExtension_iff`** ✓✅（**拆卸形** ✓：三款合取 ✓）；
**(ii)** **`isGenericExtension_of_clauses`** ✓✅（**装配形** ✓：三款 ⟹ `IsGenericExtension` ✓）；
**(iii)** **`genericExtensionWitness_of_clauses`** ✓✅（**见证装配** ✓：三款 ＋ 载体数据 ⟹
**`GenericExtensionWitness F A`** ✓）。

**⚠ 意义** ✓：源 `theorem-2-1` 的**结论形**（`Nonempty (GenericExtensionWitness F A)` ✓）此后**只需三款** ✓：
**(a)** `R` 为**局部化多项式环** ✓（`∃ n w, w ≠ 0 ∧ R ≃ₐ[F] Localization.Away w` ✓）；
**(b)** **`IsGaloisWithGroup R S A hRG`** ✓（**域档已完** ✓ —— 环档为**余项** ✗）；
**(c)** **`RealizationProperty F A R S`** ✓（源 §2 构造的**内容** ✗）。
⟹ **本轮把源 `theorem-2-1` 的缺口"分割包围"为三个具名子目标** ✓（毛式 ✓），其中 **(b)** 在域档**已克** ✓。

**⚠ 工艺** ✓（入 §5.1 ✓）：**`IsGenericExtension`／`RealizationProperty` 在 `ABGV52.BTier` 命名空间** ✓ ⟹
**须限定** ✓（未限定被 `autoImplicit` 误读为隐式变量 ✗，实测 ✓）。

**🔴 不声称** ✗：**不**声称 `IsGenericExtension` 的任何实例已构造 ✗（**只**落拆装件 ✓）；
**不**声称 `GenericExtensionWitness` **非空** ✗；**不**声称源 `theorem-2-1` 已证 ✗；**不**声称残余 ①／③ 已证 ✗。 -/

section GenericExtensionInterface322

/-- **`IsGenericExtension` 拆装（拆卸形）** ✓。 -/
theorem isGenericExtension_iff {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G]
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra F R] [Algebra R S]
    [Algebra F S] [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    BTier.IsGenericExtension F G R S hRG ↔
      (∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))
      ∧ BTier.IsGaloisWithGroup R S G hRG ∧ BTier.RealizationProperty F G R S :=
  Iff.rfl

/-- **`IsGenericExtension` 拆装（装配形）** ✓。 -/
theorem isGenericExtension_of_clauses {F : Type u} [Field F] {G : Type u} [Group G] [Fintype G]
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra F R] [Algebra R S]
    [Algebra F S] [IsScalarTower F R S] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (h1 : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))
    (h2 : BTier.IsGaloisWithGroup R S G hRG)
    (h3 : BTier.RealizationProperty F G R S) :
    BTier.IsGenericExtension F G R S hRG :=
  ⟨h1, h2, h3⟩

/-- **见证装配** ✓：三款齐 ⟹ `GenericExtensionWitness` ✓。 -/
noncomputable def genericExtensionWitness_of_clauses {F : Type u} [Field F]
    {A : Type u} [Group A] [Fintype A] {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra F R] [Algebra R S] [Algebra F S] [IsScalarTower F R S] [MulSemiringAction A S]
    (hRG : ∀ (g : A) (r : R) (t : S), g • (r • t) = r • (g • t))
    (h1 : ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧ Nonempty (R ≃ₐ[F] Localization.Away w))
    (h2 : BTier.IsGaloisWithGroup R S A hRG)
    (h3 : BTier.RealizationProperty F A R S) :
    GenericExtensionWitness F A where
  R := R
  S := S
  hRG := hRG
  isGeneric := isGenericExtension_of_clauses hRG h1 h2 h3

end GenericExtensionInterface322

#print axioms isGenericExtension_iff
#print axioms isGenericExtension_of_clauses
#print axioms genericExtensionWitness_of_clauses


/-! ### 4.111 **忠实形的单射／双射（接口收口）**（第 323 轮）
—— §4.104／§4.105 的**忠实形** ✓（调用方持 `FaithfulSMul` 时**免转形** ✓）

**落成两件** ✓✅：**(i)** **`delta_injective_of_field_of_faithful`** ✓✅（§4.104 ＋ §4.109 ✓）；
**(ii)** **`delta_bijective_of_field_of_faithful`** ✓✅（§4.105 ＋ §4.109 ✓）。

**⚠ 意义** ✓：**§4.106 已用忠实形** ✓，而 §4.104／§4.105 用**单射形** ✓ ⟹ 本件**补齐对称** ✓：
无论调用方手里是 `FaithfulSMul G L` ✓（源侧常见 ✓）还是 `Function.Injective (fun g => actionAlgEquiv hfix g)` ✓，
都**恰有一件**对得上 ✓ ⟹ **组装时少一次转形** ✓（对**源两条陈述的实例化**有用 ✓）。

**🔴 不声称** ✗：**不**声称新数学 ✗（**只**接口收口 ✓）；**不**声称环档判据 ✓；**不**声称残余 ①／③ 已证 ✗；
**不**声称源两条陈述已证 ✗。 -/

section FaithfulForms323

open ABGV52.BTier

set_option maxHeartbeats 4000000 in
/-- **忠实形：域档 `δ` 单射** ✓。 -/
theorem delta_injective_of_field_of_faithful {K : Type u} [CommRing K] {L : Type u} [Field L]
    [Algebra K L] {G : Type u} [Group G] [Fintype G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r)
    (hRG : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hfaith : FaithfulSMul G L) :
    Function.Injective (deltaToEndRingHom (S := L) hRG) :=
  delta_injective_of_field hfix hRG (actionAlgEquiv_injective_of_faithful hfaith hfix)

set_option maxHeartbeats 4000000 in
/-- **忠实形：域档 `δ` 双射** ✓。 -/
theorem delta_bijective_of_field_of_faithful {K : Type u} [Field K] {L : Type u} [Field L]
    [Algebra K L] {G : Type u} [Group G] [Fintype G] [MulSemiringAction G L]
    (hfix : ∀ (g : G) (r : K), g • algebraMap K L r = algebraMap K L r)
    (hRG : ∀ (g : G) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hfaith : FaithfulSMul G L)
    (hcard : Module.finrank K L = Fintype.card G) :
    Function.Bijective (deltaToEndRingHom (S := L) hRG) :=
  delta_bijective_of_field hfix hRG (actionAlgEquiv_injective_of_faithful hfaith hfix) hcard

end FaithfulForms323

#print axioms delta_injective_of_field_of_faithful
#print axioms delta_bijective_of_field_of_faithful


/-! ### 4.112 **子目标 (a) 的范式：`Localization.Away w` 自身**（第 325 轮）
—— 源 def-1-1(a)（`R` 为**局部化多项式环** ✓）的**范式供给件** ✓

**落成** ✓✅：**`away_isLocalizationAway`** ✓✅：对任意**非零** `w : MvPolynomial (Fin n) F` ✓，
**`∃ m v, v ≠ 0 ∧ Nonempty (Localization.Away w ≃ₐ[F] Localization.Away v)`** ✓
（取 `m := n` ✓、`v := w` ✓、等价取 `AlgEquiv.refl` ✓）。

**⚠ 意义** ✓：源 def-1-1(a) 的**形状** ✓ 对**一切** `Localization.Away w` **自动满足** ✓ ⟹
源 `theorem-2-1` 的三子目标中 **(a) 对"多项式环的局部化"这一族载体是免费的** ✓ ——
⟹ **实际难点只剩 (b) 环档判据 ＋ (c) `RealizationProperty`** ✓（**缺口再缩小一格** ✓）。

**⚠ 未竟（精确，供交接）** ✗：**`F[x]` 档**（`R = Polynomial F` ✓）**未收口** ✗ ——
式子写作 `Polynomial F ≃ₐ[F] Localization.Away w` ✓（`w : MvPolynomial (Fin 1) F` ✓）须经
**(i)** `MvPolynomial.uniqueAlgEquiv F (Fin 1) : MvPolynomial (Fin 1) F ≃ₐ[F] Polynomial F` ✓（**已核** ✓）
＋ **(ii)** `Localization.Away (1) ≃ₐ[F] MvPolynomial (Fin 1) F` ✓；**(ii)** 实测受阻 ✗：
`IsLocalization` 的实例是 **`Submonoid.powers (1)`** ✓ 而**非** `Submonoid.closure {1}` ✗
（报 `synthInstanceFailed` ✓）⟹ **下一手**：用 **`Submonoid.powers (1) = ⊤`** ✓（`IsLocalization.self` 或
`⊤`-档实例 ✓）拼 **(i)(ii)** ✓（**预估半轮** ✓）。

**🔴 不声称** ✗：**不**声称 `F[x]` 档已收口 ✗；**不**声称 (b)／(c) 有任何进展 ✗；
**不**声称源 `theorem-2-1` 已证 ✗；**不**声称残余 ①／③ 已证 ✗。 -/

section SubgoalA325

/-- **子目标 (a) 的范式** ✓：`Localization.Away w` 自身满足「为局部化多项式环」✓。 -/
theorem away_isLocalizationAway (F : Type u) [Field F] {n : ℕ} (w : MvPolynomial (Fin n) F)
    (hw : w ≠ 0) :
    ∃ (m : ℕ) (v : MvPolynomial (Fin m) F), v ≠ 0 ∧
      Nonempty (Localization.Away w ≃ₐ[F] Localization.Away v) :=
  ⟨n, w, hw, ⟨AlgEquiv.refl⟩⟩

end SubgoalA325

#print axioms away_isLocalizationAway


/-! ### 4.113 🔴 **子目标 (a) 收官：`F[x]` 档**（第 328 轮）
—— 源 def-1-1(a) 对**源实际用的基环 `R = F[x]`** ✓✅

**落成** ✓✅：**`polynomial_isLocalizationAway`** ✓✅：
**`∃ n w, w ≠ 0 ∧ Nonempty (Polynomial F ≃ₐ[F] Localization.Away w)`** ✓
（取 `n = 1` ✓、`w = 1` ✓ —— 即 **`F[x]` 是 `MvPolynomial (Fin 1) F` 在 `1` 处的局部化** ✓）。

**证明（三件拼接）** ✓：**(i)** `MvPolynomial.uniqueAlgEquiv F (Fin 1) :
MvPolynomial (Fin 1) F ≃ₐ[F] Polynomial F` ✓（**已核** ✓）；
**(ii)** `Localization.Away (1 : MvPolynomial (Fin 1) F) ≃ₐ[·] MvPolynomial (Fin 1) F` ✓ ——
由 **`IsLocalization.algEquiv`** ✓ ＋ 新供给的实例 ✓；
**(iii)** 新实例 ✓：`IsLocalization.Away (1) (MvPolynomial (Fin 1) F)` ✓ ——
由 **`IsLocalization.away_of_isUnit_of_bijective`** ✓（`1` 是单位 ✓ ＋ `algebraMap` 为恒等 ✓ 双射 ✓）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：
**(甲)** 该引理**须加 `Mathlib.RingTheory.Localization.Away.Basic` 导入** ✓ 且**须命名空间限定** ✓
（`IsLocalization.away_of_isUnit_of_bijective` ✓；裸名**未知** ✗，实测 ✓）；
**(乙)** `IsLocalization.algEquiv` 给出的是 **`≃ₐ[MvPolynomial (Fin 1) F]`** ✗（基环是它自己 ✓）
⟹ 须用 **`AlgEquiv.restrictScalars F`** ✓ **降到 `≃ₐ[F]`** ✓（否则报 "type mismatch … ≃ₐ[MvPolynomial (Fin 1) F] / ≃ₐ[F]" ✗）；
**(丙)** `import` **加入文件头** ✓ 后**全库真编须重跑** ✓（本件即按全量收口 ✓）。

**⚠ 意义（子目标 (a) 收官）** ✓✅：**(a)** 此前只对「多项式环的局部化」族**自动成立** ✓（§4.112 ✓）；
**本件补上源实际用的 `R = F[x]`** ✓ ⟹ **源 `theorem-2-1` 的三子目标中 (a) 已全克** ✓✅
—— **余 (b) 环档判据 ✗ ＋ (c) `RealizationProperty`（源 §2）✗** ✓。

**🔴 不声称** ✗：**不**声称 (b)／(c) 有进展 ✗；**不**声称源 `theorem-2-1` 已证 ✗；
**不**声称 `GenericExtensionWitness` 非空 ✗；**不**声称残余 ①／③ 已证 ✗。 -/

section SubgoalAPolynomial328

/-- **子目标 (a) 的 `F[x]` 档** ✓：`Polynomial F` 是局部化多项式环 ✓。 -/
theorem polynomial_isLocalizationAway (F : Type u) [Field F] :
    ∃ (n : ℕ) (w : MvPolynomial (Fin n) F), w ≠ 0 ∧
      Nonempty (Polynomial F ≃ₐ[F] Localization.Away w) := by
  refine ⟨1, 1, one_ne_zero, ?_⟩
  let _inst : IsLocalization.Away (1 : MvPolynomial (Fin 1) F) (MvPolynomial (Fin 1) F) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  refine ⟨(MvPolynomial.uniqueAlgEquiv F (Fin 1)).symm.trans
    (AlgEquiv.restrictScalars F (IsLocalization.algEquiv
      (Submonoid.powers (1 : MvPolynomial (Fin 1) F))
      (Localization.Away (1 : MvPolynomial (Fin 1) F)) (MvPolynomial (Fin 1) F))).symm⟩

end SubgoalAPolynomial328

#print axioms polynomial_isLocalizationAway

/-! ### 4.114 🔴 **`AdjoinRoot` 的基变换**（第 329 轮）
—— 子目标 (c) 的**第一口** ✓：源 `definition-1-1` 的 `S ⊗_φ K` ✓

**源侧路线** ✓（**照源走** ✓）：`raw/Saltman1982.tex:174`（label `theorem-1-2` ✓ 的证明 ✓，**逐字** ✓）：
「If `K ⊇ F` is a field and `L/K` is Galois with group `C_p`, then by `proposition-0-5(e)`
`L ≅ K{y^p − y − a}`, for some `a ∈ K`. We define `φ : R → K` by setting **`φ(x) = a`**
and observe that `φ` realizes `L/K`」 ✓
⟹ **第一步 ＝ 把 `K ⊗_R R{y^p − y − a}` 认成 `K{y^p − y − φ(a)}`** ✓ —— 即本节的**基变换件** ✓。

**落成四件** ✓✅：**(i)** **`adjoinRoot_algHom_ext`** ✓（出 `AdjoinRoot` 的代数同态**由根值决定** ✓ ——
`AdjoinRoot.induction_on` ✓ ＋ `Polynomial.aeval_algHom_apply` ✓）；
**(ii)** **`tensorProduct_adjoinRoot`** ✓✅：`K ⊗_R R[y]/(f) ≃ₐ[K] K[y]/(f.map (algebraMap R K))` ✓；
**(iii)** **`ASpoly_map`** ✓（`(X^p − X − C a).map = X^p − X − C (φ a)` ✓）；
**(iv)** **`asCarrier_tensorProduct`** ✓✅：`K ⊗_R R{y^p−y−a} ≃ₐ[K] K{y^p−y−φ(a)}` ✓
（**源 `S ⊗_φ K` 的逐字形** ✓）＋ 映射形 `asCarrier_tensorProduct_map` ✓。

**机制（四步，全部消费 mathlib 现成件 ✓）** ✓：
**(甲)** 前向 `Φ` ✓：`AdjoinRoot.liftAlgHom` ✓ 给 `g : AdjoinRoot f →ₐ[R] AdjoinRoot (f.map φ)` ✓（`root ↦ root` ✓），
再经 **`AlgHom.liftEquiv`** ✓（**基变换的泛性质** ✓）升为 `K`-代数同态 ✓；
**(乙)** 反向 `Ψ` ✓：`AdjoinRoot.liftAlgHom` ✓（`root ↦ 1 ⊗ root` ✓），义务 ＝ `(f.map φ).eval₂ … = 0` ✓ ——
由 `Polynomial.eval₂_map` ✓ ＋ `IsScalarTower.algebraMap_eq` ✓ ＋ `Polynomial.hom_eval₂` ✓ ＋ `AdjoinRoot.eval₂_root` ✓ 四步收口 ✓；
**(丙)** 两向复合 ＝ 恒等 ✓：一向用 (i) ✓（**根值判定** ✓）；
另一向用 **`Algebra.TensorProduct.adjoin_one_tmul_image_eq_top`** ✓ ＋ **`Algebra.adjoin_induction`** ✓
（`1 ⊗ root` **生成** `K ⊗_R AdjoinRoot f` ✓ —— 与 `AdjoinRoot.adjoinRoot_eq_top` ✓ 合成 ✓）。

**⚠ 口径** ✓：`K` 是 **`R`-代数** ✓（**`φ` 即 `algebraMap R K`** ✓ —— 源文的 `φ : R → K` 正是此形 ✓）。
**⚠ 工艺** ✓（入 §5.1 ✓）：**(甲)** 本件**须 `open scoped TensorProduct`** ✓（`⊗ₜ` 记法 ✓；本文件此前未开 ✗）；
**(乙)** 宿主 `open … MvPolynomial` ✓ 下 ✓ 多项式类名**一律具名限定** ✓（`Polynomial.X`／`Polynomial.C`／`Polynomial.map` ✓）。

**本节不含** ✗：**AS 根在 `L` 中的存在性** ✗（源 `proposition-0-5(e)` ✓ —— 那是**下一手** ✓）；
**次数计数** ✗（`L ≃ₐ[K] …` 的**另一向** ✓）。

**🔴 不声称** ✗：**不**声称子目标 (c) 已克 ✗（**只**落其**第一件** ✓）；
**不**声称 `RealizationProperty` 有实例 ✗；**不**声称 (b) 环档判据有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

open scoped TensorProduct

section BaseChangeAdjoinRoot329

/-- **出 `AdjoinRoot` 的代数同态由根值决定** ✓（`AdjoinRoot.induction_on` ✓
＋ `Polynomial.aeval_algHom_apply` ✓）。 -/
theorem adjoinRoot_algHom_ext {K B : Type u} [CommRing K] [Semiring B] [Algebra K B]
    {p : Polynomial K} {φ ψ : AdjoinRoot p →ₐ[K] B}
    (h : φ (AdjoinRoot.root p) = ψ (AdjoinRoot.root p)) : φ = ψ := by
  refine AlgHom.ext fun x => ?_
  induction x using AdjoinRoot.induction_on with
  | ih P =>
    rw [← AdjoinRoot.aeval_eq (f := p) P, ← Polynomial.aeval_algHom_apply φ,
      ← Polynomial.aeval_algHom_apply ψ, h]

/-- **基变换件** ✓✅：`K ⊗_R R[y]/(f) ≃ₐ[K] K[y]/(f.map (algebraMap R K))` ✓。 -/
noncomputable def tensorProduct_adjoinRoot {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (f : Polynomial R) :
    K ⊗[R] AdjoinRoot f ≃ₐ[K] AdjoinRoot (f.map (algebraMap R K)) := by
  have hroot : f.eval₂ (algebraMap R (AdjoinRoot f)) (AdjoinRoot.root f) = 0 := by
    simp [AdjoinRoot.algebraMap_eq]
  have hroot' : f.eval₂ (algebraMap R (AdjoinRoot (f.map (algebraMap R K))))
      (AdjoinRoot.root (f.map (algebraMap R K))) = 0 := by
    rw [IsScalarTower.algebraMap_eq R K (AdjoinRoot (f.map (algebraMap R K))),
      ← Polynomial.eval₂_map (f := algebraMap R K), AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root _
  have hcomp : algebraMap R (K ⊗[R] AdjoinRoot f) =
      (Algebra.TensorProduct.includeRight (A := K) (R := R)).toRingHom.comp
        (algebraMap R (AdjoinRoot f)) :=
    RingHom.ext fun r =>
      ((Algebra.TensorProduct.includeRight (A := K) (R := R)).commutes r).symm
  -- 前向：`root ↦ root`
  set g : AdjoinRoot f →ₐ[R] AdjoinRoot (f.map (algebraMap R K)) :=
    AdjoinRoot.liftAlgHom (S := R) f
      (Algebra.ofId R (AdjoinRoot (f.map (algebraMap R K))))
      (AdjoinRoot.root (f.map (algebraMap R K))) hroot' with hg
  have hg_root : g (AdjoinRoot.root f) = AdjoinRoot.root (f.map (algebraMap R K)) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  set Φ : K ⊗[R] AdjoinRoot f →ₐ[K] AdjoinRoot (f.map (algebraMap R K)) :=
    AlgHom.liftEquiv R K (AdjoinRoot f) (AdjoinRoot (f.map (algebraMap R K))) g
    with hΦ
  have hΦ_tmul : ∀ (s : K) (a : AdjoinRoot f), Φ (s ⊗ₜ[R] a) = s • g a := by
    intro s a
    simp only [hΦ, AlgHom.liftEquiv_tmul]
  have hΦ_root : Φ ((1 : K) ⊗ₜ[R] AdjoinRoot.root f) =
      AdjoinRoot.root (f.map (algebraMap R K)) := by
    rw [hΦ_tmul, one_smul, hg_root]
  -- 反向：`AdjoinRoot.liftAlgHom`
  have hzero : (f.map (algebraMap R K)).eval₂
      (algebraMap K (K ⊗[R] AdjoinRoot f)) ((1 : K) ⊗ₜ[R] AdjoinRoot.root f) = 0 := by
    rw [Polynomial.eval₂_map (f := algebraMap R K),
      ← IsScalarTower.algebraMap_eq R K (K ⊗[R] AdjoinRoot f), hcomp,
      ← Algebra.TensorProduct.includeRight_apply (A := K) (R := R)
        (b := AdjoinRoot.root f),
      show (Algebra.TensorProduct.includeRight (A := K) (R := R)) (AdjoinRoot.root f)
        = (Algebra.TensorProduct.includeRight (A := K) (R := R)).toRingHom
            (AdjoinRoot.root f) from rfl,
      ← Polynomial.hom_eval₂ (f := algebraMap R (AdjoinRoot f))
        (g := (Algebra.TensorProduct.includeRight (A := K) (R := R)).toRingHom)
        (p := f) (x := AdjoinRoot.root f), hroot, map_zero]
  set Ψ : AdjoinRoot (f.map (algebraMap R K)) →ₐ[K] K ⊗[R] AdjoinRoot f :=
    AdjoinRoot.liftAlgHom (f.map (algebraMap R K))
      (Algebra.ofId K (K ⊗[R] AdjoinRoot f)) ((1 : K) ⊗ₜ[R] AdjoinRoot.root f) hzero
    with hΨ
  have hΨ_root : Ψ (AdjoinRoot.root (f.map (algebraMap R K))) =
      (1 : K) ⊗ₜ[R] AdjoinRoot.root f :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  -- 生成性：`1 ⊗ root` 生成 `K ⊗_R AdjoinRoot f`
  have hgen : Algebra.adjoin K
      ({(1 : K) ⊗ₜ[R] AdjoinRoot.root f} : Set (K ⊗[R] AdjoinRoot f)) = ⊤ := by
    have h := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (R := R) (A := K)
      (B := AdjoinRoot f) ({AdjoinRoot.root f} : Set (AdjoinRoot f))
      AdjoinRoot.adjoinRoot_eq_top
    simpa using h
  refine AlgEquiv.ofAlgHom Φ Ψ ?_ ?_
  · -- `Φ ∘ Ψ = id`
    refine adjoinRoot_algHom_ext ?_
    simp [AlgHom.comp_apply, hΨ_root, hΦ_root]
  · -- `Ψ ∘ Φ = id`
    refine AlgHom.ext fun x => ?_
    have hx : x ∈ Algebra.adjoin K
        ({(1 : K) ⊗ₜ[R] AdjoinRoot.root f} : Set (K ⊗[R] AdjoinRoot f)) := by
      rw [hgen]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simp [AlgHom.comp_apply, hΦ_root, hΨ_root]
    | algebraMap r => simpa using (Ψ.comp Φ).commutes r
    | add y z hy hz ihy ihz => simp [map_add, ihy, ihz]
    | mul y z hy hz ihy ihz => simp [map_mul, ihy, ihz]

/-- **定义多项式的基变换** ✓：`(X^p − X − C a).map = X^p − X − C (φ a)` ✓。 -/
theorem ASpoly_map {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    (p : ℕ) (a : R) :
    (ASpoly R p a).map (algebraMap R K) = ASpoly K p (algebraMap R K a) := by
  simp [ASpoly]

/-- **AS 载体的基变换（映射形）** ✓：`K ⊗_R R{y^p−y−a} ≃ₐ[K] K[y]/((y^p−y−a).map)` ✓。 -/
noncomputable def asCarrier_tensorProduct_map {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (p : ℕ) (a : R) :
    K ⊗[R] asCarrier R p a ≃ₐ[K] AdjoinRoot ((ASpoly R p a).map (algebraMap R K)) :=
  tensorProduct_adjoinRoot (ASpoly R p a)

/-- **AS 载体的基变换** ✓✅：`K ⊗_R R{y^p−y−a} ≃ₐ[K] K{y^p−y−φ(a)}` ✓
（即源 `definition-1-1` 的 **`S ⊗_φ K`** ✓）。 -/
noncomputable def asCarrier_tensorProduct {R K : Type u} [CommRing R] [CommRing K]
    [Algebra R K] (p : ℕ) (a : R) :
    K ⊗[R] asCarrier R p a ≃ₐ[K] asCarrier K p (algebraMap R K a) := by
  show K ⊗[R] AdjoinRoot (ASpoly R p a) ≃ₐ[K] AdjoinRoot (ASpoly K p (algebraMap R K a))
  rw [← ASpoly_map]
  exact tensorProduct_adjoinRoot (ASpoly R p a)

end BaseChangeAdjoinRoot329

#print axioms tensorProduct_adjoinRoot

/-! ### 4.115 🔴 **移位根的生成性 ＋ AS 载体同构**（第 330 轮）
—— 子目标 (c) 的**第二件**（**次数半边** ✓）：源 `proposition-0-5(e)` ✓ 的「**生成**」一半 ✓

**源侧路线** ✓（**照源走** ✓）：`raw/Saltman1982.tex:174`（label `theorem-1-2` ✓ 的证明 ✓，**逐字** ✓）：
「If `K ⊇ F` is a field and `L/K` is Galois with group `C_p`, then by `proposition-0-5(e)`
`L ≅ K{y^p − y − a}`, for some `a ∈ K`」✓ —— 源把「`L` **由 AS 根生成**」整体归给 `proposition-0-5(e)` ✓。
**本件拆其一** ✓：**给定移位根 `y`（`σ y = y + 1` ✓）时的「生成 ＋ 计数」半边** ✓
（**另一件 ＝ AS 根的存在性** ✗，**未落** ✗ —— 那是**下一手** ✓）。

**落成七件** ✓✅：**(i)** **`algebraMap_injective_of_field`** ✓（域到非平凡环的代数映射单射 ✓）；
**(ii)** **`shift_pow_apply`** ✓（`(σ ^ i) y = y + i` ✓）；
**(iii)** **`aeval_shift_eq_zero`** ✓（共轭元仍是根 ✓ —— `Polynomial.aeval_algHom_apply` ✓）；
**(iv)** **`shift_add_ne`** ✓（`i ≠ j`（`i, j < p`）⟹ `y + i ≠ y + j` ✓ ——
`CharP L p` ✓ ＋ `CharP.cast_eq_zero_iff` ✓ ＋ `Nat.le_of_dvd` ✓）；
**(v)** **`natDegree_le_of_aeval_eq_zero_of_shift`** ✓✅：`σ y = y + 1` ⟹ 以 `y` 为根的 `K`-多项式
**要么为零、要么次数 ≥ `p`** ✓；
**(vi)** **`dvd_of_aeval_eq_zero_of_shift`** ✓✅：`f` **首一**、**次数 `p`**、以 `y` 为根 ⟹
**`f` 整除**一切以 `y` 为根的 `K`-多项式 ✓（`modByMonic_add_div` ✓ ＋ (v) ✓）；
**(vii)** **`asCarrier_algEquiv_of_shift_root`** ✓✅：`L` 为域（`IsDomain` ✗ ＋ `K`-有限维 ✗）、
`y ∈ L` 满足 `σ y = y + 1` ✓ 与 **`y^p − y = b`（`b ∈ K`）** ✓、**`finrank K L = p`** ✓
⟹ **`L ≃ₐ[K] K{y^p − y − b}`** ✓✅（即 `asCarrier K p b` ✓）。

**机制（四步，全部消费 mathlib 现成件 ✓）** ✓：
**(甲)** **移位迭代** ✓：`AlgEquiv.commutes` ✓（`σ` 固定 `K` ✓）⟹ `σ (i : L) = (i : L)` ✓；
**(乙)** **`aeval` 换元** ✓：`Polynomial.aeval_algHom_apply` ✓（`aeval (σ^i y) P = σ^i (aeval y P)` ✓）；
**(丙)** **`p` 个互异共轭根** ✓：`Finset.image` ＋ `Finset.card_image_of_injOn` ✓ ⟹
`p ≤ (P.map _).roots.card ≤ P.natDegree` ✓（`card_roots'` ✓ ＋ `natDegree_map_eq_of_injective` ✓）；
**(丁)** **同构** ✓：`AdjoinRoot.liftAlgHom` ✓（根 ↦ `y` ✓）＋ (vi) ⟹ **单射** ✓（`AdjoinRoot.mk_eq_zero` ✓）
＋ `asCarrier_finrank` ✓（§4.91 ✓）＋ **秩相等 ⟹ 双射** ✓（`AlgEquiv.ofBijective` ✓）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：
**(甲)** **「结论不含 `K`」⟹ section 实例被 Lean 剔除** ✗：`shift_add_ne` 的结论只含 `L` ✓ ⟹
`[Field K]`／`[Algebra K L]`／`[CharP K p]` **不进签名** ✗（实测：证明体内报 `unknown identifier K` ✗）
⟹ **正解 ＝ 把 `[CharP L p]` 提到语句里** ✓（**不是**在证明体内引用 `K` ✗）；
**(乙)** **`Function.Injective` 的 `intro` 形状** ✗：它是 `∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂` ✓
（**不是** `∀ a, f a = 0 → a = 0` ✗）⟹ `intro x hx` **错** ✗ ⟹ **先证核平凡** ✓ 再 `sub_eq_zero` ✓；
**(丙)** **实例注册用 `let _inst`** ✓、**`haveI` 计样式警告** ✗（§5.1 #14 ✓ 的**第三次命中** ✓）。

**🔴 不声称** ✗：**不**声称子目标 (c) 已克 ✗（**只**落「给定移位根」的半边 ✓）；
**不**声称 **AS 根的存在性** ✗（源 `proposition-0-5(e)` 的**另一半** ✗ —— **下一手** ✓）；
**不**声称环档判据（(b)）有进展 ✗；**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

/-- 域到非平凡环的代数映射单射 ✓。 -/
theorem algebraMap_injective_of_field {K L : Type u} [Field K] [CommRing L] [Nontrivial L]
    [Algebra K L] : Function.Injective (algebraMap K L) := by
  intro a b hab
  have h : algebraMap K L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h2 : a - b = 0 := by
    by_contra hne
    have hunit : IsUnit (algebraMap K L (a - b)) := (IsUnit.mk0 _ hne).map (algebraMap K L)
    rw [h] at hunit
    exact not_isUnit_zero hunit
  exact sub_eq_zero.mp h2

section ASShiftRoot330

variable {K L : Type u} [Field K] [CommRing L] [Algebra K L]
variable {p : ℕ} [CharP K p] {σ : L ≃ₐ[K] L} {y : L}

omit [CharP K p] in
/-- **移位迭代** ✓：`(σ ^ i) y = y + i` ✓。 -/
theorem shift_pow_apply (hy : σ y = y + 1) (i : ℕ) : (σ ^ i) y = y + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hfix : σ ((i : L)) = (i : L) := by
      rw [show (i : L) = algebraMap K L (i : K) from (map_natCast (algebraMap K L) i).symm,
        AlgEquiv.commutes]
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, hy, hfix]
    push_cast
    ring

omit [CharP K p] in
/-- **共轭元仍是根** ✓。 -/
theorem aeval_shift_eq_zero {P : Polynomial K} (i : ℕ)
    (hP : Polynomial.aeval y P = 0) : Polynomial.aeval ((σ ^ i) y) P = 0 := by
  rw [Polynomial.aeval_algHom_apply, hP, map_zero]

/-- **共轭元的互异性** ✓：`i ≠ j`（`i, j < p`）⟹ `y + i ≠ y + j` ✓。 -/
theorem shift_add_ne [Nontrivial L] [CharP L p] (i j : ℕ) (hi : i < p) (hj : j < p)
    (hij : i ≠ j) : y + (i : L) ≠ y + (j : L) := by
  intro h
  have h1 : ((i : L)) = ((j : L)) := add_left_cancel h
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hsub : ((j - i : ℕ) : L) = 0 := by
      rw [Nat.cast_sub hlt.le, h1, sub_self]
    have hdvd : p ∣ (j - i) := (CharP.cast_eq_zero_iff L p (j - i)).mp hsub
    have hpos : 0 < j - i := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  · exact hij heq
  · have hsub : ((i - j : ℕ) : L) = 0 := by
      rw [Nat.cast_sub hgt.le, h1, sub_self]
    have hdvd : p ∣ (i - j) := (CharP.cast_eq_zero_iff L p (i - j)).mp hsub
    have hpos : 0 < i - j := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega

/-- **移位根的生成性** ✓✅：`σ y = y + 1` ⟹ 以 `y` 为根的 `K`-多项式要么为零、要么次数 ≥ `p` ✓。 -/
theorem natDegree_le_of_aeval_eq_zero_of_shift [IsDomain L]
    (hy : σ y = y + 1) {P : Polynomial K}
    (hP : Polynomial.aeval y P = 0) : P = 0 ∨ p ≤ P.natDegree := by
  classical
  rcases eq_or_ne P 0 with rfl | hP0
  · exact Or.inl rfl
  · right
    have hIa : Function.Injective (algebraMap K L) := algebraMap_injective_of_field
    let _inst : CharP L p := charP_of_injective_algebraMap hIa p
    have hmap0 : P.map (algebraMap K L) ≠ 0 := fun h =>
      hP0 ((Polynomial.map_eq_zero_iff hIa).mp h)
    have hroot : ∀ i ∈ Finset.range p, (P.map (algebraMap K L)).IsRoot (y + (i : L)) := by
      intro i _
      rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
        ← shift_pow_apply (σ := σ) hy i]
      exact aeval_shift_eq_zero (σ := σ) i hP
    have hinj : Set.InjOn (fun i : ℕ => y + (i : L)) ↑(Finset.range p) := by
      intro i hi j hj hij
      by_contra hne
      exact shift_add_ne (y := y) i j (Finset.mem_range.mp hi)
        (Finset.mem_range.mp hj) hne hij
    have hcard : p ≤ Multiset.card (P.map (algebraMap K L)).roots := by
      have h1 : Finset.card (Finset.image (fun i : ℕ => y + (i : L)) (Finset.range p)) = p := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      have h2 : (Finset.image (fun i : ℕ => y + (i : L)) (Finset.range p)) ⊆
          (P.map (algebraMap K L)).roots.toFinset := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hmap0]
        exact hroot i hi
      calc p = Finset.card (Finset.image (fun i : ℕ => y + (i : L)) (Finset.range p)) := h1.symm
        _ ≤ Finset.card ((P.map (algebraMap K L)).roots.toFinset) := Finset.card_le_card h2
        _ ≤ Multiset.card (P.map (algebraMap K L)).roots := Multiset.toFinset_card_le _
    calc p ≤ Multiset.card (P.map (algebraMap K L)).roots := hcard
      _ ≤ (P.map (algebraMap K L)).natDegree := Polynomial.card_roots' _
      _ = P.natDegree := Polynomial.natDegree_map_eq_of_injective hIa P

/-- **移位根的整除性** ✓✅：`f` 首一、次数 `p`、以 `y` 为根 ⟹ `f` 整除一切以 `y` 为根的 `K`-多项式 ✓。 -/
theorem dvd_of_aeval_eq_zero_of_shift [IsDomain L] {f P : Polynomial K} (hf : f.Monic)
    (hfd : f.natDegree = p) (hp0 : p ≠ 0) (hy : σ y = y + 1)
    (hf0 : Polynomial.aeval y f = 0) (hP : Polynomial.aeval y P = 0) : f ∣ P := by
  classical
  have hr : Polynomial.aeval y (P %ₘ f) = 0 := by
    have h := congrArg (Polynomial.aeval y) (Polynomial.modByMonic_add_div P f)
    simp only [map_add, map_mul, hf0, zero_mul, add_zero] at h
    rw [h, hP]
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [Polynomial.natDegree_one] at hfd
    exact hp0 hfd.symm
  rcases natDegree_le_of_aeval_eq_zero_of_shift (p := p) (σ := σ) hy hr with h | h
  · exact (Polynomial.modByMonic_eq_zero_iff_dvd hf).mp h
  · exfalso
    have hlt := Polynomial.natDegree_modByMonic_lt P hf hf1
    omega

/-- **移位根 ⟹ AS 载体同构** ✓✅：`L` 为域（`IsDomain` ＋ `K`-有限维）、`y ∈ L` 满足
`σ y = y + 1` 与 `y^p − y = b`（`b ∈ K`）、`finrank K L = p` ⟹ `L ≃ₐ[K] K{y^p − y − b}` ✓。 -/
theorem asCarrier_algEquiv_of_shift_root [IsDomain L] [Module.Finite K L]
    (hp : p.Prime) {b : K} {y : L} (hy : σ y = y + 1)
    (hb : algebraMap K L b = y ^ p - y) (hcard : Module.finrank K L = p) :
    Nonempty (L ≃ₐ[K] asCarrier K p b) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hroot : Polynomial.aeval y (ASpoly K p b) = 0 := by
    rw [ASpoly, map_sub, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hb]
    ring
  have hroot' : (ASpoly K p b).eval₂ (↑(Algebra.ofId K L)) y = 0 := by
    rw [Algebra.toRingHom_ofId, ← Polynomial.aeval_def]
    exact hroot
  set Φ : asCarrier K p b →ₐ[K] L :=
    AdjoinRoot.liftAlgHom (ASpoly K p b) (Algebra.ofId K L) y hroot' with hΦ
  have hval : ∀ P : Polynomial K,
      Φ (AdjoinRoot.mk (ASpoly K p b) P) = Polynomial.aeval y P := by
    intro P
    rw [hΦ, AdjoinRoot.liftAlgHom_mk, Polynomial.aeval_def, Algebra.toRingHom_ofId]
  have hker : ∀ x : asCarrier K p b, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective x
    rw [← hP] at hx ⊢
    have h0 : Polynomial.aeval y P = 0 := by rw [← hval P, hx]
    have hdvd := dvd_of_aeval_eq_zero_of_shift (σ := σ) (aspoly_monic (R := K) hp2 b)
      (aspoly_natDegree (R := K) hp2 b) hp.ne_zero hy hroot h0
    exact AdjoinRoot.mk_eq_zero.mpr hdvd
  have hinj : Function.Injective Φ := by
    intro x z hxz
    have h1 : Φ (x - z) = 0 := by rw [map_sub, hxz, sub_self]
    exact sub_eq_zero.mp (hker (x - z) h1)
  have hfin : Module.finrank K (asCarrier K p b) = p := asCarrier_finrank hp2 b
  let _inst : Module.Finite K (asCarrier K p b) :=
    Module.finite_of_finrank_pos (by rw [hfin]; omega)
  have hbij : Function.Bijective Φ := by
    refine ⟨hinj, ?_⟩
    have hinjL : Function.Injective (Φ.toLinearMap : asCarrier K p b →ₗ[K] L) := hinj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := asCarrier K p b) (V₂ := L) (f := Φ.toLinearMap) (by rw [hfin, hcard])).mp hinjL
  exact ⟨(AlgEquiv.ofBijective Φ hbij).symm⟩

end ASShiftRoot330

#print axioms asCarrier_algEquiv_of_shift_root

/-! ### 4.116 🔴 **素数次扩域上非平凡自同构的不动点 ＝ 基域**（第 331 轮）
—— 子目标 (c) 的**第三件之一** ✓：**`L^σ = K`** ✓

**用途** ✓：§4.115 ✓ 的 `asCarrier_algEquiv_of_shift_root` 需要 **`y^p − y = b ∈ K`** ✓ ——
而 `σ (y^p − y) = y^p − y` ✓（**char p** ✓ ＋ `σ y = y + 1` ✓）⟹ **`y^p − y ∈ L^σ`** ✓
⟹ 本件给出 **`L^σ = K`** ✓（**须 `[L : K]` 为素数** ✓）。
**同理** ✓：第三件（`∃ y, σ y = y + 1` ✓）的**秩论证**需要 **`ker (σ − 1) = K`** ✓ ——
本件正是其**点值形** ✓（`σ` 忠实 ✓ ＋ `[L : K] = p` ✓）。

**落成一件** ✓✅：**`fixed_of_finrank_prime`** ✓✅：`[L : K] = p` 为**素数** ✓、`σ ≠ 1` 为 `K`-代数自同构 ✓
⟹ **`σ z = z ⟹ z ∈ K`** ✓（`∃ c : K, algebraMap K L c = z` ✓）。

**机制（中间域论证，三步，全部消费 mathlib 现成件 ✓）** ✓：
**(甲)** 取 **`F := K⟮z⟯`** ✓（`IntermediateField.adjoin` ✓）；
**(乙)** **`[F : K] ∣ [L : K] = p`** ✓（`IntermediateField.finrank_dvd_of_le_right` ✓ ＋ `finrank_top'` ✓）
⟹ **`[F : K] ∈ {1, p}`** ✓（`p` 素 ✓ ＋ `Nat.Prime.eq_one_or_self_of_dvd` ✓）；
**(丙)** **两分** ✓：**若 `[F : K] = p`** ⟹ `F = ⊤` ✓（`eq_of_le_of_finrank_eq` ✓）
⟹ `σ` **固定 `K⟮z⟯`** ✓（`IntermediateField.adjoin_induction` ✓ ＋ `AlgEquiv.commutes` ✓）
⟹ `σ = 1` ✗（**与 `hσ1` 矛盾** ✓）；**故 `[F : K] = 1`** ⟹ `F = ⊥` ✓（`finrank_bot` ✓）
⟹ **`z ∈ K`** ✓（`IntermediateField.mem_bot` ✓）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：
**(甲)** **`IsField L` ≠ `Field L`** ✗：`IntermediateField` **要 `Field L` 实例** ✓ ⟹ 须
**`IsField.toField (IsField.of_isDomain_of_finite K L)`** ✓ 并**注册为 `let _inst : Field L`** ✓
（**只给 `IsField L` 不够** ✗ —— 实测 `failed to synthesize Field L` ✗）；
**(乙)** **`finrank_top` 与 `finrank_top'` 同名不同义** ✗：前者是 **`finrank ↥⊤ L = 1`** ✓
（**顶域上的次数** ✓），后者（`@[simp]` ✓）才是 **`finrank K ↥⊤ = finrank K L`** ✓ —— **实测踩中** ✗；
**(丙)** **`subset_adjoin` 的实参形状** ✗：它是 `s ⊆ ↑(adjoin K s)` ✓ ⟹ 须
**`subset_adjoin K ({z} : Set L) (Set.mem_singleton z)`** ✓（**不是** `subset_adjoin K (Set.mem_singleton z)` ✗）。

**🔴 不声称** ✗：**不**声称子目标 (c) 已克 ✗（**只**落**第三件的「不动点」半边** ✓）；
**不**声称 **`∃ y, σ y = y + 1`** ✗（**未落** ✗ —— **下一手** ✓）；**不**声称环档判据（(b)）有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section FixedOfFinrankPrime331

/-- **素数次扩域上非平凡 `K`-自同构的不动点全部落在 `K` 内** ✓✅。 -/
theorem fixed_of_finrank_prime {K L : Type u} [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] [Module.Finite K L] {p : ℕ} (hp : p.Prime)
    (hcard : Module.finrank K L = p) {σ : L ≃ₐ[K] L} (hσ1 : σ ≠ 1)
    {z : L} (hz : σ z = z) : ∃ c : K, algebraMap K L c = z := by
  let _inst : Field L := IsField.toField (IsField.of_isDomain_of_finite K L)
  set F : IntermediateField K L := IntermediateField.adjoin K ({z} : Set L) with hF
  have hfix : ∀ x ∈ F, σ x = x := by
    intro x hx
    rw [hF] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hz
    | algebraMap c => exact σ.commutes c
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
    | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]
    | inv x hx ih => simp [ih]
  have hdvd : Module.finrank K F ∣ p := by
    have h := IntermediateField.finrank_dvd_of_le_right (K := K) (F := F) (E := ⊤) le_top
    rwa [IntermediateField.finrank_top', hcard] at h
  have hzF : z ∈ F := by
    rw [hF]
    exact IntermediateField.subset_adjoin K ({z} : Set L) (Set.mem_singleton z)
  rcases hp.eq_one_or_self_of_dvd (Module.finrank K F) hdvd with h1 | hp'
  · have hbot : F = ⊥ := by
      refine (IntermediateField.eq_of_le_of_finrank_eq (K := K) (F := ⊥) (E := F) bot_le ?_).symm
      rw [h1, IntermediateField.finrank_bot]
    rw [hbot] at hzF
    exact IntermediateField.mem_bot.mp hzF
  · exfalso
    apply hσ1
    have htop : F = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq (K := K) (F := F) (E := ⊤) le_top (by
        rw [hp', IntermediateField.finrank_top', hcard])
    ext x
    exact hfix x (by rw [htop]; trivial)

end FixedOfFinrankPrime331

#print axioms fixed_of_finrank_prime

/-! ### 4.117 🔴🔴 **移位根的存在性（幂零 ＋ 秩-零化，不用迹）**（第 332 轮）
—— 子目标 (c) 的**第三件之②** ✓ ⟹ **(c) 第三件由此收官** ✓✅

**靶** ✓：**`∃ y, σ y = y + 1`** ✓ —— 与 §4.116 ✓（`L^σ = K` ✓）＋ §4.115 ✓
（`asCarrier_algEquiv_of_shift_root` ✓）合成 ⟹ **`RealizationProperty` 的 `C_p` 档** ✓
（**库内零实例 → 首例** ✓）。

**落成一件** ✓✅：**`exists_shift_root`** ✓✅：`char K = p` ✓、`[L : K] = p` 素数 ✓、`σ ^ p = 1` ✓、`σ ≠ 1` ✓
⟹ **`∃ y : L, σ y = y + 1`** ✓✅。

**🔴 机制（初等；不用迹、不用正规基、不走加法 Hilbert 90 的经典路线）** ✓：
**(甲)** `N := σ − 1` ✓（`Module.End K L` ✓）；**char p** ✓ ⟹ **`N ^ p = σ ^ p − 1 = 0`** ✓
（`sub_pow_char_of_commute` ✓ ＋ `AlgEquiv.pow_toLinearMap` ✓；`CharP (End K L) p` ✓ 由
`charP_of_injective_algebraMap` ✓ ＋ **`algebraMap K (End K L)` 单射** ✓（`Module.algebraMap_end_apply` ✓
＋ §4.115 的 `algebraMap_injective_of_field` ✓））；
**(乙)** **`ker N = K ∙ 1`** ✓ —— 由 §4.116 ✓（**其点值形** ✓）＋ `N 1 = 0` ✓；
**(丙)** **反设 `1 ∉ range N`** ✓ ⟹ `ker N ⊓ range N = ⊥` ✓ ⟹ `finrank (range N) = p − 1` ✓
（**秩-零化** ✓）⟹ `finrank (ker N ⊔ range N) = p` ✓（`finrank_sup_add_finrank_inf_eq` ✓）
⟹ **`ker N ⊔ range N = ⊤`** ✓；
**(丁)** **`range N = range (N ∘ N)`** ✓：`range N = map N ⊤ = map N (ker ⊔ range) = ⊥ ⊔ range (N∘N)` ✓
（`range_eq_map` ✓／`map_sup` ✓／`map N ker = ⊥` ✓／`range_comp` ✓）；
**(戊)** **迭代稳定** ✓（`Module.End.iterate_succ'` ✓）＋ **`range (N^p) = ⊥`** ✓ ⟹ `range N = ⊥` ✓
⟹ `N = 0` ✓（`range_eq_bot` ✓）⟹ `σ = 1` ✗ **矛盾** ✓ ⟹ **`1 ∈ range N`** ✓ ⟹ **`∃ y, Ny = 1`** ✓✅。

**⚠ 意义** ✓：**`Tr ≠ 0` 的经典路线不作首选** ✗（那一步**要正规基定理** ✓，代价高 ✗）——
本件只用**幂零 ＋ 秩-零化 ＋ 直和** ✓ ⟹ **省一整条路线** ✓。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：
**(甲)** `sub_pow_char_of_commute` ✓ **要 `[Fact p.Prime]`** ✗ ⟹ **由 `hp : p.Prime` 现场注册
`let _inst : Fact p.Prime := ⟨hp⟩`** ✓；
**(乙)** **`Module.End.mul_eq_comp`／`Module.End.iterate_succ'` 在 `Module.End` 命名空间** ✓
（**`LinearMap.mul_eq_comp` 不存在** ✗）；
**(丙)** **`Submodule` 的 `map_ker` 不存在** ✗ ⟹ **`Submodule.eq_bot_iff` ＋ `rintro y ⟨x, hx, rfl⟩`** ✓（实测 ✓）。

**🔴 不声称** ✗：**不**声称 `RealizationProperty` 已有实例 ✗（**装配未落** ✗ —— **下一手** ✓）；
**不**声称环档 `L` 的分量形已处理 ✗；**不**声称 (b) 环档判据有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

open Module

section ShiftRootExistence332

/-- **移位根存在** ✓：`char K = p`、`[L : K] = p` 素数、`σ^p = 1`、`σ ≠ 1` ⟹
`∃ y, σ y = y + 1` ✓（**幂零 `N = σ − 1` ＋ 秩-零化**，**不用迹**）。 -/
theorem exists_shift_root {K L : Type u} [Field K] [CommRing L] [IsDomain L] [Algebra K L]
    [Module.Finite K L] {p : ℕ} (hp : p.Prime) [CharP K p]
    (hcard : Module.finrank K L = p) {σ : L ≃ₐ[K] L} (hσ : σ ^ p = 1) (hσ1 : σ ≠ 1) :
    ∃ y : L, σ y = y + 1 := by
  classical
  let _inst : Fact p.Prime := ⟨hp⟩
  -- `End K L` 的 char p
  have hEnd : Function.Injective (algebraMap K (Module.End K L)) := by
    intro c d hcd
    have h := congrArg (fun f : Module.End K L => f 1) hcd
    simp only [Module.algebraMap_end_apply, Algebra.smul_def, mul_one] at h
    exact algebraMap_injective_of_field h
  let _inst : CharP (Module.End K L) p := charP_of_injective_algebraMap hEnd p
  set N : Module.End K L := σ.toLinearMap - 1 with hN
  have hNp : N ^ p = 0 := by
    have hcomm : Commute σ.toLinearMap (1 : Module.End K L) := Commute.one_right _
    have h1 : (σ.toLinearMap - 1 : Module.End K L) ^ p
        = σ.toLinearMap ^ p - 1 := by
      simpa using sub_pow_char_of_commute (R := Module.End K L) (p := p)
        (x := σ.toLinearMap) (y := 1) hcomm
    rw [hN, h1, ← AlgEquiv.pow_toLinearMap σ p, hσ]
    simp
  -- `N` 的核
  have hNapply : ∀ x : L, N x = σ x - x := by
    intro x
    simp [hN]
  have hker : ∀ x : L, N x = 0 → x ∈ (K ∙ (1 : L)) := by
    intro x hx
    have hσx : σ x = x := by
      have h : σ x - x = 0 := by rw [← hNapply]; exact hx
      exact sub_eq_zero.mp h
    obtain ⟨c, hc⟩ := fixed_of_finrank_prime hp hcard hσ1 hσx
    exact Submodule.mem_span_singleton.mpr ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  have hker_eq : N.ker = K ∙ (1 : L) := by
    refine le_antisymm (fun x hx => hker x hx) ?_
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [LinearMap.mem_ker, hNapply, map_smul, map_one, sub_self]
  -- 反设 `1 ∉ range N`
  by_contra hcon
  have h1notin : (1 : L) ∉ N.range := by
    rintro ⟨y, hy⟩
    refine hcon ⟨y, ?_⟩
    have h : σ y - y = 1 := by rw [← hNapply]; exact hy
    have h2 : σ y = 1 + y := sub_eq_iff_eq_add.mp h
    exact h2.trans (add_comm y 1).symm
  have hfin_ker : Module.finrank K (N.ker) = 1 := by
    rw [hker_eq]
    exact finrank_span_singleton (K := K) (v := (1 : L)) one_ne_zero
  have hfin_range : Module.finrank K (N.range) = p - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (K := K) N
    rw [hcard, hfin_ker] at h
    omega
  have hinf : N.ker ⊓ N.range = ⊥ := by
    rw [hker_eq]
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    by_contra hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hc (by simp)
    refine h1notin ?_
    have : (1 : L) = c⁻¹ • (c • (1 : L)) := by
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hx2
  have htop : N.ker ⊔ N.range = ⊤ := by
    have hp1 : 1 ≤ p := le_trans (by norm_num) hp.two_le
    have h := Submodule.finrank_sup_add_finrank_inf_eq (K := K) N.ker N.range
    rw [hinf, hfin_ker, hfin_range, finrank_bot, add_zero] at h
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [h, add_comm, hcard, Nat.sub_add_cancel hp1]
  -- 稳定化：`range N = range (N ∘ N)`
  have hstab : N.range = (N.comp N).range := by
    conv_lhs => rw [LinearMap.range_eq_map N]
    rw [← htop, Submodule.map_sup]
    have hmapker : Submodule.map N N.ker = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro y ⟨x, hx, rfl⟩
      simpa using hx
    rw [hmapker, bot_sup_eq]
    exact (LinearMap.range_comp N N).symm
  have hind : ∀ k : ℕ, 1 ≤ k → (N ^ k).range = N.range := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp
      · rw [Module.End.iterate_succ', LinearMap.range_comp, ih hkpos,
          ← LinearMap.range_comp N N]
        exact hstab.symm
  have hbot : N.range = ⊥ := by
    have h := hind p hp.pos
    rw [hNp, LinearMap.range_zero] at h
    exact h.symm
  have hN0 : N = 0 := LinearMap.range_eq_bot.mp hbot
  refine hσ1 ?_
  have hlin : σ.toLinearMap = 1 := by
    have h : σ.toLinearMap - 1 = 0 := hN0
    exact sub_eq_zero.mp h
  ext x
  have := congrArg (fun f : L →ₗ[K] L => f x) hlin
  simpa using this


end ShiftRootExistence332

#print axioms exists_shift_root

/-! ### 4.118 🔴🔴 **AS 结构定理（域档）**（第 333 轮）
—— 子目标 (c) 的**装配之一** ✓：源 `proposition-0-5(e)` ✓ 的**域档结论** ✓✅

**源侧定位** ✓（**逐字** ✓）：`raw/Saltman1982.tex:174`（label `theorem-1-2` ✓ 的证明 ✓）：
「If `K ⊇ F` is a field and `L/K` is Galois with group `C_p`, then **by `proposition-0-5(e)`
`L ≅ K{y^p − y − a}`, for some `a ∈ K`**」✓ —— 本件**即该结论的域档机检形** ✓✅。

**落成一件** ✓✅：**`exists_algEquiv_asCarrier`** ✓✅：`char K = p` ✓、`[L : K] = p` **素数** ✓、
`σ ^ p = 1` ✓、`σ ≠ 1` ✓ ⟹ **`∃ b : K, Nonempty (L ≃ₐ[K] asCarrier K p b)`** ✓✅。

**机制（三件拼装，全部为本工程已落件 ✓）** ✓：
**(甲)** **§4.117** ✓ 给移位根 `y`（`σ y = y + 1` ✓）；
**(乙)** **`σ (y^p − y) = y^p − y`** ✓（`add_pow_char` ✓ ＋ **`CharP L p`** ✓（`charP_of_injective_algebraMap` ✓
＋ §4.115 的 `algebraMap_injective_of_field` ✓））⟹ **§4.116** ✓ 给 **`b : K`**（`algebraMap K L b = y^p − y` ✓）；
**(丙)** **§4.115** ✓ 给 **`L ≃ₐ[K] asCarrier K p b`** ✓✅。

**⚠ 意义** ✓：**源 `proposition-0-5(e)` 的域档半边全克** ✓✅ ——
**(c) 的「装配」只剩两小步** ✗：**(i)** 把 `σ` 从 **`G`-作用**（`actionAlgEquiv` ✓ §4.98 ✓）**造出来** ✓
＋ **`finrank K L = p`** ✓（`finrank_eq_card_of_isGaloisWithGroup` ✓）；**(ii)** **分裂档**（`L ≅ K^p` ✗）。

**⚠ 工艺** ✓（入 §5.1 ✓）：**`add_pow_char` 要 `[Fact p.Prime]`** ✗ ⟹ 由 `hp : p.Prime` **现场注册
`let _inst : Fact p.Prime := ⟨hp⟩`** ✓（**§5.1 #27 的第二次命中** ✓）。

**🔴 不声称** ✗：**不**声称 `RealizationProperty` 已有实例 ✗（**装配未落** ✗）；
**不**声称**分裂档**已处理 ✗；**不**声称环档 `L` 的一般形已处理 ✗；**不**声称 (b) 环档判据有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section ASStructureTheorem333

/-- **AS 结构定理（域档）** ✓✅：素数次 `C_p`-Galois 域扩张都是 Artin–Schreier 扩张 ✓
（即源 `proposition-0-5(e)` 的域档结论 ✓）。 -/
theorem exists_algEquiv_asCarrier {K L : Type u} [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] [Module.Finite K L] {p : ℕ} (hp : p.Prime) [CharP K p]
    (hcard : Module.finrank K L = p) {σ : L ≃ₐ[K] L} (hσ : σ ^ p = 1) (hσ1 : σ ≠ 1) :
    ∃ b : K, Nonempty (L ≃ₐ[K] asCarrier K p b) := by
  classical
  let _inst : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_shift_root hp hcard hσ hσ1
  have hIa : Function.Injective (algebraMap K L) := algebraMap_injective_of_field
  let _inst : CharP L p := charP_of_injective_algebraMap hIa p
  have hfix : σ (y ^ p - y) = y ^ p - y := by
    rw [map_sub, map_pow, hy, add_pow_char, one_pow]
    ring
  obtain ⟨b, hb⟩ := fixed_of_finrank_prime hp hcard hσ1 hfix
  exact ⟨b, asCarrier_algEquiv_of_shift_root (σ := σ) hp hy hb hcard⟩

end ASStructureTheorem333

#print axioms exists_algEquiv_asCarrier

/-! ### 4.119 🔴 **装配之二的承重前置：`σ` 与次数由 `G`-作用提取**（第 334 轮）
—— 子目标 (c) 的**装配之二（域档装配）的输入** ✓

**靶** ✓：§4.115–§4.118 的**全部前提**都要**显式数据** ✓（`σ : L ≃ₐ[K] L` ✓、`σ ^ p = 1` ✓、`σ ≠ 1` ✓、
`finrank K L = p` ✓）—— 而 `RealizationProperty` 的假设里**只有 `G`-作用** ✓ ⟹ **本件把数据从作用提取出来** ✓。

**落成两件** ✓✅：
**(i)** **`exists_shift_automorphism`** ✓✅：`IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL` ✓
（`p` 素 ✓、`[NeZero p]` ✓）⟹ **`∃ σ : L ≃ₐ[K] L, σ ^ p = 1 ∧ σ ≠ 1`** ✓✅；
**(ii)** **`finrank_eq_prime_of_isGaloisWithGroup`** ✓✅：同假设 ＋ `[Module.Finite K L]` ✓ ＋ `[Nontrivial L]` ✓
⟹ **`Module.finrank K L = p`** ✓✅。

**机制** ✓：**(i)** `g₀ := Multiplicative.ofAdd (1 : ZMod p)` ✓（**生成元** ✓）⟹
`σ := actionAlgEquiv hfix g₀` ✓（§4.98 ✓）⟹ `σ ^ p = 1` ✓（`ofAdd_nsmul` ✓ ＋ **`ZMod.natCast_self`** ✓
＋ `ofAdd_zero` ✓ ＋ **同态律** `actionAlgEquiv (a * b) = actionAlgEquiv a * actionAlgEquiv b` ✓
（`ext x; simp [actionAlgEquiv, mul_smul]` ✓））；**`σ ≠ 1`** ✓ 由 **忠实性** ✓
（`faithfulSMul_iff` ✓ ＋ `g₀ ≠ 1` ✓ —— 后者的证法：`ofAdd.injective` ✓ ＋ **`p ∤ 1`** ✓
（`CharP.cast_eq_zero_iff` ✓ ＋ `hp.not_dvd_one` ✓））；
**(ii)** `finrank_eq_card_of_isGaloisWithGroup` ✓（§286 件 ✓）＋ `Fintype.card (Multiplicative (ZMod p)) = Fintype.card (ZMod p)` ✓
（`Fintype.card_congr (Multiplicative.ofAdd)` ✓）＋ **`ZMod.card`** ✓。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：
**(甲)** **宇宙约束（§5.1 #12 的新命中）** ✗：`finrank_eq_card_of_isGaloisWithGroup` ✓（本工程 §286 件 ✓）
**要求 `R`／`S`／`G` 同宇宙** ✗ ⟹ 而 `G = Multiplicative (ZMod p) : Type` ✓ ⟹ **(ii) 须在 `Type`（宇宙 0）陈述** ✓
（**(i) 无此约束** ✓ —— `actionAlgEquiv` ✓ 与 `faithfulSMul_iff` ✓ 皆多宇宙 ✓）；
**(乙)** **`ofAdd_nsmul`／`ofAdd_zero` 在根命名空间** ✗（**`Multiplicative.ofAdd_nsmul` 不存在** ✗ ——
实测 ✓）；`Multiplicative.ofAdd.injective` ✓ 走 `Equiv.injective` ✓；
**(丙)** **`one_ne_zero` 在此处不可用** ✗（实测 `synthInstanceFailed : NeZero 1` ✗）⟹
**正解 ＝ `CharP.cast_eq_zero_iff` ✓ ＋ `Nat.Prime.not_dvd_one` ✓** 证 `(1 : ZMod p) ≠ 0` ✓。

**🔴 不声称** ✗：**不**声称装配已完成 ✗（**只**落其**输入提取** ✓ —— `φ` 与张量半边**未落** ✗）；
**不**声称分裂档已处理 ✗；**不**声称 (b) 环档判据有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

open ABGV52.BTier

section CpDataExtraction334

/-- **移位自同构的提取** ✓：`C_p`-Galois 作用给出非平凡的 `p` 阶 `K`-代数自同构 ✓。 -/
theorem exists_shift_automorphism {K L : Type u} [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] {p : ℕ} (hp : p.Prime) [NeZero p]
    [MulSemiringAction (Multiplicative (ZMod p)) L]
    (hKL : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hgal : IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL) :
    ∃ σ : L ≃ₐ[K] L, σ ^ p = 1 ∧ σ ≠ 1 := by
  classical
  have hfix : ∀ (g : Multiplicative (ZMod p)) (r : K),
      g • algebraMap K L r = algebraMap K L r := hgal.2.1
  set g₀ : Multiplicative (ZMod p) := Multiplicative.ofAdd (1 : ZMod p) with hg₀
  have hhom : ∀ a b : Multiplicative (ZMod p),
      actionAlgEquiv (S := L) hfix (a * b) =
        actionAlgEquiv (S := L) hfix a * actionAlgEquiv (S := L) hfix b := by
    intro a b
    ext x
    simp [actionAlgEquiv, mul_smul]
  have hone : actionAlgEquiv (S := L) hfix 1 = 1 := by
    ext x
    simp [actionAlgEquiv]
  have hg₀p : g₀ ^ p = 1 := by
    rw [hg₀, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self,
      zero_mul, ofAdd_zero]
  have hg₀1 : g₀ ≠ 1 := by
    rw [hg₀]
    intro h
    have h1 : (1 : ZMod p) = 0 := Multiplicative.ofAdd.injective h
    have h2 : ¬ ((1 : ZMod p) = 0) := by
      intro hz
      exact hp.not_dvd_one ((CharP.cast_eq_zero_iff (ZMod p) p 1).mp (by simpa using hz))
    exact h2 h1
  refine ⟨actionAlgEquiv (S := L) hfix g₀, ?_, ?_⟩
  · -- σ ^ p = 1
    have : ∀ n : ℕ, (actionAlgEquiv (S := L) hfix g₀) ^ n
        = actionAlgEquiv (S := L) hfix (g₀ ^ n) := by
      intro n
      induction n with
      | zero => simp [hone]
      | succ n ih => rw [pow_succ, ih, pow_succ, hhom]
    rw [this, hg₀p, hone]
  · -- σ ≠ 1
    intro hσ
    have hpt : ∀ x : L, g₀ • x = x := by
      intro x
      have := congrArg (fun φ : L ≃ₐ[K] L => φ x) hσ
      simpa [actionAlgEquiv] using this
    exact hg₀1 ((faithfulSMul_iff.mp hgal.1) g₀ hpt)

/-- **次数的提取** ✓：`C_p`-Galois 域档 ⟹ `[L : K] = p` ✓。 -/
theorem finrank_eq_prime_of_isGaloisWithGroup {K L : Type} [Field K] [CommRing L] [Nontrivial L]
    [Algebra K L] [Module.Finite K L] {p : ℕ} [NeZero p]
    [MulSemiringAction (Multiplicative (ZMod p)) L]
    (hKL : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hgal : IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL) :
    Module.finrank K L = p := by
  rw [BTier.finrank_eq_card_of_isGaloisWithGroup hKL hgal,
    ← Fintype.card_congr (Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p)), ZMod.card p]


end CpDataExtraction334

#print axioms exists_shift_automorphism
#print axioms finrank_eq_prime_of_isGaloisWithGroup

/-! ### 4.120 🔴🔴 **域档装配收口：`RealizationProperty` 的域档形**（第 335 轮）
—— 子目标 (c) 的**装配之二收口** ✓✅（**首个 `RealizationProperty` 形的结果** ✓）

**靶** ✓：**源 `theorem-1-2(a)`** ✓（`R = F[x]` ✓、`S = R{y^p − y − x}` ✓、`G = C_p` ✓）的
**域档 `(c)` 款** ✓（＝ `RealizationPropertyExplicit` ✓ 的域档形 ✓）。

**落成一件** ✓✅：**`realization_Cp_domain`** ✓✅：`char F = p` ✓、`C_p`-Galois **域档** ＋ 有限性 ⟹
**`∃ (φ : F[x] →ₐ[F] K) (A : Algebra F[x] K), algebraMap = φ.toRingHom ∧
Nonempty (L ≃ₐ[K] K ⊗_{F[x]} S)`** ✓✅（`S = asCarrier F[x] p x` ✓）。

**机制（四步拼装，全为本工程已落件 ✓）** ✓：
**(甲)** **§4.119** ✓ 给 `σ` ✓（`σ^p = 1` ✓、`σ ≠ 1` ✓）＋ **`finrank K L = p`** ✓；
**(乙)** **§4.118** ✓ 给 **`b : K`** ＋ **`e : L ≃ₐ[K] asCarrier K p b`** ✓；
**(丙)** **`φ := Polynomial.aeval b`** ✓（**它本身就是 `AlgHom`** ✓；`Polynomial.aeval_X` ✓ 给 `φ X = b` ✓）
＋ **`A := φ.toRingHom.toAlgebra`** ✓（**`algebraMap = φ.toRingHom` 为 `rfl`** ✓）；
**(丁)** **§4.114** ✓ 在 `let _inst : Algebra F[x] K := A` ✓ 下给
**`K ⊗_{F[x]} S ≃ₐ[K] asCarrier K p (algebraMap F[x] K x)`** ✓，而
**`algebraMap F[x] K x = φ x = b`** ✓ ⟹ 与 (乙) 的 `e` 复合 ⟹ **结论** ✓✅。

**⚠ 意义** ✓：**(c) 的域档已闭环** ✓✅ —— 从 **`G`-作用**到 **`L ≃ₐ[K] K ⊗_R S`** 全程机检 ✓。
**⚠ 未覆盖** ✗：**分裂档**（`L ≅ K^p` ✗）＋ **`L` 非域的一般环档** ✗ —— 二者**都不在本件量词域** ✗
（本件**逐字限定** `[IsDomain L]` ✓ ＋ `[Module.Finite K L]` ✓ ⟹ **不是** `RealizationProperty` 本身 ✗）。

**⚠ 工艺（三条，入 §5.1；均本轮实测）** ✓：
**(甲)** `exists_algEquiv_asCarrier` ✓ **要 `[CharP K p]`** ✗ ⟹ **现场注册**
`let _inst : CharP K p := charP_of_injective_algebraMap (algebraMap_injective_of_field) p` ✓；
**(乙)** **`let _inst : Algebra R K := A`** ✓（**`letI` 计样式警告** ✗ —— §5.1 #14／#23 同款 ✓）；
**(丙)** **`algebraMap` 的改写须在项内做** ✗：目标里已是 `b` ✓ ⟹ 须先把
**`asCarrier_tensorProduct` 的结论取成 `have ht := ....symm`** ✓ **再 `rw [hX] at ht`** ✓（**直接 `rw` 命中不了目标** ✗）。

**🔴 不声称** ✗：**不**声称 `RealizationProperty`（源形 ✓）已证 ✗（**本件只覆盖域档** ✗ —— 分裂档 ✗、
非域环档 ✗ 未处理）；**不**声称 `IsGenericExtension` 有实例 ✗；**不**声称见证非空 ✗；
**不**声称 (b) 环档判据有进展 ✗；**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section CpDomainAssembly335

/-- **域档装配收口** ✓✅：`C_p`-Galois **域档** ⟹ `∃ φ A, … ∧ L ≃ₐ[K] K ⊗_R S` ✓
（**即 `RealizationPropertyExplicit` 的域档形** ✓）。 -/
theorem realization_Cp_domain {F : Type} [Field F] {p : ℕ} (hp : p.Prime) [CharP F p]
    [NeZero p] (K : Type) [Field K] [Algebra F K]
    (L : Type) [CommRing L] [IsDomain L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction (Multiplicative (ZMod p)) L] [Module.Finite K L]
    (hKL : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : L), g • (r • t) = r • (g • t))
    (hgal : IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL) :
    ∃ (φ : Polynomial F →ₐ[F] K) (A : Algebra (Polynomial F) K),
      (@Algebra.algebraMap (Polynomial F) K _ _ A : Polynomial F →+* K) = φ.toRingHom ∧
      letI : Algebra (Polynomial F) K := A
      Nonempty (L ≃ₐ[K] (TensorProduct (Polynomial F) K
        (asCarrier (Polynomial F) p Polynomial.X))) := by
  classical
  let _inst : CharP K p :=
    charP_of_injective_algebraMap (algebraMap_injective_of_field (K := F) (L := K)) p
  have hcard : Module.finrank K L = p := finrank_eq_prime_of_isGaloisWithGroup hKL hgal
  obtain ⟨σ, hσ, hσ1⟩ := exists_shift_automorphism (K := K) (L := L) hp hKL hgal
  obtain ⟨b, ⟨e⟩⟩ := exists_algEquiv_asCarrier (K := K) (L := L) hp hcard hσ hσ1
  refine ⟨Polynomial.aeval b, (Polynomial.aeval b : Polynomial F →ₐ[F] K).toRingHom.toAlgebra,
    rfl, ?_⟩
  let _inst : Algebra (Polynomial F) K :=
    (Polynomial.aeval b : Polynomial F →ₐ[F] K).toRingHom.toAlgebra
  have hX : (algebraMap (Polynomial F) K Polynomial.X) = b := by
    show (Polynomial.aeval b : Polynomial F →ₐ[F] K) Polynomial.X = b
    simp
  refine ⟨e.trans ?_⟩
  have ht := (asCarrier_tensorProduct (R := Polynomial F) (K := K) p Polynomial.X).symm
  rw [hX] at ht
  exact ht


end CpDomainAssembly335

#print axioms realization_Cp_domain

/-! ### 4.121 🔴 **分裂档之一：分裂载体的根点**（第 336 轮）
—— 子目标 (c) 的**装配之三（分裂档）**的**第一件** ✓

**靶** ✓：**分裂档** = `L ≅ K^p` ✓ 的支 ✓（源 `theorem-1-2(a)` ✓ 的另一支 ✓）。
**拆分（分割包围 ✓）**：**(甲)** **分裂载体必为分裂代数** ✓：**`asCarrier K p 0 ≃ₐ[K] (ZMod p → K)`** ✗（**下一手** ✓）；
**(乙)** **结构事实** ✗：**`L ≅ K^p`** ✓ —— **须先判** ✓（**库内未证** ✗；源 `proposition-0-5(e)` ✓ 的**非域支** ✓）。
**本件只落 (甲) 的「根点」半步** ✓。

**落成一件** ✓✅：**`asCarrier_zero_aeval_eq_zero`** ✓✅：**`(i : K)` 是 `X^p − X` 的根** ✓
（`i : ZMod p` ✓、**`ZMod.castHom (dvd_refl p) K`** ✓）—— 即 **`p` 个互异根点** ✓
（互异性用 §4.86 ✓ 的 `zmod_castHom_injective` ✓）。

**机制** ✓：`ASpoly K p 0 = X^p − X − C 0` ✓ ⟹ `aeval` 展开为 **`(i:K)^p − (i:K)`** ✓ ⟹
**`map_pow`** ✓ ＋ **`ZMod.pow_card`** ✓（**Fermat**：`i^p = i` ✓）⟹ `0` ✓。

**⚠ 工艺（两条，入 §5.1；均本轮实测）** ✓：
**(甲)** **`Algebra (ZMod p) K` 不是实例** ✗（`ZMod.algebra` ✓ 是 `abbrev` ✗）⟹ **语句里不得写 `(i : K)`** ✗
（**实测**：`Type mismatch` ✗）⟹ **正解 ＝ 用环同态 `ZMod.castHom (dvd_refl p) K`** ✓ 显式书写 ✓；
**(乙)** **`Polynomial.eval_def` 不存在** ✗（**实测** `unknown identifier` ✗）—— 而**误以为其存在**会**静默留下 `sorryAx`** ✗
（**实测**：`#print axioms` 报 `sorryAx` ✗）⟹ **正解 ＝ 只落 `aeval` 形** ✓，
**`eval` 形留待下一手用正确的引理**（**候选**：`Polynomial.eval₂_at_apply` ✓／`eval_eq_eval₂` ✓ —— **先 `#check` 再写** ✓）。

**🔴 不声称** ✗：**不**声称 `asCarrier K p 0 ≃ₐ[K] K^p` 已证 ✗（**未落** ✗）；
**不**声称 `L ≅ K^p` ✗（**结构事实未落** ✗）；**不**声称分裂档已克 ✗；
**不**声称 `RealizationProperty` 有实例 ✗；**不**声称 (b) 环档判据有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section SplitCarrierRoot336

/-- **分裂载体的根点** ✓：`(i : K)`（`i : ZMod p`）是 `X^p − X` 的根 ✓（**Fermat ＋ char p**）。 -/
theorem asCarrier_zero_aeval_eq_zero (K : Type u) [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (i : ZMod p) :
    Polynomial.aeval (ZMod.castHom (dvd_refl p) K i) (ASpoly K p 0) = 0 := by
  rw [ASpoly]
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_zero]
  rw [show (ZMod.castHom (dvd_refl p) K i) ^ p = ZMod.castHom (dvd_refl p) K (i ^ p) from
    (map_pow (ZMod.castHom (dvd_refl p) K) i p).symm, ZMod.pow_card]
  simp

end SplitCarrierRoot336

#print axioms asCarrier_zero_aeval_eq_zero

/-! ### 4.122 🔴🔴 **分裂载体同构（T6-E-1 收口）**（第 337 轮）
—— 子目标 (c) 的**装配之三（分裂档）第一件** ✓✅

**靶** ✓：**`asCarrier K p 0 ≃ₐ[K] (ZMod p → K)`** ✓（**`K[X]/(X^p − X) ≅ K^p`** ✓）——
即**分裂档的「载体侧」** ✓（`b = 0` ✓ 时的目标代数 ✓）。

**落成两件** ✓✅：**(i)** **`aeval_eq_eval_self`** ✓（`K`-代数自求值下 **`aeval` ＝ `eval`** ✓ ——
**§5.1 #38 的桥梁件** ✓）；**(ii)** 🔴 **`asCarrier_zero_algEquiv_pi`** ✓✅：
**`Nonempty (asCarrier K p 0 ≃ₐ[K] (ZMod p → K))`** ✓✅（`p` 素 ✓、`[CharP K p]` ✓）。

**机制（三步，求值通道 ✓）** ✓：
**(甲)** **求值通道** ✓：`Φ := AlgHom.pi (fun i : ZMod p => AdjoinRoot.liftAlgHom …)` ✓
（**`AlgHom.pi`** ✓ —— `AlgHom.pi_apply` ✓；义务由 **§4.121** ✓ 的根点供给 ✓）；
**(乙)** **单射** ✓：`Φ (mk P) = 0 ⟹ ∀ i, P(i) = 0` ✓（`hval` ✓ —— `liftAlgHom_mk` ✓ ＋ **`aeval_def`** ✓）
⟹ **`modByMonic` 归约** ✓（`modByMonic_add_div` ✓／`natDegree_modByMonic_lt` ✓／
`modByMonic_eq_zero_iff_dvd` ✓）⟹ **`(P %ₘ f)` 在 `p` 个点上为零且次数 `< p`** ✓
⟹ **`eq_zero_of_natDegree_lt_card_of_eval_eq_zero`** ✓（**插值零判** ✓ ＋
**§4.86 的 `zmod_castHom_injective`** ✓ 给互异性 ✓）⟹ **`f ∣ P`** ✓ ⟹ **`mk P = 0`** ✓；
**(丙)** **秩相等 ⟹ 双射** ✓：**§4.91** ✓（`asCarrier_finrank` ✓）＋ **`Module.finrank_pi`** ✓ ＋
**`ZMod.card`** ✓ ⟹ **`AlgEquiv.ofBijective`** ✓✅。

**⚠ 意义** ✓：**分裂档的「载体侧」已全克** ✓✅ —— 分裂档只余**结构事实 `L ≅ K^p`** ✗（**T6-E-2** ✓）。

**⚠ 工艺（两条，入 §5.1；均本轮实测）** ✓：
**(甲)** 🔴 **`aeval`／`eval` 的桥接须自带** ✗：`liftAlgHom_mk` ✓ 给 **`eval₂`** 形 ✓、插值零判要 **`eval`** 形 ✗、
§4.121 ✓ 给 **`aeval`** 形 ✓ ⟹ **正解 ＝ ①`hval` 用 `aeval` 形**（`(Polynomial.aeval_def ..).symm` ✓）
**②末尾落一步 `rw [← aeval_eq_eval_self]`** ✓（**§5.1 #38** ✓）；
**(乙)** **`set` 定义的局部变量不可 `rintro rfl`／`subst`** ✗（实测 ✓）⟹ **用 `intro h; rw [h, …]`** ✓。

**🔴 不声称** ✗：**不**声称 **`L ≅ K^p`** ✗（**T6-E-2 未落** ✗）；**不**声称分裂档已克 ✗；
**不**声称 `RealizationProperty` 有实例 ✗；**不**声称非域环档已处理 ✗；**不**声称 (b) 环档判据有进展 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section SplitCarrierIso337

/-- `K`-代数自求值时 `aeval` ＝ `eval` ✓。 -/
theorem aeval_eq_eval_self (K : Type u) [CommRing K] (x : K) (P : Polynomial K) :
    Polynomial.aeval x P = P.eval x := by
  rw [Polynomial.aeval_def]
  rfl

/-- **分裂载体的分裂同构** ✓✅：`K[X]/(X^p − X) ≃ₐ[K] K^p` ✓（**求值通道 ＋ 插值 ＋ 秩相等** ✓）。 -/
theorem asCarrier_zero_algEquiv_pi (K : Type u) [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] :
    Nonempty (asCarrier K p 0 ≃ₐ[K] (ZMod p → K)) := by
  classical
  let _inst : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set Φ : asCarrier K p 0 →ₐ[K] (ZMod p → K) :=
    AlgHom.pi (fun i : ZMod p =>
      AdjoinRoot.liftAlgHom (ASpoly K p 0) (Algebra.ofId K K) (ZMod.castHom (dvd_refl p) K i)
        (by simpa [Polynomial.aeval_def] using asCarrier_zero_aeval_eq_zero K i)) with hΦ
  have hval : ∀ (P : Polynomial K) (i : ZMod p),
      Φ (AdjoinRoot.mk (ASpoly K p 0) P) i =
        Polynomial.aeval (ZMod.castHom (dvd_refl p) K i) P := by
    intro P i
    rw [hΦ, AlgHom.pi_apply, AdjoinRoot.liftAlgHom_mk]
    exact (Polynomial.aeval_def ..).symm
  have hker : ∀ x : asCarrier K p 0, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [AdjoinRoot.mk_eq_zero]
    have hP : ∀ i : ZMod p, Polynomial.aeval (ZMod.castHom (dvd_refl p) K i) P = 0 := by
      intro i
      have h := congrFun hx i
      rw [hval P i] at h
      exact h
    set f := ASpoly K p 0 with hf
    have hfmonic : f.Monic := aspoly_monic (R := K) hp2 0
    have hfd : f.natDegree = p := aspoly_natDegree (R := K) hp2 0
    have hf1 : f ≠ 1 := by
      intro h
      rw [h, Polynomial.natDegree_one] at hfd
      exact (Fact.out : p.Prime).ne_zero hfd.symm
    have hfroot : ∀ i : ZMod p,
        Polynomial.aeval (ZMod.castHom (dvd_refl p) K i) f = 0 := by
      intro i
      exact asCarrier_zero_aeval_eq_zero K i
    have hR : ∀ i : ZMod p,
        Polynomial.aeval (ZMod.castHom (dvd_refl p) K i) (P %ₘ f) = 0 := by
      intro i
      have h := Polynomial.modByMonic_add_div P f
      have h2 := congrArg (Polynomial.aeval (ZMod.castHom (dvd_refl p) K i)) h
      simp only [map_add, map_mul, hP i, hfroot i, zero_mul, add_zero] at h2
      exact h2
    have hReval : ∀ i : ZMod p,
        Polynomial.eval (ZMod.castHom (dvd_refl p) K i) (P %ₘ f) = 0 := by
      intro i
      rw [← aeval_eq_eval_self]
      exact hR i
    have hdeg : (P %ₘ f).natDegree < p := by
      have := Polynomial.natDegree_modByMonic_lt P hfmonic hf1
      rw [hfd] at this
      exact this
    have hzero : P %ₘ f = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P %ₘ f)
        (zmod_castHom_injective (R := K)) hReval (by rw [ZMod.card]; exact hdeg)
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hfmonic).mp hzero
  have hinj : Function.Injective Φ := by
    intro x z hxz
    have h1 : Φ (x - z) = 0 := by rw [map_sub, hxz, sub_self]
    exact sub_eq_zero.mp (hker (x - z) h1)
  have hfin1 : Module.finrank K (asCarrier K p 0) = p := asCarrier_finrank hp2 0
  have hfin2 : Module.finrank K (ZMod p → K) = p := by
    rw [Module.finrank_pi, ZMod.card]
  let _inst2 : Module.Finite K (asCarrier K p 0) :=
    Module.finite_of_finrank_pos (by rw [hfin1]; exact (Fact.out : p.Prime).pos)
  let _inst3 : Module.Finite K (ZMod p → K) :=
    Module.finite_of_finrank_pos (by rw [hfin2]; exact (Fact.out : p.Prime).pos)
  have hbij : Function.Bijective Φ := by
    refine ⟨hinj, ?_⟩
    have hinjL : Function.Injective (Φ.toLinearMap : asCarrier K p 0 →ₗ[K] (ZMod p → K)) := hinj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := asCarrier K p 0) (V₂ := ZMod p → K) (f := Φ.toLinearMap)
      (by rw [hfin1, hfin2])).mp hinjL
  exact ⟨AlgEquiv.ofBijective Φ hbij⟩


end SplitCarrierIso337

#print axioms asCarrier_zero_algEquiv_pi

/-! ### 4.123 🔴 **T7 前置：AS 载体的环档有限性**（第 339 轮）
—— 子目标 (b)（环档判据）的**承重前置** ✓（**任意交换环 `R`** ✓，非域 ✓）

**用途** ✓：环档款③ 的**秩论证**（§4.93 ✓ 的 `skew_finrank` ✓／`end_finrank` ✓）与
**任何投影／有限性通道**（源 `proposition-0-5(c)` ✓ 的「`S ≅ R[G]`」✓）**都要 `S` 在 `R` 上模有限** ✓ ——
**库内此前只有域档的 `let _inst`** ✗（§4.120／§4.122 各一处 ✓）⟹ **本件补环档** ✓。

**落成一件** ✓✅：**`asCarrier_finite`** ✓✅：`[CommRing R] [Nontrivial R]` ✓、`2 ≤ p` ✓ ⟹
**`Module.Finite R (asCarrier R p a)`** ✓✅。

**机制** ✓：**§4.91** ✓ 的幂基 `asCarrierBasis` ✓ ⟹ **`Module.Free.of_basis`** ✓ 注册 `[Module.Free R _]` ✓
（**§5.1 #41** ✓ —— **`finite_of_finrank_pos` 要 `Module.Free`** ✗，而幂基例**不自动**注册 `Free` ✗）⟹
`Module.finite_of_finrank_pos` ✓ ＋ **`asCarrier_finrank`** ✓（秩 ＝ `p` ✓）。

**⚠ 第 340 轮追加** ✓：**`asCarrier_projective`** ✓✅（**同一幂基 ⟹ 自由 ⟹ 投射** ✓ ——
**源 `proposition-0-5(c)`** ✓ 的**结论项** ✓；**⚠ étale 轮子已判「仅域档」** ✗ ——
`Algebra.FormallyEtale.iff_exists_algEquiv_prod` ✓ 的**量词域是域 `K`** ✗（`Etale/Field.lean:25` ✓ 的文档：**「finite product of separable field extensions」** ✗）⟹ **对环档不可直用** ✗）。

**🔴 不声称** ✗：**不**声称环档 `δ` 双射有进展 ✗（**本件只补前置** ✓）；
**不**声称源 `proposition-0-5(c)` ✓ 已证 ✗；**不**声称 `RealizationProperty` 有实例 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section ASCarrierFinite339

/-- **AS 载体的环档有限性** ✓✅：任意非平凡交换环上 `asCarrier R p a` 模有限 ✓。 -/
theorem asCarrier_finite {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p) (a : R) :
    Module.Finite R (asCarrier R p a) := by
  let _inst : Module.Free R (asCarrier R p a) :=
    Module.Free.of_basis (asCarrierBasis (R := R) hp a)
  exact Module.finite_of_finrank_pos (by rw [asCarrier_finrank (R := R) hp a]; omega)

end ASCarrierFinite339

/-- **AS 载体的环档投射性** ✓✅（**源 `proposition-0-5(c)`** ✓ 的**结论项之一** ✓；**由幂基 ⟹ 自由 ⟹ 投射** ✓）。 -/
theorem asCarrier_projective {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p) (a : R) :
    Module.Projective R (asCarrier R p a) := by
  let _inst : Module.Free R (asCarrier R p a) :=
    Module.Free.of_basis (asCarrierBasis (R := R) hp a)
  exact Module.Projective.of_free

#print axioms asCarrier_finite
#print axioms asCarrier_projective

/-! ### 4.124 🔴 **T7 路线（乙）第一小步：高权元的轨道**（第 341 轮）
—— 子目标 (b)（环档判据）的**路线（乙）**（**显式逆 ＋ 环档正规基**）的**第 (i) 步** ✓

**路线（乙）三小步** ✓：**(i)** `θ` 取**高权**元 ✓（`θ := root^(p−1)` ✓）；**(ii)** 证 **`{φ_g θ}` 是 `R`-基** ✗；
**(iii)** 由基写 **`δ^{-1}`** ✗ ⟹ 款③ ✓ ⟹ 组装（§4.89 ✓）。
**⚠ 路线（甲）已判否** ✗（**仅域档** ✓ —— §302 ✓）；**已判否两条捷径** ✗（§272.1 ✓／§4.92 ✓）。

**落成一件** ✓✅：**`asShiftH_root_pow_sub_one`** ✓✅ —— **`φ_k (θ) = (root + k)^(p−1)`** ✓✅
（`φ_k := asShiftH a k _` ✓，`k^p = k` ✓）—— **即 `θ` 的轨道逐点显式形** ✓。

**机制** ✓：`map_pow` ✓ ＋ **§4.92 的 `asShiftH_root`** ✓（**根 ↦ `root + k`** ✓）。

**⚠ 用途（路线（乙）为何需要它）** ✓：**(ii)** 的**基性**将由**过渡矩阵**证 ✓ ——
`(root + k)^(p−1) = Σ_j binom(p−1, j) k^(p−1−j) root^j` ✓ ⟹ **过渡矩阵的下三角首项为 `k^(p−1−j)`** ✓
—— **本件给出该展开的左端** ✓；**⚠ 但件本身不含基性结论** ✗。

**🔴 不声称** ✗：**不**声称 **`{φ_g θ}` 是 `R`-基** ✗（**(ii) 未落** ✗）；**不**声称环档 `δ` 双射有进展 ✗；
**不**声称 **`δ^{-1}` 已显式给出** ✗；**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section HighWeightOrbit341

/-- **高权元的轨道** ✓✅：`φ_k (root^(p−1)) = (root + k)^(p−1)` ✓（`φ_k` ＝ 移位 `asShiftH` ✓）。 -/
theorem asShiftH_root_pow_sub_one {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a k : R) (hk : k ^ p = k) :
    asShiftH a k hk ((AdjoinRoot.root (ASpoly R p a)) ^ (p - 1))
      = (AdjoinRoot.root (ASpoly R p a) + AdjoinRoot.of (ASpoly R p a) k) ^ (p - 1) := by
  rw [map_pow, asShiftH_root]

end HighWeightOrbit341

#print axioms asShiftH_root_pow_sub_one


/-! ### 4.125 🔴 **T7 路线（丙″）行列式半：移位节点 Vandermonde 为单位**（第 342 轮）
—— 子目标 (b)（环档判据）的**路线（丙″）** ✓ —— **矩量映射 ＋ 单位行列式** ✓（**§303.3 的改判** ✓）

**为何改判（第 342 轮探针实测）** ✗：**(a)** 路线（丙′）须 `End_R(S)` 的 **`S`-模结构** ✗ ——
实测 **`Algebra S (Module.End R S)` 不可合成** ✗（`Module.End.instAlgebra` ✓ 要求 `[SMul S R]` ✗，
而 `Algebra R S` **只给 `R → S`** ✗；逐件实测：`SMulCommClass R S S` ✓ 可合成，**卡在 `SMul S R`** ✗）；
**(b)** **路线（丙″）绕开 `End_R(S)` 的模结构** ✓：改用**矩量映射**
`Λ : (Fin p → S) →ₗ[S] (Fin p → S)` ✓（`Λ s i = Σ_j s_j * (root + of (castHom j))^i` ✓），
其矩阵 **`M_{i,j} = (root + of (castHom j))^i`** ✓（＝ `(vandermonde shiftNode)ᵀ` ✓）的行列式**为单位** ✓
⟹ **`Λ` 可逆** ✓（接线件：`Matrix.GeneralLinearGroup.toLin` ✓ ＋ `Matrix.toLin'` ✓ —— **下一手** ✗）。
**本件 ＝ 该行列式的单位性** ✓✅（**路线（丙″）的"行列式半"** ✓）。

**落成八件** ✓✅：**(甲)** **`isUnit_zmodCast_sub`** ✓✅ —— `k ≠ k'` ⟹ **`castHom k − castHom k'` 为单位** ✓
（`ZMod p` **域** ✓ ⟹ `k − k' ≠ 0` 是单位 ✓ ⟹ **环同态保单位** ✓）；
**(乙)** **`shiftNode_sub`** ✓✅ —— `(root + of k) − (root + of k') = of (k − k')` ✓（`map_sub` ✓）；
**(丙)** **`isUnit_shiftNode_sub`** ✓✅；**(丁)** **`isUnit_det_vandermonde_of_isUnit_sub`** ✓✅ ——
**逐对差为单位 ⟹ Vandermonde 行列式为单位** ✓（`det_vandermonde` ✓ ＋ `IsUnit.prod_univ_iff`／`IsUnit.prod_iff` ✓）；
**(戊)** **`shiftNode a i := root + of (castHom (i : ZMod p))`** ✓✅；
**(己)** **`finToZMod_injective`** ✓✅（`natCast_eq_natCast_iff` ✓ ＋ `Nat.ModEq.eq_of_lt_of_lt` ✓）；
**(庚)** **`isUnit_det_vandermonde_shiftNode`** ✓✅ —— **移位节点 Vandermonde 之 det 为单位** ✓✅；
**(辛)** **`isUnit_det_momentMatrix_shiftNode`** ✓✅ —— `M = (vandermonde shiftNode)ᵀ` ✓ 之 det 为单位 ✓
（`Matrix.det_transpose` ✓）—— **即下一手要接线的矩阵** ✓。

**⚠ 工艺（四条，入 §5.1）** ✓：**(#45)** `ring` 在**含 `AdjoinRoot.of` 项的加减恒等式**上**不闭合** ✗（实测 ✓）
⟹ 用 **`ring_nf`** ✓；**(#46)** **`ZMod.val_natCast_of_lt` 的改写模式不命中** ✗（目标 `(i : ZMod p)` 的 `Nat.cast` 形与模式不符 ✓）
⟹ **正解 ＝ `ZMod.natCast_eq_natCast_iff` ＋ `Nat.ModEq.eq_of_lt_of_lt`** ✓；
**(#47)** **`ᵀ` 记法在本文件不可用** ✗（实测 "unexpected token" ✓）⟹ 用 **`Matrix.transpose`** ✓；
**(#48)** **`IsUnit.prod_iff`／`IsUnit.prod_univ_iff` 在 `IsUnit` 命名空间** ✓（**非** `Finset.` ✗）。

**⚠ 与「源 `proposition-0-5(c)`（正规基）」的关系** ✓：**本件不用正规基** ✗ —— 用的是
**移位节点两两差为单位** ✓（＝ **素域是域**这一事实的推论 ✓）；**与源不矛盾** ✗（源在**域档**用正规基 ✓，
环档两条源命题走 `[DI71]` ✓）。

**🔴 不声称** ✗：**不**声称 **`Λ` 可逆已落** ✗（**只落其行列式为单位** ✓）；**不**声称 **`δ` 的矩量形已接线** ✗；
**不**声称环档 `δ` 双射有进展 ✗；**不**声称源 `proposition-0-6(b)`／`theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section DetHalf342

/-- **素域相异元之差的单位性** ✓：`k ≠ k'` ⟹ `castHom k − castHom k'` 在 `R` 中为单位 ✓
（`k − k' ≠ 0` 在**域** `ZMod p` 中 ⟹ 单位 ✓ ⟹ **环同态保单位** ✓）。 -/
theorem isUnit_zmodCast_sub {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {k k' : ZMod p} (h : k ≠ k') :
    IsUnit (ZMod.castHom (dvd_refl p) R k - ZMod.castHom (dvd_refl p) R k') := by
  rw [← map_sub]
  exact IsUnit.map _ (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h))

/-- **移位节点之差** ✓：`(root + of k) − (root + of k') = of (k − k')` ✓。 -/
theorem shiftNode_sub {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) (k k' : ZMod p) :
    (AdjoinRoot.root (ASpoly R p a) + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k))
        - (AdjoinRoot.root (ASpoly R p a)
            + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k'))
      = AdjoinRoot.of (ASpoly R p a)
          (ZMod.castHom (dvd_refl p) R k - ZMod.castHom (dvd_refl p) R k') := by
  have h : (AdjoinRoot.root (ASpoly R p a)
        + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k))
      - (AdjoinRoot.root (ASpoly R p a)
        + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k'))
      = AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k)
        - AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k') := by ring_nf
  rw [h, map_sub]

/-- **移位节点之差的单位性** ✓。 -/
theorem isUnit_shiftNode_sub {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) {k k' : ZMod p} (h : k ≠ k') :
    IsUnit ((AdjoinRoot.root (ASpoly R p a)
          + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k))
        - (AdjoinRoot.root (ASpoly R p a)
          + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R k'))) := by
  rw [shiftNode_sub a k k']
  exact IsUnit.map _ (isUnit_zmodCast_sub h)

/-- **一般形** ✓：**逐对差为单位 ⟹ Vandermonde 行列式为单位** ✓。 -/
theorem isUnit_det_vandermonde_of_isUnit_sub {S : Type u} [CommRing S] {n : ℕ} {v : Fin n → S}
    (h : ∀ i j : Fin n, i ≠ j → IsUnit (v i - v j)) :
    IsUnit (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde, IsUnit.prod_univ_iff]
  intro i
  rw [IsUnit.prod_iff]
  intro j hj
  exact h j i (Finset.mem_Ioi.mp hj).ne'

/-- **移位节点族** ✓：`v i := root + of (castHom (i : ZMod p))` ✓。 -/
noncomputable def shiftNode {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) (i : Fin p) : asCarrier R p a :=
  AdjoinRoot.root (ASpoly R p a)
    + AdjoinRoot.of (ASpoly R p a) (ZMod.castHom (dvd_refl p) R (i : ZMod p))

/-- **`Fin p → ZMod p` 的单射性** ✓。 -/
theorem finToZMod_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (fun i : Fin p => (i : ZMod p)) := by
  intro i j h
  have h1 : (i : ℕ) ≡ (j : ℕ) [MOD p] := (ZMod.natCast_eq_natCast_iff (i : ℕ) (j : ℕ) p).mp h
  exact Fin.eq_of_val_eq (h1.eq_of_lt_of_lt i.isLt j.isLt)

/-- **移位节点 Vandermonde 的行列式为单位** ✓✅（**路线（丙″）的行列式半** ✓）。 -/
theorem isUnit_det_vandermonde_shiftNode {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    IsUnit (Matrix.vandermonde (shiftNode (p := p) a)).det := by
  refine isUnit_det_vandermonde_of_isUnit_sub (fun i j hij => ?_)
  have hne : (i : ZMod p) ≠ (j : ZMod p) := fun h => hij (finToZMod_injective h)
  exact isUnit_shiftNode_sub a hne

/-- **矩量矩阵（转置形）的行列式为单位** ✓（`M i j = v j ^ i` ＝ `(vandermonde v)ᵀ` ✓）。 -/
theorem isUnit_det_momentMatrix_shiftNode {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    IsUnit (Matrix.det (fun i j : Fin p => (shiftNode (p := p) a j) ^ (i : ℕ))) := by
  have h : (fun i j : Fin p => (shiftNode (p := p) a j) ^ (i : ℕ))
      = Matrix.transpose (Matrix.vandermonde (shiftNode (p := p) a)) := rfl
  rw [h, Matrix.det_transpose]
  exact isUnit_det_vandermonde_shiftNode a

end DetHalf342

#print axioms isUnit_zmodCast_sub
#print axioms shiftNode_sub
#print axioms isUnit_shiftNode_sub
#print axioms isUnit_det_vandermonde_of_isUnit_sub
#print axioms isUnit_det_vandermonde_shiftNode
#print axioms isUnit_det_momentMatrix_shiftNode


/-! ### 4.126 🔴🔴 **T7 路线（丙″）接线半之一：矩量映射可逆 ＋ 环档 `δ` 单射**（第 343 轮）
—— 子目标 (b)（环档判据）的**第二步** ✓（**行列式半** ✓ §4.125 ⟹ **矩量映射** ✓）

**路线（丙″）的接线** ✓：**(甲)** **矩量映射 `Λ` 可逆** ✓✅（**本件** ✓）；
**(乙)** **`δ` 单射** ✓✅（**本件** ✓ —— **不用 Dedekind、不用正规基** ✗）；
**(丙)** **`δ` 满射** ✗（**须幂基取值引理** ✓ —— **下一手** ✓）；**(丁)** 组装 §4.89 ✓。

**落成五件** ✓✅：**(L1)** **`asCarrierMSA_smul_root_pow`** ✓✅ —— **`k • root^n = (root + of (castHom (toAdd k)))^n`** ✓
（**§4.124 的幂基推广** ✓；机制：`map_pow` ✓ ＋ `asShiftH_root` ✓）；
**(L2)** **`finEquivG`** ✓✅ —— **`Fin p ≃ Multiplicative (ZMod p)`** ✓（`i ↦ ofAdd (i : ZMod p)` ✓，
**逐点定义形** ✓ —— 供 `Equiv.sum_comp` 重索引 ✓；单射由 §4.125 的 `finToZMod_injective` ✓，
满射由 `ZMod.val_lt` ✓ ＋ `ZMod.natCast_zmod_val` ✓）；
**(L3)** **`delta_root_pow_eq_moment`** ✓✅ —— **`δ` 的矩量形** ✓：
**`(δ z) (root^i) = ∑_j (coeff z (ofAdd j)) * (shiftNode a j)^i`** ✓；
**(L4)** **`momentMatrix`** ✓✅（`M_{i,j} = (shiftNode a j)^i` ✓）＋ **`momentMap`** ✓✅（`＝ Matrix.toLin' M` ✓）
＋ **`momentMap_bijective`** ✓✅（**由 §4.125 的单位行列式** ✓ ＋ `Matrix.toLinearEquiv'` ✓）
＋ **`momentMap_apply`** ✓✅；
**(L5)** **`delta_injective_of_moment`** ✓✅ —— **环档 `δ` 单射** ✓✅：
`δ z = 0` ⟹ **矩量方程** ✓ ⟹ **`Λ` 单射** ⟹ **系数全零** ✓ ⟹ `z = 0` ✓。

**⚠ 意义** ✓：**(乙) 是域档单射（§4.104，**Dedekind 通道** ✓）的**环档替代** ✓ ——
域档须**除**（`[Field L]` ✓）以把系数归一 ✗；环档**不可除** ✗ ⟹ 改由**矩量映射的可逆性** ✓ 供给 ✓
（**`Λ` 的可逆性来自行列式为单位** ✓，而单位性来自**素域是域** ✓ —— **与源环档走 `[DI71]` 不矛盾** ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#49)** **`k • x` 不显式暴露 `asShiftH`** ✗ ⟹ `rw [map_pow, …]` **不命中** ✗；
**正解 ＝ `change`** ✓（`asCarrierMSA` 是 `@[instance_reducible]` ✓，`change` 按 defeq 通过 ✓）；
**(#50)** **「单位行列式 ⟹ 可逆线性映射」的接线** ✓：**`Matrix.invertibleOfIsUnitDet`** ✓ ＋
**`Matrix.toLinearEquiv'`** ✓，其 **`toLinearEquiv'_apply` 为 `rfl`** ✓（**无须给基底** ✓ —— 比 `toLinearEquiv` 省一层 ✓）；
**(#51)** **群和重索引到 `Fin p`** ✓：用 **`Equiv.sum_comp`** ✓ ＋ **`Equiv.ofBijective`** 自建等价 ✓
（**关键** ✓：以 **`fun i => ofAdd (i : ZMod p)`** 为 `toFun` ⟹ **逐点值定义相等** ✓ ⟹ 后续 `rfl` 收口 ✓）；
满射支用 **`ZMod.val_lt`** ✓ ＋ **`ZMod.natCast_zmod_val`** ✓；**`NeZero p` 须 `let _inst`** ✓（`haveI` 计样式警告 ✗）。

**🔴 不声称** ✗：**不**声称 **`δ` 满射已落** ✗（**须幂基取值引理** ✓）；**不**声称环档 `δ` 双射已证 ✗；
**不**声称 `IsGaloisWithGroup R S G hRG` 已证 ✗；**不**声称源 `proposition-0-6(b)`／`theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section MomentWiring343

attribute [local instance] asCarrierMSA

open ABGV52.BTier

/-- **(L1) 群作用在幂基上的值** ✓：`k • root^n = (root + of (castHom (toAdd k)))^n` ✓。 -/
theorem asCarrierMSA_smul_root_pow {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) (k : Multiplicative (ZMod p)) (n : ℕ) :
    k • ((AdjoinRoot.root (ASpoly R p a)) ^ n)
      = (AdjoinRoot.root (ASpoly R p a)
          + AdjoinRoot.of (ASpoly R p a)
              (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))) ^ n := by
  change asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      (castHom_pow (p := p) (Multiplicative.toAdd k)) ((AdjoinRoot.root (ASpoly R p a)) ^ n) = _
  rw [map_pow, asShiftH_root]

/-- **(L2) 编号等价** ✓：`Fin p ≃ Multiplicative (ZMod p)`（`i ↦ ofAdd (i : ZMod p)` ✓，
**逐点定义形** ✓ —— 供 `Equiv.sum_comp` 重索引 ✓）。 -/
noncomputable def finEquivG (p : ℕ) [Fact p.Prime] : Fin p ≃ Multiplicative (ZMod p) :=
  Equiv.ofBijective (fun i : Fin p => Multiplicative.ofAdd (i : ZMod p))
    ⟨fun i j h => finToZMod_injective (Equiv.injective Multiplicative.ofAdd h), by
      intro g
      let _inst : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
      refine ⟨⟨(Multiplicative.toAdd g).val, ZMod.val_lt _⟩, ?_⟩
      show Multiplicative.ofAdd (((Multiplicative.toAdd g).val : ℕ) : ZMod p) = g
      rw [ZMod.natCast_zmod_val]
      exact Equiv.apply_symm_apply Multiplicative.ofAdd g⟩

/-- **(L3) `δ` 的矩量形** ✓：`(δ z) (root^i) = ∑_{j} (coeff z (ofAdd j)) * (shiftNode a j)^i` ✓。 -/
theorem delta_root_pow_eq_moment {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R)
    (hRG : ∀ (g : Multiplicative (ZMod p)) (r : R) (t : asCarrier R p a), g • (r • t) = r • (g • t))
    (z : SkewMonoidAlgebra (asCarrier R p a) (Multiplicative (ZMod p))) (i : Fin p) :
    deltaToEndRingHom hRG z ((AdjoinRoot.root (ASpoly R p a)) ^ (i : ℕ))
      = ∑ j : Fin p, z.coeff (Multiplicative.ofAdd (j : ZMod p)) * (shiftNode a j) ^ (i : ℕ) := by
  rw [delta_apply_sum hRG z, delta_sum_univ z]
  rw [← Equiv.sum_comp (finEquivG p) (fun g : Multiplicative (ZMod p) =>
    z.coeff g * (g • ((AdjoinRoot.root (ASpoly R p a)) ^ (i : ℕ))))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [asCarrierMSA_smul_root_pow]
  rfl

/-- **(L4-a) 矩量矩阵** ✓：`M_{i,j} = (shiftNode a j)^i` ✓。 -/
noncomputable def momentMatrix {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) : Matrix (Fin p) (Fin p) (asCarrier R p a) :=
  fun i j => (shiftNode a j) ^ (i : ℕ)

/-- **(L4-b) 矩量映射** ✓：`Λ = Matrix.toLin' M` ✓。 -/
noncomputable def momentMap {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) : (Fin p → asCarrier R p a) →ₗ[asCarrier R p a] (Fin p → asCarrier R p a) :=
  Matrix.toLin' (momentMatrix a)

/-- **(L4-c) 矩量映射可逆** ✓✅（**单位行列式 ＋ `toLinearEquiv'`** ✓）。 -/
theorem momentMap_bijective {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) : Function.Bijective (momentMap a) :=
  (Matrix.toLinearEquiv' (momentMatrix a)
    (Matrix.invertibleOfIsUnitDet _ (isUnit_det_momentMatrix_shiftNode a))).bijective

/-- **(L4-d) 矩量映射的取值形** ✓。 -/
theorem momentMap_apply {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) (s : Fin p → asCarrier R p a) (i : Fin p) :
    momentMap a s i = ∑ j : Fin p, s j * (shiftNode a j) ^ (i : ℕ) := by
  rw [momentMap, Matrix.toLin'_apply, Matrix.mulVec]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **(L5) 环档 `δ` 单射** ✓✅（**矩量形 ＋ 矩量映射单射 ＋ 系数消去** ✓ —— **不用幂基取值引理** ✓）。 -/
theorem delta_injective_of_moment {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R)
    (hRG : ∀ (g : Multiplicative (ZMod p)) (r : R) (t : asCarrier R p a), g • (r • t) = r • (g • t)) :
    Function.Injective (deltaToEndRingHom (S := asCarrier R p a) hRG) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hzero : ∀ i : Fin p,
      momentMap a (fun j : Fin p => z.coeff (Multiplicative.ofAdd (j : ZMod p))) i = 0 := by
    intro i
    rw [momentMap_apply, ← delta_root_pow_eq_moment a hRG z i, hz]
    rfl
  have hvec : (fun j : Fin p => z.coeff (Multiplicative.ofAdd (j : ZMod p))) = 0 := by
    apply (momentMap_bijective a).1
    ext i
    simp [hzero i]
  apply SkewMonoidAlgebra.coeff_eq_zero.mp
  ext g
  obtain ⟨i, hi⟩ := (finEquivG p).surjective g
  rw [← hi]
  change z.coeff (Multiplicative.ofAdd (i : ZMod p)) = 0
  exact congrFun hvec i

end MomentWiring343

#print axioms asCarrierMSA_smul_root_pow
#print axioms delta_root_pow_eq_moment
#print axioms momentMap_bijective
#print axioms momentMap_apply
#print axioms delta_injective_of_moment


/-! ### 4.127 🔴🔴🔴 **T7 收官：环档 `δ` 双射 ⟹ 源 `proposition-0-6(b)` 落库**（第 344 轮）
—— 子目标 (b)（环档判据）**全克** ✓✅（**(甲)(乙) §4.126** ✓ ＋ **(丙)(丁) 本件** ✓）

**落成四件** ✓✅：**(甲)** **`asCarrierBasis_apply`** ✓✅ —— **`asCarrierBasis hp a i = root^(i:ℕ)`** ✓
（**幂基取值引理** ✓ —— 满射的"幂基上相符"步所需 ✓）；
**(乙)** **`delta_surjective_of_moment`** ✓✅ —— **环档 `δ` 满射** ✓✅（**矩量解 ＋ `ofCoeff` 造元 ＋ 幂基相符 ＋ `Basis.ext`** ✓）；
**(丙)** **`delta_bijective_of_moment`** ✓✅ —— **环档 `δ` 双射** ✓✅（**＝ 源 §0 判据的第三款** ✓）；
**(丁)** **`asCarrier_isGaloisWithGroup`** ✓✅ —— **`IsGaloisWithGroup R (asCarrier R p a) (Multiplicative (ZMod p)) (asCarrier_hRG a)`** ✓✅
—— **即源 `proposition-0-6(b)`** ✓✅（**`raw/Saltman1982.tex:143`** ✓：`S = R{y^p − y − a}` ⟹ `S/R` 是 `C_p`-Galois ✓）。

**机制（(乙) 满射）** ✓：给定 `f : End_R S` ✓，取 **`c i := f (root^i)`** ✓ ⟹ 由 **§4.126 的 `momentMap_bijective`** ✓
解 **`s`**（`Λ s = c` ✓）⟹ 造元 **`z := ofCoeff F`** ✓（`F (ofAdd j) = s j` ✓）⟹
**§4.126 的矩量形** ✓ 给出 `δ z (root^i) = Σ_j s_j (shiftNode j)^i = c i = f (root^i)` ✓ ⟹
**`Module.Basis.ext`** ✓（幂基 ✓ ＋ **`asCarrierBasis_apply`** ✓）⟹ **`δ z = f`** ✓✅。

**⚠ 量词域** ✗：本件限定 **`[IsDomain R]`** ✓（款① 的 `of` 单射通道 §4.87 ✓ 须域 ✓）——
**源 `proposition-0-6(b)` 对任意 `F`-代数 `R` 陈述** ✓；本件给出其**域档** ✓；
**源的实际用例 `R = F[x]` 是域** ✓（**`theorem-1-2(a)` 的 `(b)` 款所需** ✓）。

**⚠ 工艺（四条，入 §5.1）** ✓：**(#52)** **`PowerBasis.basis_eq_pow` 是结构字段** ✗（**非**独立引理 ✗）——
`rw` 时**须显式给索引** ✓（否则报 "not type-correct under implicit transparency" ✗）；
且 **`gen = root`** ✓ 与**指数相等** ✓ 须各作 `have` ✓（`gen` 的 `PowerBasis.dim` 与 `natDegree` 的 defeq 不参与 `rw` ✗）；
**(#53)** **`Finsupp.coe_equivFunOnFinite_symm : ⇑(equivFunOnFinite.symm f) = f`** ✓（**`rfl`** ✓）——
**`equivFunOnFinite_symm_apply` 不存在** ✗；
**(#54)** **造"系数已知"的 `SkewMonoidAlgebra` 元用 `ofCoeff`** ✓（`(ofCoeff F).coeff = F` **由 `rfl`** ✓）——
**旁路**「有限个 `single` 之和的系数」✗（`coeff` 是**普通函数** ✗ ⟹ `rw [map_sum]` **不触发** ✗，
须经 `coeffAddEquiv.toAddMonoidHom` ✓ 再对 Finsupp 之和取值 ✗ —— **两处皆不必走** ✓）；
**(#55)** **`Module.Basis.ext`** ✓（**限定名** ✓；`Basis.ext` 报 unknown ✗）—— 由基上相符证线性映射相等 ✓。

**⚠ 与已判否路线的关系** ✓：**（乙）（环档正规基）** 未使用 ✗；**（丙′）（`End_R(S)` 的 `S`-基）** 未使用 ✗
（§304 已判受阻 ✓）；**（甲）（étale 轮子）** 未使用 ✗（§302 已判仅域档 ✓）——
**路线（丙″）独立走通** ✓。

**🔴 不声称** ✗：**不**声称 **任意（非域）`R` 上的 `IsGaloisWithGroup`** ✗（**本件限定 `[IsDomain R]`** ✓）；
**不**声称源 `proposition-0-6(a)`（`n` 档）／`proposition-0-6(c)`（张量积档）已证 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗；**不**声称 **(c) 残支已克** ✗
（**(c) 分裂档模型侧** ⚠ 缺外部理论、真值未定 ⚠；**非域环档** ✗）；**`RealizationProperty` 仍零实例** ✗。 -/

section T7Finale344

attribute [local instance] asCarrierMSA

open ABGV52.BTier

/-- **(甲) 幂基取值引理** ✓：`asCarrierBasis hp a i = root^(i:ℕ)` ✓。 -/
theorem asCarrierBasis_apply {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p) (a : R)
    (i : Fin p) :
    asCarrierBasis (R := R) hp a i = (AdjoinRoot.root (ASpoly R p a)) ^ (i : ℕ) := by
  rw [asCarrierBasis, Module.Basis.reindex_apply]
  have hb := (AdjoinRoot.powerBasis' (aspoly_monic (R := R) hp a)).basis_eq_pow
    ((finCongr (aspoly_natDegree (R := R) hp a)).symm i)
  rw [show (AdjoinRoot.powerBasisAux' (aspoly_monic (R := R) hp a))
        ((finCongr (aspoly_natDegree (R := R) hp a)).symm i)
      = (AdjoinRoot.powerBasis' (aspoly_monic (R := R) hp a)).basis
          ((finCongr (aspoly_natDegree (R := R) hp a)).symm i) from rfl, hb]
  have hgen : (AdjoinRoot.powerBasis' (aspoly_monic (R := R) hp a)).gen
      = AdjoinRoot.root (ASpoly R p a) := rfl
  have hexp : (((finCongr (aspoly_natDegree (R := R) hp a)).symm i : Fin _) : ℕ) = (i : ℕ) := by
    simp [finCongr_symm, finCongr_apply]
  rw [hgen, hexp]

/-- **(乙) 环档 `δ` 满射** ✓✅（**矩量解 ＋ `ofCoeff` 造元 ＋ 幂基相符 ＋ `Basis.ext`** ✓）。 -/
theorem delta_surjective_of_moment {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R)
    (hRG : ∀ (g : Multiplicative (ZMod p)) (r : R) (t : asCarrier R p a), g • (r • t) = r • (g • t)) :
    Function.Surjective (deltaToEndRingHom (S := asCarrier R p a) hRG) := by
  classical
  intro f
  have hp : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  obtain ⟨s, hs⟩ := (momentMap_bijective a).2
    (fun i : Fin p => f ((AdjoinRoot.root (ASpoly R p a)) ^ (i : ℕ)))
  let F : Multiplicative (ZMod p) →₀ asCarrier R p a :=
    Finsupp.equivFunOnFinite.symm (fun g : Multiplicative (ZMod p) => s ((finEquivG p).symm g))
  refine ⟨SkewMonoidAlgebra.ofCoeff F, ?_⟩
  have hcoeff : ∀ j : Fin p,
      (SkewMonoidAlgebra.ofCoeff F).coeff (Multiplicative.ofAdd (j : ZMod p)) = s j := by
    intro j
    have h1 : (SkewMonoidAlgebra.ofCoeff F).coeff = F := rfl
    rw [h1]
    have h2 : F (Multiplicative.ofAdd (j : ZMod p))
        = s ((finEquivG p).symm (Multiplicative.ofAdd (j : ZMod p))) :=
      congrFun (Finsupp.coe_equivFunOnFinite_symm
        (fun g : Multiplicative (ZMod p) => s ((finEquivG p).symm g)))
        (Multiplicative.ofAdd (j : ZMod p))
    rw [h2]
    have h3 : (finEquivG p).symm (Multiplicative.ofAdd (j : ZMod p)) = j :=
      Equiv.symm_apply_apply (finEquivG p) j
    rw [h3]
  have hval : ∀ i : Fin p,
      deltaToEndRingHom hRG (SkewMonoidAlgebra.ofCoeff F)
          ((AdjoinRoot.root (ASpoly R p a)) ^ (i : ℕ))
        = f ((AdjoinRoot.root (ASpoly R p a)) ^ (i : ℕ)) := by
    intro i
    rw [delta_root_pow_eq_moment a hRG _ i]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hcoeff j])]
    rw [← momentMap_apply a s i, hs]
  refine Module.Basis.ext (b := asCarrierBasis (R := R) hp a) (f₁ := _) (f₂ := f)
    (fun i => ?_)
  rw [asCarrierBasis_apply]
  exact hval i

/-- **(丙) 环档 `δ` 双射** ✓✅（**＝ 源 §0 判据的第三款** ✓）。 -/
theorem delta_bijective_of_moment {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R)
    (hRG : ∀ (g : Multiplicative (ZMod p)) (r : R) (t : asCarrier R p a), g • (r • t) = r • (g • t)) :
    Function.Bijective (deltaToEndRingHom (S := asCarrier R p a) hRG) :=
  ⟨delta_injective_of_moment a hRG, delta_surjective_of_moment a hRG⟩

/-- **(丁) 源 `proposition-0-6(b)` 的机检形** ✓✅：**AS 载体在任意 `[IsDomain R]` 上是 `C_p`-Galois** ✓✅。 -/
theorem asCarrier_isGaloisWithGroup {R : Type u} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    IsGaloisWithGroup R (asCarrier R p a) (Multiplicative (ZMod p)) (asCarrier_hRG a) :=
  asCarrier_isGaloisWithGroup_of_delta a
    (delta_bijective_of_moment a (asCarrier_hRG a))

end T7Finale344

#print axioms asCarrierBasis_apply
#print axioms delta_surjective_of_moment
#print axioms delta_bijective_of_moment
#print axioms asCarrier_isGaloisWithGroup


/-! ### 4.128 🔴🔴🔴 **去条件化：`of` 单射（任意交换环）⟹ 源 `proposition-0-6(b)` 全一般形**（第 345 轮）
—— **`[IsDomain R]` 限制的去除** ✓（**源对任意 `F`-代数陈述** ✓）

**缺口** ✓：§4.127 的 `asCarrier_isGaloisWithGroup` **限定 `[IsDomain R]`** ✗ —— 因其款① 走
**`AdjoinRoot.of.injective_of_degree_ne_zero`** ✓（**须 `[IsDomain R]`** ✗，`AdjoinRoot.lean` ✓）。
**其余三件皆不须域** ✓（**已核** ✓）：款② `asCarrier_smul_algebraMap` ✓（§4.85 ✓，只须 `CommRing` ✓）、
款① 的**归约形** `asCarrierMSA_faithful_of_ofInjective` ✓（§4.86 ✓，只须 `of` 单射 ＋ 素域像单射 ✓）、
`hRG` ✓（§4.89 的证明**未用** `[IsDomain R]` ✗）。

**落成六件** ✓✅：**(甲)** **`nontrivial_of_charP`** ✓✅（`CharP R p` ＋ `p` 素 ⟹ `Nontrivial R` ✓，§4.86 同法 ✓）；
**(乙)** **`asCarrier_of_eq_zero`** ✓✅ —— **`of x = 0 ⟹ x = 0`（任意交换环 ✓）** ✓：
`C x ∈ (f)` ✓（`AdjoinRoot.mk_eq_zero` ✓）⟹ **`C x %ₘ f = 0`** ✓ 且 **`= C x`** ✓（**`f` 首一 ＋ 次数 `p ≥ 2`** ✓
—— **`modByMonic_eq_zero_iff_dvd`** ✓ ＋ **`modByMonic_eq_self_iff`** ✓）⟹ `C x = 0` ✓ ⟹ `x = 0` ✓；
**(丙)** **`asCarrier_of_injective`** ✓✅（**任意交换环** ✓）；**(丁)** **`asCarrierMSA_faithful`** ✓✅
（**款① 全一般形** ✓ —— **不须 `[IsDomain R]`** ✓）；**(戊)** **`asCarrier_hRG'`** ✓✅（**`hRG` 全一般形** ✓）；
**(己)** **`asCarrier_isGaloisWithGroup'`** ✓✅ —— **`IsGaloisWithGroup R (asCarrier R p a) (Multiplicative (ZMod p)) (asCarrier_hRG' a)`** ✓✅
—— **任意特征 `p` 的交换环** ✓✅（**非域亦可** ✓）＝ **源 `proposition-0-6(b)` 的**全一般形** ✓✅**。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#56)** **`aspoly_monic`／`aspoly_natDegree` 须 `[Nontrivial R]`** ✗ ⟹
由 **`nontrivial_of_charP`** ✓ ＋ **`let _inst`** ✓ 现场注册 ✓（`CharP` ＋ 素 ⟹ 非平凡 ✓）；
**(#57)** **`Polynomial.modByMonic_eq_self_of_degree_lt` 不存在** ✗ ⟹ 用 **`modByMonic_eq_self_iff`** ✓（**`↔` 形** ✓）
＋ **`lt_of_le_of_lt Polynomial.degree_C_le`** ✓（**`degree_C_le` 是 `≤` 证明** ✗，**不可 `rw`** ✗）；
**(#58)** **`isGaloisWithGroup_of_clauses`（§4.107）须三型同宇宙** ✗（`{R S G : Type u}` ✓ —— **§5.1 #30 同型** ✓）
而 **`G = Multiplicative (ZMod p) : Type`** ✓ ⟹ **正解 ＝ 直接以匿名构造子填三款** ✓
（`IsGaloisWithGroup` 是 `def` ✓ ⟹ `⟨款①, 款②, 款③⟩` ✓）—— **绕开同宇宙约束** ✓。

**⚠ 与 §4.127 的关系** ✓：**本件严格推广** ✓（§4.127 的 `[IsDomain R]` 档由本件在 `[IsDomain R]` 下复得 ✓）；
两者的**款③ 同源** ✓（均为 `delta_bijective_of_moment` ✓）；**`hRG` 的载体**不同 ✓
（§4.127 用 `asCarrier_hRG` ✓；本件用 `asCarrier_hRG'` ✓ —— **两者皆为真** ✓，后者假设更少 ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)`（`n` 档）／`(c)`（张量积档）已证 ✗；
**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗；**不**声称 **(c) 残支已克** ✗
（**分裂档模型侧** ⚠ 缺外部理论、真值未定 ⚠；**非域环档的 `RealizationProperty`** ✗）；**`RealizationProperty` 仍零实例** ✗。 -/

section UnconditionalRingTier345

attribute [local instance] asCarrierMSA

open ABGV52.BTier

/-- **(甲) `CharP R p` ＋ `p` 素 ⟹ `Nontrivial R`** ✓（§4.86 同法 ✓）。 -/
theorem nontrivial_of_charP {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] :
    Nontrivial R := by
  rw [← not_subsingleton_iff_nontrivial]
  intro h
  have h1 : (1 : R) = 0 := Subsingleton.elim 1 0
  exact (Fact.out : Nat.Prime p).not_dvd_one
    ((CharP.cast_eq_zero_iff R p 1).mp (by simpa using h1))

/-- **(乙) `of x = 0 ⟹ x = 0`（任意交换环 ✓，**不需 `[IsDomain R]`** ✓）**。 -/
theorem asCarrier_of_eq_zero {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (a : R)
    {x : R} (h : AdjoinRoot.of (ASpoly R p a) x = 0) : x = 0 := by
  let _inst : Nontrivial R := nontrivial_of_charP (R := R) (p := p)
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hmonic : (ASpoly R p a).Monic := aspoly_monic (R := R) hp2 a
  have hdeg : (ASpoly R p a).natDegree = p := aspoly_natDegree (R := R) hp2 a
  have hdvd : ASpoly R p a ∣ Polynomial.C x := by
    rw [← AdjoinRoot.mk_eq_zero]
    exact h
  have hmod : (Polynomial.C x) %ₘ (ASpoly R p a) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have hself : (Polynomial.C x) %ₘ (ASpoly R p a) = Polynomial.C x := by
    refine (Polynomial.modByMonic_eq_self_iff hmonic).mpr ?_
    have hdeg' : (ASpoly R p a).degree = (p : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [hdeg']
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [hself] at hmod
  exact Polynomial.C_eq_zero.mp hmod

/-- **(丙) `of` 单射（任意交换环）** ✓。 -/
theorem asCarrier_of_injective {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) : Function.Injective (AdjoinRoot.of (ASpoly R p a)) := by
  intro r s h
  have hsub : AdjoinRoot.of (ASpoly R p a) (r - s) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (asCarrier_of_eq_zero (R := R) (p := p) a hsub)

/-- **(丁) 款①（忠实）全一般形** ✓：**任意交换环** ✓（**不须 `[IsDomain R]`** ✓）。 -/
theorem asCarrierMSA_faithful {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (a : R) : FaithfulSMul (Multiplicative (ZMod p)) (asCarrier R p a) :=
  asCarrierMSA_faithful_of_ofInjective a (asCarrier_of_injective (R := R) (p := p) a)

/-- **(戊) `hRG` 全一般形** ✓（**不须 `[IsDomain R]`** ✓）。 -/
theorem asCarrier_hRG' {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] (a : R) :
    ∀ (g : Multiplicative (ZMod p)) (r : R) (t : asCarrier R p a),
      g • (r • t) = r • (g • t) := by
  intro k r t
  rw [Algebra.smul_def, Algebra.smul_def]
  show asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
      (castHom_pow (p := p) (Multiplicative.toAdd k))
      (algebraMap R (asCarrier R p a) r * t)
    = algebraMap R (asCarrier R p a) r
      * asShiftH a (ZMod.castHom (dvd_refl p) R (Multiplicative.toAdd k))
        (castHom_pow (p := p) (Multiplicative.toAdd k)) t
  rw [map_mul]
  congr 1
  rw [show algebraMap R (asCarrier R p a) r = AdjoinRoot.of (ASpoly R p a) r from rfl]
  rw [asShiftH_of]

/-- **(己) 源 `proposition-0-6(b)` 全一般形** ✓✅：**任意特征 `p` 的交换环** ✓（**非域亦可** ✓）。 -/
theorem asCarrier_isGaloisWithGroup' {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (a : R) :
    IsGaloisWithGroup R (asCarrier R p a) (Multiplicative (ZMod p)) (asCarrier_hRG' a) := by
  let _inst : Nontrivial R := nontrivial_of_charP (R := R) (p := p)
  exact ⟨asCarrierMSA_faithful a, asCarrier_smul_algebraMap a,
    delta_bijective_of_moment a (asCarrier_hRG' a)⟩

end UnconditionalRingTier345

#print axioms nontrivial_of_charP
#print axioms asCarrier_of_eq_zero
#print axioms asCarrier_of_injective
#print axioms asCarrierMSA_faithful
#print axioms asCarrier_hRG'
#print axioms asCarrier_isGaloisWithGroup'


/-! ### 4.129 🔴🔴 **T6-F 第一口：分裂档实现 ＋ (c) 缺口的二分精确化**（第 346 轮）
—— 子目标 (c) 的**分裂支**落库 ✓ ＋ **缺口缩到单一二分命题** ✓

**靶** ✓：(c)（`RealizationProperty` ✓）的**分裂档** —— 源 `proposition-0-5(e)` ✓ 覆盖**任意** `C_p`-Galois 代数
（`L` **不必是域** ✗，可为**域之积** ✓ —— `raw/Saltman1982.tex:106` ✓ 逐字「here and in the rest of the paper,
`L` is not necessarily a field. Of course, `L` is the direct sum of fields」✓）。

**落成两件** ✓✅：**(甲)** **`realization_Cp_split`** ✓✅ —— 给定**分裂模型侧**
**`Nonempty (L ≃ₐ[K] (ZMod p → K))`** ✓ ⟹ **`∃ φ A, algebraMap = φ.toRingHom ∧ L ≃ₐ[K] K ⊗_{F[x]} S`** ✓✅
（**取 `φ := Polynomial.aeval 0`** ✓ ⟹ **`a = 0` 支** ✓）；
**(乙)** **`realization_Cp_of_dichotomy`** ✓✅ —— **二分命题**（**未证** ✗）⟹ **`RealizationPropertyExplicit F C_p F[x] S`** ✓✅。

**机制（(甲)，三步复合 ✓，全为本工程已落件）** ✓：**`φ := aeval 0`** ✓ ⟹ `algebraMap F[x] K X = 0` ✓ ⟹
**§4.114** ✓ 给 **`K ⊗_{F[x]} S ≃ₐ[K] asCarrier K p 0`** ✓ ⟹ **§4.122** ✓ 给
**`asCarrier K p 0 ≃ₐ[K] (ZMod p → K)`** ✓（取 `.symm` ✓）⟹ 与 `hsplit` 的 `e` 复合 ✓✅。
**⚠ 本件不用 `hgal`／`hKL`** ✗ —— 分裂支的**实现**只需**模型侧同构** ✓（**判据本身的假设**在分支内**未被使用** ✓）。

**机制（(乙)，二分 ✓）** ✓：**二分假设** ＝ **「`C_p`-Galois 代数 ＝ 有限域（`IsDomain` ＋ `Module.Finite`）或分裂（`≅ K^p`）」** ✓
（**登记假设** ✓，见 `wiki/hyp-cp-galois-dichotomy.md` ✓）⟹ 两支分别由 **§4.120** ✓（域档 ✓）与 **(甲)** ✓（分裂档 ✓）供给 ✓
⟹ **`RealizationPropertyExplicit`** ✓✅ —— **即 (c) 只欠这一个二分命题** ✓。

**⚠ 工艺（一条，入 §5.1）** ✓：**(#59)** **张量同构的方向** ✗：**`asCarrier_tensorProduct` 的原方向是
`K ⊗_R S ≃ₐ[K] asCarrier K p (algebraMap a)`** ✓ ⟹ 取 **`.symm`** ✓ 后才是
**`asCarrier ≃ₐ[K] K ⊗_R S`** ✓（**复合时勿再取一次 `.symm`** ✗ —— **本轮实测** ✓，与 §4.120 的 `ht` 用法同 ✓）。

**🔴 不声称** ✗：**不**声称**二分命题**为真 ✗（**登记假设** ✓，**未证** ✗，**真值未定** ⚠）；
**不**声称 `RealizationProperty`（源形 ✓）已证 ✗（**本件只把它归约到二分** ✓）；
**不**声称 **`L ≅ K^p`** 可自证 ✗（**缺外部理论** ✓ —— §300 ✓：**mathlib 无「Galois 代数有限投射」＋「有限维交换代数 ＝ 局部积」** ✗）；
**不**声称 `IsGenericExtension` 有实例 ✗；**不**声称源 `theorem-1-2`／`theorem-2-1`／`theorem-5-1` 已证 ✗。 -/

section SplitCaseAndDichotomy346

open ABGV52.BTier

/-- **(甲) 分裂档实现** ✓：给定 **`L ≃ₐ[K] (ZMod p → K)`**（分裂模型侧 ✓）⟹
**`∃ φ A, algebraMap = φ.toRingHom ∧ L ≃ₐ[K] K ⊗_{F[x]} S`** ✓（**取 `φ := aeval 0`** ✓）。 -/
theorem realization_Cp_split {F : Type} [Field F] {p : ℕ} (hp : p.Prime) [CharP F p]
    [NeZero p] (K : Type) [Field K] [Algebra F K]
    (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [MulSemiringAction (Multiplicative (ZMod p)) L]
    (hsplit : Nonempty (L ≃ₐ[K] (ZMod p → K))) :
    ∃ (φ : Polynomial F →ₐ[F] K) (A : Algebra (Polynomial F) K),
      (@Algebra.algebraMap (Polynomial F) K _ _ A : Polynomial F →+* K) = φ.toRingHom ∧
      letI : Algebra (Polynomial F) K := A
      Nonempty (L ≃ₐ[K] (TensorProduct (Polynomial F) K
        (asCarrier (Polynomial F) p Polynomial.X))) := by
  classical
  let _inst : Fact p.Prime := ⟨hp⟩
  let _inst2 : CharP K p :=
    charP_of_injective_algebraMap (algebraMap_injective_of_field (K := F) (L := K)) p
  refine ⟨Polynomial.aeval (0 : K),
    ((Polynomial.aeval (0 : K) : Polynomial F →ₐ[F] K)).toRingHom.toAlgebra, rfl, ?_⟩
  let _inst : Algebra (Polynomial F) K :=
    ((Polynomial.aeval (0 : K) : Polynomial F →ₐ[F] K)).toRingHom.toAlgebra
  have hX : (algebraMap (Polynomial F) K Polynomial.X) = (0 : K) := by
    show (Polynomial.aeval (0 : K) : Polynomial F →ₐ[F] K) Polynomial.X = 0
    simp
  obtain ⟨e⟩ := hsplit
  obtain ⟨e0⟩ := asCarrier_zero_algEquiv_pi K (p := p)
  have ht := (asCarrier_tensorProduct (R := Polynomial F) (K := K) p Polynomial.X).symm
  rw [hX] at ht
  exact ⟨e.trans (e0.symm.trans ht)⟩

/-- **(乙) (c) 缺口的二分精确化** ✓：**二分命题**（**登记假设** ✓，**未证** ✗）⟹
**`RealizationPropertyExplicit F C_p F[x] S`** ✓✅。 -/
theorem realization_Cp_of_dichotomy {F : Type} [Field F] {p : ℕ} (hp : p.Prime) [CharP F p]
    [NeZero p]
    (hdich : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction (Multiplicative (ZMod p)) L]
      (hKL : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : L), g • (r • t) = r • (g • t)),
      IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL →
      (IsDomain L ∧ Module.Finite K L) ∨ Nonempty (L ≃ₐ[K] (ZMod p → K))) :
    RealizationPropertyExplicit F (Multiplicative (ZMod p)) (Polynomial F)
      (asCarrier (Polynomial F) p Polynomial.X) := by
  intro K _ _ L _ _ _ _ _ hKL hgal
  rcases hdich K L hKL hgal with ⟨hdom, hfin⟩ | hsplit
  · let _inst : IsDomain L := hdom
    let _inst2 : Module.Finite K L := hfin
    exact realization_Cp_domain (F := F) (p := p) hp K L hKL hgal
  · exact realization_Cp_split (F := F) (p := p) hp K L hsplit

end SplitCaseAndDichotomy346

#print axioms realization_Cp_split
#print axioms realization_Cp_of_dichotomy


/-! ### 4.130 🔴🔴🔴 **条件形源 `theorem-1-2(a)`：二分假设下三款齐**（第 347 轮）
—— **源 `theorem-1-2(a)` 的**条件形**落库** ✓✅（**唯一未证件 ＝ 二分命题** ⚠ —— [[hyp-cp-galois-dichotomy]] ✓）

**靶** ✓：**源 `theorem-1-2(a)`** ✓（`raw/Saltman1982.tex:166–175` ✓）：**`R = F[x]`** ✓、**`S = R{y^p − y − x}`** ✓、
**`G = C_p`** ✓ ⟹ **`S/R` 是 `F` 上 `C_p` 的 generic extension** ✓（**def-1-1 三款** ✓）。

**落成两件** ✓✅：**(甲)** **`isGenericExtension_Cp_of_dichotomy`** ✓✅ —— **二分假设** ✓（§4.129 ✓）⟹
**`IsGenericExtension F (Multiplicative (ZMod p)) (Polynomial F) (asCarrier (Polynomial F) p Polynomial.X) …`** ✓✅
（**＝ 源 `theorem-1-2(a)` 的结论** ✓）；**(乙)** **`nonempty_genericExtensionWitness_Cp_of_dichotomy`** ✓✅ ——
**二分假设 ⟹ `Nonempty (GenericExtensionWitness F (Multiplicative (ZMod p)))`** ✓✅（**`C_p` 档的见证形** ✓）。

**机制（三款齐 ✓，全为本工程已落件）** ✓：**(a)** **`polynomial_isLocalizationAway F`** ✓（§4.113 ✓：
`R = F[x]` 是 `Localization.Away 1` ✓）；**(b)** **`asCarrier_isGaloisWithGroup'`** ✓（§4.128 ✓ —— **任意交换环** ✓）；
**(c)** **`realizationProperty_of_realizationPropertyExplicit`** ✓（`GenericExtension.lean:746` ✓ —— **显式形 ⟹ 旧形** ✓）
∘ **`realization_Cp_of_dichotomy`** ✓（§4.129 ✓）⟹ **`RealizationProperty`** ✓ ⟹
**`isGenericExtension_of_clauses`** ✓（§4.110 ✓）／**`genericExtensionWitness_of_clauses`** ✓（§4.110 ✓）收口 ✓✅。

**⚠ 意义** ✓：**源 `theorem-1-2(a)` 的**全部内容**已形式化** ✓ —— **只差二分命题** ⚠（**登记假设** ✓，**未证** ✗）；
即 **「源 `theorem-1-2(a)` ⟺ 二分」** ✓（**归纳到底** ✓）。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#60)** **`asCarrierMSA` 须注册为局部实例** ✗ ——
**凡语句中出现 `g • t`（`asCarrier` 档 ✓）者，须 `attribute [local instance] asCarrierMSA`** ✓
（**否则报 `MulSemiringAction` 合成失败** ✗）；**(#61)** **`asCarrier_hRG'`／`asCarrier_isGaloisWithGroup'` 的实参序** ✗：
其 `R` **隐式** ✓、`a` **显式** ✓ ⟹ 须写 **`(R := Polynomial F) (p := p) Polynomial.X`** ✓
（**写成 `(Polynomial F) (p := p)` 会把 `Polynomial F` 当作 `a` ⟹ 报 `CommRing Type`** ✗，**本轮实测** ✓）；
且**语句含 `g • t` 时不能用 `(hp : p.Prime)`** ✗ ⟹ **须 `[Fact p.Prime]`** ✓（**§5.1 #27 同族** ✓）。

**🔴 不声称** ✗：**不**声称**二分命题**为真 ✗（**登记假设** ✓，**真值未定** ⚠）；
**不**声称源 `theorem-1-2(a)` **无条件**成立 ✗（**本件为条件形** ✓）；
**不**声称源 `theorem-1-2(b)`（`n` 档 ✓）／`theorem-2-1`／`theorem-5-1` 已证 ✗；
**不**声称 `RealizationProperty`（源形 ✓）**无条件**已证 ✗；**不**声称源 `proposition-0-6(a)`／`(c)` 已证 ✗。 -/

section ConditionalTheorem12347

attribute [local instance] asCarrierMSA

open ABGV52.BTier

/-- **(甲) 条件形 `IsGenericExtension`** ✓✅：**二分假设** ⟹ **源 `theorem-1-2(a)` 的结论** ✓。 -/
theorem isGenericExtension_Cp_of_dichotomy {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    [CharP F p] [NeZero p]
    (hdich : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction (Multiplicative (ZMod p)) L]
      (hKL : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : L), g • (r • t) = r • (g • t)),
      IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL →
      (IsDomain L ∧ Module.Finite K L) ∨ Nonempty (L ≃ₐ[K] (ZMod p → K))) :
    IsGenericExtension F (Multiplicative (ZMod p)) (Polynomial F)
      (asCarrier (Polynomial F) p Polynomial.X) (asCarrier_hRG' (R := Polynomial F) (p := p) Polynomial.X) :=
  isGenericExtension_of_clauses
    (asCarrier_hRG' (R := Polynomial F) (p := p) Polynomial.X)
    (polynomial_isLocalizationAway F)
    (asCarrier_isGaloisWithGroup' (R := Polynomial F) (p := p) Polynomial.X)
    (realizationProperty_of_realizationPropertyExplicit
      (realization_Cp_of_dichotomy (F := F) (p := p) (Fact.out : p.Prime) hdich))

/-- **(乙) 见证形** ✓✅：**二分假设 ⟹ `Nonempty (GenericExtensionWitness F C_p)`** ✓（**`C_p` 档的见证** ✓）。 -/
theorem nonempty_genericExtensionWitness_Cp_of_dichotomy {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    [CharP F p] [NeZero p]
    (hdich : ∀ (K : Type) [Field K] [Algebra F K]
      (L : Type) [CommRing L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
      [MulSemiringAction (Multiplicative (ZMod p)) L]
      (hKL : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : L), g • (r • t) = r • (g • t)),
      IsGaloisWithGroup K L (Multiplicative (ZMod p)) hKL →
      (IsDomain L ∧ Module.Finite K L) ∨ Nonempty (L ≃ₐ[K] (ZMod p → K))) :
    Nonempty (GenericExtensionWitness F (Multiplicative (ZMod p))) :=
  ⟨genericExtensionWitness_of_clauses
    (asCarrier_hRG' (R := Polynomial F) (p := p) Polynomial.X)
    (polynomial_isLocalizationAway F)
    (asCarrier_isGaloisWithGroup' (R := Polynomial F) (p := p) Polynomial.X)
    (realizationProperty_of_realizationPropertyExplicit
      (realization_Cp_of_dichotomy (F := F) (p := p) (Fact.out : p.Prime) hdich))⟩

end ConditionalTheorem12347

#print axioms isGenericExtension_Cp_of_dichotomy
#print axioms nonempty_genericExtensionWitness_Cp_of_dichotomy


/-! ### 4.131 🔴 **T6-F 第二口：Kummer 档地基（源 `proposition-0-6(a)` 的载体链）**（第 348 轮）
—— **`C_n` 档（乘法／Kummer 档）的载体 ＋ 幂基 ＋ 秩 ＋ 移位** ✓（**路线（丙″）的乘法类比** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓（`raw/Saltman1982.tex:142` ✓）：**`char F ∤ n`** ✓、**`ρ(n) ∈ F`** ✓、
**`a` 是 `R` 的单位** ✓ ⟹ **`S = R{y^n − a}` 是 `C_n`-Galois** ✓ ——
**本件落其**载体链**（Kummer 载体 ＋ 幂基 ＋ 秩 ＋ 移位自同态 ✓），**与 AS 档 §4.79／§4.91 对偶** ✓。

**落成七件** ✓✅：**(甲)** **`kummerCarrier R n a := AdjoinRoot (X^n − C a)`** ✓✅（源 `R{y^n − a}` ✓）；
**(乙)** **`kpoly_monic`** ✓✅（**`n ≥ 1`** ✓）＋ **`kpoly_natDegree`** ✓✅（**`= n`** ✓）；
**(丙)** **`kummerBasis`** ✓✅（**幂基 `{1, y, …, y^{n−1}}`** ✓）＋ **`kummer_finrank`** ✓✅（**秩 `= n`** ✓）；
**(丁)** **`kummer_subst`** ✓✅ —— **代入 `X ↦ C ρ · X` **保持定义多项式** ✓**（`ρ^n = 1` ✓）：
**`X^n − C a ↦ C(ρ^n) X^n − C a = X^n − C a`** ✓ —— **与 AS 档 `X ↦ X + C k`（差一常数 ✓）对偶** ✓；
**(戊)** **`kummerShift_eval`** ✓✅（**`eval₂` 义务** ✓：`of ρ · root` 满足定义关系 ✓ —— 由 **`root^n = of a`** ✓
（**`AdjoinRoot.eval₂_root`** ✓）＋ **`(of ρ)^n = of 1`** ✓）；
**(己)** **`kummerShiftH`** ✓✅ —— **载体上 `y ↦ ρ · y`** ✓（源 `C_n`-作用的**生成端** ✓）；
**(庚)** **`kummerShiftH_of`** ✓✅（**固定系数** ✓）＋ **`kummerShiftH_root`** ✓✅（**根 ↦ `ρ · root`** ✓）。

**⚠ 与 AS 档的关键差别（**路线（丙″）在乘法档为何更易** ✓）** ✓：**(i)** **定义多项式被移位固定** ✓
（AS 档差一常数 `k^p − k` ✓）；**(ii)** **节点差为单位** ✓ —— 节点 `y ρ^k` ✓，差
**`y ρ^{k'}(ρ^{k−k'} − 1)`** ✓：**`y` 单位** ✓ 由 **`a` 单位** ✓（`y^n = a` ✓），
**`ρ^m − 1` 单位** ✓ 由 **`F` 是域** ✓（**`0 < m < n` ⟹ `ρ^m ≠ 1` ⟹ `ρ^m − 1 ≠ 0`** ✓ ⟹ **`F` 中为单位** ✓
⟹ **其在 `R` 中的像是单位** ✓）—— **故 Kummer 档的 `det` 为单位可望同法落地** ✓（**下一手** ✗）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#62)** **`Polynomial.monic_X_pow_sub_C` 要 `n ≠ 0`** ✗（**非** `1 ≤ n` ✗）⟹
由 `hn : 1 ≤ n` 用 **`by omega`** ✓ 转写 ✓；**(#63)** **`Polynomial.natDegree_X_pow_sub_C` 无该假设** ✗
（但须 **`[Nontrivial R]`** ✓，且**未用的显式假设须 `_` 前缀** ✓ —— **§5.1 #2** ✓）；
**(#64)** **`Polynomial.aeval_C` 给 `algebraMap R (Polynomial R) a`** ✗ ⟹ 须 **`← Polynomial.C_eq_algebraMap`** ✓ 桥接
（**`AdjoinRoot.aeval_root` 不存在** ✗ ⟹ 用 **`AdjoinRoot.eval₂_root`** ✓ 取 `sub_eq_zero.mp` ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**只落载体链** ✓ —— **判据 ＋ 移位自同构 ＋ `C_n`-作用 ＋ 实现均未落** ✗）；
**不**声称移位是**自同构** ✗（**只落自同态** ✓）；**不**声称源 `theorem-1-2(b)` 已证 ✗；
**不**声称源 `proposition-0-6(c)`（张量积档 ✓）已证 ✗。 -/

section KummerCarrierCore348

/-- **Kummer 载体** ✓（源 `R{y^n − a}` ✓）：`R[y]/(y^n − a)` ✓。 -/
abbrev kummerCarrier (R : Type u) [CommRing R] (n : ℕ) (a : R) : Type u :=
  AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)

/-- **首一性** ✓（`n ≥ 1` ✓）。 -/
theorem kpoly_monic {R : Type u} [CommRing R] {n : ℕ} (hn : 1 ≤ n) (a : R) :
    ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a).Monic :=
  Polynomial.monic_X_pow_sub_C a (by omega)

/-- **次数** ✓。 -/
theorem kpoly_natDegree {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (_hn : 1 ≤ n) (a : R) :
    ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a).natDegree = n :=
  Polynomial.natDegree_X_pow_sub_C

/-- **Kummer 幂基** ✓：`{1, y, …, y^{n−1}}` ✓。 -/
noncomputable def kummerBasis {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n)
    (a : R) : Module.Basis (Fin n) R (kummerCarrier R n a) :=
  (AdjoinRoot.powerBasisAux' (kpoly_monic (R := R) hn a)).reindex
    (finCongr (kpoly_natDegree (R := R) hn a))

/-- **Kummer 载体的秩 ＝ `n`** ✓。 -/
theorem kummer_finrank {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) (a : R) :
    Module.finrank R (kummerCarrier R n a) = n := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' (kpoly_monic (R := R) hn a)),
    Fintype.card_fin, kpoly_natDegree (R := R) hn a]

/-- **代入恒等式** ✓：`X ↦ C ρ · X` **保持** `X^n − C a`（当 `ρ^n = 1` ✓）。 -/
theorem kummer_subst {R : Type u} [CommRing R] (a ρ : R) {n : ℕ} (hρ : ρ ^ n = 1) :
    Polynomial.aeval ((Polynomial.C ρ) * (Polynomial.X : Polynomial R))
        ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
      = (Polynomial.X : Polynomial R) ^ n - Polynomial.C a := by
  rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, ← Polynomial.C_eq_algebraMap]
  rw [mul_pow, ← Polynomial.C_pow, hρ, Polynomial.C_1, one_mul]

/-- **载体上的义务** ✓（`eval₂` 形 ✓）：`of ρ · root` 满足定义关系 ✓。 -/
theorem kummerShift_eval {R : Type u} [CommRing R] {n : ℕ} (a ρ : R) (hρ : ρ ^ n = 1) :
    Polynomial.eval₂
      (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ρ
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) = 0 := by
  have hroot : (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ n
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) a := by
    have h := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    mul_pow, ← map_pow, hρ, map_one, one_mul, hroot, sub_self]

/-- **Kummer 移位自同态** ✓：**载体上 `y ↦ ρ · y`** ✓（`ρ^n = 1` ✓）。 -/
noncomputable def kummerShiftH {R : Type u} [CommRing R] {n : ℕ} (a ρ : R) (hρ : ρ ^ n = 1) :
    kummerCarrier R n a →+* kummerCarrier R n a :=
  AdjoinRoot.lift (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
    (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ρ
      * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
    (kummerShift_eval a ρ hρ)

/-- **计算件 ①** ✓：移位**固定系数** ✓。 -/
theorem kummerShiftH_of {R : Type u} [CommRing R] {n : ℕ} (a ρ : R) (hρ : ρ ^ n = 1) (r : R) :
    kummerShiftH a ρ hρ
        (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r)
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r :=
  AdjoinRoot.lift_of (kummerShift_eval a ρ hρ)

/-- **计算件 ②** ✓：移位把根送到 `ρ · root` ✓。 -/
theorem kummerShiftH_root {R : Type u} [CommRing R] {n : ℕ} (a ρ : R) (hρ : ρ ^ n = 1) :
    kummerShiftH a ρ hρ (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ρ
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) :=
  AdjoinRoot.lift_root (kummerShift_eval a ρ hρ)

end KummerCarrierCore348

#print axioms kpoly_monic
#print axioms kpoly_natDegree
#print axioms kummer_finrank
#print axioms kummer_subst
#print axioms kummerShift_eval
/-! ### 4.132 🔴 **T6-F 第二口（续）：Kummer 移位自同构 ＋ 复合律**（第 349 轮）
—— **Kummer 档第二步** ✓（**§4.82／§4.84 的乘法类比** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓（`raw/Saltman1982.tex:142` ✓）的**移位群结构** ✓ ——
**`y ↦ ρ · y` 构成 `C_n`-作用的生成端** ✓（**下一步** ✗：**`C_n`-作用 ＋ 判据** ✓）。

**落成三件** ✓✅：**(甲)** **`kummerShiftH_comp`** ✓✅ —— **`φ_ρ ∘ φ_{ρ'} = φ_{ρ·ρ'}`** ✓
（**根支 ＋ 系数支** ✓，与 §4.84 的 `asShiftHMSA_comp` 同型 ✓）；
**(乙)** **`kummerShiftH_one`** ✓✅ —— **`φ_1 = id`** ✓（`y ↦ 1 · y = y` ✓，与 §4.84 的 `asShiftH_zero` 对偶 ✓）；
**(丙)** **`kummerShiftH_bijective`** ✓✅ —— **`ρ` 为单位 ⟹ `φ_ρ` 是自同构** ✓
（**逆 ＝ `φ_{ρ⁻¹}`** ✓；**两边复合均为恒等** ✓）。

**机制（(丙)）** ✓：**两边复合** ✓（**系数支** ✓：移位固定系数 ✓；**根支** ✓：
`root ↦ ρ⁻¹·(ρ·root) = root` ✓）⟹ **`hL : f ∘ g = id`** ✓ ⟹ **单射** ✓（`x = g(f x) = g(f y) = y` ✓）；
**`hR : g ∘ f = id`** ✓ ⟹ **满射** ✓（`y = f (g y)` ✓）✓。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#65)** **依赖位重写须避开** ✗ —— 复合法则的右端 `kummerShiftH a (ρ * ρ') _`
**不能**把 `ρ * ρ'` 改写为 `1` ✗（**证明项的类型依赖该参数** ✓ —— **§5.1 的"依赖位重写"族** ✓，§4.84 ✓ 同款）；
**正解 ＝ 在载体内算积** ✓：**`← map_mul`** ✓ ＋ **`Units.inv_mul`／`Units.mul_inv`** ✓ ＋ `map_one` ✓；
**(#66)** **`simp only` 的未用参数计警告** ✗（`linter.unusedSimpArgs` ✓ —— 实测 `kummerShiftH_of`／`map_mul` 被报未用 ✓）
⟹ **凡 `simp only` 参数表须按提示裁剪** ✓；且**大 `simp only` 表（含 `←` 规则）易不收敛** ✗ ⟹
**改逐步 `rw`** ✓（**本轮实测** ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**只落移位群结构** ✓ —— **`C_n`-作用 ＋ 判据 ＋ 实现未落** ✗）；
**不**声称 `IsPrimitiveRoot ρ n` 已用 ✗（**本件只须 `ρ^n = 1` ＋ `ρ` 单位** ✓ —— **单射性留给 `C_n`-作用件** ✗）；
**不**声称源 `theorem-1-2(b)` 已证 ✗；**不**声称源 `proposition-0-6(c)` 已证 ✗。 -/

section KummerShiftGroup349

/-- **(甲) 复合律** ✓：`φ_ρ ∘ φ_{ρ'} = φ_{ρ·ρ'}` ✓（**根支 ＋ 系数支** ✓）。 -/
theorem kummerShiftH_comp {R : Type u} [CommRing R] {n : ℕ} (a ρ ρ' : R) (hρ : ρ ^ n = 1)
    (hρ' : ρ' ^ n = 1) (hρρ' : (ρ * ρ') ^ n = 1) :
    (kummerShiftH a ρ hρ).comp (kummerShiftH a ρ' hρ')
      = kummerShiftH a (ρ * ρ') hρρ' := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span
    {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (kummerShiftH a ρ hρ)
        ((kummerShiftH a ρ' hρ')
          ((Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)))
      = (kummerShiftH a (ρ * ρ') hρρ')
          ((Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r))
    rw [show (Ideal.Quotient.mk (Ideal.span
          {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)
        = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
    rw [kummerShiftH_of, kummerShiftH_of, kummerShiftH_of]
  · show (kummerShiftH a ρ hρ)
        ((kummerShiftH a ρ' hρ')
          ((Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)))
      = (kummerShiftH a (ρ * ρ') hρρ')
          ((Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X))
    rw [show (Ideal.Quotient.mk (Ideal.span
          {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)
        = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) from rfl]
    simp only [kummerShiftH_root, kummerShiftH_of, map_mul]
    ring

/-- **(乙) 单位移位 ＝ 恒等** ✓：`ρ = 1` 时 `y ↦ 1 · y = y` ✓。 -/
theorem kummerShiftH_one {R : Type u} [CommRing R] {n : ℕ} (a : R) (h1 : (1 : R) ^ n = 1) :
    kummerShiftH a (1 : R) h1 = RingHom.id (kummerCarrier R n a) := by
  refine Ideal.Quotient.ringHom_ext (I := Ideal.span
    {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)}) ?_
  refine Polynomial.ringHom_ext ?_ ?_
  · intro r
    show (kummerShiftH a 1 h1)
        ((Ideal.Quotient.mk (Ideal.span
          {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r))
      = (RingHom.id (kummerCarrier R n a))
          ((Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r))
    rw [show (Ideal.Quotient.mk (Ideal.span
          {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)
        = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
    simp only [kummerShiftH_of, RingHom.id_apply]
  · show (kummerShiftH a 1 h1)
        ((Ideal.Quotient.mk (Ideal.span
          {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X))
      = (RingHom.id (kummerCarrier R n a))
          ((Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X))
    rw [show (Ideal.Quotient.mk (Ideal.span
          {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)
        = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) from rfl]
    simp only [kummerShiftH_root, map_one, one_mul, RingHom.id_apply]

/-- **(丙) 移位是自同构** ✓✅（`ρ` 为单位 ✓）：**两边复合均为恒等** ✓
（**⚠ 避依赖位重写** ✗：`ρ · ρ⁻¹` 的化简**在载体内做** ✓ —— `← map_mul` ＋ `Units.inv_mul` ✓）。 -/
theorem kummerShiftH_bijective {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (hρi : (((ρ⁻¹ : Rˣ) : R)) ^ n = 1) :
    Function.Bijective (kummerShiftH a (ρ : R) hρ) := by
  have hleft : (kummerShiftH a (ρ : R) hρ).comp (kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi)
      = RingHom.id (kummerCarrier R n a) := by
    refine Ideal.Quotient.ringHom_ext (I := Ideal.span
      {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)}) ?_
    refine Polynomial.ringHom_ext ?_ ?_
    · intro r
      show (kummerShiftH a (ρ : R) hρ)
          ((kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi)
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)))
        = (RingHom.id (kummerCarrier R n a))
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r))
      rw [show (Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)
          = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
      simp only [kummerShiftH_of, RingHom.id_apply]
    · show (kummerShiftH a (ρ : R) hρ)
          ((kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi)
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)))
        = (RingHom.id (kummerCarrier R n a))
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X))
      rw [show (Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)
          = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) from rfl]
      rw [kummerShiftH_root, map_mul, kummerShiftH_of, kummerShiftH_root]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rfl
  have hright : (kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi).comp (kummerShiftH a (ρ : R) hρ)
      = RingHom.id (kummerCarrier R n a) := by
    refine Ideal.Quotient.ringHom_ext (I := Ideal.span
      {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)}) ?_
    refine Polynomial.ringHom_ext ?_ ?_
    · intro r
      show (kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi)
          ((kummerShiftH a (ρ : R) hρ)
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)))
        = (RingHom.id (kummerCarrier R n a))
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r))
      rw [show (Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.C r)
          = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
      simp only [kummerShiftH_of, RingHom.id_apply]
    · show (kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi)
          ((kummerShiftH a (ρ : R) hρ)
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)))
        = (RingHom.id (kummerCarrier R n a))
            ((Ideal.Quotient.mk (Ideal.span
              {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X))
      rw [show (Ideal.Quotient.mk (Ideal.span
            {((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)})) (Polynomial.X)
          = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) from rfl]
      rw [kummerShiftH_root, map_mul, kummerShiftH_of, kummerShiftH_root]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
      rfl
  have hL : ∀ z : kummerCarrier R n a,
      (kummerShiftH a (ρ : R) hρ) ((kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi) z) = z := by
    intro z
    have h := congrArg
      (fun (f : kummerCarrier R n a →+* kummerCarrier R n a) => f z) hleft
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  have hR : ∀ z : kummerCarrier R n a,
      (kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi) ((kummerShiftH a (ρ : R) hρ) z) = z := by
    intro z
    have h := congrArg
      (fun (f : kummerCarrier R n a →+* kummerCarrier R n a) => f z) hright
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  exact ⟨fun x y hxy => by rw [← hR x, ← hR y, hxy],
    fun y => ⟨(kummerShiftH a ((ρ⁻¹ : Rˣ) : R) hρi) y, hL y⟩⟩

end KummerShiftGroup349

/-! ### 4.133 🔴 **T6-F 第二口（再续）：Kummer 根的幂与单位性**（第 350 轮）
—— **Kummer 档第三步的承重前置** ✓（**`C_n`-作用的幂端 ＋ 判据的节点差** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓（`a` **为单位** ✓）—— 本件落 **`ρ` 的幂在移位下的作用** ✓
＋ **`root` 的单位性** ✓（**判据的"节点差为单位"一步所需** ✓）。

**落成三件** ✓✅：**(甲)** **`kummerRoot_isUnit`** ✓✅ —— **`a` 单位（＋ `n ≥ 1`）⟹ `root` 是单位** ✓
（**`root · root^{n−1} = root^n = of a`** ✓ 为单位 ⟹ **`isUnit_of_mul_isUnit_left`** ✓）；
**(乙)** **`kummerShiftH_pow_of`** ✓✅ —— **`φ_ρ^m` 仍固定系数** ✓（归纳 ✓）；
**(丙)** **`kummerShiftH_pow_root`** ✓✅ —— **`φ_ρ^m (root) = of (ρ^m) · root`** ✓（归纳 ＋ §4.132 的根公式 ✓）。

**机制（(丙)）** ✓：**归纳步** ✓：`φ^{m+1} root = φ^m (φ root)` ✓（`pow_succ` ＋ `show` 展开 ✓ ——
**⚠ `φ^m * φ` 的取值须 `show` 显式给出** ✗，**无 `RingHom.mul_apply`** ✗）⟹ **`kummerShiftH_root`** ✓ ⟹
**`map_mul`** ✓ ＋ **`kummerShiftH_pow_of`** ✓ ＋ **归纳假设** ✓ ⟹ **`← mul_assoc` ＋ `← map_mul` ＋ `← pow_succ'`** ✓ 收口 ✓
（**⚠ 须 `pow_succ'` 而非 `pow_succ`** ✗ —— 前者给 `ρ * ρ^m` ✓ 后者给 `ρ^m * ρ` ✗）。

**⚠ 用途** ✓：**(甲)** 是**判据的节点差** `y ρ^{k'}(ρ^{k−k'} − 1)` **为单位** ✓ 的一半 ✓；
**(丙)** 是 **`C_n`-作用**（**下一步** ✗）的**幂端** ✓ —— **故本件为 `C_n`-作用与判据的公共前置** ✓。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#67)** **`RingHom.mul_apply` 不存在** ✗ ⟹ **`φ^m * φ` 的取值须 `show` 显式展开** ✓
（`(f * g) x = f (g x)` 由 **defeq** ✓ 而非引理 ✓）；**(#68)** **`pow_succ` 与 `pow_succ'` 的方向** ✗ ——
**`φ^(m+1) = φ^m * φ`** ✓（`pow_succ` ✓）而 **`ρ^(m+1) = ρ * ρ^m`** ✓（`pow_succ'` ✓）⟹
**同一证明内两者须分别取用** ✓（**实测**：用错即报 "Did not find an occurrence" ✗）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**只落幂与单位性** ✓ —— **`C_n`-作用 ＋ 判据 ＋ 实现未落** ✗）；
**不**声称 **`C_n`-作用已构造** ✗；**不**声称 **`IsPrimitiveRoot ρ n` 已用** ✗；**不**声称源 `theorem-1-2(b)` 已证 ✗。 -/

section KummerPowUnits350

/-- **(甲) `root` 是单位** ✓（`a` 单位 ＋ `n ≥ 1` ✓）：`root * root^{n−1} = of a` ✓ 为单位 ⟹ `root` 为单位 ✓。 -/
theorem kummerRoot_isUnit {R : Type u} [CommRing R] {n : ℕ} (hn : 1 ≤ n) {a : R}
    (ha : IsUnit a) :
    IsUnit (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) := by
  have hroot : (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ n
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) a := by
    have h := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  have hmul : (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      * (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (n - 1)
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) a := by
    rw [← pow_succ', Nat.sub_add_cancel hn, hroot]
  have hunit : IsUnit ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      * (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (n - 1)) := by
    rw [hmul]
    exact ha.map _
  exact isUnit_of_mul_isUnit_left hunit

/-- **(乙) 幂保持系数** ✓：`φ_ρ^m (of r) = of r` ✓（归纳 ✓）。 -/
theorem kummerShiftH_pow_of {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (m : ℕ) (r : R) :
    ((kummerShiftH a (ρ : R) hρ) ^ m)
        (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r)
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ]
    show ((kummerShiftH a (ρ : R) hρ) ^ m)
        ((kummerShiftH a (ρ : R) hρ)
          (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r)) = _
    rw [kummerShiftH_of, ih]

/-- **(丙) 幂迭代** ✓：`φ_ρ^m (root) = of (ρ^m) · root` ✓（**归纳 ＋ 复合律** ✓）。 -/
theorem kummerShiftH_pow_root {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (m : ℕ) :
    ((kummerShiftH a (ρ : R) hρ) ^ m)
        (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ((ρ : R) ^ m)
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    show ((kummerShiftH a (ρ : R) hρ) ^ m)
        ((kummerShiftH a (ρ : R) hρ)
          (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))) = _
    rw [kummerShiftH_root, map_mul, kummerShiftH_pow_of, ih]
    rw [← mul_assoc, ← map_mul, ← pow_succ']

end KummerPowUnits350

/-! ### 4.134 🔴🔴 **T6-F 第二口（三续）：Kummer 载体的 `C_n`-作用**（第 351 轮）
—— **源 `proposition-0-6(a)` 的作用端落库** ✓（**§4.84 的乘法类比** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓（`raw/Saltman1982.tex:142` ✓）：**`S = R{y^n − a}` 上 `C_n` 的作用
`σ(y) = ρ · y`** ✓ —— **本件构造该作用** ✓（**判据 ＋ 实现仍欠** ✗）。

**落成四件** ✓✅：**(甲)** **`kummer_pow_coeff_pow`** ✓✅ —— **`((ρ^m))^n = 1`** ✓（**具名** ✓ ⟹
`smul` 的**证明项句法稳定** ✓ —— **本件的关键工艺** ✓）；**(乙)** **`kummerShiftH_congr`** ✓✅（同值同证 ✓，
**proof irrelevance** ✓）；**(丙)** **`kummerShiftH_congr_val`** ✓✅ —— **值相等 ⟹ 移位相等** ✓
（`subst` ＋ **proof irrelevance** ✓ —— **避依赖位重写** ✗）；**(丁)** **`kummerMSA`** ✓✅ ——
**`MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)`** ✓✅，`smul k x := φ_{ρ^{k.val}} x` ✓。

**机制（(丁) 的群律）** ✓：**(i)** **`one_smul`** ✓：`(1 : Multiplicative (ZMod n)).toAdd = 0` ✓ ⟹
`ρ^{(0).val} = ρ^0 = 1` ✓（`ZMod.val_zero` ✓ ＋ `pow_zero` ✓）⟹ **`kummerShiftH_one`** ✓（§4.132 ✓）⟹ `1 • x = x` ✓；
**(ii)** **`mul_smul`** ✓：**§4.132 的复合律** ✓ 给 `φ_{ρ^B} ∘ φ_{ρ^C} = φ_{ρ^B · ρ^C}` ✓；
**`ZMod.val_add`** ✓ ＋ **`pow_eq_pow_mod`** ✓ 给 **`ρ^{k.val + k'.val} = ρ^{(k+k').val}`** ✓
（`ZMod.val_add` ✓：`(k+k').val = (k.val + k'.val) % n` ✓）⟹ **值相等引理** ✓ 收口 ✓；
**(iii)** **`smul_zero／add／mul／one`** ✓ ＝ 环同态的相应定律 ✓（**一行各** ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#69)** **`smul` 的证明项须具名** ✗ —— 若把 `((ρ^m)^n = 1)` 的证明**内联** ✗，
则 `show`／`rw` 对其**无法句法匹配** ✗（且 `rw` 会因**证明项依赖被改写项**而报
**"motive is not type correct"** ✗）⟹ **正解 ＝ 提出具名引理 `kummer_pow_coeff_pow`** ✓
（**§5.1 #65／#67 同族 третья 命中** ✓）；
**(#70)** **值相等须走独立引理** ✗：**不得**直接 `rw [hpow]` 于含 `φ t h` 的项 ✗（**同上 motive 错** ✗）⟹
**正解 ＝ `kummerShiftH_congr_val`（`subst` ＋ proof irrelevance）** ✓ 再 `congrArg (fun f => f x)` ✓；
**(#71)** **`kummerShiftH_comp` 的实参须给足** ✗（`n` **与三个证明项** ✓ —— 否则报
"don't know how to synthesize implicit argument" ✗，**实测** ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**作用已构造** ✓，**判据 ＋ 实现未落** ✗）；
**不**声称作用**忠实** ✗（**须 `IsPrimitiveRoot ρ n`** ✗ —— **本件未用** ✗）；
**不**声称源 `theorem-1-2(b)`／`proposition-0-6(c)` 已证 ✗。 -/

section KummerMSA351

/-- **(甲) 幂系数的 `n` 次幂为 1** ✓（具名 ✓ —— 供 `smul` 的证明项**句法稳定** ✓）。 -/
theorem kummer_pow_coeff_pow {R : Type u} [CommRing R] {n : ℕ} (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (m : ℕ) : (((ρ : R)) ^ m) ^ n = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hρ, one_pow]

/-- **(乙) 移位只依赖系数的值** ✓（proof irrelevance ✓）。 -/
theorem kummerShiftH_congr {R : Type u} [CommRing R] {n : ℕ} (a t : R) (h1 : t ^ n = 1)
    (h2 : t ^ n = 1) : kummerShiftH a t h1 = kummerShiftH a t h2 :=
  congrArg (fun h => kummerShiftH a t h) (Subsingleton.elim h1 h2)

/-- **(乙′) 值相等 ⟹ 移位相等** ✓（`subst` ＋ proof irrelevance ✓ —— **避依赖位重写** ✗）。 -/
theorem kummerShiftH_congr_val {R : Type u} [CommRing R] {n : ℕ} (a : R) {t1 t2 : R}
    (h : t1 = t2) (h1 : t1 ^ n = 1) (h2 : t2 ^ n = 1) :
    kummerShiftH a t1 h1 = kummerShiftH a t2 h2 := by
  subst h
  exact kummerShiftH_congr a t1 h1 h2

/-- **(丙) `C_n`-作用** ✓✅：`k ↦ φ_{ρ^{k.val}}` ✓（**群律由 `ZMod.val_add` ＋ `pow_eq_pow_mod`** ✓）。 -/
@[instance_reducible] noncomputable def kummerMSA {R : Type u} [CommRing R] {n : ℕ} [NeZero n]
    (a : R) (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1) :
    MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a) where
  smul k x := kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd k).val)
    (kummer_pow_coeff_pow ρ hρ _) x
  one_smul x := by
    have h0 : (ρ : R) ^ ((0 : ZMod n).val) = 1 := by rw [ZMod.val_zero, pow_zero]
    have h1 : (1 : R) ^ n = 1 := one_pow n
    exact (congrArg (fun f => f x) (kummerShiftH_congr_val a h0 _ h1)).trans
      (congrArg (fun f => f x) (kummerShiftH_one a h1))
  mul_smul k k' x := by
    show kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd (k * k')).val)
        (kummer_pow_coeff_pow ρ hρ _) x
      = kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd k).val) (kummer_pow_coeff_pow ρ hρ _)
          (kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd k').val)
            (kummer_pow_coeff_pow ρ hρ _) x)
    have hBC : (((ρ : R) ^ (Multiplicative.toAdd k).val
        * (ρ : R) ^ (Multiplicative.toAdd k').val)) ^ n = 1 := by
      rw [← pow_add]
      exact kummer_pow_coeff_pow ρ hρ _
    have hcomp := kummerShiftH_comp (n := n) a ((ρ : R) ^ (Multiplicative.toAdd k).val)
      ((ρ : R) ^ (Multiplicative.toAdd k').val) (kummer_pow_coeff_pow ρ hρ _)
      (kummer_pow_coeff_pow ρ hρ _) hBC
    rw [← RingHom.comp_apply, hcomp]
    have hpow : (ρ : R) ^ (Multiplicative.toAdd k).val
          * (ρ : R) ^ (Multiplicative.toAdd k').val
        = (ρ : R) ^ (Multiplicative.toAdd (k * k')).val := by
      rw [← pow_add,
        show Multiplicative.toAdd (k * k')
          = Multiplicative.toAdd k + Multiplicative.toAdd k' from rfl,
        ZMod.val_add]
      exact pow_eq_pow_mod _ hρ
    exact congrArg (fun f => f x) (kummerShiftH_congr_val a hpow.symm _ _)
  smul_zero k := map_zero _
  smul_add k x y := map_add _ x y
  smul_mul k x y := map_mul _ x y
  smul_one k := map_one _

end KummerMSA351

/-! ### 4.135 🔴🔴 **T6-F 第二口（四续）：Kummer 档的 `of` 单射与作用忠实性**（第 352 轮）
—— **源 `proposition-0-6(a)` 的款①（忠实性）落库** ✓（**§4.86／§4.87 的乘法类比** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓ 的**款①** ✓ —— **`C_n`-作用的忠实性** ✓
（**⚠ 须 `IsPrimitiveRoot ρ n`** ✗ —— **乘法档的新增输入** ✓，AS 档无对应物 ✓）。

**落成三件** ✓✅：**(甲)** **`kummer_of_eq_zero`** ✓✅ —— **`of x = 0 ⟹ x = 0`** ✓（**与 §4.128 同法** ✓：
`C x %ₘ f = C x = 0` ✓ —— **首一 ＋ 正次数** ✓）；**(乙)** **`kummer_of_injective`** ✓✅；
**(丙)** **`kummerShift_faithful`** ✓✅ —— **核平凡形** ✓：**`ρ` 本原 `n` 次单位根 ＋ `a` 单位** ✓ ⟹
**`∀ k, (∀ x, φ_{ρ^{k.val}} x = x) → k = 1`** ✓。

**机制（(丙)，链六步）** ✓：**在根上取一次值** ✓（§4.86 同法 ✓）⟹ `of(ρ^{k.val}) · root = root` ✓ ⟹
`(of(ρ^{k.val}) − 1) · root = 0` ✓ ⟹ **`root` 单位** ✓（§4.133 ✓）⟹ **`of (ρ^{k.val} − 1) = 0`** ✓ ⟹
**(甲)** ✓ ⟹ **`ρ^{k.val} = 1`** ✓ ⟹ **`IsPrimitiveRoot.pow_eq_one_iff_dvd`** ✓ ⟹ `n ∣ k.val` ✓ ⟹
**`ZMod.val_lt`** ✓ ⟹ `k.val = 0` ✓ ⟹ **`ZMod.natCast_zmod_val`** ✓ ⟹ `k = 1` ✓。

**⚠ 口径（重要 ✓）** ✗：**`kummerMSA` 不能注册为类型类实例** ✗ —— **Lean 拒登** ✓（**`ρ` 与 `hρ` 不出现在返回类型中** ✓，
**无法由类型类合成推断** ✗；AS 档的 `asCarrierMSA` 之 `a` **出现在返回类型** ✓ 故可登 ✓）⟹
**正解 ＝ 结论取"核平凡"形** ✓（**免 `FaithfulSMul` 的实例要求** ✓，**内容与忠实性等价** ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#72)** **`IsUnit` 的乘法消去须先 `obtain` 出单位** ✗ ——
**直接 `rw [hu.unit_spec]` 会因 `hu` 的类型依赖被改写项而报 "motive is not type correct"** ✗
（**依赖位重写第四次命中** ✓）⟹ **正解 ＝ `obtain ⟨u, hu_eq⟩ := hu`** ✓ 再 `rw [hu_eq]` ✓；
**(#73)** **`← map_pow` 的方向** ✗ —— 目标里 `(of ρ)^m`（**像的幂** ✓）与 `of (ρ^m)`（**幂的像** ✓）**须用 `← map_pow`** ✓
（**用 `map_pow` 报 "Did not find an occurrence"** ✗，**实测** ✓）；**(#74)** **`Units.mul_inv` 后零在左** ✗ ⟹
**`zero_mul` 而非 `mul_zero`** ✓（**实测** ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**款① 已落** ✓ —— **款②（不动基）＋ 款③（判据）＋ 实现未落** ✗）；
**不**声称 **`FaithfulSMul` 实例形已落** ✗（**只落核平凡形** ✓ —— **口径已登记** ✓）；**不**声称源 `theorem-1-2(b)` 已证 ✗。 -/

section KummerFaithful352

/-- **(甲) `of x = 0 ⟹ x = 0`（Kummer 档）** ✓（与 §4.128 同法 ✓）。 -/
theorem kummer_of_eq_zero {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) (a : R)
    {x : R} (h : AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) x = 0) :
    x = 0 := by
  have hmonic : ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a).Monic :=
    kpoly_monic (R := R) hn a
  have hdeg : ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a).natDegree = n :=
    kpoly_natDegree (R := R) hn a
  have hdvd : ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ∣ Polynomial.C x := by
    rw [← AdjoinRoot.mk_eq_zero]
    exact h
  have hmod : (Polynomial.C x) %ₘ ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
  have hself : (Polynomial.C x) %ₘ ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
      = Polynomial.C x := by
    refine (Polynomial.modByMonic_eq_self_iff hmonic).mpr ?_
    have hdeg' : ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a).degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [hdeg']
    exact_mod_cast hn
  rw [hself] at hmod
  exact Polynomial.C_eq_zero.mp hmod

/-- **(乙) `of` 单射（Kummer 档）** ✓。 -/
theorem kummer_of_injective {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) (a : R) :
    Function.Injective (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) := by
  intro r s h
  have hsub : AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) (r - s) = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (kummer_of_eq_zero (R := R) (n := n) hn a hsub)

/-- **(丙) 忠实性（核平凡形）** ✓✅：`ρ` **本原 `n` 次单位根** ✓ ＋ **`a` 单位** ✓ ⟹
**作用核平凡** ✓（**在根上取一次值** ✓ —— §4.86 同法 ✓）。
**⚠ 口径** ✗：`kummerMSA` **不能注册为实例** ✗（`ρ`／`hρ` **不出现在返回类型中** ✓，
与 AS 档的 `a` 不同 ✗ —— Lean 拒登 ✓）⟹ **结论取"核平凡"形** ✓（**免 `FaithfulSMul` 的实例要求** ✓，
**内容等价** ✓）。 -/
theorem kummerShift_faithful {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1)
    (hprim : IsPrimitiveRoot (ρ : R) n) (ha : IsUnit a) :
    ∀ k : Multiplicative (ZMod n),
      (∀ x : kummerCarrier R n a,
        kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd k).val)
          (kummer_pow_coeff_pow ρ hρ _) x = x) → k = 1 := by
  intro k hk
  have hroot : kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd k).val)
      (kummer_pow_coeff_pow ρ hρ _)
      (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) := hk _
  rw [kummerShiftH_root] at hroot
  have hu : IsUnit (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) :=
    kummerRoot_isUnit (R := R) (n := n) hn ha
  have hof : AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
      ((ρ : R) ^ (Multiplicative.toAdd k).val - 1) = 0 := by
    have h1 : (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) (ρ : R)
          ^ (Multiplicative.toAdd k).val - 1)
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) = 0 := by
      rw [sub_mul, one_mul, ← map_pow, hroot, sub_self]
    obtain ⟨u, hu_eq⟩ := hu
    have h3 : (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) (ρ : R)
          ^ (Multiplicative.toAdd k).val - 1) * (↑u : AdjoinRoot ((Polynomial.X : Polynomial R) ^ n
            - Polynomial.C a)) = 0 := by
      rw [hu_eq]
      exact h1
    have h4 := congrArg (fun t => t
      * (↑u⁻¹ : AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))) h3
    rw [mul_assoc, Units.mul_inv, mul_one, zero_mul] at h4
    rw [map_sub, map_pow, map_one]
    exact h4
  have hzero : (ρ : R) ^ (Multiplicative.toAdd k).val - 1 = 0 :=
    kummer_of_eq_zero (R := R) (n := n) hn a hof
  have hpow : (ρ : R) ^ (Multiplicative.toAdd k).val = 1 := sub_eq_zero.mp hzero
  have hdvd : n ∣ (Multiplicative.toAdd k).val := (hprim.pow_eq_one_iff_dvd _).mp hpow
  have hval : (Multiplicative.toAdd k).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
  have htoAdd : Multiplicative.toAdd k = 0 := by
    have h := ZMod.natCast_zmod_val (Multiplicative.toAdd k)
    rw [hval] at h
    simpa using h.symm
  have h1 : Multiplicative.toAdd (1 : Multiplicative (ZMod n)) = 0 := rfl
  exact Multiplicative.toAdd.injective (by rw [htoAdd, h1])

end KummerFaithful352

/-! ### 4.136 🔴🔴 **T6-F 第二口（五续）：Kummer 款②（不动基）＋ 行列式半**（第 353 轮）
—— **源 `proposition-0-6(a)` 款②（不动基）落库 ＋ 款③（判据）的行列式半落库** ✓

**靶** ✓：**源 `proposition-0-6(a)`** ✓ 的**款②** ✓（**作用不动基** ✓）＋ **款③（`δ` 双射）的行列式半** ✓
（**§4.125 的乘法档类比** ✓）。

**落成八件** ✓✅：**(甲)** **`kummer_hRG`** ✓✅ —— **`φ_k (r · t) = r · (φ_k t)`** ✓（**显式移位形** ✓ ——
**⚠ `kummerMSA` 不能作实例** ✗ §4.135 ✓）；**(乙)** **`kummerNode`** ✓✅ —— **乘法档节点 `v k := of (ρ^k) · root`** ✓
（AS 档为 `root + of k` ✓）；**(丙)** **`kummerNode_sub`** ✓✅ —— **`ρ^i y − ρ^j y = (ρ^i − ρ^j) y`** ✓；
**(丁)** **`isUnit_kummerNode_sub`** ✓✅（**差为单位 × `root` 为单位** ✓ —— **`IsUnit.map`** ✓ ＋ §4.133 ✓）；
**(戊)** **`isUnit_det_vandermonde_kummerNode`** ✓✅ —— **节点 Vandermonde 行列式为单位** ✓
（**复用 §4.125 的一般件 ＋ AS 档泛型引理** ✓）；**(己)** **`isUnit_det_momentMatrix_kummerNode`** ✓✅
（**转置形** ✓ ＝ 矩量矩阵 ✓）；**(庚)** **`kummerCoeff_sub_ne_zero`** ✓✅ —— **`ρ` 本原 ＋ `i ≠ j` ⟹ `ρ^i − ρ^j ≠ 0`** ✓
（**`sub_eq_zero` ＋ `IsPrimitiveRoot.pow_inj`** ✓ —— **一行** ✓）；**(辛)** **`isUnit_kummerCoeff_sub`** ✓✅。

**机制（(庚)，关键简化）** ✓：**乘法档的差非零只需 `pow_inj`** ✓ —— **`ρ^i = ρ^j` ＋ `i,j < n` ⟹ `i = j`** ✓
（**AS 档须 `k^p − k` 的因式分解 ＋ `CharP`** ✗ —— **乘法档更省** ✓）；
**单位性由域性质** ✓（`isUnit_iff_ne_zero` ✓）；**`R` 侧**由 **`IsUnit.map`** ✓ 送入载体 ✓。

**⚠ 与 AS 档结构差别** ✓：**AS 档节点差为单位须 `k^p − k` 的因式分解** ✗（§4.125 ✓）；
**乘法档只须 `pow_inj` ＋ 域中非零即单位** ✓ ⟹ **乘法档的判据路更短** ✓（**下一手** ✗：矩量映射可逆 ＋ `δ` 双射 ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#75)** **`algebraMap R (AdjoinRoot f) r` 与 `of f r` 须 `show … from rfl` 桥接** ✗
（**`rw [kummerShiftH_of]` 直接命中失败** ✗ —— **§4.128 的 `asCarrier_hRG'` 同款** ✓）；
**(#76)** **`← sub_mul` 用于"提出公因子"** ✗（**`sub_mul` 是展开方向** ✓ —— **实测报 "Did not find an occurrence"** ✗）；
**(#77)** **`kummerNode a ρ` 的 `n` 须显式** ✗（`(n := n)` ✓ —— **否则语句里报 "don't know how to synthesize implicit argument M／R"** ✗，**实测** ✓）；
**(#78)** **`IsUnit.map` 用于把 `R` 中单位送入载体** ✗（**`hdiff … : IsUnit (… : R)` 与目标的 `of (…)` 不同环** ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**款① §4.135 ＋ 款② ＋ 行列式半已落** ✓ —— **矩量映射可逆 ＋ `δ` 双射 ＋ 款③ 未落** ✗）；
**不**声称 **`FaithfulSMul`／`IsGaloisWithGroup` 实例形已落** ✗；**不**声称源 `theorem-1-2(b)` 已证 ✗。 -/

section KummerHRGDetHalf353

/-- **(甲) 款②（不动基）** ✓：`φ_k (r · t) = r · φ_k t` ✓（**移位是环同态且固定系数** ✓）。
**⚠ 口径** ✗：`kummerMSA` **不能作实例** ✗（§4.135 已登记 ✓）⟹ **语句用显式移位形** ✓。 -/
theorem kummer_hRG {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1)
    (r : R) (t : kummerCarrier R n a) (m : ℕ) :
    kummerShiftH a ((ρ : R) ^ m) (kummer_pow_coeff_pow ρ hρ m) (r • t)
      = r • (kummerShiftH a ((ρ : R) ^ m) (kummer_pow_coeff_pow ρ hρ m) t) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  rw [show algebraMap R (kummerCarrier R n a) r
    = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
  rw [kummerShiftH_of]



/-- **Kummer 节点族** ✓：`v k := of (ρ^k) · root` ✓（**乘法档节点** ✓ —— AS 档为 `root + of k` ✓）。 -/
noncomputable def kummerNode {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ) (k : Fin n) :
    kummerCarrier R n a :=
  AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ((ρ : R) ^ (k : ℕ))
    * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)

/-- **节点差** ✓：`ρ^i·y − ρ^j·y = (ρ^i − ρ^j)·y` ✓。 -/
theorem kummerNode_sub {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ) (i j : Fin n) :
    kummerNode a ρ i - kummerNode a ρ j
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
          ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ))
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) := by
  rw [kummerNode, kummerNode, ← sub_mul, ← map_sub]

/-- **(乙) 节点差为单位** ✓✅（**差为单位 ＋ `root` 为单位** ✓）。 -/
theorem isUnit_kummerNode_sub {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n)
    (a : R) (ρ : Rˣ) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ)))
    {i j : Fin n} (hij : i ≠ j) : IsUnit (kummerNode a ρ i - kummerNode a ρ j) := by
  rw [kummerNode_sub]
  exact IsUnit.mul
    ((hdiff i j hij).map (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)))
    (kummerRoot_isUnit (R := R) (n := n) hn ha)

/-- **(丙) 节点 Vandermonde 的行列式为单位** ✓✅（**路线（丙″）的乘法档行列式半** ✓）。 -/
theorem isUnit_det_vandermonde_kummerNode {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ))) :
    IsUnit (Matrix.vandermonde (kummerNode (n := n) a ρ)).det :=
  isUnit_det_vandermonde_of_isUnit_sub (v := kummerNode (n := n) a ρ)
    (fun i j hij => isUnit_kummerNode_sub hn a ρ ha hdiff (i := i) (j := j) hij)

/-- **(丁) 矩量矩阵（转置形）的行列式为单位** ✓（`M i j = v j ^ i` ＝ `(vandermonde v)ᵀ` ✓）。 -/
theorem isUnit_det_momentMatrix_kummerNode {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ))) :
    IsUnit (Matrix.det (fun i j : Fin n => (kummerNode (n := n) a ρ j) ^ (i : ℕ))) := by
  have h : (fun i j : Fin n => (kummerNode (n := n) a ρ j) ^ (i : ℕ))
      = Matrix.transpose (Matrix.vandermonde (kummerNode (n := n) a ρ)) := rfl
  rw [h, Matrix.det_transpose]
  exact isUnit_det_vandermonde_kummerNode hn a ρ ha hdiff

/-- **(戊) 差非零（`F` 侧供给）** ✓✅：**`ρ` 本原 `n` 次单位根 ＋ `i ≠ j` ⟹ `ρ^i − ρ^j ≠ 0`** ✓
（**`sub_eq_zero` ＋ `IsPrimitiveRoot.pow_inj`** ✓ —— **一行** ✓）。 -/
theorem kummerCoeff_sub_ne_zero {F : Type u} [Field F] {n : ℕ} (ρ : Fˣ)
    (hprim : IsPrimitiveRoot (ρ : F) n) {i j : Fin n} (hij : i ≠ j) :
    (ρ : F) ^ (i : ℕ) - (ρ : F) ^ (j : ℕ) ≠ 0 := fun h =>
  hij (Fin.eq_of_val_eq (hprim.pow_inj i.isLt j.isLt (sub_eq_zero.mp h)))

/-- **(己) 差为单位（`F` 侧）** ✓✅。 -/
theorem isUnit_kummerCoeff_sub {F : Type u} [Field F] {n : ℕ} (ρ : Fˣ)
    (hprim : IsPrimitiveRoot (ρ : F) n) {i j : Fin n} (hij : i ≠ j) :
    IsUnit ((ρ : F) ^ (i : ℕ) - (ρ : F) ^ (j : ℕ)) :=
  isUnit_iff_ne_zero.mpr (kummerCoeff_sub_ne_zero ρ hprim hij)


end KummerHRGDetHalf353

#print axioms kummer_hRG
#print axioms kummerNode_sub
#print axioms isUnit_kummerNode_sub
#print axioms isUnit_det_vandermonde_kummerNode
#print axioms isUnit_det_momentMatrix_kummerNode
/-! ### 4.137 🔴🔴🔴 **T6-F 第二口（六续）：Kummer 档矩量映射可逆 ＋ `δ` 单射**（第 354 轮）
—— **源 `proposition-0-6(a)` 款③ 的接线半之一落库** ✓（**§4.126 的乘法类比** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓ 的**款③（`δ` 双射）之单射半** ✓ —— **乘法档矩量通道** ✓。

**落成九件** ✓✅：**(甲)** **`kummerShiftK`** ✓✅（**位移的 `k`-形** ✓ —— 与 `kummerMSA` 的 `smul` 同值 ✓）
＋ 两条计算件 ✓；**(乙)** **`kummerMSA_smul_pow`** ✓✅（`φ_k (root^m) = (of(ρ^{k.val})·root)^m` ✓）；
**(丙)** **`finEquivGZMod`** ✓✅（**`Fin n ≃ Multiplicative (ZMod n)`** ✓ —— 供 `Equiv.sum_comp` 重索引 ✓）；
**(丁)** **`kummerDelta_root_pow_eq_moment`** ✓✅ —— **`δ` 的矩量形** ✓；
**(戊)** **`kummerMomentMatrix`／`kummerMomentMap`** ✓✅；**(己)** **`kummerMomentMap_bijective`** ✓✅
（**单位行列式（§4.136 ✓）＋ `toLinearEquiv'`** ✓）；**(庚)** **`kummerMomentMap_apply`** ✓✅；
**(辛)** **`kummerDelta_injective_of_moment`** ✓✅ —— **款③ 单射半** ✓（**矩量形 ＋ 矩量映射单射 ＋ 系数消去** ✓）。

**⚠ 口径（承重 ✓）** ✗：**`kummerMSA` 不能作实例** ✗（§4.135 ✓）⟹ **本件取"抽象作用 ＋ 桥假设"形** ✓：
`[MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)]` ✓ ＋
**`hRG`** ✓ ＋ **`hact : ∀ k x, k • x = kummerShiftK a ρ hρ k x`** ✓ ——
**与 §4.126 的 `hRG` 抽象形同构** ✓（**故本件是该件在乘法档的逐字类比** ✓）；
**⚠ 出口** ✓：**Kummer 档的 `IsGaloisWithGroup` 实例形** ✗ 须**先解决实例口径** ✗（**下一手** ✓ ——
**候选**：**引入 `KummerDatum` 类型类把 `ρ`／`hprim` 挂进类型类** ✓，**使 `MulSemiringAction` 实例可合成** ✓）。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#79)** **`kummerShiftK` 上的计算件须给全具名实参** ✗ ——
**用 `_` 占位会报 "CommRing ?m" 类的 stuck 实例问题** ✗（**系数是第 2 位置实参** ✓ ——
**`(ρ := (ρ:R)^k.val)` 而非 `(ρ := (ρ:R))`** ✗，**实测** ✓）；
**(#80)** **指数对齐须显式 `show` ＋ `ZMod.val_natCast` ＋ `Nat.mod_eq_of_lt`** ✗ ——
**`(j : ZMod n).val` 与 `j` 只 mod `n` 相等** ✓ ⟹ **末步 `rfl` 不足** ✗。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 已证 ✗（**款①＋款②＋行列式半＋单射半已落** ✓ ——
**满射／双射 ＋ `IsGaloisWithGroup` ＋ 实现未落** ✗）；**不**声称 `IsGaloisWithGroup`（Kummer 档）已落 ✗；
**不**声称源 `theorem-1-2(b)` 已证 ✗。 -/

section KummerMoment354

/-- **Kummer 位移的 `k`-形** ✓（`k ↦ φ_{ρ^{k.val}}` ✓ —— 与 `kummerMSA` 的 `smul` 同值 ✓）。 -/
noncomputable def kummerShiftK {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (k : Multiplicative (ZMod n)) :
    kummerCarrier R n a →+* kummerCarrier R n a :=
  kummerShiftH a ((ρ : R) ^ (Multiplicative.toAdd k).val) (kummer_pow_coeff_pow ρ hρ _)

/-- 计算件 ①：固定系数 ✓。 -/
theorem kummerShiftK_of {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (k : Multiplicative (ZMod n)) (r : R) :
    kummerShiftK a ρ hρ k (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r)
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r :=
  kummerShiftH_of (a := a) (ρ := (ρ : R) ^ (Multiplicative.toAdd k).val)
    (hρ := kummer_pow_coeff_pow ρ hρ (Multiplicative.toAdd k).val) (r := r)

/-- 计算件 ②：根 ↦ `ρ^{k.val} · root` ✓。 -/
theorem kummerShiftK_root {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (k : Multiplicative (ZMod n)) :
    kummerShiftK a ρ hρ k (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
          ((ρ : R) ^ (Multiplicative.toAdd k).val)
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) :=
  kummerShiftH_root (a := a) (ρ := (ρ : R) ^ (Multiplicative.toAdd k).val)
    (hρ := kummer_pow_coeff_pow ρ hρ (Multiplicative.toAdd k).val)

/-- **(L1) 作用在幂基上的值** ✓：`φ_k (root^m) = (of (ρ^{k.val}) · root)^m` ✓。 -/
theorem kummerMSA_smul_pow {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (hρ : ((ρ : R)) ^ n = 1) (k : Multiplicative (ZMod n)) (m : ℕ) :
    kummerShiftK a ρ hρ k
        ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ m)
      = (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
            ((ρ : R) ^ (Multiplicative.toAdd k).val)
          * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ m := by
  rw [map_pow, kummerShiftK_root]

/-- **(L2) 编号等价** ✓：`Fin n ≃ Multiplicative (ZMod n)` ✓（**逐点定义形** ✓）。 -/
noncomputable def finEquivGZMod (n : ℕ) [NeZero n] : Fin n ≃ Multiplicative (ZMod n) :=
  Equiv.ofBijective (fun i : Fin n => Multiplicative.ofAdd (i : ZMod n))
    ⟨fun i j h => Fin.eq_of_val_eq (by
        have h1 : (i : ZMod n) = (j : ZMod n) := Equiv.injective Multiplicative.ofAdd h
        exact ((ZMod.natCast_eq_natCast_iff (i : ℕ) (j : ℕ) n).mp h1).eq_of_lt_of_lt i.isLt j.isLt),
      fun g => ⟨⟨(Multiplicative.toAdd g).val, ZMod.val_lt _⟩, by
        show Multiplicative.ofAdd (((Multiplicative.toAdd g).val : ℕ) : ZMod n) = g
        rw [ZMod.natCast_zmod_val]
        exact Equiv.apply_symm_apply Multiplicative.ofAdd g⟩⟩

/-- **(L3) `δ` 的矩量形（Kummer）** ✓：`(δ z)(root^i) = Σ_j (coeff z (ofAdd j)) · (kummerNode a ρ j)^i` ✓。 -/
theorem kummerDelta_root_pow_eq_moment {R : Type u} [CommRing R] {n : ℕ} [NeZero n] (a : R)
    (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1)
    [MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)]
    (hRG : ∀ (g : Multiplicative (ZMod n)) (r : R) (t : kummerCarrier R n a),
      g • (r • t) = r • (g • t))
    (hact : ∀ (k : Multiplicative (ZMod n)) (x : kummerCarrier R n a),
      k • x = kummerShiftK a ρ hρ k x)
    (z : SkewMonoidAlgebra (kummerCarrier R n a) (Multiplicative (ZMod n))) (i : Fin n) :
    deltaToEndRingHom hRG z
        ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (i : ℕ))
      = ∑ j : Fin n, z.coeff (Multiplicative.ofAdd (j : ZMod n)) * (kummerNode a ρ j) ^ (i : ℕ) := by
  rw [delta_apply_sum hRG z, delta_sum_univ z]
  rw [← Equiv.sum_comp (finEquivGZMod n) (fun g : Multiplicative (ZMod n) =>
    z.coeff g * (g • ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      ^ (i : ℕ))))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hact, kummerMSA_smul_pow]
  show z.coeff (Multiplicative.ofAdd ((j : ℕ) : ZMod n))
      * (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
          ((ρ : R) ^ (ZMod.val ((j : ℕ) : ZMod n)))
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (i : ℕ)
    = z.coeff (Multiplicative.ofAdd ((j : ℕ) : ZMod n))
      * (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) ((ρ : R) ^ (j : ℕ))
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (i : ℕ)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt]

/-- **(L4-a) Kummer 矩量矩阵** ✓：`M_{i,j} = (kummerNode a ρ j)^i` ✓。 -/
noncomputable def kummerMomentMatrix {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ) :
    Matrix (Fin n) (Fin n) (kummerCarrier R n a) :=
  fun i j => (kummerNode (n := n) a ρ j) ^ (i : ℕ)

/-- **(L4-b) Kummer 矩量映射** ✓：`Λ = Matrix.toLin' M` ✓。 -/
noncomputable def kummerMomentMap {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ) :
    (Fin n → kummerCarrier R n a) →ₗ[kummerCarrier R n a] (Fin n → kummerCarrier R n a) :=
  Matrix.toLin' (kummerMomentMatrix a ρ)

/-- **(L4-c) Kummer 矩量映射可逆** ✓✅（**单位行列式 ＋ `toLinearEquiv'`** ✓ —— §4.136 的行列式半 ✓）。 -/
theorem kummerMomentMap_bijective {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ))) :
    Function.Bijective (kummerMomentMap (n := n) a ρ) :=
  (Matrix.toLinearEquiv' (kummerMomentMatrix (n := n) a ρ)
    (Matrix.invertibleOfIsUnitDet _ (isUnit_det_momentMatrix_kummerNode hn a ρ ha hdiff))).bijective

/-- **(L4-d) Kummer 矩量映射的取值形** ✓。 -/
theorem kummerMomentMap_apply {R : Type u} [CommRing R] {n : ℕ} (a : R) (ρ : Rˣ)
    (s : Fin n → kummerCarrier R n a) (i : Fin n) :
    kummerMomentMap (n := n) a ρ s i
      = ∑ j : Fin n, s j * (kummerNode (n := n) a ρ j) ^ (i : ℕ) := by
  rw [kummerMomentMap, Matrix.toLin'_apply, Matrix.mulVec]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **(L5) Kummer 档 `δ` 单射** ✓✅（**矩量形 ＋ 矩量映射单射 ＋ 系数消去** ✓ —— §4.126 的乘法类比 ✓）。 -/
theorem kummerDelta_injective_of_moment {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ)))
    [MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)]
    (hRG : ∀ (g : Multiplicative (ZMod n)) (r : R) (t : kummerCarrier R n a),
      g • (r • t) = r • (g • t))
    (hact : ∀ (k : Multiplicative (ZMod n)) (x : kummerCarrier R n a),
      k • x = kummerShiftK a ρ hρ k x) :
    Function.Injective (deltaToEndRingHom (S := kummerCarrier R n a) hRG) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hzero : ∀ i : Fin n,
      kummerMomentMap (n := n) a ρ
        (fun j : Fin n => z.coeff (Multiplicative.ofAdd (j : ZMod n))) i = 0 := by
    intro i
    rw [kummerMomentMap_apply, ← kummerDelta_root_pow_eq_moment a ρ hρ hRG hact z i, hz]
    rfl
  have hvec : (fun j : Fin n => z.coeff (Multiplicative.ofAdd (j : ZMod n))) = 0 := by
    apply (kummerMomentMap_bijective hn a ρ ha hdiff).1
    ext i
    simp [hzero i]
  apply SkewMonoidAlgebra.coeff_eq_zero.mp
  ext g
  obtain ⟨i, hi⟩ := (finEquivGZMod n).surjective g
  rw [← hi]
  change z.coeff (Multiplicative.ofAdd (i : ZMod n)) = 0
  exact congrFun hvec i


end KummerMoment354

#print axioms kummerShiftK_of
#print axioms kummerShiftK_root
#print axioms kummerMSA_smul_pow
#print axioms kummerDelta_root_pow_eq_moment
/-! ### 4.138 🔴🔴🔴 **T6-F 第二口（七续）：Kummer 档 `δ` 满射／双射 —— 款③ 完成**（第 355 轮）
—— **源 `proposition-0-6(a)` 的款③落库** ✓（**§4.127 的乘法类比** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓ 的**款③（`δ` 双射）** ✓ —— **本件完成后，源 `proposition-0-6(a)` 的三款内容全部落库** ✓✅
（**⚠ 但判据的"实例形"尚欠** ✗ —— **见下"口径"** ✓）。

**落成三件** ✓✅：**(甲)** **`kummerBasis_apply`** ✓✅ —— **幂基取值 `kummerBasis hn a i = root^i`** ✓
（§4.127 的 `asCarrierBasis_apply` 逐字类比 ✓，**复用 `AdjoinRoot.powerBasis'` 的 `basis_eq_pow`** ✓）；
**(乙)** **`kummerDelta_surjective_of_moment`** ✓✅ —— **满射** ✓（**矩量映射满射 ＋ 系数装配（`ofCoeff` ＋ `equivFunOnFinite` 逆）＋ 幂基取值收口** ✓）；
**(丙)** **`kummerDelta_bijective_of_moment`** ✓✅ —— **双射** ✓（**单射（§4.137）＋ 满射** ✓）。

**⚠ 源 `proposition-0-6(a)` 的三款对照** ✓：**款①（忠实）** ✓ §4.135 ✓；**款②（不动基）** ✓ §4.136 ✓；
**款③（`δ` 双射）** ✓ 本件 ✓ —— **三款皆已落** ✓✅（**在"抽象作用 ＋ `hRG` ＋ `hact` 桥"口径下** ✓）。

**⚠ 口径（承重，未变）** ✗：本件仍取**抽象作用 ＋ 桥假设**形 ✓（**`kummerMSA` 不能作实例** ✗ §4.135 ✓）
⟹ **源 `proposition-0-6(a)` 的"实例形"（`IsGaloisWithGroup`）尚欠** ✗ ——
**下一手 ＝ 引入 `KummerDatum` 类型类把 `ρ`／`hρ`／`hprim` 挂进类型类** ✓，**使 `MulSemiringAction` 实例可合成** ✓
（**⚠ 之后本件与 §4.135–§4.137 的桥假设由该实例自动满足** ✓）。

**⚠ 工艺** ✓：**无新工艺坑** ✓（**本件一次通过** ✓ —— **§4.137 的 `show`／`ZMod.val_natCast`／`Nat.mod_eq_of_lt` 三件套已备** ✓；
**`kummerBasis_apply` 的 `finCongr_symm`／`finCongr_apply` 化简与 AS 档同** ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 的**实例形**已证 ✗（**三款内容已落** ✓，**`IsGaloisWithGroup` 装配欠** ✗）；
**不**声称源 `proposition-0-6(a)` 整体已证 ✗（**尚欠实例口径 ＋ 源侧"`a` 单位"的完整假设链核对** ✗）；
**不**声称源 `theorem-1-2(b)` 已证 ✗（**Kummer 实现未落** ✗）。 -/

section KummerSurj355

/-- **幂基的取值形（Kummer 档）** ✓：`kummerBasis hn a i = root^i` ✓（§4.127 的 `asCarrierBasis_apply` 类比 ✓）。 -/
theorem kummerBasis_apply {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) (a : R)
    (i : Fin n) :
    kummerBasis (R := R) hn a i
      = (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (i : ℕ) := by
  rw [kummerBasis, Module.Basis.reindex_apply]
  have hb := (AdjoinRoot.powerBasis' (kpoly_monic (R := R) hn a)).basis_eq_pow
    ((finCongr (kpoly_natDegree (R := R) hn a)).symm i)
  rw [show (AdjoinRoot.powerBasisAux' (kpoly_monic (R := R) hn a))
        ((finCongr (kpoly_natDegree (R := R) hn a)).symm i)
      = (AdjoinRoot.powerBasis' (kpoly_monic (R := R) hn a)).basis
          ((finCongr (kpoly_natDegree (R := R) hn a)).symm i) from rfl, hb]
  have hgen : (AdjoinRoot.powerBasis' (kpoly_monic (R := R) hn a)).gen
      = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) := rfl
  have hexp : (((finCongr (kpoly_natDegree (R := R) hn a)).symm i : Fin _) : ℕ) = (i : ℕ) := by
    simp [finCongr_symm, finCongr_apply]
  rw [hgen, hexp]

/-- **(甲) Kummer 档 `δ` 满射** ✓✅（**矩量映射满射 ＋ 系数装配 ＋ 幂基取值** ✓ —— §4.127 的乘法类比 ✓）。 -/
theorem kummerDelta_surjective_of_moment {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ)))
    [MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)]
    (hRG : ∀ (g : Multiplicative (ZMod n)) (r : R) (t : kummerCarrier R n a),
      g • (r • t) = r • (g • t))
    (hact : ∀ (k : Multiplicative (ZMod n)) (x : kummerCarrier R n a),
      k • x = kummerShiftK a ρ hρ k x) :
    Function.Surjective (deltaToEndRingHom (S := kummerCarrier R n a) hRG) := by
  classical
  intro f
  obtain ⟨s, hs⟩ := (kummerMomentMap_bijective hn a ρ ha hdiff).2
    (fun i : Fin n => f ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      ^ (i : ℕ)))
  let F : Multiplicative (ZMod n) →₀ kummerCarrier R n a :=
    Finsupp.equivFunOnFinite.symm (fun g : Multiplicative (ZMod n) => s ((finEquivGZMod n).symm g))
  refine ⟨SkewMonoidAlgebra.ofCoeff F, ?_⟩
  have hcoeff : ∀ j : Fin n,
      (SkewMonoidAlgebra.ofCoeff F).coeff (Multiplicative.ofAdd (j : ZMod n)) = s j := by
    intro j
    have h1 : (SkewMonoidAlgebra.ofCoeff F).coeff = F := rfl
    rw [h1]
    have h2 : F (Multiplicative.ofAdd (j : ZMod n))
        = s ((finEquivGZMod n).symm (Multiplicative.ofAdd (j : ZMod n))) :=
      congrFun (Finsupp.coe_equivFunOnFinite_symm
        (fun g : Multiplicative (ZMod n) => s ((finEquivGZMod n).symm g)))
        (Multiplicative.ofAdd (j : ZMod n))
    rw [h2]
    have h3 : (finEquivGZMod n).symm (Multiplicative.ofAdd (j : ZMod n)) = j :=
      Equiv.symm_apply_apply (finEquivGZMod n) j
    rw [h3]
  have hval : ∀ i : Fin n,
      deltaToEndRingHom hRG (SkewMonoidAlgebra.ofCoeff F)
          ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (i : ℕ))
        = f ((AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)) ^ (i : ℕ)) := by
    intro i
    rw [kummerDelta_root_pow_eq_moment a ρ hρ hRG hact _ i]
    rw [Finset.sum_congr rfl (fun j _ => by rw [hcoeff j])]
    rw [← kummerMomentMap_apply a ρ s i, hs]
  refine Module.Basis.ext (b := kummerBasis (R := R) hn a) (f₁ := _) (f₂ := f) (fun i => ?_)
  rw [kummerBasis_apply]
  exact hval i

/-- **(乙) Kummer 档 `δ` 双射** ✓✅（**＝ 源 `proposition-0-6(a)` 的款③** ✓）。 -/
theorem kummerDelta_bijective_of_moment {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n]
    (hn : 1 ≤ n) (a : R) (ρ : Rˣ) (hρ : ((ρ : R)) ^ n = 1) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit ((ρ : R) ^ (i : ℕ) - (ρ : R) ^ (j : ℕ)))
    [MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)]
    (hRG : ∀ (g : Multiplicative (ZMod n)) (r : R) (t : kummerCarrier R n a),
      g • (r • t) = r • (g • t))
    (hact : ∀ (k : Multiplicative (ZMod n)) (x : kummerCarrier R n a),
      k • x = kummerShiftK a ρ hρ k x) :
    Function.Bijective (deltaToEndRingHom (S := kummerCarrier R n a) hRG) :=
  ⟨kummerDelta_injective_of_moment hn a ρ hρ ha hdiff hRG hact,
    kummerDelta_surjective_of_moment hn a ρ hρ ha hdiff hRG hact⟩


end KummerSurj355

/-! ### 4.139 🔴🔴🔴🔴 **T6-F 第二口收官：实例形判据 —— 源 `proposition-0-6(a)` 落库**（第 356 轮）
—— **`KummerDatum` 类型类解开实例口径** ✓（**§4.135 的悬案收口** ✓）

**靶** ✓：**源 `proposition-0-6(a)`** ✓ 的**实例形** ✓ —— **§4.135–§4.138 的"抽象作用 ＋ 桥假设"口径之解** ✓。

**落成七件** ✓✅：**(甲)** **`KummerDatum R n a`** ✓✅ —— **类型类** ✓：字段 **`ρ : Rˣ`** ✓、**`hρ : (ρ:R)^n = 1`** ✓、
**`hpow_dvd : ∀ m, (ρ:R)^m = 1 ↔ n ∣ m`** ✓（**阶恰为 `n`** ✓ —— **`IsPrimitiveRoot` 的可合成替身** ✓，
**因 `IsPrimitiveRoot` 须域 `F` 而 `F` 不出现在载体类型中** ✗）；**(乙)** **`instMSA`** ✓✅ ——
**`MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a)` 实例** ✓✅（**由 `kummerMSA` 供给** ✓，
**⭐ 此即 §4.135 悬案之解** ✓）；**(丙)** **`smul_eq_shift`** ✓✅（**`hact` 桥定义即同（`rfl`）** ✓）；
**(丁)** **`smul_algebraMap`** ✓✅（**款②实例形** ✓）；**(戊)** **`hRG`** ✓✅（**实例形 `hRG`** ✓ —— **桥件自动满足** ✓）；
**(己)** **`faithful`** ✓✅（**款①实例形** ✓ —— **`hpow_dvd` 版核平凡 ＋ `faithfulSMul_iff`** ✓）；
**(庚)** **`kummer_isGaloisWithGroup`** ✓✅🔴 —— **`IsGaloisWithGroup R (kummerCarrier R n a) C_n hRG`** ✓✅
（**源 `proposition-0-6(a)` 的实例形** ✓ —— **款①（己）＋ 款②（丁）＋ 款③（§4.138 ✓）** ✓）。

**⚠ 类的设计要点** ✓：**(i)** **类参数只含 `R`／`n`／`a`** ✓（**不出现在载体类型中的 `F` 不得入类** ✗ ——
**否则实例合成无法回推** ✗，**§4.135 的失败正是此因** ✓）；**(ii)** **阶信息以 `hpow_dvd` 表达** ✓（**`↔ n ∣ m`** ✓）——
**纯 `R` 内可写** ✓，**且忠实性证明只需此形** ✓；**(iii)** **实例声明带 `[NeZero n]`** ✓（**可合成** ✓）。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#81)** **`omit … in` 须写在文档注释之前** ✗ ——
**写在 `/-- … -/` 与 `theorem` 之间报 "unexpected token 'omit'"** ✗（**实测** ✓）⟹
**正解 ＝ 把该实例假设改为定理上的显式 binder** ✓（**§5.1 的 "变量声明位置" 族** ✓）；
**(#82)** **类投影须给全具名实参** ✗（`KummerDatum.ρ (R := R) (n := n) (a := a)` ✓ ——
**用 `_` 占位报 "don't know how to synthesize placeholder for argument hρ"** ✗，**实测** ✓）。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` **无条件**已证 ✗（**须 `KummerDatum` 实例 ＋ `hdiff`（差为单位）假设** ✓ ——
**两者皆为具名假设而非定理** ✓）；**不**声称源侧"`ρ(n) ∈ F`"的完整假设链已核 ✗（**本件以 `hpow_dvd` 代之** ✓）；
**不**声称源 `theorem-1-2(b)` 已证 ✗（**Kummer 实现未落** ✗）；**不**声称源 `proposition-0-6(c)` 已证 ✗。 -/

section KummerDatum356

/-- **Kummer 数据类** ✓✅：`ρ` 是 `R` 中**阶恰为 `n`** 的单位（`(ρ:R)^m = 1 ↔ n ∣ m` ✓）——
**把 `ρ` 与其阶信息挂进类型类** ✓ ⟹ **`MulSemiringAction` 实例可合成** ✓（**§4.135 的实例口径之解** ✓）。 -/
class KummerDatum (R : Type u) [CommRing R] (n : ℕ) (a : R) where
  ρ : Rˣ
  hρ : ((ρ : R)) ^ n = 1
  hpow_dvd : ∀ m : ℕ, ((ρ : R)) ^ m = 1 ↔ n ∣ m

namespace KummerDatum

variable {R : Type u} [CommRing R] {n : ℕ} {a : R} [KummerDatum R n a]

/-- **(甲) `C_n`-作用实例** ✓✅（**由 `kummerMSA` 供给** ✓）。 -/
@[instance_reducible] noncomputable instance instMSA [NeZero n] :
    MulSemiringAction (Multiplicative (ZMod n)) (kummerCarrier R n a) :=
  kummerMSA a (KummerDatum.ρ (R := R) (n := n) (a := a))
    (KummerDatum.hρ (R := R) (n := n) (a := a))

/-- **(乙) 作用 ＝ 位移** ✓（**定义即同** ✓ —— `hact` 桥自动满足 ✓）。 -/
theorem smul_eq_shift [NeZero n] (k : Multiplicative (ZMod n)) (x : kummerCarrier R n a) :
    k • x = kummerShiftK a (KummerDatum.ρ (R := R) (n := n) (a := a))
      (KummerDatum.hρ (R := R) (n := n) (a := a)) k x := rfl

/-- **(丙) 款②（不动基，实例形）** ✓：`g • algebraMap r = algebraMap r` ✓。 -/
theorem smul_algebraMap [NeZero n] (k : Multiplicative (ZMod n)) (r : R) :
    k • algebraMap R (kummerCarrier R n a) r = algebraMap R (kummerCarrier R n a) r := by
  show kummerShiftK a (KummerDatum.ρ (R := R) (n := n) (a := a))
      (KummerDatum.hρ (R := R) (n := n) (a := a)) k (algebraMap R (kummerCarrier R n a) r) = _
  rw [show algebraMap R (kummerCarrier R n a) r
    = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
  rw [kummerShiftK_of]

/-- **(丁) `hRG`（实例形）** ✓。 -/
theorem hRG [NeZero n] :
    ∀ (g : Multiplicative (ZMod n)) (r : R) (t : kummerCarrier R n a),
      g • (r • t) = r • (g • t) := by
  intro k r t
  rw [Algebra.smul_def, Algebra.smul_def]
  show kummerShiftK a (KummerDatum.ρ (R := R) (n := n) (a := a))
      (KummerDatum.hρ (R := R) (n := n) (a := a)) k
      (algebraMap R (kummerCarrier R n a) r * t)
    = algebraMap R (kummerCarrier R n a) r
      * kummerShiftK a (KummerDatum.ρ (R := R) (n := n) (a := a))
        (KummerDatum.hρ (R := R) (n := n) (a := a)) k t
  rw [map_mul]
  congr 1
  rw [show algebraMap R (kummerCarrier R n a) r
    = AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) r from rfl]
  rw [kummerShiftK_of]

/-- **(戊) 款①（忠实性，实例形）** ✓✅（**`hpow_dvd` 版核平凡 ＋ `faithfulSMul_iff`** ✓）。 -/
theorem faithful [Nontrivial R] [NeZero n] (hn : 1 ≤ n) (ha : IsUnit a) :
    FaithfulSMul (Multiplicative (ZMod n)) (kummerCarrier R n a) := by
  rw [faithfulSMul_iff]
  intro k hk
  have hρ := KummerDatum.hρ (R := R) (n := n) (a := a)
  have hρpow := KummerDatum.hpow_dvd (R := R) (n := n) (a := a)
  have hroot : kummerShiftK a (KummerDatum.ρ (R := R) (n := n) (a := a)) hρ k
      (AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a))
      = AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) := hk _
  rw [kummerShiftK_root] at hroot
  have hof : AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
      (((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R)
        ^ (Multiplicative.toAdd k).val - 1) = 0 := by
    have h1 : (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
          (((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R)
            ^ (Multiplicative.toAdd k).val) - 1)
        * AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a) = 0 := by
      rw [sub_mul, one_mul, hroot, sub_self]
    obtain ⟨u, hu_eq⟩ := kummerRoot_isUnit (R := R) (n := n) hn ha
    have h3 : (AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C a)
          (((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R)
            ^ (Multiplicative.toAdd k).val) - 1)
        * (↑u : kummerCarrier R n a) = 0 := by
      rw [hu_eq]
      exact h1
    have h4 := congrArg (fun t => t * (↑u⁻¹ : kummerCarrier R n a)) h3
    rw [mul_assoc, Units.mul_inv, mul_one, zero_mul] at h4
    rw [map_sub, map_one]
    exact h4
  have hzero : ((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R)
      ^ (Multiplicative.toAdd k).val - 1 = 0 :=
    kummer_of_eq_zero (R := R) (n := n) hn a hof
  have hpow : ((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R)
      ^ (Multiplicative.toAdd k).val = 1 := sub_eq_zero.mp hzero
  have hdvd : n ∣ (Multiplicative.toAdd k).val := (hρpow _).mp hpow
  have hval : (Multiplicative.toAdd k).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
  have htoAdd : Multiplicative.toAdd k = 0 := by
    have h := ZMod.natCast_zmod_val (Multiplicative.toAdd k)
    rw [hval] at h
    simpa using h.symm
  have h1 : Multiplicative.toAdd (1 : Multiplicative (ZMod n)) = 0 := rfl
  exact Multiplicative.toAdd.injective (by rw [htoAdd, h1])

/-- **(己) 🔴🔴 实例形判据** ✓✅：**`IsGaloisWithGroup R (kummerCarrier R n a) C_n hRG`** ✓✅
（**源 `proposition-0-6(a)` 的实例形** ✓）。 -/
theorem kummer_isGaloisWithGroup [Nontrivial R] [NeZero n] (hn : 1 ≤ n) (ha : IsUnit a)
    (hdiff : ∀ i j : Fin n, i ≠ j → IsUnit
      (((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R) ^ (i : ℕ)
        - ((KummerDatum.ρ (R := R) (n := n) (a := a) : Rˣ) : R) ^ (j : ℕ))) :
    IsGaloisWithGroup R (kummerCarrier R n a) (Multiplicative (ZMod n))
      (hRG (R := R) (n := n) (a := a)) :=
  ⟨faithful (R := R) (n := n) (a := a) hn ha,
    fun g r => smul_algebraMap (R := R) (n := n) (a := a) g r,
    kummerDelta_bijective_of_moment hn a (KummerDatum.ρ (R := R) (n := n) (a := a))
      (KummerDatum.hρ (R := R) (n := n) (a := a)) ha hdiff
      (hRG (R := R) (n := n) (a := a))
      (fun k x => smul_eq_shift (R := R) (n := n) (a := a) k x)⟩


end KummerDatum
end KummerDatum356

/-! ### 4.140 🔴🔴 **T6-F 第三口：Kummer 分裂档载体同构**（第 357 轮）
—— **源 `theorem-1-2(b)` 的 (c) 款第一件** ✓（**§4.122 的乘法类比** ✓）

**靶** ✓：**`K{y^n − 1} ≅ K^n`** ✓ —— **分裂档的「载体侧」** ✓（源 `theorem-1-2(b)` 的 `R = F[x](1/x)` 档之分裂端 ✓）。

**落成三件** ✓✅：**(甲)** **`kummer_one_aeval_eq_zero`** ✓✅ —— **`aeval (ρ^i) (X^n − C 1) = 0`** ✓
（`(ρ^i)^n = (ρ^n)^i = 1` ✓）；**(乙)** **`kummer_splitPoint_injective`** ✓✅ —— **分裂点 `i ↦ ρ^{i.val}` 单射** ✓
（**由 `ρ` 的阶恰为 `n`** ✓：`ρ^{|i−j|} = 1` ⟹ `n ∣ |i−j|` ⟹ `< n` ⟹ `= 0` ✓）；
**(丙)** 🔴 **`kummer_one_algEquiv_pi`** ✓✅ —— **`Nonempty (kummerCarrier K n 1 ≃ₐ[K] (ZMod n → K))`** ✓✅
（**求值通道 ＋ 插值零判 ＋ 秩相等** ✓ —— **§4.122 的逐字类比** ✓）。

**⚠ 与 AS 档的结构差别（承重 ✓）** ✗：**AS 档的互异性由 `zmod_castHom_injective` 供给** ✓（§4.86 ✓，
**因 `ℤ/p → K` 在 `CharP K p` 下是单射** ✓）；**乘法档不能用它** ✗ ——
**`ℤ/n → K` 在 `p ∣ k`（`k < n`）时非单** ✗（**实反例** ✓：**`K = 𝔽₅`、`n = 6`、`k = 5`：`5·1 = 0`** ✗）
⟹ **正解 ＝ 互异性由 `ρ` 的阶供给** ✓（**`hpow` 的 `↔ n ∣ m` 形** ✓ —— **本件即其首个用户** ✓）。

**⚠ 工艺（三条，入 §5.1）** ✓：**(#83)** **`intro i j hij` 后的等式是函数应用形** ✗
（`(fun i => ρ^{i.val}) i = (fun i => ρ^{i.val}) j` ✗）⟹ **`rw [← hij]` 无法命中** ✗ ⟹
**正解 ＝ 先 `have hij' : ρ^{i.val} = ρ^{j.val} := hij`** ✓（**beta 归约显式化** ✓ —— **§5.1 #20 族** ✓）；
**(#84)** **`le_total` 的两支公式须对号** ✗（**`Or.inl : a ≤ b`** ✓ —— **写反即报 "Did not find an occurrence"** ✗，
**本轮实测** ✓）；**(#85)** **`omega` 不识整除** ✗（**须先 `Nat.eq_zero_of_dvd_of_lt`** ✓ 给 `= 0` ✓ 再 `omega` ✓）。

**🔴 不声称** ✗：**不**声称 **`L ≅ K^n`（分裂档模型侧）** ✗（**载体侧已落** ✓ —— **模型侧须结构定理** ✗）；
**不**声称源 `theorem-1-2(b)` 已证 ✗；**不**声称 Kummer 实现（域档）已落 ✗；**不**声称源 `proposition-0-6(c)` 已证 ✗。 -/

section KummerSplitIso357

/-- **Kummer 分裂点满足定义关系** ✓：`aeval (ρ^i) (X^n − C 1) = 0` ✓（`(ρ^i)^n = (ρ^n)^i = 1` ✓）。 -/
theorem kummer_one_aeval_eq_zero (K : Type u) [Field K] {n : ℕ} [NeZero n] (ρ : Kˣ)
    (hpow : ∀ m : ℕ, ((ρ : K)) ^ m = 1 ↔ n ∣ m) (i : ZMod n) :
    Polynomial.aeval (((ρ : K)) ^ (i.val)) ((Polynomial.X : Polynomial K) ^ n - Polynomial.C 1) = 0 := by
  rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, map_one, ← pow_mul, Nat.mul_comm,
    pow_mul, (hpow n).mpr (dvd_refl n), one_pow, sub_self]

/-- **分裂点互异** ✓（**由 `ρ` 的阶恰为 `n`** ✓ —— AS 档用 `zmod_castHom_injective` ✗，
**乘法档不能用它** ✗：`ℤ/n → K` 在 `p ∣ k` 时非单 ✗）。 -/
theorem kummer_splitPoint_injective (K : Type u) [Field K] {n : ℕ} [NeZero n] (ρ : Kˣ)
    (hpow : ∀ m : ℕ, ((ρ : K)) ^ m = 1 ↔ n ∣ m) :
    Function.Injective (fun i : ZMod n => ((ρ : K)) ^ (i.val)) := by
  intro i j hij
  have hij' : ((ρ : K)) ^ i.val = ((ρ : K)) ^ j.val := hij
  have hne_i : ((ρ : K)) ^ i.val ≠ 0 := pow_ne_zero _ (Units.ne_zero ρ)
  have hne_j : ((ρ : K)) ^ j.val ≠ 0 := pow_ne_zero _ (Units.ne_zero ρ)
  rcases le_total i.val j.val with hle | hle
  · have hd : ((ρ : K)) ^ (j.val - i.val) = 1 := by
      have h2 : ((ρ : K)) ^ (i.val + (j.val - i.val)) = ((ρ : K)) ^ i.val := by
        rw [Nat.add_sub_cancel' hle, ← hij']
      rw [pow_add] at h2
      exact mul_left_cancel₀ hne_i (by rw [h2, mul_one])
    have hdvd : n ∣ (j.val - i.val) := (hpow _).mp hd
    have hlt : j.val - i.val < n := lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt j)
    have hzero : j.val - i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact ZMod.val_injective n (by omega)
  · have hd : ((ρ : K)) ^ (i.val - j.val) = 1 := by
      have h2 : ((ρ : K)) ^ (j.val + (i.val - j.val)) = ((ρ : K)) ^ j.val := by
        rw [Nat.add_sub_cancel' hle, hij']
      rw [pow_add] at h2
      exact mul_left_cancel₀ hne_j (by rw [h2, mul_one])
    have hdvd : n ∣ (i.val - j.val) := (hpow _).mp hd
    have hlt : i.val - j.val < n := lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt i)
    have hzero : i.val - j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact ZMod.val_injective n (by omega)

/-- 🔴 **Kummer 分裂档载体同构** ✓✅：**`K{y^n − 1} ≅ K^n`** ✓（**求值通道 ＋ 插值 ＋ 秩相等** ✓ ——
§4.122 的乘法类比 ✓）。 -/
theorem kummer_one_algEquiv_pi (K : Type u) [Field K] {n : ℕ} [NeZero n] (ρ : Kˣ)
    (hpow : ∀ m : ℕ, ((ρ : K)) ^ m = 1 ↔ n ∣ m) :
    Nonempty (kummerCarrier K n 1 ≃ₐ[K] (ZMod n → K)) := by
  classical
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  set Φ : kummerCarrier K n 1 →ₐ[K] (ZMod n → K) :=
    AlgHom.pi (fun i : ZMod n =>
      AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial K) ^ n - Polynomial.C 1)
        (Algebra.ofId K K) (((ρ : K)) ^ (i.val))
        (by simpa [Polynomial.aeval_def] using kummer_one_aeval_eq_zero K ρ hpow i)) with hΦ
  have hval : ∀ (P : Polynomial K) (i : ZMod n),
      Φ (AdjoinRoot.mk ((Polynomial.X : Polynomial K) ^ n - Polynomial.C 1) P) i
        = Polynomial.aeval (((ρ : K)) ^ (i.val)) P := by
    intro P i
    rw [hΦ, AlgHom.pi_apply, AdjoinRoot.liftAlgHom_mk]
    exact (Polynomial.aeval_def ..).symm
  have hker : ∀ x : kummerCarrier K n 1, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [AdjoinRoot.mk_eq_zero]
    have hP : ∀ i : ZMod n, Polynomial.aeval (((ρ : K)) ^ (i.val)) P = 0 := by
      intro i
      have h := congrFun hx i
      rw [hval P i] at h
      exact h
    set f := (Polynomial.X : Polynomial K) ^ n - Polynomial.C 1 with hf
    have hfmonic : f.Monic := kpoly_monic (R := K) hn 1
    have hfd : f.natDegree = n := kpoly_natDegree (R := K) hn 1
    have hf1 : f ≠ 1 := by
      intro h
      rw [h, Polynomial.natDegree_one] at hfd
      exact (NeZero.ne n) hfd.symm
    have hfroot : ∀ i : ZMod n,
        Polynomial.aeval (((ρ : K)) ^ (i.val)) f = 0 := by
      intro i
      exact kummer_one_aeval_eq_zero K ρ hpow i
    have hR : ∀ i : ZMod n,
        Polynomial.aeval (((ρ : K)) ^ (i.val)) (P %ₘ f) = 0 := by
      intro i
      have h := Polynomial.modByMonic_add_div P f
      have h2 := congrArg (Polynomial.aeval (((ρ : K)) ^ (i.val))) h
      simp only [map_add, map_mul, hP i, hfroot i, zero_mul, add_zero] at h2
      exact h2
    have hReval : ∀ i : ZMod n,
        Polynomial.eval (((ρ : K)) ^ (i.val)) (P %ₘ f) = 0 := by
      intro i
      rw [← aeval_eq_eval_self]
      exact hR i
    have hdeg : (P %ₘ f).natDegree < n := by
      have := Polynomial.natDegree_modByMonic_lt P hfmonic hf1
      rw [hfd] at this
      exact this
    have hzero : P %ₘ f = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (P %ₘ f)
        (kummer_splitPoint_injective K ρ hpow) hReval (by rw [ZMod.card]; exact hdeg)
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hfmonic).mp hzero
  have hinj : Function.Injective Φ := by
    intro x z hxz
    have h1 : Φ (x - z) = 0 := by rw [map_sub, hxz, sub_self]
    exact sub_eq_zero.mp (hker (x - z) h1)
  have hfin1 : Module.finrank K (kummerCarrier K n 1) = n := kummer_finrank (R := K) hn 1
  have hfin2 : Module.finrank K (ZMod n → K) = n := by
    rw [Module.finrank_pi, ZMod.card]
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let _inst2 : Module.Finite K (kummerCarrier K n 1) :=
    Module.finite_of_finrank_pos (by rw [hfin1]; exact hpos)
  let _inst3 : Module.Finite K (ZMod n → K) :=
    Module.finite_of_finrank_pos (by rw [hfin2]; exact hpos)
  have hbij : Function.Bijective Φ := by
    refine ⟨hinj, ?_⟩
    have hinjL : Function.Injective (Φ.toLinearMap : kummerCarrier K n 1 →ₗ[K] (ZMod n → K)) := hinj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := kummerCarrier K n 1) (V₂ := ZMod n → K) (f := Φ.toLinearMap)
      (by rw [hfin1, hfin2])).mp hinjL
  exact ⟨AlgEquiv.ofBijective Φ hbij⟩


end KummerSplitIso357

/-! ### 4.141 🔴 **T6-F 第四口（第一小步）：源侧供给的承重前置**（第 358 轮）
—— **`KummerDatum` 的源侧供给之基件** ✓ ＋ **受阻点登记** ✗

**靶** ✓：**源 `proposition-0-6(a)` 的源侧假设形** ✓ —— **"`a` 是单位 ＋ `ρ(n) ∈ F`"** ✓
（`raw/Saltman1982.tex:142` ✓）⟹ **本件落其承重前置** ✓：**`F` 的像单射** ✓。

**落成一件** ✓✅：**`algebraMap_injective_of_field_univ`** ✓✅（**⚠ 库内已有同宇宙版 `algebraMap_injective_of_field`** ✓ §4.115 档 ✓ —— **本件为跨宇宙版** ✓） —— **`F` 域 ＋ `R` 非平凡 ⟹ `algebraMap F R` 单射** ✓
（**证法** ✓：`F` 是域 ⟹ `x - y ≠ 0` ⟹ `(x−y)⁻¹(x−y) = 1` ✓ 而像为 `0` ✓ ⟹ **`1 = 0`** ✗ 与 `Nontrivial` 矛盾 ✓）。

**⚠ 本件之用途** ✓：**源侧供给的两条都要它** ✗ ——
**(i)** **`KummerDatum.hpow_dvd`** ✗（`(algebraMap ρ)^m = 1 ⟹ algebraMap (ρ^m) = algebraMap 1` ⟹ **单射** ⟹ `ρ^m = 1` ✓
⟹ **`IsPrimitiveRoot.pow_eq_one_iff_dvd`** ✓）；**(ii)** **`hdiff` 的供给** ✗（**`ρ^i − ρ^j` 非零 ⟹ `F` 中单位 ⟹ `IsUnit.map`** ✓）。

**⚠ 受阻点登记（本轮未落，**不谎报** ✗）** ✗：**(甲) `KummerDatum.ofAlgebra`** ✗ 与 **(乙) `hdiff` 的源侧供给** ✗
**本轮尝试未过** ✗ —— **障碍** ✗：**`Units.coe_map` 的强制转换形与环同态应用形不同一** ✗
（`↑(algebraMap F R) x` vs `algebraMap F R x` ✓ —— **`rw`／`rfl`／`simp only [map_pow]` 三者皆不能弥合** ✗，
**实测** ✓）⟹ **下一手候选** ✓：**(i)** 在**单位群内**做幂运算（`(Units.map f ρ)^m` ✓ ＋ **`map_pow`** ✓ ＋
**`Units.ext`** ✓）以**绕开强制转换** ✓；**(ii)** 或**改以 `ρR : Rˣ` 为类字段** ✓（**放弃 `F` 侧成像** ✓）。
**⚠ 本件之"受阻"为**探针级读数** ✗（**非判假** ✗）—— **不做否定性声称** ✗。

**🔴 不声称** ✗：**不**声称 `KummerDatum.ofAlgebra` 已落 ✗；**不**声称源侧供给已落 ✗；
**不**声称 **`KummerDatum` 的源侧可用性已收口** ✗；**不**声称源 `proposition-0-6(a)` 的假设链已核 ✗。 -/

section KummerSupply358

theorem algebraMap_injective_of_field_univ (F : Type u) [Field F] (R : Type v) [CommRing R]
    [Nontrivial R] [Algebra F R] : Function.Injective (algebraMap F R) := by
  intro x y hxy
  by_contra hne
  have hx : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h0 : algebraMap F R (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 : algebraMap F R ((x - y)⁻¹ * (x - y)) = 0 := by rw [map_mul, h0, mul_zero]
  rw [inv_mul_cancel₀ hx, map_one] at h1
  exact one_ne_zero h1

end KummerSupply358

/-! ### 4.142 🔴 **T6-F 第四口（第二小步）：自档供给 ＋ 一般档障碍精确化**（第 359 轮）

**靶** ✓：**源 `proposition-0-6(a)` 的源侧供给** ✓（**"`a` 单位 ＋ `ρ(n) ∈ F`"** ✓）—— **本件落"基域自身"档** ✓
＋ **把一般档的障碍精确到一步** ✗。

**落成一件** ✓✅：**`kummerDatumSelf`** ✓✅ —— **`R = F` 时 `ρ : Fˣ` 直接入类** ✓
（**`ρ := ρ`** ✓、**`hρ := hprim.pow_eq_one`** ✓、**`hpow_dvd := hprim.pow_eq_one_iff_dvd`** ✓ —— **零强制转换** ✗）。

**⚠ 一般档障碍（本轮再探，**精确化** ✓，**仍不谎报** ✗）** ✗：**单位群内做幂** ✓ 的路线**本轮进了一步** ✓ ——
**`(Units.map f ρ)^n = 1`** ✓ 与 **`h1 : …^m = 1`** ✓ **皆可落** ✓（**`Units.ext` ＋ `Units.coe_pow` ＋ `rw [← map_pow]`** ✓）；
**残余障碍** ✗：**`IsPrimitiveRoot.pow_eq_one`／`pow_eq_one_iff_dvd` 的陈述是对"被强制的元素" `(ρ:F)`** ✗，
**而单位群内需要的是"单位的幂" `ρ^n`** ✗ ⟹ **须插入搬运** ✓：**`Units.ext (by rw [Units.coe_pow, Units.coe_one]; exact hprim.pow_eq_one)`** ✓
得 **`ρ ^ n = 1`（单位档）** ✓；**同理** ✗：**`↑(Units.map f ρ)`（`Units.coe_map` 后的强制形 ✗）与环同态应用形** ✗
**在 `h3` 的 `rw [Units.coe_map]` 后再 `rw [map_pow]` 仍不弥合** ✗（**实测** ✓）。
⟹ **下一手（精确）** ✓：**(i)** 先证 **`ρ ^ m = 1`（单位档）** ✓ 再 **`congrArg (fun u : Rˣ => (u:R))`** ✓ ——
**全程不出现 `algebraMap` 的应用形** ✓；**(ii)** 或**把类的 `hpow_dvd` 改为对 `↑(Units.map f ρ)` 陈述** ✓。

**🔴 不声称** ✗：**不**声称一般档供给已落 ✗；**不**声称源侧可用性已收口 ✗；**不**声称源 `proposition-0-6(a)` 假设链已核 ✗。 -/

section KummerSupply359

/-- **(甲) 自档供给** ✓✅：**`R = F` 时 `ρ` 直接入类** ✓（**无强制转换** ✗）。 -/
@[instance_reducible] noncomputable def kummerDatumSelf (F : Type u) [Field F] (n : ℕ) (a : F)
    (ρ : Fˣ) (hprim : IsPrimitiveRoot (ρ : F) n) : KummerDatum F n a where
  ρ := ρ
  hρ := hprim.pow_eq_one
  hpow_dvd := fun m => hprim.pow_eq_one_iff_dvd m

end KummerSupply359

/-! ### 4.143 🔴🔴🔴 **T6-F 第四口收官：一般档供给 ＋ 源侧可用性收口**（第 360 轮）
—— **源 `proposition-0-6(a)` 的源侧假设链闭合成类实例** ✓✅

**靶** ✓：**§4.141／§4.142 登记的受阻点** ✗ —— **`KummerDatum.ofAlgebra`（一般档供给）** ✗ 与
**`hdiff` 的源侧供给** ✗（障碍 ＝ **强制转换形 ≠ 环同态应用形** ✗ —— **§5.1 #86／#88 同族** ✓）。

**落成七件** ✓✅：**(甲)** **`units_map_coe_pow`** ✓✅ —— **通用桥** ✓：
**`(↑(Units.map f ρ))^m = f (↑ρ^m)`** ✓（**纯 `MonoidHom` 形** ✓ —— **证法 ＝ `Units.coe_map` ＋ `← map_pow`** ✓，
**全程零强制转换** ✗）；**(乙)** **`units_map_algebraMap_coe_pow`** ✓✅ —— **`algebraMap` 档桥** ✓
（**`rw` 后须显式补 `rfl`** ✓ —— **#86 族的最终解** ✓）；**(丙)** **`units_map_algebraMap_pow_eq_one_iff`** ✓✅ ——
**`(↑ρ_R)^m = 1 ↔ (↑ρ)^m = 1`** ✓（**单射 ＋ `map_one`** ✓）；**(丁)** **`kummerDatumOfAlgebra`** ✓✅🔴 ——
**一般档供给** ✓✅：**`F` 域 ＋ `R` 非平凡 `F`-代数 ＋ `ρ` 为本原 `n` 次单位根 ⟹ `KummerDatum R n a`** ✓✅
（**`ρ := Units.map (algebraMap F R).toMonoidHom ρ`** ✓；**`hρ`／`hpow_dvd` 皆由 (丙) 供给** ✓）；
**(戊-1)** **`kummer_pow_fin_ne`** ✓✅ —— **`Fin n` 上本原根的幂互异** ✓（**§4.140 的 `ZMod` 版之 `Fin` 对应物** ✓）；
**(戊)** **`isUnit_kummerCoeff_sub_of_primitiveRoot`** ✓✅ —— **`hdiff` 的源侧供给** ✓✅（**`ρ^i − ρ^j ≠ 0` ⟹ `F` 中单位 ＋
`IsUnit.map`** ✓，**系数桥用 (乙) ＋ `← map_sub`** ✓）；**(己)** **`kummer_isGaloisWithGroup_of_algebra`** ✓✅🔴🔴 ——
**源侧可用性收口** ✓✅：**`1 ≤ n` ＋ `IsUnit a` ＋ `IsPrimitiveRoot (ρ:F) n` ⟹
`IsGaloisWithGroup R (kummerCarrier R n a) C_n`** ✓✅（**实例以具名项供给** ✓ ——
**`@KummerDatum.instMSA` ＋ `@KummerDatum.hRG` 逐槽指名** ✓，**§5.1 #58 同法** ✓）。

**⚠ 源侧假设链（对照 `raw/Saltman1982.tex:142`** ✓）：源 `proposition-0-6(a)` 的条件 ＝
**「`n` 与 `char F` 互素 ＋ `ρ = ρ(n) ∈ F` ＋ `a` 是 `R` 的单位 ＋ `S = R{y^n − a}`」** ✓ ——
本件把 **「`ρ = ρ(n) ∈ F`」实现为 `ρ : Fˣ` ＋ `IsPrimitiveRoot (ρ:F) n`** ✓、「**`a` 是单位**」实现为 **`ha : IsUnit a`** ✓、
「**`S = R{y^n − a}`**」实现为**载体 `kummerCarrier R n a`** ✓（§4.131 ✓）⟹ **三条源侧条件皆已接线** ✓✅。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#89)** **`rw` 在本版 Lean 不以 `rfl` 自动收尾** ✗ ——
当残留目标是 **`↑(algebraMap F R) x = (algebraMap F R) x`** ✗（**`RingHom`→`MonoidHom` 强制形 vs `RingHom` 应用形** ✓，
**二者 defeq** ✓）时，`rw` 报 **unsolved goals** ✗ ⟹ **正解 ＝ 显式补一行 `rfl`** ✓（**#86 族：不是"避免"，是"显式桥接"** ✓）；
**(#90)** **`Units.coe_pow`／`Units.coe_one` 在本版 mathlib 不存在** ✗（**§4.142 的"下一手"曾写这两个名字** ✗ ——
**实测 `unknown constant`** ✗）⟹ **正解 ＝ `Units.val_pow_eq_pow_val`** ✓／**`Units.val_one`** ✓；
**且本件的正解根本不用它们** ✓ —— **改在 `Rˣ` 内做幂（(甲) 桥一次出到环）** ✓。

**🔴 不声称** ✗：**不**声称源 `proposition-0-6(a)` 无条件已证 ✗（**本件只把源侧假设接成类实例 ＋ 供给 `hdiff`** ✓）；
**不**声称类的 `hpow_dvd` 与源「`ρ = ρ(n)`」**逐字等价** ✗（**前者是阶的刻画** ✓，**后者另有构造性内容** ✓）；
**不**声称「`n` 与 `char F` 互素」已单独接线 ✗（**本件以「`F` 中确有本原 `n` 次单位根」代之** ✓）；
**不**声称源 `theorem-1-2(b)` 已证 ✗；**不**声称源 `proposition-0-6(c)` 已证 ✗；**不**声称二分命题已证 ✗。 -/

section KummerSupply360

/-- **(甲) 通用桥** ✓✅：**`Units.map` 的像的幂 ＝ 原像幂的像** ✓ ——
**纯 `MonoidHom` 形** ✓，**全程零强制转换** ✗（**#86 族的一般解** ✓）。 -/
theorem units_map_coe_pow {M : Type u} {N : Type v} [Monoid M] [Monoid N] (f : M →* N) (ρ : Mˣ)
    (m : ℕ) : (((Units.map f ρ : Nˣ)) : N) ^ m = f ((ρ : M) ^ m) := by
  rw [Units.coe_map, ← map_pow]

/-- **(乙) `algebraMap` 档桥** ✓✅：**右端写 `algebraMap` 的应用形** ✓（**须显式补 `rfl`** ✓ —— **§5.1 #89** ✓）。 -/
theorem units_map_algebraMap_coe_pow (F : Type u) [Field F] (R : Type v) [CommRing R]
    [Algebra F R] (ρ : Fˣ) (m : ℕ) :
    (((Units.map (algebraMap F R).toMonoidHom ρ : Rˣ)) : R) ^ m
      = algebraMap F R ((ρ : F) ^ m) := by
  rw [Units.coe_map, ← map_pow]
  rfl

/-- **(丙) 幂一判别** ✓✅：**成像的幂为 `1` ⟺ 原像的幂为 `1`** ✓（**单射 ＋ `map_one`** ✓）——
**此即一般档供给的承重件** ✓。 -/
theorem units_map_algebraMap_pow_eq_one_iff (F : Type u) [Field F] (R : Type v) [CommRing R]
    [Nontrivial R] [Algebra F R] (ρ : Fˣ) (m : ℕ) :
    (((Units.map (algebraMap F R).toMonoidHom ρ : Rˣ)) : R) ^ m = 1 ↔ (ρ : F) ^ m = 1 := by
  have hinj : Function.Injective (algebraMap F R) := algebraMap_injective_of_field_univ F R
  rw [units_map_algebraMap_coe_pow]
  constructor
  · intro h
    exact hinj (by rw [h, map_one])
  · intro h
    rw [h, map_one]

/-- **(丁) 🔴 一般档供给** ✓✅：**`F` 域 ＋ `R` 非平凡 `F`-代数 ＋ `ρ` 为本原 `n` 次单位根 ⟹
`KummerDatum R n a`** ✓✅ —— **§4.141／§4.142 受阻点之解** ✓（**单位群内做幂 ＋ 一次桥出到环** ✓）。 -/
@[instance_reducible] noncomputable def kummerDatumOfAlgebra (F : Type u) [Field F] (R : Type v)
    [CommRing R] [Nontrivial R] [Algebra F R] (n : ℕ) (a : R) (ρ : Fˣ)
    (hprim : IsPrimitiveRoot (ρ : F) n) : KummerDatum R n a where
  ρ := Units.map (algebraMap F R).toMonoidHom ρ
  hρ := (units_map_algebraMap_pow_eq_one_iff F R ρ n).mpr hprim.pow_eq_one
  hpow_dvd := fun m =>
    (units_map_algebraMap_pow_eq_one_iff F R ρ m).trans (hprim.pow_eq_one_iff_dvd m)

/-- **(戊-1) `Fin n` 上本原根的幂互异** ✓✅（**§4.140 的 `ZMod` 版之 `Fin` 对应物** ✓ ——
**互异性由 `ρ` 的阶供给** ✓）。 -/
theorem kummer_pow_fin_ne (F : Type u) [Field F] {n : ℕ} (ρ : Fˣ)
    (hprim : IsPrimitiveRoot (ρ : F) n) {i j : Fin n} (hij : i ≠ j) :
    (ρ : F) ^ i.val ≠ (ρ : F) ^ j.val := by
  intro h
  apply hij
  have hne_i : (ρ : F) ^ i.val ≠ 0 := pow_ne_zero _ (Units.ne_zero ρ)
  have hne_j : (ρ : F) ^ j.val ≠ 0 := pow_ne_zero _ (Units.ne_zero ρ)
  rcases le_total i.val j.val with hle | hle
  · have hd : (ρ : F) ^ (j.val - i.val) = 1 := by
      have h2 : (ρ : F) ^ (i.val + (j.val - i.val)) = (ρ : F) ^ i.val := by
        rw [Nat.add_sub_cancel' hle, ← h]
      rw [pow_add] at h2
      exact mul_left_cancel₀ hne_i (by rw [h2, mul_one])
    have hdvd : n ∣ (j.val - i.val) := (hprim.pow_eq_one_iff_dvd _).mp hd
    have hlt : j.val - i.val < n := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
    have hzero : j.val - i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (by omega)
  · have hd : (ρ : F) ^ (i.val - j.val) = 1 := by
      have h2 : (ρ : F) ^ (j.val + (i.val - j.val)) = (ρ : F) ^ j.val := by
        rw [Nat.add_sub_cancel' hle, h]
      rw [pow_add] at h2
      exact mul_left_cancel₀ hne_j (by rw [h2, mul_one])
    have hdvd : n ∣ (i.val - j.val) := (hprim.pow_eq_one_iff_dvd _).mp hd
    have hlt : i.val - j.val < n := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    have hzero : i.val - j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (by omega)

/-- **(戊) 🔴 `hdiff` 的源侧供给** ✓✅：**本原根的两个不同幂之差是单位** ✓✅ ——
**源侧 `hdiff`（§4.139 的假设）自此自动满足** ✓（**非零 ⟹ 单位 ＋ `IsUnit.map`** ✓）。 -/
theorem isUnit_kummerCoeff_sub_of_primitiveRoot (F : Type u) [Field F] (R : Type v) [CommRing R]
    [Algebra F R] {n : ℕ} (ρ : Fˣ) (hprim : IsPrimitiveRoot (ρ : F) n) (i j : Fin n)
    (hij : i ≠ j) :
    IsUnit ((((Units.map (algebraMap F R).toMonoidHom ρ : Rˣ)) : R) ^ i.val
      - (((Units.map (algebraMap F R).toMonoidHom ρ : Rˣ)) : R) ^ j.val) := by
  have hne : (ρ : F) ^ i.val - (ρ : F) ^ j.val ≠ 0 :=
    sub_ne_zero.mpr (kummer_pow_fin_ne F ρ hprim hij)
  have hunit : IsUnit ((ρ : F) ^ i.val - (ρ : F) ^ j.val) := hne.isUnit
  rw [units_map_algebraMap_coe_pow, units_map_algebraMap_coe_pow, ← map_sub]
  exact hunit.map (algebraMap F R)

/-- **(己) 🔴🔴 源侧可用性收口** ✓✅：**`1 ≤ n` ＋ `IsUnit a` ＋ `IsPrimitiveRoot (ρ:F) n` ⟹
`IsGaloisWithGroup R (kummerCarrier R n a) C_n`** ✓✅ —— **源 `proposition-0-6(a)` 的源侧假设链闭合** ✓
（**实例以具名项供给** ✓ —— **合成器无须回推** ✓）。 -/
theorem kummer_isGaloisWithGroup_of_algebra (F : Type u) [Field F] (R : Type v) [CommRing R]
    [Nontrivial R] [Algebra F R] {n : ℕ} [NeZero n] (hn : 1 ≤ n) (a : R) (ha : IsUnit a)
    (ρ : Fˣ) (hprim : IsPrimitiveRoot (ρ : F) n) :
    @BTier.IsGaloisWithGroup R (kummerCarrier R n a) _ _ _
      (Multiplicative (ZMod n)) _ _
      (@KummerDatum.instMSA R _ n a (kummerDatumOfAlgebra F R n a ρ hprim) _)
      (@KummerDatum.hRG R _ n a (kummerDatumOfAlgebra F R n a ρ hprim) _) := by
  let _inst := kummerDatumOfAlgebra F R n a ρ hprim
  exact KummerDatum.kummer_isGaloisWithGroup (R := R) (n := n) (a := a) hn ha
    (fun i j hij => isUnit_kummerCoeff_sub_of_primitiveRoot F R ρ hprim i j hij)

end KummerSupply360

/-! ### 4.144 🔴🔴🔴 **靶 1ʹ（有限性）第一件：不动环 —— 无条件形**（第 361 轮）
—— **既有件 `SaltGeneric:5128` 的 `[FiniteDimensional K L]` 假设被去掉** ✓（**严格更强** ✓）

**靶** ✓：**§4.2 靶 1ʹ（有限性（甲））之第一件** ✓ —— **不动环 `L^G = K`** ✓，**且不用任何有限性假设** ✗。

**机制（初等，不借 Artin）** ✓：**款③ 的 `δ` 双射** ✓ ＋ **一条线性泛函** ✗：
**(i)** **`im δ ⊆ {L^G-线性映射}`** ✓ —— **每个 `g` 固定 `L^G` 的元素** ✓（`g • (μ * x) = (g • μ) * (g • x) = μ * (g • x)` ✓），
**由 `induction_on` 升为整体** ✓；
**(ii)** **`im δ = End_K L`** ✓（**款③** ✓）⟹ **`End_{L^G}(L) = End_K(L)`** ✓ —— **即『`K`-线性 ⟺ `L^G`-线性』** ✓✅；
**(iii)** **若 `a ∈ L^G \ K`** ✗：取 **`φ : L →ₗ[K] K` 使 `φ 1 = 1`** ✓（`Module.Projective.exists_dual_eq_one` ✓ —— **`K` 域 ⟹ `L` 投射** ✓），
令 **`f := id − φ(·)·1`** ✓ ⟹ **`f 1 = 0`** ✓、**`f a = a − φ(a)·1 ≠ 0`** ✓（**否则 `a = algebraMap (φ a)`** ✗）；
**(iv)** 由 **(ii)** `f` 是 `L^G`-线性 ✓ ⟹ **`f a = f (a · 1) = a · f 1 = 0`** ✗ —— **矛盾** ✓✅。

**⚠ 与既有件的关系** ✓：**`SaltGeneric_ABGV52.lean:5128` 的 `fixedPoints_eq_of_isGaloisWithGroup`** ✓ **走 Artin ＋ 次数** ✓
⟹ **带 `[FiniteDimensional K L]`** ✗；**本件走 `δ` 的像** ✓ ⟹ **无需有限性** ✓✅（**两者结论同形** ✓ ——
**本件为严格更强版** ✓；**既有件保留在册** ✓，**不作废** ✗）。

**⚠ 工艺（两条，入 §5.1）** ✓：**(#91)** **`show` 对 `let`-局部定义须带类型标注** ✗ ——
`show (LinearMap.id - φ.smulRight (1:L)) 1 = 0` 报 **"Function expected … ?m.158"** ✗（**类型未定 ⟹ 不能作函数应用** ✗）⟹
**正解 ＝ `show (… : L →ₗ[K] L) 1 = 0`** ✓；**(#92)** **`rw` 会改写被改写项内部的同名子项** ✗ ——
目标 `algebraMap K L (φ a) = a` 上 `rw [h']`（`h' : a = φ a • 1` ✓）**连 `φ a` 里的 `a` 一起改写** ✗ ⟹
**正解 ＝ 先作 `h2 : algebraMap K L (φ a) = φ a • 1`** ✓ **再 `h2.trans h'.symm`** ✓（**§5.1 #35 同族** ✓）。

**🔴 不声称** ✗：**有限性（甲）未证** ✗（**本件只给不动环** ✓）；**`L` 域档的次数未证** ✗（**须把 `L^G` 与 `K` 的
`finrank` 对齐** ✗ —— **下一手** ✓）；**二分未证** ✗；**源 `theorem-1-2(a)` 未无条件成立** ✗。 -/

section FixedRing361

/-- **🔴🔴 不动环（无条件形）** ✓✅：**`G` 的不动点全在 `K` 的像中** ✓ ——
**不假设 `[FiniteDimensional K L]`** ✗（**较 `SaltGeneric:5128` 严格更强** ✓）。
**机制** ✓：**`δ` 的像 ＝ `End_K L`** ✓（款③ ✓）**而 `im δ` 中的每个映射都是 `L^G`-线性的** ✓
（**每个 `g` 固定 `L^G`** ✓）⟹ **`End_{L^G}(L) = End_K(L)`** ✓ ⟹ **一条 `K`-线性泛函造出的 `f` 既 `K`-线性
（故 `L^G`-线性）又在 `1` 上为 `0`、在 `a` 上非零** ✓ —— **矛盾** ✗。 -/
theorem fixed_mem_of_isGaloisWithGroup {K : Type u} [Field K] {L : Type v} [CommRing L]
    [Nontrivial L] [Algebra K L] {G : Type w} [Group G] [Fintype G] [MulSemiringAction G L]
    (hKL : ∀ (g : G) (r : K) (x : L), g • (r • x) = r • (g • x))
    (hgal : BTier.IsGaloisWithGroup K L G hKL) :
    ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x := by
  intro a ha
  by_contra hne
  obtain ⟨-, -, hbij⟩ := hgal
  obtain ⟨φ, hφ1⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero (α := L))
  let f : L →ₗ[K] L := LinearMap.id - φ.smulRight (1 : L)
  have hf1 : f 1 = 0 := by
    show (LinearMap.id - φ.smulRight (1 : L) : L →ₗ[K] L) 1 = 0
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, hφ1, one_smul,
      sub_self]
  have hfa : f a ≠ 0 := by
    intro h
    apply hne
    have h' : a = φ a • (1 : L) := by
      have h2 : a - φ a • (1 : L) = 0 := h
      exact sub_eq_zero.mp h2
    have h3 : algebraMap K L (φ a) = φ a • (1 : L) := by
      rw [Algebra.smul_def, mul_one]
    exact ⟨φ a, h3.trans h'.symm⟩
  obtain ⟨y, hy⟩ := hbij.2 f
  have hAlin : ∀ y : SkewMonoidAlgebra L G, ∀ μ : L, (∀ g : G, g • μ = μ) → ∀ x : L,
      BTier.deltaToEndRingHom hKL y (μ * x) = μ * BTier.deltaToEndRingHom hKL y x := by
    intro y
    induction y using SkewMonoidAlgebra.induction_on with
    | zero => intro μ _ x; simp
    | single g s =>
      intro μ hμ x
      show BTier.deltaToEndAdd hKL (SkewMonoidAlgebra.single g s) (μ * x)
        = μ * BTier.deltaToEndAdd hKL (SkewMonoidAlgebra.single g s) x
      rw [BTier.deltaToEndAdd_single]
      show s * (g • (μ * x)) = μ * (s * (g • x))
      rw [MulSemiringAction.smul_mul, hμ g]
      ring
    | add y z hy hz =>
      intro μ hμ x
      simp only [map_add, LinearMap.add_apply]
      rw [hy μ hμ x, hz μ hμ x, mul_add]
  have hlin := hAlin y a ha 1
  rw [hy] at hlin
  rw [mul_one, hf1, mul_zero] at hlin
  exact hfa hlin

end FixedRing361

#print axioms kummerDatumSelf
#print axioms units_map_coe_pow
#print axioms units_map_algebraMap_coe_pow
#print axioms units_map_algebraMap_pow_eq_one_iff
#print axioms kummerDatumOfAlgebra
#print axioms kummer_pow_fin_ne
#print axioms isUnit_kummerCoeff_sub_of_primitiveRoot
#print axioms kummer_isGaloisWithGroup_of_algebra
#print axioms fixed_mem_of_isGaloisWithGroup


end ABGV52
