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
import ABGV52.SaltLocalLift_ABGV52
import ABGV52.SaltCor_ABGV52
import Mathlib.RingTheory.Localization.InvSubmonoid
open TensorProduct MvPolynomial
universe u
noncomputable section

namespace ABGV52

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

end ABGV52
