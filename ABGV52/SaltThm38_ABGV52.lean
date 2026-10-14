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
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single m 1)) hfix
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
      (p := fun x _ => ∀ g : G, g • x = x) ?_ ?_ ?_ ?_ ?_
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


end ABGV52
