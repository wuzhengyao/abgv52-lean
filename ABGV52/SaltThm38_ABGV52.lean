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

end ABGV52
