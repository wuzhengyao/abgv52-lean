/-
  ABGV-5.2 —— **本体形式化 B · M2（续作）：Saltman 1984 cor3.4 与 lem3.5**

  蓝图（`wiki/proj-ABGV52-formalize-saltman.md` §1.1 步表第 5、6 行／§3.1 M2 行）：
  「lem3.3 → cor3.4 → lem3.5」（证明全在源中）。本件在已交付的 Swan 引理
  （`SaltSwan_ABGV52.lean`，lem3.3）之上续作，承重链的下一环。

  源（逐字，`raw/Saltman1984.tex`；印刷页 = PDF 页 + 164；label 为主锚）：

  * "localized polynomial retraction"（tex :408）：
    "If \(S\), \(T\) are \(F\) algebras, and \(\phi :S\to T\); \(\psi :T\to S\) are
     \(F\) algebra maps such that \(\psi \circ \phi = \Id_S\), we say that \(S\) is a
     \((\psi ,\phi)\) retraction of \(T\). If the maps need not be specified, \(S\) is
     just called a retraction of \(T\). If \(T\) has the form \(F[x_1,\dots ,x_n](1/w)\),
     we say \(S\) is a localized polynomial retraction."
  * 局部化观察（tex :408–410）：
    "Suppose \(S\), \(T\) are domains and \(S\) is a \((\psi ,\phi)\) retraction of
     \(T\). If \(0\neq s\in S\), then \(S(1/s)\) is a retraction of \(T(1/\phi (s))\)
     via the unique extensions of \(\psi\) and \(\phi\)."
  * cor3.4（tex :426–428）：
    "If \(K/F\) is retract rational, and \(S\subseteq K\) is an affine \(F\) subalgebra
     such that \(q(S)=K\), then for some \(0\neq s\in S\), \(S(1/s)\) is a localized
     polynomial retract."
  * 有用事实（tex :430–432）：
    "Let \(S''\) be a domain with \(q(S'')=K\). For some \(0\neq s''\in S''\), set
     \(S'=S''(1/s'')\). Repeat the process for some \(0\neq s'\in S'\). One now verifies
     that for some \(0\neq s\in S''\), \(S(1/s)=S'(1/s')\); ... if \(s'=t'/(s'')^{n}\)
     then \(S=S''(1/s''t')\)."
  * lem3.5（tex :434–436）：
    "Let \(S\) be an affine \(F\) algebra domain and set \(K=q(S)\). \(K/F\) is retract
     rational if and only if the identity \(i:S\to S\) factors rationally."
    证明（tex :438–452，逐字要点）：正向用 cor3.4（\(S(1/s)\) 是局部化多项式 retract
    ⟹ 包含映射 \(S\to S(1/s)\) 经一个局部化多项式环分解）；反向：给定
    \(0\neq s\in S\)、\(\phi :S\to F[x](1/w)\)、\(\psi :F[x](1/w)\to S(1/s)\)、
    \(\psi\circ\phi=i\)，置 \(v=\phi (s)\)（故 \(\psi (v)=s\)），\(\phi\) 唯一延拓
    \(S(1/s)\to F[x](1/wv)\)，\(\psi\) 唯一延拓 \(F[x](1/wv)\to S(1/s)\)，
    \(\psi\circ\phi\) 在 \(S(1/s)\) 上是恒等。

  形式化约定（与源陈述的偏差，逐条登记）
  =====================================
  * "affine" → `Algebra.FiniteType`；"q(S)=K" → `IsFractionRing S K`（SaltSwan 约定）。
  * 源 "localized polynomial retraction" 形式化为本件 §1 的
    `IsLocalizedPolynomialRetract`；其 ∃-链与 `SaltDef_ABGV52.lean` 的
    `IsRetractRational` 内部件一致（含 SaltDef 已登记的加性收紧 `w ≠ 0`）。
  * **"S(1/s)" 两种读法并用**：子代数读法 `Algebra.adjoin F (S ∪ {s⁻¹})`
    （SaltSwan 约定；cor3.4 的结论、lem3.5 的假设侧），抽象局部化读法
    `IsLocalization.Away s`（§3 的局部化稳定性引理及其复用）。
  * §3 的 `of_localization` 把源的局部化观察写成**一条一般引理**，其复合假设取
    "在局部化映射下等于结构映射"的**一般形式**（源情形 = 复合为恒等的特化；
    lem3.5 反向所需的一般形式同被覆盖）——故 §4、§5 均复用之。
  * **cor3.4 证明中源未验证的一步（加性收紧）**：源以 def3.1 的见证 \(S\) 直接充当
    lem3.3 所需的第二个仿射子代数，但 def3.1 不要求 \(S\) 仿射。本件 §4 补足该步
    （retract rational 的见证可取为**有限型**：\(\psi\) 满射 ⟹ 多项式环的商），
    故 cor3.4 在此闭合。此步为**默认成立但未验证**的补充，非源的陈述。
  * lem3.5 的 "identity \(i:S\to S\) factors rationally" 形式化为
    `FactorsRationally F ↥S ↥S (AlgHom.id F ↥S)`（\(S\) 读作 \(K\) 的仿射子代数，
    与源 "\(S\subseteq K\), \(q(S)=K\)" 一致）。
  * lem3.5 反向的输出侧见证取抽象读法：`IsRetractRational F K` 的实现取
    `S₀ := Localization.Away r`（\(r\) 为 factors-rationally 数据中的 `0 ≠ r : ↥S`），
    K 上的 \(S₀\)-代数结构以 `IsLocalization.Away.liftAlgHom` 沿
    `↥S → K` 下降取得（源中对应"ψ 唯一延拓"一步的下降形式）；
    与子代数读法 `S(1/r) = adjoin F (S ∪ {r⁻¹})` 同构，而 `IsRetractRational`
    的 ∃-量化对两种同构实现不敏感。

  本件结构（§ 号与代码内一致）
  ============================
  §1 def `IsLocalizedPolynomialRetract`（＋`mk'`／`of_algEquiv` 外形锁定）
  §2 单位引理 `isUnit_of_mul_left`
  §3 `of_localization`（局部化稳定性，一般形式）
  §4 `localized_retract_of_witness`（cor3.4 核心）
  §5 `cor3_4`（源 tex :426–428）
  §6 `localize_adjoin_to_away`（`S(1/s)` 两读法的识别引理）
  §7 `lem3_5`（源 tex :434–452，双向）
  §8 非空洞探针（`cor3_4_probe`／`lem3_5_probe_roundtrip`，取 \(K=F\)、\(S=\top\)）
  §9 `#print axioms` 闸门（各声明均三项标准公理）

  **无 sorry、无自造公理**。
-/
import ABGV52.SaltDef_ABGV52
import ABGV52.SaltSwan_ABGV52
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.FiniteType

universe u

namespace ABGV52

/-! ## 1. 局部化多项式 retract（源 tex :408，逐字对应） -/

/-- **源 tex :408 "localized polynomial retraction"（逐字对应）**：`S` 是局部化
多项式 retract ⟺ 存在局部化多项式环 `T = F[x₁,…,xₙ](1/w)`（`w ≠ 0`）与 F-代数
映射 `φ : S → T`、`ψ : T → S`，使得 `ψ ∘ φ = id_S`。 -/
def IsLocalizedPolynomialRetract (F S : Type u) [Field F] [CommRing S] [IsDomain S]
    [Algebra F S] : Prop :=
  ∃ (n : ℕ) (w : MvPolynomial (Fin n) F) (_ : w ≠ 0),
    ∃ (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S),
      ψ.comp φ = AlgHom.id F S

/-- **构造子（兼定义外形锁定）**：`IsLocalizedPolynomialRetract` 的全部见证显式
列出——定义形状若漂移，本构造立即编译失败。 -/
theorem IsLocalizedPolynomialRetract.mk' (F S : Type u) [Field F] [CommRing S] [IsDomain S]
    [Algebra F S] (n : ℕ) (w : MvPolynomial (Fin n) F) (hw : w ≠ 0)
    (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S)
    (h : ψ.comp φ = AlgHom.id F S) : IsLocalizedPolynomialRetract F S :=
  ⟨n, w, hw, φ, ψ, h⟩

/-- **沿 `F`-代数同构搬运**：`S` 是局部化多项式 retract 且 `e : S ≃ₐ[F] T`
⟹ `T` 亦然（沿 `e.symm`／`e` 搬运 φ、ψ，复合等式原样传递）。 -/
theorem IsLocalizedPolynomialRetract.of_algEquiv {F S T : Type u} [Field F] [CommRing S]
    [IsDomain S] [Algebra F S] [CommRing T] [IsDomain T] [Algebra F T] (e : S ≃ₐ[F] T)
    (h : IsLocalizedPolynomialRetract F S) : IsLocalizedPolynomialRetract F T := by
  obtain ⟨n, w, hw, φ, ψ, hcomp⟩ := h
  exact ⟨n, w, hw, φ.comp e.symm.toAlgHom, e.toAlgHom.comp ψ, by
    refine AlgHom.ext fun x => ?_
    show e (ψ (φ (e.symm x))) = x
    have h : ψ (φ (e.symm x)) = e.symm x := by
      have h0 := (AlgHom.ext_iff.mp hcomp) (e.symm x)
      simpa [AlgHom.comp_apply] using h0
    exact (congrArg e h).trans (e.apply_symm_apply x)⟩

/-! ## 2. 交换幺半群中的单位引理（局部化稳定性用） -/

/-- 交换幺半群中：`a * b` 可逆 ⟹ `a` 可逆。（`IsUnit.mul_iff` 碍于
`IsDedekindFiniteMonoid` 限制不可用于一般 `CommMonoid`，此处手证。） -/
private theorem isUnit_of_mul_left {M : Type*} [CommMonoid M] {a b : M}
    (h : IsUnit (a * b)) : IsUnit a := by
  obtain ⟨c, hc⟩ := h.exists_right_inv
  have h1 : a * (b * c) = 1 := by
    rw [← mul_assoc]
    exact hc
  have h2 : (b * c) * a = 1 := by
    rw [mul_comm (b * c) a, ← mul_assoc]
    exact hc
  exact ⟨⟨a, b * c, h1, h2⟩, rfl⟩

/-! ## 3. 局部化稳定性（源的局部化观察，tex :408–410；"有用事实" tex :430 的机制） -/

/-- **局部化稳定性（源 tex :408–410，局部化观察；＝"有用事实" tex :430 的机制）**：

设 `S` 是 F-代数整环，`T = F[x₁,…,xₙ](1/w)` 是局部化多项式环，`S` 经 `(ψ,φ)`
是 `T` 的 retraction（在局部化映射下：`algMap ∘ ψ ∘ φ = algMap`；源情形为
`ψ ∘ φ = id_S`）；设 `0 ≠ s ∈ S`，`S̃ = S(1/s)`（`IsLocalization.Away s S̃`）。
则 `S̃` 是局部化多项式 retract。

构造（源的 "unique extensions"，具体选择如下）：由 `IsLocalization.Away.sec`
取 `a ∈ R`、`k ∈ ℕ` 使 `φ(s) · wᵏ = a`（在 `F[x](1/w)` 中）；置
`P := F[x₁,…,xₙ](1/(w·a))`，`ρ : T →ₐ[F] P` 为沿 `F[x] → P` 的下降
（`w ∣ w·a` ⟹ `w` 在 `P` 中可逆）；`φ̃ : S̃ →ₐ[F] P` 为 `ρ ∘ φ` 沿
`S → S̃` 的下降（`ρ(φ s)` 可逆：`sec` 关系 ＋ `a`、`w` 在 `P` 中可逆）；
`ψ̃ : P →ₐ[F] S̃` 为 `algMap ∘ ψ` 沿 `F[x] → P` 的下降（`w` 在 `T` 中可逆
⟹ 其像在 `S` 中可逆；`ψ(a)` 由 `S` 中单位 `s` 与 `ψ(w)` 之积给出）。复合在
`S` 的像上等于 `algMap`，由 `IsLocalization.algHom_ext` 两次（先在 `P` 上、
再在 `S̃` 上）闭合。 -/
theorem IsLocalizedPolynomialRetract.of_localization {F S : Type u} [Field F] [CommRing S]
    [IsDomain S] [Algebra F S] {St : Type u} [CommRing St] [IsDomain St] [Algebra F St]
    [Algebra S St] [IsScalarTower F S St] (s : S) (hs : s ≠ 0) [IsLocalization.Away s St]
    {n : ℕ} (w : MvPolynomial (Fin n) F) (hw : w ≠ 0)
    (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S)
    (hcomp : (IsScalarTower.toAlgHom F S St).comp (ψ.comp φ) = IsScalarTower.toAlgHom F S St) :
    IsLocalizedPolynomialRetract F St := by
  classical
  -- sec 分解：φ s · wᵏ = a（在 T 中）
  obtain ⟨k, a, hsec⟩ := IsLocalization.Away.surj (x := w) (φ s)
  have hsa : algebraMap S St s ≠ 0 :=
    (IsLocalization.Away.algebraMap_isUnit (x := s) (S := St)).ne_zero
  -- a ≠ 0：否则 φ s = 0（T 中单位算术），沿 ψ 推出 s 的像为 0，与 s 可逆矛盾
  have ha : a ≠ 0 := by
    intro ha0
    have hφs : φ s = 0 := by
      have h0 : φ s
          * (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w) ^ k = 0 := by
        rw [hsec, ha0]
        exact (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w)).map_zero
      obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_pow_isUnit (x := w)
        (S := Localization.Away w) k
      have h1 : φ s * (u : Localization.Away w) = 0 := by
        rw [← hu] at h0
        exact h0
      calc φ s = ((u⁻¹ : (Localization.Away w)ˣ) : Localization.Away w)
            * (u : Localization.Away w) * φ s := by rw [Units.inv_mul, one_mul]
        _ = ((u⁻¹ : (Localization.Away w)ˣ) : Localization.Away w)
            * ((u : Localization.Away w) * φ s) := by rw [mul_assoc]
        _ = ((u⁻¹ : (Localization.Away w)ˣ) : Localization.Away w)
            * (φ s * (u : Localization.Away w)) := by
            rw [mul_comm (u : Localization.Away w) (φ s)]
        _ = ((u⁻¹ : (Localization.Away w)ˣ) : Localization.Away w) * 0 := by rw [h1]
        _ = 0 := mul_zero _
    have h2 : algebraMap S St s = 0 := by
      have h3 : algebraMap S St (ψ (φ s)) = algebraMap S St s := by
        simpa [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] using
          (AlgHom.ext_iff.mp hcomp) s
      rw [hφs, map_zero ψ, (algebraMap S St).map_zero] at h3
      exact h3.symm
    exact hsa h2
  have hwa : w * a ≠ 0 := mul_ne_zero hw ha
  -- P 中 w、a 可逆
  have hunit_w : IsUnit ((IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
      (Localization.Away (w * a))) w) := by
    rw [IsScalarTower.toAlgHom_apply]
    exact IsLocalization.Away.isUnit_of_dvd (x := w * a) (r := w) ⟨a, rfl⟩
  have hunit_a : IsUnit (algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) a) :=
    IsLocalization.Away.isUnit_of_dvd (x := w * a) (r := a) ⟨w, mul_comm w a⟩
  -- ρ : T →ₐ[F] P
  let ρ : Localization.Away w →ₐ[F] Localization.Away (w * a) :=
    IsLocalization.Away.liftAlgHom (x := w)
      (f := IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away (w * a)))
      hunit_w
  have hρ (c : MvPolynomial (Fin n) F) :
      ρ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c)
        = algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) c := by
    show IsLocalization.Away.liftAlgHom (x := w)
        (f := IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away (w * a)))
        hunit_w (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c)
      = algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) c
    rw [IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq (x := w) hunit_w c]
    rw [show (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
        (Localization.Away (w * a))).toRingHom c
      = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
        (Localization.Away (w * a))) c from rfl]
    rw [IsScalarTower.toAlgHom_apply]
  -- ρ (φ s) 可逆
  have hunit_φs : IsUnit ((ρ.comp φ) s) := by
    have h1 : (ρ.comp φ) s * (algebraMap (MvPolynomial (Fin n) F)
          (Localization.Away (w * a)) w) ^ k
        = algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) a := by
      have h := congrArg ρ hsec
      simpa [map_mul, map_pow, AlgHom.comp_apply, hρ] using h
    have h3 : IsUnit ((ρ.comp φ) s
        * (algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) w) ^ k) := by
      rw [h1]
      exact hunit_a
    exact isUnit_of_mul_left h3
  -- φ̃ : S̃ →ₐ[F] P
  let φt : St →ₐ[F] Localization.Away (w * a) :=
    IsLocalization.Away.liftAlgHom (x := s) (f := ρ.comp φ) hunit_φs
  have hφt (x : S) : φt (algebraMap S St x) = ρ (φ x) := by
    show IsLocalization.Away.liftAlgHom (x := s) (f := ρ.comp φ) hunit_φs
        (algebraMap S St x) = ρ (φ x)
    rw [IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq (x := s) hunit_φs x]
    rw [show (ρ.comp φ).toRingHom x = (ρ.comp φ) x from rfl]
    exact AlgHom.comp_apply ρ φ x
  -- ψ(w)、ψ(a) 在 S 中的像（沿 algMap 到 S̃）可逆
  have hunit_ψw : IsUnit (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w)) :=
    IsUnit.map ψ (IsLocalization.Away.algebraMap_isUnit (x := w)
      (S := Localization.Away w))
  have hunit_ψw' : IsUnit (algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F)
      (Localization.Away w) w))) :=
    IsUnit.map (algebraMap S St) hunit_ψw
  have hunit_ψa : IsUnit (algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F)
      (Localization.Away w) a))) := by
    have h : algebraMap S St (ψ (φ s))
        * (algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w))) ^ k
        = algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) a)) := by
      have h0 := congrArg (fun y => algebraMap S St (ψ y)) hsec
      simpa [map_mul, map_pow] using h0
    have hs' : algebraMap S St (ψ (φ s)) = algebraMap S St s := by
      simpa [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] using
        (AlgHom.ext_iff.mp hcomp) s
    rw [← h, hs']
    exact (IsLocalization.Away.algebraMap_isUnit (x := s) (S := St)).mul
      (IsUnit.pow k hunit_ψw')
  -- g : F[x] →ₐ[F] S̃（= algMap ∘ ψ ∘ 结构映射）
  let g : MvPolynomial (Fin n) F →ₐ[F] St :=
    (IsScalarTower.toAlgHom F S St).comp
      (ψ.comp (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away w)))
  have hg (c : MvPolynomial (Fin n) F) : g c = algebraMap S St
      (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c)) := by
    show (IsScalarTower.toAlgHom F S St).comp (ψ.comp
        (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away w))) c
      = algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c))
    rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      IsScalarTower.toAlgHom_apply]
  have hunit_g : IsUnit (g (w * a)) := by
    rw [hg (w * a), map_mul, map_mul, map_mul]
    exact hunit_ψw'.mul hunit_ψa
  -- ψ̃ : P →ₐ[F] S̃
  let ψt : Localization.Away (w * a) →ₐ[F] St :=
    IsLocalization.Away.liftAlgHom (x := w * a) (f := g) hunit_g
  have hψt (c : MvPolynomial (Fin n) F) : ψt (algebraMap (MvPolynomial (Fin n) F)
        (Localization.Away (w * a)) c)
      = algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c)) := by
    show IsLocalization.Away.liftAlgHom (x := w * a) (f := g) hunit_g
        (algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) c)
      = algebraMap S St (ψ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c))
    rw [IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq (x := w * a) hunit_g c]
    rw [show g.toRingHom c = g c from rfl]
    exact hg c
  -- 关键：ψ̃ ∘ ρ = algMap ∘ ψ（两条 T →ₐ[F] S̃ 在 F[x] 的像上一致）
  have hψtρ : ψt.comp ρ = (IsScalarTower.toAlgHom F S St).comp ψ := by
    refine IsLocalization.algHom_ext (W := Submonoid.powers w) ?_
    refine AlgHom.ext fun c => ?_
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
    rw [show (Algebra.algHom F (MvPolynomial (Fin n) F) (Localization.Away w)) c
      = algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) c from rfl]
    rw [hρ c, hψt c]
  -- 复合闭合：ψ̃ ∘ φ̃ = id（先在 F[x] 的像上、再沿 S → S̃ 下降）
  refine IsLocalizedPolynomialRetract.mk' F St n (w * a) hwa φt ψt ?_
  refine IsLocalization.algHom_ext (W := Submonoid.powers s) ?_
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  calc ψt (φt (algebraMap S St x)) = ψt (ρ (φ x)) := by rw [hφt x]
    _ = algebraMap S St (ψ (φ x)) := by
        simpa [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] using
          (AlgHom.ext_iff.mp hψtρ) (φ x)
    _ = algebraMap S St x := by
        simpa [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] using
          (AlgHom.ext_iff.mp hcomp) x

/-! ## 4. cor3.4 的证明核心：见证像 + Swan 对齐 + 局部化稳定性（源 tex :426–428） -/

section Cor34

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- **cor3.4 的核心（源 tex :426–428）**：设 `(S, φ, ψ)` 是 `K` 的 def3.1 见证
（`ψ ∘ φ = id_S`），`T ⊆ K` 是有限型 F 子代数并以 `K` 为分式域；则存在 `0 ≠ s ∈ T`
使 `T(1/s)`（子代数读法）是局部化多项式 retract。

源未验证的一步（见文件头登记）：源的论证把 def3.1 的抽象见证 `S` 直接当作第二个
仿射子代数用。本件补足：`ψ` 满射 ⟹ `S` 有限型且 `S ≅ A := im(S → K)`（A 有限型、
`q(A) = K`）；Swan 引理（lem3.3）把 `T` 与 `A` 对齐到同一子代数，末以 §3 的
局部化稳定性把 retraction 搬到 `T(1/s)`。 -/
private theorem localized_retract_of_witness
    {S : Type u} [CommRing S] [IsDomain S] [Algebra F S] [Algebra S K]
    [IsScalarTower F S K] [IsFractionRing S K] {n : ℕ} {w : MvPolynomial (Fin n) F}
    (hw : w ≠ 0) (φ : S →ₐ[F] Localization.Away w) (ψ : Localization.Away w →ₐ[F] S)
    (hcomp : ψ.comp φ = AlgHom.id F S)
    (T : Subalgebra F K) [Algebra.FiniteType F ↥T] (hT : IsFractionRing ↥T K) :
    ∃ s : ↥T, s ≠ 0 ∧ IsLocalizedPolynomialRetract F
      ↥(Algebra.adjoin F ((T : Set K) ∪ {((s : K))⁻¹})) := by
  classical
  -- 见证在 `K` 中的像 `A = im(S → K)`
  let A : Subalgebra F K := (IsScalarTower.toAlgHom F S K).range
  -- `ψ` 满射（由 `ψ ∘ φ = id`）
  have hψ_surj : Function.Surjective ψ := fun y =>
    ⟨φ y, by simpa [AlgHom.comp_apply] using AlgHom.ext_iff.mp hcomp y⟩
  haveI hfin_S : Algebra.FiniteType F S := Algebra.FiniteType.of_surjective ψ hψ_surj
  -- `S → ↥A` 满射（A 就是它的像）
  let jA : S →ₐ[F] ↥A := (IsScalarTower.toAlgHom F S K).codRestrict A
    fun y => (AlgHom.mem_range _).mpr ⟨y, rfl⟩
  have hA_surj : Function.Surjective jA := fun y => by
    obtain ⟨y', hy'⟩ := (AlgHom.mem_range _).mp y.2
    exact ⟨y', Subtype.ext hy'⟩
  haveI hfin_A : Algebra.FiniteType F ↥A := Algebra.FiniteType.of_surjective jA hA_surj
  -- `q(A) = K`：`A ≅ S` 沿 `algebraMap S K`
  have hfrac_A : IsFractionRing ↥A K := by
    have hinj : Function.Injective jA.toRingHom := by
      intro a b hab
      have h2 : (IsScalarTower.toAlgHom F S K) a
          = (IsScalarTower.toAlgHom F S K) b :=
        congrArg (fun u : ↥A => (u : K)) hab
      rw [IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply] at h2
      exact IsFractionRing.injective S K h2
    let e : S ≃+* ↥A := RingEquiv.ofBijective jA.toRingHom ⟨hinj, hA_surj⟩
    refine IsFractionRing.of_ringEquiv_left e.symm (fun y => ?_)
    show algebraMap ↥A K y = algebraMap S K (e.symm y)
    have h2 : ((e (e.symm y) : ↥A) : K) = algebraMap S K (e.symm y) := by
      show ((jA (e.symm y) : ↥A) : K) = algebraMap S K (e.symm y)
      exact IsScalarTower.toAlgHom_apply (R := F) (S := S) (A := K) (e.symm y)
    rw [e.apply_symm_apply y] at h2
    exact h2
  -- Swan 引理（lem3.3）：把 `T` 与 `A` 对齐到同一子代数
  obtain ⟨sT, sA, hsT, hsA, hEq⟩ := swan_localization_common T A hT hfrac_A
  -- `sA` 的原像 `x ∈ S`（非零）
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp sA.2
  have hsA' : (sA : K) ≠ 0 := fun h => hsA ((Subalgebra.coe_eq_zero A).mp h)
  have hx0 : x ≠ 0 := by
    intro h0
    refine hsA' ?_
    rw [← hx, h0, map_zero]
  -- `St := A(1/sA)`（子代数读法）的生成元与包含映射
  have hmem : (sA : K) ∈ Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹}) :=
    Algebra.subset_adjoin (Set.mem_union_left _ sA.2)
  have hinv_mem : ((sA : K))⁻¹ ∈ Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹}) :=
    Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
  let j : S →ₐ[F] ↥(Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹})) :=
    (IsScalarTower.toAlgHom F S K).codRestrict
      (Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹}))
      fun y => Algebra.subset_adjoin (Set.mem_union_left _
        ((AlgHom.mem_range (IsScalarTower.toAlgHom F S K)).mpr ⟨y, rfl⟩))
  -- `St` 上的 `S`-代数结构与标量塔（局部化稳定性的一般假设）
  letI : Algebra S ↥(Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹})) :=
    j.toRingHom.toAlgebra
  haveI : IsScalarTower F S ↥(Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹})) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      refine Subtype.ext ?_
      show (algebraMap F K) c = (IsScalarTower.toAlgHom F S K) ((algebraMap F S) c)
      rw [IsScalarTower.toAlgHom_apply, IsScalarTower.algebraMap_apply F S K]
  -- `sA`（即 `x` 的像）是 `St` 中的单位
  have hunit_st : IsUnit ((⟨(sA : K), hmem⟩ : ↥(Algebra.adjoin F
      ((A : Set K) ∪ {((sA : K))⁻¹})))) :=
    ⟨⟨⟨(sA : K), hmem⟩, ⟨((sA : K))⁻¹, hinv_mem⟩,
      Subtype.ext (by simp [mul_inv_cancel₀ hsA']),
      Subtype.ext (by simp [inv_mul_cancel₀ hsA'])⟩, rfl⟩
  have hjx : j x = (⟨(sA : K), hmem⟩ : ↥(Algebra.adjoin F
      ((A : Set K) ∪ {((sA : K))⁻¹}))) := by
    refine Subtype.ext ?_
    show (IsScalarTower.toAlgHom F S K) x = (sA : K)
    exact hx
  -- `St = S(1/x)`：在 `St` 上装配 `IsLocalization.Away x`
  haveI hloc : IsLocalization.Away x ↥(Algebra.adjoin F
      ((A : Set K) ∪ {((sA : K))⁻¹})) := by
    refine IsLocalization.Away.mk (R := S) (S := ↥(Algebra.adjoin F
      ((A : Set K) ∪ {((sA : K))⁻¹}))) x ?_ ?_ ?_
    · show IsUnit (j x)
      rw [hjx]
      exact hunit_st
    · intro z
      obtain ⟨m, t, ht⟩ := fraction_extraction A (s := sA) hsA (x := (z : K)) z.2
      obtain ⟨a, ha⟩ := (AlgHom.mem_range _).mp t.2
      refine ⟨m, a, ?_⟩
      refine Subtype.ext ?_
      show (z : K) * ((IsScalarTower.toAlgHom F S K) x) ^ m
        = (IsScalarTower.toAlgHom F S K) a
      rw [hx, ha]
      exact ht
    · intro a b hab
      have h1 : (IsScalarTower.toAlgHom F S K) a
          = (IsScalarTower.toAlgHom F S K) b :=
        congrArg (fun u : ↥(Algebra.adjoin F
          ((A : Set K) ∪ {((sA : K))⁻¹})) => (u : K)) hab
      rw [IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply] at h1
      have h2 : a = b := IsFractionRing.injective S K h1
      exact ⟨0, by simp [h2]⟩
  -- §3 的局部化稳定性：`St` 是局部化多项式 retract
  have hres : IsLocalizedPolynomialRetract F ↥(Algebra.adjoin F
      ((A : Set K) ∪ {((sA : K))⁻¹})) :=
    IsLocalizedPolynomialRetract.of_localization (F := F) (S := S)
      (St := ↥(Algebra.adjoin F ((A : Set K) ∪ {((sA : K))⁻¹}))) x hx0
      (n := n) w hw φ ψ (by rw [hcomp, AlgHom.comp_id])
  -- 经 Swan 对齐 `A(1/sA) = T(1/sT)` 换成源结论的形态
  refine ⟨sT, hsT, ?_⟩
  rw [hEq]
  exact hres

end Cor34

/-! ## 5. cor3.4（源 tex :426–428，逐字对应） -/

/-- **cor3.4（源 tex :426–428，逐字）**：设 `K/F` retract rational，`↥S ⊆ K` 是仿射
F-子代数（`Algebra.FiniteType`）且 `q(S) = K`（`IsFractionRing`）。则存在
`0 ≠ s : ↥S`，使 `S(1/s)`（子代数读法 `F[S ∪ {s⁻¹}]`）是局部化多项式 retract。 -/
theorem cor3_4 {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S : Subalgebra F K) [Algebra.FiniteType F ↥S] (hS : IsFractionRing ↥S K)
    (hrt : IsRetractRational F K) :
    ∃ s : ↥S, s ≠ 0 ∧ IsLocalizedPolynomialRetract F
      ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) := by
  obtain ⟨S₀, hCR, hDom, hAFS, hASL, hTSL, hFrac, n, w, hw, φ, ψ, hcomp⟩ := hrt
  let : CommRing S₀ := hCR
  let : IsDomain S₀ := hDom
  let : Algebra F S₀ := hAFS
  let : Algebra S₀ K := hASL
  let : IsScalarTower F S₀ K := hTSL
  let : IsFractionRing S₀ K := hFrac
  exact localized_retract_of_witness hw φ ψ hcomp S hS

/-! ## 6. 识别引理：`S(1/s)` 的子代数读法 → 抽象局部化读法（源 tex :438–452 中
"unique extension" 步骤的下降形式） -/

/-- **识别引理**：设 `s : ↥S`、`s ≠ 0`，`St := F[S ∪ {s⁻¹}]`（`S(1/s)` 的子代数读法）。
则存在 F-代数映射 `v : ↥St →ₐ[F] Localization.Away s`，它在 `S` 上等于结构映射
`algebraMap ↥S (Localization.Away s)`——即两种读法在 `S` 上相容（由
`IsLocalization.Away.mk` 手工验证局部化泛性质，再以 `IsLocalization.Away.liftAlgHom`
取得 `v`）。 -/
private theorem localize_adjoin_to_away {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S : Subalgebra F K) (s : ↥S) (hs : s ≠ 0) :
    ∃ v : ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) →ₐ[F] Localization.Away s,
      ∀ x : ↥S,
        v (Subalgebra.inclusion (fun y hy => Algebra.subset_adjoin (Set.mem_union_left _ hy)) x)
          = algebraMap ↥S (Localization.Away s) x := by
  have hle : S ≤ Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹}) :=
    fun y hy => Algebra.subset_adjoin (Set.mem_union_left _ hy)
  let incl : ↥S →ₐ[F] ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) :=
    Subalgebra.inclusion hle
  letI : Algebra ↥S ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) :=
    incl.toRingHom.toAlgebra
  haveI : IsScalarTower F ↥S ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      refine Subtype.ext ?_
      show (algebraMap F K) c
        = (IsScalarTower.toAlgHom F ↥S K) ((algebraMap F ↥S) c)
      rw [IsScalarTower.toAlgHom_apply, IsScalarTower.algebraMap_apply F ↥S K]
  have hsK : (s : K) ≠ 0 := fun h => hs (Subtype.ext h)
  have hmem : (s : K) ∈ Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹}) :=
    Algebra.subset_adjoin (Set.mem_union_left _ s.2)
  have hinv_mem : ((s : K))⁻¹ ∈ Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹}) :=
    Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton _))
  have hunit_st : IsUnit ((⟨(s : K), hmem⟩ : ↥(Algebra.adjoin F
      ((S : Set K) ∪ {((s : K))⁻¹})))) :=
    ⟨⟨⟨(s : K), hmem⟩, ⟨((s : K))⁻¹, hinv_mem⟩,
      Subtype.ext (by simp [mul_inv_cancel₀ hsK]),
      Subtype.ext (by simp [inv_mul_cancel₀ hsK])⟩, rfl⟩
  have hloc : IsLocalization.Away s ↥(Algebra.adjoin F
      ((S : Set K) ∪ {((s : K))⁻¹})) := by
    refine IsLocalization.Away.mk (R := ↥S) (S := ↥(Algebra.adjoin F
      ((S : Set K) ∪ {((s : K))⁻¹}))) s ?_ ?_ ?_
    · have h1 : algebraMap ↥S ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) s
          = (⟨(s : K), hmem⟩ : ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹}))) := by
        refine Subtype.ext ?_
        rfl
      rw [h1]
      exact hunit_st
    · intro z
      obtain ⟨m, t, ht⟩ := fraction_extraction S (s := s) hs (x := (z : K)) z.2
      refine ⟨m, t, ?_⟩
      refine Subtype.ext ?_
      show (z : K) * (s : K) ^ m = (t : K)
      exact ht
    · intro a b hab
      have h1 : (a : K) = (b : K) := congrArg (fun u : ↥(Algebra.adjoin F
        ((S : Set K) ∪ {((s : K))⁻¹})) => (u : K)) hab
      exact ⟨0, by simp [Subtype.ext h1]⟩
  have hf : IsUnit ((IsScalarTower.toAlgHom F ↥S (Localization.Away s)) s) :=
    IsLocalization.Away.algebraMap_isUnit (x := s) (S := Localization.Away s)
  let v : ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) →ₐ[F] Localization.Away s :=
    IsLocalization.Away.liftAlgHom (x := s)
      (f := IsScalarTower.toAlgHom F ↥S (Localization.Away s)) hf
  refine ⟨v, fun x => ?_⟩
  change IsLocalization.Away.liftAlgHom (x := s)
      (f := IsScalarTower.toAlgHom F ↥S (Localization.Away s)) hf
      (algebraMap ↥S ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) x)
    = algebraMap ↥S (Localization.Away s) x
  rw [IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (x := s) hf x]
  rfl

/-! ## 7. lem3.5（源 tex :434–452，逐字对应；两方向证明均据源） -/

/-- **lem3.5（源 tex :434–436，逐字）**：设 `S ⊆ K` 是仿射 F-代数整环
（`Algebra.FiniteType`）且 `K = q(S)`（`IsFractionRing`）。则 `K/F` retract rational
当且仅当恒等映射 `i : S → S` factors rationally（`FactorsRationally F ↥S ↥S
(AlgHom.id F ↥S)`）。

⟸ 方向（源 tex :438–445）：设 `i` factors rationally，即存在 `0 ≠ w ∈ F[x]`、
`0 ≠ r ∈ S` 与 `f₁ : S → F[x](1/w)`、`f₂ : F[x](1/w) → S(1/r)`。取 `k` 使
`f₁(r)·w̄^k = ā`（`ā` 为 `F[x]` 的像）；在 `P := F[x](1/(w·a))` 中作下降映射
`c : F[x](1/w) → P`、`φ' : S(1/r) → P`、`ψ' : P → S(1/r)`，验证 `ψ'∘φ' = id`；
再沿 `f₂` 侧把 K 上的 `S(1/r)`-代数结构下降，并以
`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` 取证据。 -/
theorem lem3_5 {F K : Type u} [Field F] [Field K] [Algebra F K]
    (S : Subalgebra F K) [Algebra.FiniteType F ↥S] (hS : IsFractionRing ↥S K) :
    IsRetractRational F K ↔ FactorsRationally F ↥S ↥S (AlgHom.id F ↥S) := by
  constructor
  · intro hrt
    obtain ⟨s, hs, n, w, hw, φ, ψ, hcomp⟩ := cor3_4 S hS hrt
    obtain ⟨v, hv⟩ := localize_adjoin_to_away S s hs
    let incl : ↥S →ₐ[F] ↥(Algebra.adjoin F ((S : Set K) ∪ {((s : K))⁻¹})) :=
      Subalgebra.inclusion fun y hy => Algebra.subset_adjoin (Set.mem_union_left _ hy)
    refine ⟨n, w, hw, s, hs, φ.comp incl, v.comp ψ, fun x => ?_⟩
    show algebraMap ↥S (Localization.Away s) x = v (ψ (φ (incl x)))
    have h1 : ψ (φ (incl x)) = incl x := by
      have h2 := (AlgHom.ext_iff.mp hcomp) (incl x)
      simpa [AlgHom.comp_apply] using h2
    rw [h1]
    exact (hv x).symm
  · intro hFR
    obtain ⟨n, w, hw, r, hr, f₁, f₂, hcomp⟩ := hFR
    -- f₁ r 的分解：f₁ r * w̄^k = ā（在 F[x](1/w) 中）
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (x := w) (f₁ r)
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hunit : IsUnit ((algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w) ^ k) :=
        (IsLocalization.Away.algebraMap_isUnit (x := w) (S := Localization.Away w)).pow k
      have h0 : f₁ r * (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w) ^ k
          = 0 := by
        rw [ha, ha0, map_zero]
      obtain ⟨u, hu⟩ := hunit
      have h2 : f₁ r = 0 := by
        have h3 : f₁ r * (u : Localization.Away w) = 0 := by
          rw [hu]
          exact h0
        have h4 : (f₁ r * (u : Localization.Away w)) * ↑(u⁻¹) = 0 := by
          rw [h3, zero_mul]
        rwa [mul_assoc, Units.mul_inv, mul_one] at h4
      have h5 : algebraMap ↥S (Localization.Away r) r = 0 := by
        simpa [AlgHom.id_apply, h2] using hcomp r
      exact hr (IsLocalization.injective (Localization.Away r)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hr) (by rw [h5, map_zero]))
    have hW_ne : w * a ≠ 0 := mul_ne_zero hw ha_ne
    -- P := F[x](1/(w·a)) 中 w、a 可逆
    have hw_unit_W : IsUnit ((IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
        (Localization.Away (w * a))) w) := by
      rw [IsScalarTower.toAlgHom_apply]
      exact IsLocalization.Away.isUnit_of_dvd (x := w * a) (r := w) ⟨a, rfl⟩
    have ha_unit_W : IsUnit ((IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
        (Localization.Away (w * a))) a) := by
      rw [IsScalarTower.toAlgHom_apply]
      exact IsLocalization.Away.isUnit_of_dvd (x := w * a) (r := a) ⟨w, mul_comm w a⟩
    -- c : F[x](1/w) → F[x](1/(w·a))（沿 w ∣ w·a 的下降）
    let c : Localization.Away w →ₐ[F] Localization.Away (w * a) :=
      IsLocalization.Away.liftAlgHom (x := w)
        (f := IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away (w * a)))
        hw_unit_W
    have hc (z : MvPolynomial (Fin n) F) :
        c (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) z)
          = algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) z := by
      show IsLocalization.Away.liftAlgHom (x := w)
          (f := IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away (w * a)))
          hw_unit_W (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) z)
        = algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) z
      rw [IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq (x := w) hw_unit_W z]
      rfl
    -- c (f₁ r) 可逆
    have hcv : IsUnit ((c.comp f₁) r) := by
      have h1 : c (f₁ r) * (algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) w) ^ k
          = algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) a := by
        have h2 := congrArg c ha
        simpa [map_mul, map_pow, hc w, hc a] using h2
      have h3 : IsUnit (c (f₁ r) * (algebraMap (MvPolynomial (Fin n) F)
          (Localization.Away (w * a)) w) ^ k) := by
        rw [h1]
        exact ha_unit_W
      exact isUnit_of_mul_left h3
    -- φ' : S(1/r) → F[x](1/(w·a))（c ∘ f₁ 沿 r 的下降）
    let φ' : Localization.Away r →ₐ[F] Localization.Away (w * a) :=
      IsLocalization.Away.liftAlgHom (x := r) (f := c.comp f₁) hcv
    have hφ' (y : ↥S) : φ' (algebraMap ↥S (Localization.Away r) y) = c (f₁ y) := by
      show IsLocalization.Away.liftAlgHom (x := r) (f := c.comp f₁) hcv
          (algebraMap ↥S (Localization.Away r) y) = c (f₁ y)
      rw [IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq (x := r) hcv y]
      rw [show (c.comp f₁).toRingHom y = (c.comp f₁) y from rfl]
      exact AlgHom.comp_apply c f₁ y
    -- g := f₂ ∘（F[x] → F[x](1/w)）
    let g : MvPolynomial (Fin n) F →ₐ[F] Localization.Away r :=
      f₂.comp (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (Localization.Away w))
    have hg (z : MvPolynomial (Fin n) F) :
        g z = f₂ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) z) := by
      show f₂ ((IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F)
          (Localization.Away w)) z)
        = f₂ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) z)
      rw [IsScalarTower.toAlgHom_apply]
    -- g (w·a) 可逆（源 tex :443–445 的记账：f₂(ā) = r·f₂(w̄)^k）
    have hunit_g : IsUnit (g (w * a)) := by
      have h2 : f₂ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) a)
          = algebraMap ↥S (Localization.Away r) r
            * (f₂ (algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) w)) ^ k := by
        have h3 := congrArg f₂ ha
        rw [map_mul, map_pow] at h3
        rw [← h3]
        rw [show f₂ (f₁ r) = algebraMap ↥S (Localization.Away r) r from (hcomp r).symm]
      rw [hg (w * a), map_mul, map_mul, h2]
      exact (IsUnit.map f₂ (IsLocalization.Away.algebraMap_isUnit (x := w)
          (S := Localization.Away w))).mul
        ((IsLocalization.Away.algebraMap_isUnit (x := r)
            (S := Localization.Away r)).mul
          (IsUnit.pow k (IsUnit.map f₂ (IsLocalization.Away.algebraMap_isUnit (x := w)
            (S := Localization.Away w)))))
    -- ψ' : F[x](1/(w·a)) → S(1/r)（g 沿 w·a 的下降）
    let ψ' : Localization.Away (w * a) →ₐ[F] Localization.Away r :=
      IsLocalization.Away.liftAlgHom (x := w * a) (f := g) hunit_g
    have hψ' (z : MvPolynomial (Fin n) F) : ψ' (algebraMap (MvPolynomial (Fin n) F)
        (Localization.Away (w * a)) z) = g z := by
      show IsLocalization.Away.liftAlgHom (x := w * a) (f := g) hunit_g
          (algebraMap (MvPolynomial (Fin n) F) (Localization.Away (w * a)) z) = g z
      rw [IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq (x := w * a) hunit_g z]
      rw [show g.toRingHom z = g z from rfl]
    -- ψ' ∘ c = f₂（在生成元上）
    have hψ'c : ψ'.comp c = f₂ := by
      refine IsLocalization.algHom_ext (W := Submonoid.powers w) ?_
      refine AlgHom.ext fun z => ?_
      simp only [AlgHom.comp_apply]
      rw [show (Algebra.algHom F (MvPolynomial (Fin n) F) (Localization.Away w)) z
        = algebraMap (MvPolynomial (Fin n) F) (Localization.Away w) z from rfl]
      rw [hc z, hψ' z]
      exact hg z
    -- ψ' ∘ φ' = id
    have hmain : ψ'.comp φ' = AlgHom.id F (Localization.Away r) := by
      refine IsLocalization.algHom_ext (W := Submonoid.powers r) ?_
      refine AlgHom.ext fun y => ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [show (Algebra.algHom F ↥S (Localization.Away r)) y
        = algebraMap ↥S (Localization.Away r) y from rfl]
      rw [hφ' y]
      rw [show ψ' (c (f₁ y)) = f₂ (f₁ y) from (AlgHom.ext_iff.mp hψ'c) (f₁ y)]
      exact (hcomp y).symm
    -- 见证：S' := S(1/r)；K 上的 S'-代数结构沿 f₂ 侧下降到 K
    have hunit_r : IsUnit ((IsScalarTower.toAlgHom F ↥S K) r) := by
      rw [IsScalarTower.toAlgHom_apply]
      exact isUnit_iff_ne_zero.mpr
        (fun h => hr (IsFractionRing.injective ↥S K (by rw [h, map_zero])))
    let hK : Localization.Away r →ₐ[F] K :=
      IsLocalization.Away.liftAlgHom (x := r) (f := IsScalarTower.toAlgHom F ↥S K) hunit_r
    letI : Algebra (Localization.Away r) K := hK.toRingHom.toAlgebra
    have hKlift (y : ↥S) : hK (algebraMap ↥S (Localization.Away r) y)
        = algebraMap ↥S K y := by
      show IsLocalization.Away.liftAlgHom (x := r) (f := IsScalarTower.toAlgHom F ↥S K) hunit_r
          (algebraMap ↥S (Localization.Away r) y) = algebraMap ↥S K y
      rw [IsLocalization.Away.liftAlgHom_apply,
        IsLocalization.Away.lift_eq (x := r) hunit_r y]
      rfl
    have hTK : IsScalarTower ↥S (Localization.Away r) K :=
      IsScalarTower.of_algebraMap_eq fun y => (hKlift y).symm
    have hFK : IsScalarTower F (Localization.Away r) K :=
      IsScalarTower.of_algebraMap_eq fun c => by
        show algebraMap F K c = hK (algebraMap F (Localization.Away r) c)
        rw [IsScalarTower.algebraMap_apply F ↥S (Localization.Away r) c]
        rw [hKlift ((algebraMap F ↥S) c), IsScalarTower.algebraMap_apply F ↥S K c]
    haveI hdom : IsDomain (Localization.Away r) :=
      IsLocalization.Away.isDomain (Localization.Away r) hr
    haveI hfrac : IsFractionRing (Localization.Away r) K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r)
        (Localization.Away r) K
    exact IsRetractRational.mk' F K (Localization.Away r) n (w * a) hW_ne φ' ψ' hmain

/-! ## 8. 非空洞探针（L1：两名题均取 `K = F`、`S = ⊤` 的实例实际调用） -/

section Probes

/-- 探针（cor3.4 非空洞）：基例 `K = F`、`S = ⊤ ⊆ F`（`isRetractRational_self` 的见证）
上实际调用 cor3.4，产出 `s` 与局部化多项式 retract 的见证数据。 -/
theorem cor3_4_probe (F : Type u) [Field F] :
    ∃ s : ↥(⊤ : Subalgebra F F), s ≠ 0 ∧ IsLocalizedPolynomialRetract F
      ↥(Algebra.adjoin F (((⊤ : Subalgebra F F) : Set F) ∪ {((s : F))⁻¹})) := by
  haveI : Algebra.FiniteType F ↥(⊤ : Subalgebra F F) := finiteType_top_self F
  exact cor3_4 (⊤ : Subalgebra F F) (isFractionRing_top_self F) (isRetractRational_self F)

/-- 探针（lem3.5 双向回环）：同一基例上先走 `⟹` 取出 factors-rationally 数据，
再走 `⟸` 把该数据转回 `IsRetractRational F F`——两方向均实际执行（非空洞调用）。 -/
theorem lem3_5_probe_roundtrip (F : Type u) [Field F] : IsRetractRational F F := by
  haveI : Algebra.FiniteType F ↥(⊤ : Subalgebra F F) := finiteType_top_self F
  exact (lem3_5 (⊤ : Subalgebra F F) (isFractionRing_top_self F)).mpr
    ((lem3_5 (⊤ : Subalgebra F F) (isFractionRing_top_self F)).mp (isRetractRational_self F))

end Probes

/-! ## 9. `#print axioms` 闸门（每条声明须恰为 propext／Classical.choice／Quot.sound） -/

#print axioms IsLocalizedPolynomialRetract
#print axioms IsLocalizedPolynomialRetract.mk'
#print axioms IsLocalizedPolynomialRetract.of_algEquiv
#print axioms IsLocalizedPolynomialRetract.of_localization
#print axioms localized_retract_of_witness
#print axioms cor3_4
#print axioms localize_adjoin_to_away
#print axioms lem3_5
#print axioms cor3_4_probe
#print axioms lem3_5_probe_roundtrip

end ABGV52
