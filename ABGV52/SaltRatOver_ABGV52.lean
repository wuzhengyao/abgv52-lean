/-
  ABGV-5.2 —— ③ Procesi 消费端接线 · File 1：retract 理性沿「有理 over」保持

  目标（派发件 ③ 消费端接线；本件 = 通用引理层，②③ 共用）
  ========================================================
  论文 `thm:retract`（`raw/ABGV-5.2-resolution.tex`，第三十二改后）主链结论侧的
  **最后一块一般域论**：若 `L` 在 `F` 上 retract rational，而 `K` 在 `L` 上有理
  （`K ≅ₐ[L] L(t₁,…,tₙ)`），则 `K` 在 `F` 上 retract rational。

  本件交付三项：
    * `IsRationalOver L K` —— 谓词「`K` 在 `L` 上有理」
      （定义为 `∃ n, Nonempty (K ≃ₐ[L] rationalFunctionField L n)`）＋ 类型锁定
      ＋ 探针（L1 非空洞：`L(t)` 与 `L` 自身均满足）；
    * `isRetractRational_rationalFunctionField_of_isRetractRational` —— 核心引理：
      `L/F` retract rational ⟹ `L(t₁,…,tₙ)/F` retract rational（两塔构造）；
    * `isRetractRational_of_isRationalOver` —— 主引理：`IsRationalOver L K` ＋
      `IsRetractRational F L` ⟹ `IsRetractRational F K`（核心引理经 `≃ₐ[L]` 搬运）。

  证明路线（核心引理，两塔构造）
  ==============================
  设 `(S, φ, ψ)` 是 `L` 的 retract 见证：`S ⊆ L` 分式域、`w ∈ F[x₁,…,xₘ] \ {0}`、
  `φ : S →ₐ[F] F[x](1/w)`、`ψ : F[x](1/w) →ₐ[F] S`、`ψ ∘ φ = id_S`。对 `K₀ = L(t₁,…,tₙ)`
  造新见证：
    * `S' := S[t₁,…,tₙ] = MvPolynomial (Fin n) S`（系数塔）；
    * `w' := rename (Fin.castAdd n) w ∈ F[x₁,…,x_{m+n}]`（前 m 个变元 = 原坐标，
      后 n 个 = t 坐标）；
    * `ψw : F[x](1/w) →ₐ[F] F[x₁,…,x_{m+n}](1/w')` —— 沿 `rename` 的嵌入；
    * `φ' : S[t] →ₐ[F] F[x₁,…,x_{m+n}](1/w')` —— 系数走 `ψw ∘ φ`、`t_j ↦ x_{m+j}`
      （`aevalTower`）；
    * `ψ' : F[x₁,…,x_{m+n}](1/w') →ₐ[F] S[t]` —— 沿 `w'` 下降（`Away.liftAlgHom`），
      把 `x_i`（i < m）送到 `C (ψ (x_i))`、把 `x_{m+j}` 送到 `t_j`；由此
      `ψ' ∘ ψw = C ∘ ψ`（`algHom_ext` 于局部化）。
  复合检查 `ψ' ∘ φ' = id_{S[t]}`：在 `C s` 上由 `ψ' ∘ ψw = C ∘ ψ` 与 `ψ ∘ φ = id`
  得；在 `t_j` 上直接计算。最后 `K = Frac(L[t])` 上的 `S[t]`-代数结构由
  `φc = (L[t] ↪ K) ∘ (S[t] → L[t])`（系数扩张）给出，`IsFractionRing S[t] K` 走
  `isLocalization_iff` 三条件（单位：系数扩张与分式环嵌入均单；剩余：两段
  `IsLocalization.surj` 通分；唯一性：系数扩张单），并给
  `IsScalarTower F S[t] K`。三件齐备后交 `IsRetractRational.mk'`。

  与既有件的关系：本件不改动任何既有文件。`SaltT2` 的
  `isRetractRational_rationalFunctionField`（`L = F` 特例）与 §4 探针经「有理 over」
  绕行二次导出同一命题——两条独立路线互为对照（L19 正例）。

  形式化约定（与自然语言的偏差，逐条登记）
  =====================================
  ① 「`K` 在 `L` 上有理」的形式化 = `∃ n, Nonempty (K ≃ₐ[L] rationalFunctionField L n)`，
     与 D1 的 `EM.IsRational`（基为 `F`）逐字同形，此处把基一般化为 `L`；桥引理
     `isRationalOver_iff_isRational` 为 `Iff.rfl`（定义级同一）。
  ② 核心引理（多项式扩张保持 retract 理性）本件**自证**——两塔构造是本文件给出的
     证明，不是对某条具名引文的转述，故按防幽灵引用纪律**不写** locator；论文
     `thm:retract` 中该步为域论包装（`F(V)^H ≅ F(M|_H)^H` 且右侧有理），本件
     形式化的是同一数学内容的一般形。
  ③ 宇宙 pin：全部量在 `Type u`（与 `IsRetractRational`/`mk'` 一致）；`EM.IsRational`
     是 `Type*`，桥引理在 `Type u` 实例化。
  ④ 非计算性：局部化提升与 `liftAlgHom` 非计算，但全部出现于 `Prop`-层证明，
     不影响复算性；§5 逐条核 `#print axioms`（仅 3 标准公理）。

  **无 sorry、无自造公理。**
-/
import ABGV52.SaltT2_ABGV52
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization

universe u

namespace ABGV52

/-! ## 1. 谓词「有理 over」与类型锁定 -/

/-- **「有理 over」**：`K` 在 `L` 上有理，即 `K ≅ₐ[L] L(t₁,…,tₙ)`（某 `n`）。
与 D1 的 `EM.IsRational`（基为 `F`）逐字同形，基一般化为 `L`（②③ 共用）。 -/
def IsRationalOver (L : Type u) [Field L] (K : Type u) [Field K] [Algebra L K] : Prop :=
  ∃ n : ℕ, Nonempty (K ≃ₐ[L] EM.rationalFunctionField L n)

/-- **类型锁定**：`IsRationalOver` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
theorem isRationalOver_typeLock (L : Type u) [Field L] (K : Type u) [Field K]
    [Algebra L K] :
    IsRationalOver L K = (∃ n : ℕ, Nonempty (K ≃ₐ[L] EM.rationalFunctionField L n)) :=
  rfl

/-- 与 D1 `EM.IsRational` 的桥：同一 `∃`-形（定义级同一，`Iff.rfl`）。 -/
theorem isRationalOver_iff_isRational (L : Type u) [Field L] (K : Type u) [Field K]
    [Algebra L K] : IsRationalOver L K ↔ EM.IsRational L K :=
  Iff.rfl

/-! ## 2. 非空洞探针（L1：谓词类非空，两条） -/

/-- 探针一：`L(t₁,…,tₙ)` 在 `L` 上有理。 -/
theorem isRationalOver_rationalFunctionField (L : Type u) [Field L] (n : ℕ) :
    IsRationalOver L (EM.rationalFunctionField L n) :=
  ⟨n, ⟨AlgEquiv.refl (A₁ := EM.rationalFunctionField L n)⟩⟩

/-- 探针二：`L` 在 `L` 上有理（`n = 0`，经 `EM.rationalFunctionFieldZero`）。 -/
theorem isRationalOver_self (L : Type u) [Field L] : IsRationalOver L L :=
  ⟨0, ⟨(EM.rationalFunctionFieldZero L).symm⟩⟩

/-! ## 3. 核心引理：多项式扩张保持 retract 理性（两塔构造） -/

/-- **核心引理**：若 `L` 在 `F` 上 retract rational，则 `L(t₁,…,tₙ)` 亦然。
构造 = 系数塔（`S ↦ S[t]`）＋ 变量塔（`w ↦ rename (castAdd n) w`），见文件头
「证明路线」。 -/
theorem isRetractRational_rationalFunctionField_of_isRetractRational
    {F L : Type u} [Field F] [Field L] [Algebra F L] (n : ℕ)
    (h : IsRetractRational F L) :
    IsRetractRational F (EM.rationalFunctionField L n) := by
  classical
  obtain ⟨S, hCR, hDom, hAFS, hASL, hTSL, hFracL, m, w, hw, φ, ψ, hcomp⟩ := h
  let : CommRing S := hCR
  let : IsDomain S := hDom
  let : Algebra F S := hAFS
  let : Algebra S L := hASL
  let : IsScalarTower F S L := hTSL
  let : IsFractionRing S L := hFracL
  -- (i) 见证多项式 `w' := rename (castAdd n) w ≠ 0`（`rename` 单）
  have hw' : MvPolynomial.rename (Fin.castAdd n) w ≠ 0 := by
    intro h0
    exact hw (MvPolynomial.rename_injective (Fin.castAdd n) (Fin.castAdd_injective m n)
      (h0.trans (map_zero (MvPolynomial.rename (Fin.castAdd n))).symm))
  -- (ii) `ψw : F[x](1/w) →ₐ[F] F[x₁,…,x_{m+n}](1/w')`（沿 rename 的嵌入）
  have hunit_ψw : IsUnit (((IsScalarTower.toAlgHom F (MvPolynomial (Fin (m + n)) F)
      (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w))).comp
      (MvPolynomial.rename (Fin.castAdd n))) w) := by
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
    exact IsLocalization.Away.algebraMap_isUnit (x := MvPolynomial.rename (Fin.castAdd n) w)
  let ψw : Localization.Away w →ₐ[F]
      Localization.Away (MvPolynomial.rename (Fin.castAdd n) w) :=
    IsLocalization.Away.liftAlgHom (x := w) (f := (IsScalarTower.toAlgHom F
      (MvPolynomial (Fin (m + n)) F)
      (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w))).comp
      (MvPolynomial.rename (Fin.castAdd n))) hunit_ψw
  have hψw (c : MvPolynomial (Fin m) F) :
      ψw (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) c)
        = algebraMap (MvPolynomial (Fin (m + n)) F)
            (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w))
            (MvPolynomial.rename (Fin.castAdd n) c) := by
    change IsLocalization.Away.liftAlgHom (x := w) (f := (IsScalarTower.toAlgHom F
      (MvPolynomial (Fin (m + n)) F)
      (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w))).comp
      (MvPolynomial.rename (Fin.castAdd n))) hunit_ψw
      (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) c) = _
    rw [IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq (x := w) hunit_ψw c]
    rfl
  -- (iii) `φ' : S[t] →ₐ[F] F[x₁,…,x_{m+n}](1/w')`（系数 ψw ∘ φ，变量 t_j ↦ x_{m+j}）
  let yvec : Fin n → Localization.Away (MvPolynomial.rename (Fin.castAdd n) w) :=
    fun j => algebraMap (MvPolynomial (Fin (m + n)) F)
      (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w))
      (MvPolynomial.X (Fin.natAdd m j))
  let φ' : MvPolynomial (Fin n) S →ₐ[F]
      Localization.Away (MvPolynomial.rename (Fin.castAdd n) w) :=
    MvPolynomial.aevalTower (R := S) (σ := Fin n) (ψw.comp φ) yvec
  have hφ'C (s : S) : φ' (MvPolynomial.C s) = ψw (φ s) :=
    MvPolynomial.aevalTower_C (ψw.comp φ) yvec s
  have hφ'X (j : Fin n) : φ' (MvPolynomial.X j) = yvec j :=
    MvPolynomial.aevalTower_X (ψw.comp φ) yvec j
  -- (iv) `ψ' : F[x₁,…,x_{m+n}](1/w') →ₐ[F] S[t]`（沿 w' 下降；
  --      变量映射：x_i ↦ C (ψ (x_i))，x_{m+j} ↦ t_j）
  let z' : Fin m → S := fun i =>
    ψ (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) (MvPolynomial.X i))
  let zvec : Fin (m + n) → MvPolynomial (Fin n) S :=
    Fin.addCases (fun i => MvPolynomial.C (z' i)) (fun j => MvPolynomial.X j)
  let g' : MvPolynomial (Fin (m + n)) F →ₐ[F] MvPolynomial (Fin n) S :=
    MvPolynomial.aeval zvec
  have hzvec : zvec ∘ Fin.castAdd n = fun i => MvPolynomial.C (z' i) := by
    funext i
    show zvec (Fin.castAdd n i) = MvPolynomial.C (z' i)
    exact Fin.addCases_left i
  -- zvec 在左坐标块上的求值 = 系数逐项 ψ
  have hzval (p : MvPolynomial (Fin m) F) :
      MvPolynomial.aeval z' p
        = ψ (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) p) := by
    have h1 : MvPolynomial.aeval z'
        = (ψ.comp (IsScalarTower.toAlgHom F (MvPolynomial (Fin m) F)
            (Localization.Away w))) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
    rw [h1]
    rfl
  -- zvec 沿 C 的提升：C 与 aeval 交换
  have hCnat (p : MvPolynomial (Fin m) F) :
      MvPolynomial.aeval (fun i => (MvPolynomial.C (z' i) : MvPolynomial (Fin n) S)) p
        = (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S))
            (ψ (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) p)) := by
    have h1 : MvPolynomial.aeval (fun i => (MvPolynomial.C (z' i) : MvPolynomial (Fin n) S))
        = (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S)).comp
          (MvPolynomial.aeval z') := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X,
        IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq]
    rw [h1]
    simp only [AlgHom.comp_apply, hzval p, IsScalarTower.toAlgHom_apply]
  -- g' 在 rename 像上的取值
  have hg'rename (c : MvPolynomial (Fin m) F) :
      g' (MvPolynomial.rename (Fin.castAdd n) c)
        = (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S))
            (ψ (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) c)) := by
    show MvPolynomial.aeval zvec (MvPolynomial.rename (Fin.castAdd n) c) = _
    rw [MvPolynomial.aeval_rename]
    rw [hzvec]
    exact hCnat c
  have hunit_g' : IsUnit (g' (MvPolynomial.rename (Fin.castAdd n) w)) := by
    rw [show g' (MvPolynomial.rename (Fin.castAdd n) w)
        = (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S))
            (ψ (algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) w))
        from hg'rename w]
    exact IsUnit.map (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S))
      (IsUnit.map ψ (IsLocalization.Away.algebraMap_isUnit (x := w)
        (S := Localization.Away w)))
  let ψ' : Localization.Away (MvPolynomial.rename (Fin.castAdd n) w) →ₐ[F]
      MvPolynomial (Fin n) S :=
    IsLocalization.Away.liftAlgHom (x := MvPolynomial.rename (Fin.castAdd n) w)
      (f := g') hunit_g'
  have hψ' (c : MvPolynomial (Fin (m + n)) F) :
      ψ' (algebraMap (MvPolynomial (Fin (m + n)) F)
          (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w)) c) = g' c := by
    change IsLocalization.Away.liftAlgHom (x := MvPolynomial.rename (Fin.castAdd n) w)
      (f := g') hunit_g'
      (algebraMap (MvPolynomial (Fin (m + n)) F)
        (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w)) c) = _
    rw [IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq (x := MvPolynomial.rename (Fin.castAdd n) w) hunit_g' c]
    rw [show g'.toRingHom c = g' c from rfl]
  -- (v) 关键等式：`ψ' ∘ ψw = (沿 C 的嵌入) ∘ ψ`
  have hψ'ψw : ψ'.comp ψw
      = (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S)).comp ψ := by
    refine IsLocalization.algHom_ext (W := Submonoid.powers w) ?_
    refine AlgHom.ext fun c => ?_
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
    rw [show (Algebra.algHom F (MvPolynomial (Fin m) F) (Localization.Away w)) c
      = algebraMap (MvPolynomial (Fin m) F) (Localization.Away w) c from rfl]
    rw [hψw c, hψ' (MvPolynomial.rename (Fin.castAdd n) c), hg'rename c]
    rfl
  -- (vi) 复合检查：`ψ' ∘ φ' = id`
  have hcomp' : ψ'.comp φ' = AlgHom.id F (MvPolynomial (Fin n) S) := by
    refine MvPolynomial.algHom_ext' ?_ ?_
    · refine AlgHom.ext fun s => ?_
      simp only [AlgHom.comp_apply, AlgHom.id_apply, IsScalarTower.toAlgHom_apply,
        MvPolynomial.algebraMap_eq]
      rw [hφ'C s]
      rw [show ψ' (ψw (φ s))
          = (IsScalarTower.toAlgHom F S (MvPolynomial (Fin n) S)) (ψ (φ s))
          from AlgHom.ext_iff.mp hψ'ψw (φ s)]
      rw [show ψ (φ s) = (AlgHom.id F S) s from AlgHom.ext_iff.mp hcomp s]
      rw [AlgHom.id_apply, IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq]
    · intro j
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [hφ'X j]
      change ψ' (algebraMap (MvPolynomial (Fin (m + n)) F)
        (Localization.Away (MvPolynomial.rename (Fin.castAdd n) w))
        (MvPolynomial.X (Fin.natAdd m j))) = MvPolynomial.X j
      rw [hψ' (MvPolynomial.X (Fin.natAdd m j))]
      change MvPolynomial.aeval zvec (MvPolynomial.X (Fin.natAdd m j)) = MvPolynomial.X j
      rw [MvPolynomial.aeval_X]
      exact Fin.addCases_right j
  -- (vii) 系数塔的系数扩张（S[t] →+* L[t]）与 K₀ 上的 S[t]-代数结构
  have hD_inj : Function.Injective (MvPolynomial.map (algebraMap S L) :
      MvPolynomial (Fin n) S → MvPolynomial (Fin n) L) :=
    MvPolynomial.map_injective (algebraMap S L) (IsFractionRing.injective S L)
  let φc : MvPolynomial (Fin n) S →+* EM.rationalFunctionField L n :=
    (algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)).comp
      (MvPolynomial.map (algebraMap S L))
  let : Algebra (MvPolynomial (Fin n) S) (EM.rationalFunctionField L n) := φc.toAlgebra
  have hfrac : IsFractionRing (MvPolynomial (Fin n) S) (EM.rationalFunctionField L n) := by
    have hSL : IsLocalization (nonZeroDivisors S) L := hFracL
    let : Algebra (MvPolynomial (Fin n) S) (MvPolynomial (Fin n) L) :=
      MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := S) (S := L)
    have hB : IsLocalization ((nonZeroDivisors S).map (MvPolynomial.C (σ := Fin n)))
        (MvPolynomial (Fin n) L) :=
      MvPolynomial.isLocalization (nonZeroDivisors S) L
    refine (isLocalization_iff (nonZeroDivisors (MvPolynomial (Fin n) S))
      (EM.rationalFunctionField L n)).mpr ⟨?_, ?_, ?_⟩
    · intro y
      have hy0 : (↑y : MvPolynomial (Fin n) S) ≠ 0 :=
        mem_nonZeroDivisors_iff_ne_zero.mp y.2
      have hDy : MvPolynomial.map (algebraMap S L) (↑y : MvPolynomial (Fin n) S) ≠ 0 := by
        intro h0
        exact hy0 (hD_inj (by rw [h0, map_zero]))
      rw [RingHom.algebraMap_toAlgebra φc]
      exact isUnit_iff_ne_zero.mpr (by
        intro h0
        have h0' : (algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n))
            (MvPolynomial.map (algebraMap S L) (↑y : MvPolynomial (Fin n) S)) = 0 := h0
        exact hDy (IsFractionRing.injective (MvPolynomial (Fin n) L)
          (EM.rationalFunctionField L n) (by rw [h0', map_zero])))
    · intro z
      obtain ⟨⟨q, r⟩, hqr⟩ :=
        IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin n) L)) z
      obtain ⟨⟨x₁, m₁⟩, h₁⟩ :=
        IsLocalization.surj ((nonZeroDivisors S).map (MvPolynomial.C (σ := Fin n))) q
      obtain ⟨⟨x₂, m₂⟩, h₂⟩ :=
        IsLocalization.surj ((nonZeroDivisors S).map (MvPolynomial.C (σ := Fin n)))
          (↑r : MvPolynomial (Fin n) L)
      have h₁' : q * MvPolynomial.map (algebraMap S L) (↑m₁ : MvPolynomial (Fin n) S)
          = MvPolynomial.map (algebraMap S L) x₁ := h₁
      have h₂' : (↑r : MvPolynomial (Fin n) L)
            * MvPolynomial.map (algebraMap S L) (↑m₂ : MvPolynomial (Fin n) S)
          = MvPolynomial.map (algebraMap S L) x₂ := h₂
      obtain ⟨b₁, hb₁, hb₁'⟩ := Submonoid.mem_map.mp m₁.2
      obtain ⟨b₂, hb₂, hb₂'⟩ := Submonoid.mem_map.mp m₂.2
      have hm₁ : (↑m₁ : MvPolynomial (Fin n) S) ≠ 0 := by
        rw [← hb₁']
        intro h0
        exact (mem_nonZeroDivisors_iff_ne_zero.mp hb₁)
          (MvPolynomial.C_injective (Fin n) S (by rw [h0, map_zero]))
      have hm₂ : (↑m₂ : MvPolynomial (Fin n) S) ≠ 0 := by
        rw [← hb₂']
        intro h0
        exact (mem_nonZeroDivisors_iff_ne_zero.mp hb₂)
          (MvPolynomial.C_injective (Fin n) S (by rw [h0, map_zero]))
      have hr0 : (↑r : MvPolynomial (Fin n) L) ≠ 0 :=
        mem_nonZeroDivisors_iff_ne_zero.mp r.2
      have hDm₂ : MvPolynomial.map (algebraMap S L) (↑m₂ : MvPolynomial (Fin n) S) ≠ 0 :=
        fun h0 => hm₂ (hD_inj (by rw [h0, map_zero]))
      have hx₂ : x₂ ≠ 0 := by
        intro hx0
        have hz : r * MvPolynomial.map (algebraMap S L) (↑m₂ : MvPolynomial (Fin n) S)
            = 0 := by
          rw [h₂', hx0, map_zero]
        exact mul_ne_zero hr0 hDm₂ hz
      refine ⟨(x₁ * ↑m₂, ⟨x₂ * ↑m₁, ?_⟩), ?_⟩
      · exact mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero hx₂ hm₁)
      · change z * algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.map (algebraMap S L) (x₂ * ↑m₁))
          = algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.map (algebraMap S L) (x₁ * ↑m₂))
        have keyL : z * algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
              (MvPolynomial.map (algebraMap S L) (x₂ * ↑m₁))
            = (z * algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
                (↑r : MvPolynomial (Fin n) L))
              * (algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
                  (MvPolynomial.map (algebraMap S L) (↑m₂ : MvPolynomial (Fin n) S))
                * algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
                  (MvPolynomial.map (algebraMap S L) (↑m₁ : MvPolynomial (Fin n) S))) := by
          simp only [map_mul, ← h₂']
          ring
        have keyR : algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
              (MvPolynomial.map (algebraMap S L) (x₁ * ↑m₂))
            = algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n) q
              * (algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
                  (MvPolynomial.map (algebraMap S L) (↑m₁ : MvPolynomial (Fin n) S))
                * algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
                  (MvPolynomial.map (algebraMap S L) (↑m₂ : MvPolynomial (Fin n) S))) := by
          simp only [map_mul, ← h₁']
          ring
        rw [keyL, keyR, hqr]
        ring
    · intro x y hxy
      have hxy' : x = y := by
        have h1 : algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.map (algebraMap S L) x)
          = algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.map (algebraMap S L) y) := hxy
        exact hD_inj (IsFractionRing.injective (MvPolynomial (Fin n) L)
          (EM.rationalFunctionField L n) h1)
      exact ⟨1, by rw [hxy']⟩
  have htower : IsScalarTower F (MvPolynomial (Fin n) S)
      (EM.rationalFunctionField L n) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have h2 : algebraMap (MvPolynomial (Fin n) S) (EM.rationalFunctionField L n)
          (algebraMap F (MvPolynomial (Fin n) S) a)
        = algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.C (algebraMap F L a)) := by
        rw [IsScalarTower.algebraMap_apply F S (MvPolynomial (Fin n) S) a,
          MvPolynomial.algebraMap_eq S (Fin n),
          RingHom.algebraMap_toAlgebra φc]
        show algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.map (algebraMap S L) (MvPolynomial.C (algebraMap F S a)))
          = algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
            (MvPolynomial.C (algebraMap F L a))
        rw [MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply F S L a]
      have h3 : algebraMap (MvPolynomial (Fin n) L) (EM.rationalFunctionField L n)
          (MvPolynomial.C (algebraMap F L a))
        = algebraMap F (EM.rationalFunctionField L n) a := by
        rw [← MvPolynomial.algebraMap_eq L (Fin n),
          ← IsScalarTower.algebraMap_apply F L (MvPolynomial (Fin n) L) a,
          ← IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) L)
            (EM.rationalFunctionField L n) a]
      rw [← h3, h2]
  -- (viii) 三件齐备：交 `mk'`
  exact IsRetractRational.mk' F (EM.rationalFunctionField L n) (MvPolynomial (Fin n) S)
    (m + n) (MvPolynomial.rename (Fin.castAdd n) w) hw' φ' ψ' hcomp'

/-! ## 4. 主引理：`IsRationalOver` 保持 retract 理性 -/

/-- **主引理**：若 `K` 在 `L` 上有理（`K ≃ₐ[L] L(t₁,…,tₙ)`）且 `L` 在 `F` 上
retract rational，则 `K` 在 `F` 上 retract rational。 -/
theorem isRetractRational_of_isRationalOver {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [Algebra L K] [IsScalarTower F L K]
    (hRat : IsRationalOver L K) (hRet : IsRetractRational F L) :
    IsRetractRational F K := by
  obtain ⟨n, ⟨e⟩⟩ := hRat
  exact (isRetractRational_rationalFunctionField_of_isRetractRational (F := F) (L := L) n
    hRet).of_algEquiv (e.restrictScalars F)

/-! ## 5. 端到端探针与公理闸门 -/

/-- 端到端探针（L1 对照）：取 `L = F`，经「有理 over」链二次导出
`isRetractRational_rationalFunctionField`（与 `SaltT2` §1 的独立路线互为对照）。 -/
theorem isRetractRational_rationalFunctionField_probe (F : Type u) [Field F] (n : ℕ) :
    IsRetractRational F (EM.rationalFunctionField F n) :=
  isRetractRational_of_isRationalOver (isRationalOver_rationalFunctionField F n)
    (isRetractRational_self F)

/-- 端到端探针二（迭代塔）：`IsRationalOver` 对有理函数域二次扩张可迭代。 -/
theorem isRetractRational_of_isRationalOver_probe (F : Type u) [Field F] (n m : ℕ)
    (h : IsRetractRational F (EM.rationalFunctionField F m)) :
    IsRetractRational F (EM.rationalFunctionField (EM.rationalFunctionField F m) n) :=
  isRetractRational_of_isRationalOver
    (isRationalOver_rationalFunctionField (EM.rationalFunctionField F m) n) h

#print axioms IsRationalOver
#print axioms isRationalOver_typeLock
#print axioms isRationalOver_iff_isRational
#print axioms isRationalOver_rationalFunctionField
#print axioms isRationalOver_self
#print axioms isRetractRational_rationalFunctionField_of_isRetractRational
#print axioms isRetractRational_of_isRationalOver
#print axioms isRetractRational_rationalFunctionField_probe
#print axioms isRetractRational_of_isRationalOver_probe

end ABGV52
