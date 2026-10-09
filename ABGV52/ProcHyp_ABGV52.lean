/-
  ABGV-5.2 —— **C 轨（Procesi）· M2/M7 第一块：修正 `ProcesiHyp` 的命题外形**

  目标（蓝图 §3.2 T3）：旧外形（`GThm_ABGV52` §3 的 `ProcesiHyp`，核格 =
  `↥(ker φ)`，秩 73）所锁的是**假命题**；本件给出修正后的两个外形：
    * C′（精确形）`ProcesiHypExact`：`Z ≅ F((M ⊕ U)|_H)^H`，其中 `M ⊕ U` 取
      M1 已交付的 `ProcLat.Mp2 = ker φ × ℤ[Ω]`（该模 ℚ-秩 = p⁴+1，p=3 时 82）；
    * C″（稳定形，论文实际消费）`ProcesiHypStable`：`∃ k, Z ≅ K(t₁,…,t_k)`，
      `K = F(M|_H)^H = ↥(latticeInvariants F (Hp p) ↥(ker φ))`。

  蓝图出处：`wiki/proj-ABGV52-formalize-procesi.md` §3.2 T3（本件的原始规格）
  ＋ §1.3（实质发现：旧外形所锁为假命题，并给出 C′／C″ 两修正）。

  **一句话修正理由**：现 `ProcesiHyp` 的核只取 `↥(ker φ)`（秩 73），缺一个秩 p²
  （p=3 时 9）的**置换分量 U = ℤ[Ω]**——中心定理的格是 `M₂ = M ⊕ U`（秩
  73 + 9 = 82 = n²+1），trdeg 账 73 ≠ 82，见蓝图 §1.3-(i)。

  本件交付（**不改动任何既有文件**；`GThm` 的旧 `ProcesiHyp` 是否替换 = M7/M8 决策）：
    ① 两定义 ＋ 各自 `rfl` 类型锁定（命名定理，见偏差 ②）；
    ② 非空洞探针（L1）两条：取 `Z := 右端`，`RingEquiv.refl` 见证；
    ③ `Mp2` 上的 `H`-作用（局部实例，见偏差 ③）；
    ④ 桥引理四条（派发书「可选加值」的**诚实弱形式**；无条件的 C′→C″ 桥
       **未交付**，见文件末「未竟处」）。

  与蓝图写法的逐条偏差：
    ① 蓝图 C′ 用 `⊕`（`ker φ ⊕ ℤ[Ω]`）；本件经 `ProcLat.Mp2` 用 `×` 承载——
       mathlib 的 `Sum` 上无 `AddCommGroup` 实例（`ProcLat` 头注已登记同款偏离）。
    ② 类型锁定用**命名定理**（`procesiHypExact_typeLock` / `procesiHypStable_typeLock`）
       而非 `example`：内容与 `GThm:62–64` 的 `rfl` 断言相同，命名后公理闸门可覆盖。
    ③ `Mp2` 上的 `H`-作用 = 沿 G1c 正则嵌入 `thetaH` 从既有 `Gp`-作用限制
       （与 G1c 的 `Mres`（`M|_θ`）逐分量吻合：第一分量 = `Mres` 作用、
       第二分量由 `U_rho_theta` 字面 `rfl` 落入 `ℤ[Ω]` 的 `UH` 作用）。
       `ProcLat` 只装过 `Gp`-作用 ⟹ 本件局部补装，不改 `ProcLat`。
    ④ 桥 (c) 为**条件式**（M3 内容作显式假设参数）、桥 (d) 为旧外形的兼容性桥
       （只作迁移参考，**不**声称旧外形正确）——两者均按「未证明者登记为假设/
       目标、不得假证」的纪律落盘。

  **无 sorry、无自造公理**（见 §6 公理闸门：逐条 `#print axioms`）。
-/
import ABGV52.ProcLat_ABGV52
import ABGV52.G2p_ABGV52
import ABGV52.GThm_ABGV52

open ABGV52.P (Hp)

namespace ABGV52.ProcHyp

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. `Mp2` 上的 `H`-作用（局部补装；不改 `ProcLat`）

  `ProcLat` 只装了 `Gp p`-作用（`instSMulMp2` / `instDistribMulActionMp2`）；
  `EM.latticeInvariants F (Hp p) (Mp2 p)` 需要 `Hp p`-作用，正确取法 = 沿 G1c
  的正则嵌入 `thetaH : Hp p →* Equiv.Perm (OmegaP p)` 从 `Gp p`-作用限制。
  其余所需实例由既有件自动合成：`SMulCommClass (Hp p) ℤ (Mp2 p)` 来自
  `AddGroup.int_smulCommClass'`；`UniqueProds (Multiplicative (Mp2 p))` 来自
  `UniqueSums (Mp2 p)`（`Prod.instUniqueSums` × G2p 的 `uniqueSums_kerPhi`
  与 `uniqueSums_monoidAlgebra`）。 -/

/-- `Mp2` 上的 `H`-作用：沿 `thetaH` 限制 `Gp p`-作用。 -/
noncomputable instance instSMulHpMp2 : SMul (Hp p) (ProcLat.Mp2 p) :=
  ⟨fun h x => G.thetaH p h • x⟩

/-- 作用公式（展开引理，`rfl` 级）。 -/
lemma smul_Hp_Mp2_apply (h : Hp p) (x : ProcLat.Mp2 p) :
    h • x = G.thetaH p h • x := rfl

/-- 第一分量 = G1c 的 `Mres`（`M|_θ`）作用（经 `↥(ker φ)` 上的 `H`-实例）。 -/
lemma smul_Hp_Mp2_fst (h : Hp p) (x : ProcLat.Mp2 p) :
    (h • x).1 = h • x.1 := rfl

/-- 第二分量 = `ℤ[Ω]` 的 `UH`（正则）作用（`U_rho_theta`，字面 `rfl`）：
即修正所补的**置换分量** `U|_H`。 -/
lemma smul_Hp_Mp2_snd (h : Hp p) (x : ProcLat.Mp2 p) :
    (h • x).2 = (G.UH p).ρ h x.2 := rfl

/-- `Mp2` 上的 `H`-`DistribMulAction`（逐分量验证；照 `ProcLat` 的 `Gp`-版写法）。 -/
noncomputable instance instDistribMulActionHpMp2 : DistribMulAction (Hp p) (ProcLat.Mp2 p) where
  smul := (instSMulHpMp2 p).smul
  one_smul x := by
    refine Prod.ext ?_ ?_
    · show G.thetaH p (1 : Hp p) • x.1 = x.1
      rw [map_one]
      exact one_smul _ _
    · show (G.U p).ρ (G.thetaH p (1 : Hp p)) x.2 = x.2
      rw [map_one, map_one]
      rfl
  mul_smul a b x := by
    refine Prod.ext ?_ ?_
    · show G.thetaH p (a * b) • x.1 = G.thetaH p a • (G.thetaH p b • x.1)
      rw [map_mul]
      exact mul_smul _ _ _
    · show (G.U p).ρ (G.thetaH p (a * b)) x.2
          = (G.U p).ρ (G.thetaH p a) ((G.U p).ρ (G.thetaH p b) x.2)
      rw [map_mul, Rep.ρ_mul]
      rfl
  smul_zero h := by
    refine Prod.ext ?_ ?_
    · show G.thetaH p h • (0 : ↥(LinearMap.ker (G.phiFun p))) = 0
      exact smul_zero _
    · show (G.U p).ρ (G.thetaH p h) (0 : G.ZOm p) = 0
      exact map_zero _
  smul_add h x y := by
    refine Prod.ext ?_ ?_
    · show G.thetaH p h • (x.1 + y.1)
          = G.thetaH p h • x.1 + G.thetaH p h • y.1
      exact smul_add _ x.1 y.1
    · show (G.U p).ρ (G.thetaH p h) (x.2 + y.2)
          = (G.U p).ρ (G.thetaH p h) x.2 + (G.U p).ρ (G.thetaH p h) y.2
      exact map_add _ _ _

/-! ## 2. 修正后的命题外形（C′ / C″） -/

/-- **C′（精确形）**：`Z ≅ F((M ⊕ U)|_H)^H`——中心定理的格是 M1 的
`Mp2 = ker φ × ℤ[Ω]`（秩 73 + 9 = 82，蓝图 §1.3-(i)），旧外形取 `↥(ker φ)`
（秩 73）所锁为假命题。 -/
def ProcesiHypExact (F : Type*) [Field F] (Z : Type*) [Field Z] : Prop :=
  Nonempty (Z ≃+* ↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)))

/-- **C″（稳定形，论文实际消费）**：`Z` 在 `K = F(M|_H)^H` 上稳定有理
（`∃ k`：添 `k` 个变元后同构于 `K(t₁,…,t_k)`；与 `EM.rationalFunctionField` 的
对应见桥 (a)）。 -/
def ProcesiHypStable (F : Type*) [Field F] (Z : Type*) [Field Z] : Prop :=
  ∃ k : ℕ, Nonempty (Z ≃+* FractionRing (MvPolynomial (Fin k)
    ↥(EM.latticeInvariants F (Hp p) ↥(LinearMap.ker (G.phiFun p)))))

/-- **类型锁定（C′）**：外形一旦被改动，本 `rfl` 立即编译失败。 -/
theorem procesiHypExact_typeLock (F : Type*) [Field F] (Z : Type*) [Field Z] :
    ProcesiHypExact (p := p) F Z = Nonempty (Z ≃+* ↥(EM.latticeInvariants F (Hp p)
      (ProcLat.Mp2 p))) := rfl

/-- **类型锁定（C″）**：外形一旦被改动，本 `rfl` 立即编译失败。 -/
theorem procesiHypStable_typeLock (F : Type*) [Field F] (Z : Type*) [Field Z] :
    ProcesiHypStable (p := p) F Z = ∃ k : ℕ, Nonempty (Z ≃+* FractionRing
      (MvPolynomial (Fin k) ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))))) := rfl

/-! ## 3. 非空洞探针（L1：两条外形的假设类均非空） -/

/-- 探针（C′）：取 `Z := 右端` 本身，恒等同构即实例。 -/
theorem procesiHypExact_satisfiable (F : Type*) [Field F] :
    ProcesiHypExact (p := p) F ↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) :=
  ⟨RingEquiv.refl _⟩

/-- 探针（C″）：取 `Z := K(t₁)`（`k = 1` 的右端），恒等同构即实例。 -/
theorem procesiHypStable_satisfiable (F : Type*) [Field F] :
    ProcesiHypStable (p := p) F
      (EM.rationalFunctionField ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))) 1) :=
  ⟨1, ⟨RingEquiv.refl _⟩⟩

/-! ## 4. 桥引理（派发书「可选加值」的诚实弱形式） -/

/-- 桥 (a)：稳定形与 D1 的 `EM.rationalFunctionField` 的书写一致（定义级等价）。 -/
theorem procesiHypStable_iff_rationalFunctionField (F : Type*) [Field F]
    (Z : Type*) [Field Z] :
    ProcesiHypStable (p := p) F Z ↔ ∃ k : ℕ, Nonempty (Z ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))) k) :=
  Iff.rfl

/-- 桥 (b)：`Z` 在 `K = F(M|_H)^H` 上有理（D1 `IsRational`，`≃ₐ` 形态）
⟹ 稳定形（遗忘代数结构）。反向不成立（稳定有理弱于有理），故**不可**作 `↔`。 -/
theorem procesiHypStable_of_isRational (F : Type*) [Field F] (Z : Type*) [Field Z]
    [Algebra ↥(EM.latticeInvariants F (Hp p) ↥(LinearMap.ker (G.phiFun p))) Z]
    (h : EM.IsRational ↥(EM.latticeInvariants F (Hp p)
      ↥(LinearMap.ker (G.phiFun p))) Z) :
    ProcesiHypStable (p := p) F Z := by
  obtain ⟨k, ⟨e⟩⟩ := h
  exact ⟨k, ⟨e.toRingEquiv⟩⟩

/-- 桥 (c)：**条件式** C′ + M3 ⟹ C″。第二条假设 = T2（`ProcStab_ABGV52`，
Lenstra (1.4) 的格层内容）的接口：`Mp2` 的不变量域在 `K = F(M|_H)^H` 上有理
（作**显式假设参数**；本件不证明它，也不得读作已交付）。 -/
theorem procesiHypStable_of_exact_of_ratOver (F : Type*) [Field F] (Z : Type*) [Field Z]
    (hExact : ProcesiHypExact (p := p) F Z)
    (hM3 : ∃ k : ℕ, Nonempty (↥(EM.latticeInvariants F (Hp p) (ProcLat.Mp2 p)) ≃+*
      EM.rationalFunctionField ↥(EM.latticeInvariants F (Hp p)
        ↥(LinearMap.ker (G.phiFun p))) k)) :
    ProcesiHypStable (p := p) F Z := by
  obtain ⟨e⟩ := hExact
  obtain ⟨k, ⟨e'⟩⟩ := hM3
  exact ⟨k, ⟨e.trans e'⟩⟩

/-- 桥 (d)：旧外形（`GThm` 的 `ProcesiHyp`，核格不带 U）⟹ 稳定形——`k = 0` 特例
（`K ≅ K(t₁,…,t₀)`，经 `EM.rationalFunctionFieldZero` 取逆）。**兼容性桥**：
供 M7/M8 迁移消费点参考，**不**声称旧外形正确。 -/
theorem procesiHypStable_of_oldShape (F : Type*) [Field F] (Z : Type*) [Field Z]
    (h : G.ProcesiHyp (p := p) F Z) :
    ProcesiHypStable (p := p) F Z := by
  obtain ⟨e⟩ := h
  exact ⟨0, ⟨e.trans ((EM.rationalFunctionFieldZero ↥(EM.latticeInvariants F (Hp p)
    ↥(LinearMap.ker (G.phiFun p)))).toRingEquiv.symm)⟩⟩

/-! ## 5. 未竟处（诚实登记，**不**计本件交付）

  C′ → C″ 的**无条件**桥未交付：其缺口 = M3（Lenstra (1.4) 的格层内容，
  蓝图 §3.1 的 T2 / `ProcStab_ABGV52.lean`，本件写作时尚不存在）。
  证据链现状：`EMRational_ABGV52` 止于 `W_fixed_extraction`（W 层），
  `EMFixed_ABGV52` 止于 `SlI_eq_adjoin_primitive`——均未达「`Mp2` 的不变量域
  在 `K` 上有理」。故本件只把该接口在桥 (c) 中具名化（作假设参数）。

  另：旧外形消费点（`GThm` §2 的 `gThm_geometric_identification` 及其具名版、
  `GChallenge` 的独立重写件）**本件未触碰**；替换决策属 M7/M8。 -/

/-! ## 6. 公理闸门 -/

#print axioms instSMulHpMp2
#print axioms smul_Hp_Mp2_apply
#print axioms smul_Hp_Mp2_fst
#print axioms smul_Hp_Mp2_snd
#print axioms instDistribMulActionHpMp2
#print axioms ProcesiHypExact
#print axioms ProcesiHypStable
#print axioms procesiHypExact_typeLock
#print axioms procesiHypStable_typeLock
#print axioms procesiHypExact_satisfiable
#print axioms procesiHypStable_satisfiable
#print axioms procesiHypStable_iff_rationalFunctionField
#print axioms procesiHypStable_of_isRational
#print axioms procesiHypStable_of_exact_of_ratOver
#print axioms procesiHypStable_of_oldShape

end ABGV52.ProcHyp
