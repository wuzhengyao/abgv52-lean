/-
  ABGV-5.2 —— **本体形式化 A · M4b（EMRational，W 层）**：Lenstra (1.4) 的置换 N 机器

  源（`raw/Lenstra1974.tex` (1.4)，印刷页 304；逐字）：
    "Let N be a finitely generated permutation module over π. Then l(N)^π is
     rational over l^π."
  源证明（逐字要点）：取 N 的 π-置换 ℤ-基 {x_i}，W := Σ l·x_i；对 W 用 (1.3)
  （= M3 `speiser_span`）得 y_1..y_r ∈ W^π 且它们 l-张满 W；于是 l(N) = l(y_i)
  且 l(N)^π = l^π(y_i)。

  本件（M4b）= **W 层**：给定置换基 `B : Basis ι ℤ P` 与置换律 `hρ`
  （`mulEquivOfSMul σ (x i) = x (ρ σ i)`，x i := ofAdd (B i)）：
    * `permMono`／`W`（单项式张成的 l-子空间，即 Σ l·x_i）；
    * `W_smul_mem`：W 在 `semiAlgEquiv σ` 下稳定（单项式被置换）；
    * `actW`：↥W 上的 `DistribMulAction G`（由 `semiAlgEquiv` 限制）；
    * `hsemiW`：该作用的半线性（M3 `hsemi` 的口径）；
    * `W_fixed_span`：对 W 用 M3 `speiser_span`——不动点张满 W；
    * `W_fixed_extraction`：**提取** y : Fin n → ↥W——全部不动、l-无关、
      张满 W（mathlib `Submodule.exists_fun_fin_finrank_span_eq`）。

  续（M4c）：分式域层 y 的生成性（l(N) = l(y_i)）＋度账（Artin ＋ 素元素
  多项式度比较）⟹ E := l^π(y_i) = l(N)^π；再经 `aevalEquivField` 出 IsRational。

  范围注（A13）：本件对系数域取 l := latticeFunctionField F M（Route S 的
  实际用例；M4a 机器所在层），不对一般域 l 陈述。

  **无 sorry、无自造公理**。
-/
import ABGV52.EMSemilinear_ABGV52
import ABGV52.EMSpeiser_ABGV52
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace ABGV52
namespace EM

variable {F : Type*} [Field F]
variable {G : Type*} [Group G] [Fintype G]
variable {M : Type*} [AddCommGroup M] [Module ℤ M] [DistribMulAction G M]
  [SMulCommClass G ℤ M] [UniqueProds (Multiplicative M)]
variable {P : Type*} [AddCommGroup P] [Module ℤ P] [DistribMulAction G P]
  [SMulCommClass G ℤ P] [UniqueProds (Multiplicative P)]
variable {ι : Type*} [Fintype ι]

/-! ## 1. 置换基与 W -/

/-- 置换基给出的单项式 `x_i := ofAdd (B i)`（乘法记号）。 -/
noncomputable def permMono (B : Module.Basis ι ℤ P) (i : ι) : Multiplicative P :=
  Multiplicative.ofAdd (B i)

/-- **W**：置换基单项式张成的 `l`-子空间（源中 `W = Σ l·x_i`）。 -/
noncomputable def W (B : Module.Basis ι ℤ P) : Submodule (latticeFunctionField F M)
    (MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)) :=
  Submodule.span _ (Set.range fun i : ι =>
    MonoidAlgebra.single (permMono (P := P) B i) (1 : latticeFunctionField F M))

theorem permMono_single_mem_W (B : Module.Basis ι ℤ P) (i : ι) :
    MonoidAlgebra.single (permMono (P := P) B i) (1 : latticeFunctionField F M)
      ∈ W (F := F) (M := M) (P := P) B :=
  Submodule.subset_span ⟨i, rfl⟩

/-- **W 稳定**：`semiAlgEquiv σ` 把 W 映入 W（单项式被置换 `x_i ↦ x_{ρσi}`，
系数 `1 ↦ 1`）。 -/
theorem W_smul_mem (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    (σ : G) {w : MonoidAlgebra (latticeFunctionField F M) (Multiplicative P)}
    (hw : w ∈ W (F := F) (M := M) (P := P) B) :
    semiAlgEquiv (M := M) σ w ∈ W (F := F) (M := M) (P := P) B := by
  refine Submodule.span_induction
    (p := fun x _ => semiAlgEquiv (M := M) σ x
      ∈ W (F := F) (M := M) (P := P) B) ?_ ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [semiAlgEquiv_single, hρ σ i, map_one]
    exact permMono_single_mem_W B (ρ σ i)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy ihx ihy
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  · intro c x hx ih
    rw [semiAlgEquiv_smul]
    exact Submodule.smul_mem _ (coeffRingEquiv (M := M) σ c) ih

/-! ## 2. ↥W 上的 G-作用与半线性 -/

/-- **↥W 上的 `G`-作用**（`semiAlgEquiv` 的限制；`B, ρ, hρ` 显式传入，
用 `letI` 局部启用）。 -/
noncomputable def actW (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i)) :
    DistribMulAction G ↥(W (F := F) (M := M) (P := P) B) where
  smul σ w := ⟨semiAlgEquiv (M := M) σ w.1, W_smul_mem B ρ hρ σ w.2⟩
  one_smul w := Subtype.ext (semiAlgEquiv_one (M := M) w.1)
  mul_smul σ τ w := Subtype.ext (semiAlgEquiv_mul (M := M) σ τ w.1)
  smul_zero σ := Subtype.ext (map_zero (semiAlgEquiv (M := M) σ))
  smul_add σ x y := Subtype.ext (map_add (semiAlgEquiv (M := M) σ) x.1 y.1)

/-- **半线性**（M3 `hsemi` 的口径）：`σ • (a • w) = (σ•a) • (σ•w)`，
其中 `σ•a` 是 `l = F(M)` 上的 D1 作用。 -/
theorem hsemiW (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i)) :
    letI := actW (F := F) (M := M) B ρ hρ
    ∀ (σ : G) (a : latticeFunctionField F M) (w : ↥(W (F := F) (M := M) (P := P) B)),
      σ • (a • w) = (σ • a) • (σ • w) := by
  letI := actW (F := F) (M := M) B ρ hρ
  intro σ a w
  refine Subtype.ext ?_
  show semiAlgEquiv (M := M) σ (a • w.1)
    = (σ • a) • semiAlgEquiv (M := M) σ w.1
  rw [semiAlgEquiv_smul, coeffRingEquiv_apply]

/-! ## 3. Speiser 与提取 -/

/-- **对 W 用 M3**：不动点集 l-张满 W（`FaithfulSMul G l` 为 M3 的必要假设，
Route S 的 M-忠实性供它）。 -/
theorem W_fixed_span (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    [FaithfulSMul G (latticeFunctionField F M)] :
    letI := actW (F := F) (M := M) B ρ hρ
    Submodule.span (latticeFunctionField F M)
      {w : ↥(W (F := F) (M := M) (P := P) B) | ∀ σ : G, σ • w = w} = ⊤ := by
  letI := actW (F := F) (M := M) B ρ hρ
  refine speiser_span (l := latticeFunctionField F M)
    (W := ↥(W (F := F) (M := M) (P := P) B)) (π := G) ?_
  exact hsemiW (F := F) (M := M) B ρ hρ

/-- 单项式在 ↥W 中的像（具名，防大项 defeq 爆炸）。 -/
noncomputable def permMonoSub (B : Module.Basis ι ℤ P) (i : ι) :
    ↥(W (F := F) (M := M) (P := P) B) :=
  ⟨MonoidAlgebra.single (permMono (P := P) B i) (1 : latticeFunctionField F M),
    permMono_single_mem_W B i⟩

/-- **单项式子类型集张满 ↥W**（有限生成见证，供提取步骤的有限性推后）。 -/
theorem span_permMono_range_eq_top (B : Module.Basis ι ℤ P) :
    Submodule.span (latticeFunctionField F M)
      (Set.range (permMonoSub (F := F) (M := M) (P := P) B)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro w
  refine Submodule.span_induction
    (p := fun x hx => (⟨x, hx⟩ : ↥(W (F := F) (M := M) (P := P) B)) ∈
      Submodule.span (latticeFunctionField F M)
        (Set.range (permMonoSub (F := F) (M := M) (P := P) B))) ?_ ?_ ?_ ?_ w.2
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  · exact Submodule.zero_mem _
  · intro x y hx hy ihx ihy
    exact Submodule.add_mem _ ihx ihy
  · intro c x hx ih
    exact Submodule.smul_mem _ c ih

set_option maxHeartbeats 10000000 in
/-- **提取**：存在有限索引族 `y`，全部不动、`l`-无关、张满 W（Speiser ＋
`Submodule.exists_linearIndependent`（无实例需求）＋ 有限性经
`exists_finite_card_le_of_finite_of_linearIndependent_of_span` 推后）。 -/
theorem W_fixed_extraction (B : Module.Basis ι ℤ P) (ρ : G →* Equiv.Perm ι)
    (hρ : ∀ (σ : G) (i : ι),
      mulEquivOfSMul G P σ (permMono (P := P) B i) = permMono (P := P) B (ρ σ i))
    [FaithfulSMul G (latticeFunctionField F M)] :
    ∃ (n : ℕ) (y : Fin n → ↥(W (F := F) (M := M) (P := P) B)),
      (∀ (i : Fin n) (σ : G),
        (actW (F := F) (M := M) B ρ hρ).smul σ (y i) = y i) ∧
      Submodule.span (latticeFunctionField F M) (Set.range y) = ⊤ ∧
      LinearIndependent (latticeFunctionField F M) y := by
  letI := actW (F := F) (M := M) B ρ hρ
  obtain ⟨b, hbs, hbspan, hbind⟩ :=
    exists_linearIndependent (latticeFunctionField F M)
      {w : ↥(W (F := F) (M := M) (P := P) B) | ∀ σ : G, σ • w = w}
  have hbspan_top : Submodule.span (latticeFunctionField F M) b = ⊤ := by
    rw [hbspan, W_fixed_span (F := F) (M := M) B ρ hρ]
  -- 有限性：b ⊆ span(有限集 t) 且 b 线性无关 ⟹ b 有限
  have hb_indOn : LinearIndepOn (latticeFunctionField F M) id b :=
    linearIndependent_subtype_iff.mp hbind
  obtain ⟨hb_fin, -⟩ :=
    exists_finite_card_le_of_finite_of_linearIndependent_of_span
      (K := latticeFunctionField F M) (s := b)
      (t := Set.range (permMonoSub (F := F) (M := M) (P := P) B))
      (Set.finite_range _) hb_indOn
      (by
        rw [span_permMono_range_eq_top (F := F) (M := M) B]
        exact fun _ _ => Submodule.mem_top)
  letI hbFintype : Fintype ↥b := hb_fin.fintype
  refine ⟨Fintype.card ↥b, (fun k => ((Fintype.equivFin ↥b).symm k).1), ?_, ?_, ?_⟩
  · intro k σ
    exact hbs ((Fintype.equivFin ↥b).symm k).2 σ
  · rw [← hbspan_top]
    congr 1
    ext x
    exact ⟨fun ⟨k, hk⟩ => hk ▸ ((Fintype.equivFin ↥b).symm k).2,
      fun hx => ⟨Fintype.equivFin ↥b ⟨x, hx⟩,
        by simp [Equiv.symm_apply_apply]⟩⟩
  · exact hbind.comp (fun k => (Fintype.equivFin ↥b).symm k)
      (Fintype.equivFin ↥b).symm.injective

/-! ## 4. 公理闸门 -/

#print axioms permMono
#print axioms W
#print axioms W_smul_mem
#print axioms actW
#print axioms hsemiW
#print axioms W_fixed_span
#print axioms W_fixed_extraction

end EM
end ABGV52
