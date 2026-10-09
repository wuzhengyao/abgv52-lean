/-
  ABGV-5.2 —— **本体形式化 A · M3（EMSpeiser）**：Speiser = Lenstra (1.3)

  源（`raw/Lenstra1974.tex` `prop:1.3`，印刷页 303；逐字）：
    "Let W be an l-vector space on which π acts semi-linearly, i.e. W is a
     π-module and σ(λw) = (σλ)·(σw) for all σ ∈ π, λ ∈ l and w ∈ W.
     Then W^π contains an l-basis for W."
  源证明（逐字要点）：S = Σ_{σ∈π} σ；证明 SW ⊂ W^π 含 l-基——为此证明任何
  l-线性 φ 湮灭 SW 必为零：∀λ, 0 = φ(S·λw) = Σ_σ φ(σw)·σ(λ)；由域自同构
  的线性无关（Dedekind）得 φ(σw) = 0 ∀σ，特别 φ(w) = 0。

  本件形式化（mathlib 锚）：
    * 迹元 `speiserTrace w = ∑ σ, σ • w`；`speiserTrace_mem_fixed`
      （重标号 τ ↦ στ，即 `Equiv.mulLeft` 的 `sum_comp`）；
    * **主定理 `speiser_span`**：`span_l {w | ∀σ, σ•w = w} = ⊤`
      —— 对偶分离（`exists_dual_map_eq_bot_of_notMem`）
      ＋ Dedekind（`linearIndependent_algHom_toLinearMap`，@[stacks 0CKM]）
      ＋ 逐 λ 展开（`hsemi`）。
    * **射程注记（A13）**：`[FaithfulSMul π l]` 是**必要假设**——非忠实反例：
      σ 在 l 上平凡而在 W 上为 diag(1,-1)（l-线性，故满足 hsemi），此时
      W^π = l×0，span ≠ ⊤。故本件定理如实带忠实性。

  **无 sorry、无自造公理**。
-/
import ABGV52.EMArtin_ABGV52
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace ABGV52
namespace EM

/-! ## 1. 迹元与不动性 -/

/-- **迹元** `S·w = ∑_{σ∈π} σ • w`（源中 `S = Σσ ∈ ℤ[π]` 的作用；`classical` 供求和）。 -/
noncomputable def speiserTrace {W : Type*} [AddCommGroup W] {π : Type*}
    [Monoid π] [Fintype π] [DistribMulAction π W] (w : W) : W := by
  classical
  exact ∑ σ : π, σ • w

/-- **迹元不动**：`S·w ∈ W^π`（左乘 σ 重标号 τ ↦ στ）。 -/
theorem speiserTrace_mem_fixed {W : Type*} [AddCommGroup W] {π : Type*}
    [Group π] [Fintype π] [DistribMulAction π W] (w : W) :
    speiserTrace (π := π) w ∈ {w' : W | ∀ σ : π, σ • w' = w'} := by
  classical
  intro σ
  rw [speiserTrace, Finset.smul_sum]
  rw [show (∑ τ : π, σ • (τ • w)) = ∑ τ : π, (σ * τ) • w from
    Finset.sum_congr rfl (fun τ _ => (mul_smul σ τ w).symm)]
  rw [← Equiv.sum_comp (Equiv.mulLeft σ) (fun τ : π => τ • w)]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-! ## 2. 主定理：Speiser（半线性作用的迹像张满） -/

/-- **Speiser（Lenstra (1.3)）**：`W` 是 `l`-向量空间、`π` 半线性地作用
（`hsemi`），`π` 在 `l` 上忠实。则 `W` 的不动点集在 `W` 上 `l`-张满
（等价地：不动点集含 `l`-基）。 -/
theorem speiser_span {l W : Type*} [Field l] [AddCommGroup W] [Module l W]
    {π : Type*} [Group π] [Fintype π] [MulSemiringAction π l]
    [FaithfulSMul π l] [DistribMulAction π W]
    (hsemi : ∀ (σ : π) (a : l) (w : W), σ • (a • w) = (σ • a) • (σ • w)) :
    Submodule.span l {w : W | ∀ σ : π, σ • w = w} = ⊤ := by
  classical
  -- 迹像张满（对偶论证）：
  have hmain : Submodule.span l (Set.range (speiserTrace (π := π) (W := W))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx
    -- 对偶分离：∃ f, f x ≠ 0 且 f 湮灭 span(range trace)
    obtain ⟨f, hfx, hfmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    -- f 湮灭迹像
    have hfann : ∀ w : W, f (speiserTrace (π := π) w) = 0 := by
      intro w
      have hmem : speiserTrace (π := π) w ∈ Submodule.span l
          (Set.range (speiserTrace (π := π) (W := W))) :=
        Submodule.subset_span ⟨w, rfl⟩
      have h0 : f (speiserTrace (π := π) w) ∈
          (Submodule.span l (Set.range (speiserTrace (π := π) (W := W)))).map f :=
        Submodule.mem_map_of_mem hmem
      rw [hfmap] at h0
      simpa using h0
    -- 逐 a 展开：∑_σ (σa)·f(σx) = 0
    have hvanish : ∀ a : l, ∑ σ : π, (σ • a) * f (σ • x) = 0 := by
      intro a
      have h0 := hfann (a • x)
      have hcalc : f (speiserTrace (π := π) (a • x))
          = ∑ σ : π, (σ • a) * f (σ • x) := by
        rw [speiserTrace, map_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [hsemi σ a x, map_smul, smul_eq_mul]
      rw [hcalc] at h0
      exact h0
    -- Dedekind：系数全零
    have hli : LinearIndependent l
        (fun σ : π =>
          (MulSemiringAction.toAlgHom ↥(FixedPoints.subfield π l) l σ).toLinearMap) :=
      (linearIndependent_algHom_toLinearMap ↥(FixedPoints.subfield π l) l l).comp
        (MulSemiringAction.toAlgHom ↥(FixedPoints.subfield π l) l)
        (MulSemiringAction.toAlgHom_injective ↥(FixedPoints.subfield π l) l)
    have hcomb : ∑ σ : π, f (σ • x) •
        (MulSemiringAction.toAlgHom ↥(FixedPoints.subfield π l) l σ).toLinearMap = 0 := by
      apply LinearMap.ext
      intro a
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        AlgHom.toLinearMap_apply, MulSemiringAction.toAlgHom_apply, smul_eq_mul,
        mul_comm] using hvanish a
    have hzero := (Fintype.linearIndependent_iff.mp hli) (fun σ : π => f (σ • x)) hcomb
    exact hfx (by simpa using hzero 1)
  -- 迹像 ⊆ 不动点 ⟹ 不动点张满
  have hle : Submodule.span l (Set.range (speiserTrace (π := π) (W := W)))
      ≤ Submodule.span l {w : W | ∀ σ : π, σ • w = w} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span (speiserTrace_mem_fixed w)
  rw [eq_top_iff, ← hmain]
  exact hle

/-! ## 3. 公理闸门 -/

#print axioms speiserTrace
#print axioms speiserTrace_mem_fixed
#print axioms speiser_span

end EM
end ABGV52
