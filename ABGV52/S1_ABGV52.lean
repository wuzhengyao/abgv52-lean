/-
  ABGV-5.2 —— S1：`prop:stable-exp` 的机械层（一）：函子性加性 ＋ 转移

  目标（论文 `prop:stable-exp`，`raw/ABGV-5.2-resolution.tex:1001`）的**两条支柱**：

    ① **双积的「3 消没」继承**：`3` 消没 `coh²(A)` 与 `coh²(B)` ⟹ `3` 消没 `coh²(A ⊞ B)`。
       路线（**不用**长正合列、**不用**同调保双积）：双积的 total 恒等式
       `fst ≫ inl + snd ≫ inr = 𝟙` 在 `H²` 上给出 `x = inl_*(fst_* x) + inr_*(snd_* x)`，
       再用**函子性的 `ℤ`-加性**（`cohMap_add`）与两条假设分别杀掉两项。
    ② **转移（transfer）**：`L ⊞ P ≅ Q`（`P, Q` 置换）⟹ `3` 消没 `coh²(Q)` ⟹ `3` 消没 `coh²(L)`。
       路线：`L →^{ι} L ⊞ P →^{e} Q →^{e⁻¹} L ⊞ P →^{π} L` 的复合 = `𝟙_L`
       ⟹ 在 `H²` 上 `ψ_*(φ_*(x)) = x`，而 `3 • φ_*(x) = φ_*(3 • x) = 0`，故 `3 • x = 0`。

  **依赖**：仅 `ABGV52.Hyp_ABGV52`（定义层）。**无 sorry、无自造公理。**
-/
import ABGV52.Hyp_ABGV52
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## 1. 函子性的 `ℤ`-加性

`groupCohomology.map` 是 `cochainsFunctor`（**自带 `Additive` 实例**）与同调函子的复合，
故它对**表示态射的加法**加性。 -/

/-- `cochainsMap` 对表示态射的加法：`cochainsMap` 就是 `cochainsFunctor` 的态射部分。 -/
lemma cochainsMap_add {A B : Rep ℤ H} (φ ψ : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id H) (φ + ψ)
      = groupCohomology.cochainsMap (MonoidHom.id H) φ
        + groupCohomology.cochainsMap (MonoidHom.id H) ψ :=
  (groupCohomology.cochainsFunctor ℤ H).map_add

/-- **`map` 的 `ℤ`-加性**：`map (φ + ψ) = map φ + map ψ`。 -/
lemma cohMap_add {A B : Rep ℤ H} (φ ψ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id H) (φ + ψ) n
      = groupCohomology.map (MonoidHom.id H) φ n
        + groupCohomology.map (MonoidHom.id H) ψ n := by
  show HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id H) (φ + ψ)) n
      = HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id H) φ) n
        + HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id H) ψ) n
  rw [cochainsMap_add, HomologicalComplex.homologyMap_add]

/-! ## 2. 双积的「3 消没」继承 -/

/-- **`coh²` 的「3 消没」在双积下继承**。

用双积的 total 恒等式 `fst ≫ inl + snd ≫ inr = 𝟙`：它在 `H²` 上（经 `cohMap_add`）给出
`x = inl_*(fst_* x) + inr_*(snd_* x)`，两项分别被 `hA`／`hB` 杀掉。 -/
theorem kills_biprod {A B : Rep ℤ H} (hA : Coh2ExpDvd3 A) (hB : Coh2ExpDvd3 B) :
    Coh2ExpDvd3 (A ⊞ B) := by
  intro x
  have htotal : (biprod.fst : A ⊞ B ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ B)
      + (biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inr : B ⟶ A ⊞ B) = 𝟙 (A ⊞ B) :=
    biprod.total
  -- `x = inl_*(fst_* x) + inr_*(snd_* x)`
  have hx : x = (groupCohomology.map (MonoidHom.id H) (biprod.inl : A ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id H) (biprod.fst : A ⊞ B ⟶ A) 2).hom x)
      + (groupCohomology.map (MonoidHom.id H) (biprod.inr : B ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id H) (biprod.snd : A ⊞ B ⟶ B) 2).hom x) := by
    have h := congrArg (fun f => (groupCohomology.map (MonoidHom.id H) f 2).hom x) htotal
    simp only [cohMap_add, groupCohomology.map_id_comp, groupCohomology.map_id,
      ModuleCat.id_apply] at h
    exact h.symm
  have h1 : (3 : ℤ) • (groupCohomology.map (MonoidHom.id H) (biprod.inl : A ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id H) (biprod.fst : A ⊞ B ⟶ A) 2).hom x) = 0 := by
    rw [← map_zsmul, hA]
    exact map_zero _
  have h2 : (3 : ℤ) • (groupCohomology.map (MonoidHom.id H) (biprod.inr : B ⟶ A ⊞ B) 2).hom
        ((groupCohomology.map (MonoidHom.id H) (biprod.snd : A ⊞ B ⟶ B) 2).hom x) = 0 := by
    rw [← map_zsmul, hB]
    exact map_zero _
  rw [hx, zsmul_add, h1, h2, add_zero]

/-! ## 3. 同构传递：`3` 消没沿表示同构搬移 -/

/-- 表示同构诱导的上同调**线性等价**（局部副本，保持 S1 只依赖定义层）。 -/
noncomputable def cohLinearEquivOfIso {A B : Rep ℤ H} (e : A ≅ B) (n : ℕ) :
    coh A n ≃ₗ[ℤ] coh B n where
  toFun := (groupCohomology.map (MonoidHom.id H) e.hom n).hom
  invFun := (groupCohomology.map (MonoidHom.id H) e.inv n).hom
  left_inv x := by
    show (groupCohomology.map (MonoidHom.id H) e.inv n).hom
      ((groupCohomology.map (MonoidHom.id H) e.hom n).hom x) = x
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, e.hom_inv_id,
      groupCohomology.map_id]
    rfl
  right_inv x := by
    show (groupCohomology.map (MonoidHom.id H) e.hom n).hom
      ((groupCohomology.map (MonoidHom.id H) e.inv n).hom x) = x
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, e.inv_hom_id,
      groupCohomology.map_id]
    rfl
  map_add' := fun x y => (groupCohomology.map (MonoidHom.id H) e.hom n).hom.map_add x y
  map_smul' := fun c x => (groupCohomology.map (MonoidHom.id H) e.hom n).hom.map_smul c x

/-- **`3` 消没沿表示同构传递**。 -/
theorem kills_of_iso {A B : Rep ℤ H} (e : A ≅ B) (hA : Coh2ExpDvd3 A) : Coh2ExpDvd3 B := by
  intro x
  obtain ⟨y, rfl⟩ := (cohLinearEquivOfIso e 2).surjective x
  exact (map_zsmul (cohLinearEquivOfIso e 2).toLinearMap 3 y).symm.trans
    ((congrArg (cohLinearEquivOfIso e 2) (hA y)).trans (map_zero _))

/-! ## 4. 转移：`L ⊞ P ≅ Q` ⟹ `3` 消没从 `Q` 传回 `L` -/

/-- **转移引理**（论文 `prop:stable-exp` 的证明骨架）：若 `L ⊞ P ≅ Q` 且 `3` 消没 `coh²(Q)`，
则 `3` 消没 `coh²(L)`。

复合 `L →^{ι} L ⊞ P →^{e} Q →^{e⁻¹} L ⊞ P →^{π} L` 等于 `𝟙_L`，故 `ψ_* ∘ φ_* = 𝟙`，
而 `3 • φ_*(x) = φ_*(3 • x) = 0`。 -/
theorem kills_of_biprod_iso (L P Q : Rep ℤ H) (e : L ⊞ P ≅ Q)
    (hQ : Coh2ExpDvd3 Q) : Coh2ExpDvd3 L := by
  intro x
  set φ : L ⟶ Q := (biprod.inl : L ⟶ L ⊞ P) ≫ e.hom with hφ
  set ψ : Q ⟶ L := e.inv ≫ (biprod.fst : L ⊞ P ⟶ L) with hψ
  have hcomp : φ ≫ ψ = 𝟙 L := by
    rw [hφ, hψ, Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp,
      biprod.inl_fst]
  -- `ψ_*(φ_*(x)) = x`
  have hid : (groupCohomology.map (MonoidHom.id H) ψ 2).hom
      ((groupCohomology.map (MonoidHom.id H) φ 2).hom x) = x := by
    rw [← ModuleCat.comp_apply, ← groupCohomology.map_id_comp, hcomp,
      groupCohomology.map_id]
    rfl
  -- `3 • φ_*(x) = 0`（`hQ` 直接给出）
  have h3 : (3 : ℤ) • (groupCohomology.map (MonoidHom.id H) φ 2).hom x = 0 := hQ _
  calc (3 : ℤ) • x
      = (3 : ℤ) • (groupCohomology.map (MonoidHom.id H) ψ 2).hom
          ((groupCohomology.map (MonoidHom.id H) φ 2).hom x) := by rw [hid]
    _ = (groupCohomology.map (MonoidHom.id H) ψ 2).hom
          ((3 : ℤ) • (groupCohomology.map (MonoidHom.id H) φ 2).hom x) :=
        (map_zsmul (groupCohomology.map (MonoidHom.id H) ψ 2).hom 3 _).symm
    _ = (groupCohomology.map (MonoidHom.id H) ψ 2).hom 0 := by rw [h3]
    _ = 0 := map_zero _

/-! ## 5. 公理闸门 -/

#print axioms cochainsMap_add
#print axioms cohMap_add
#print axioms kills_biprod
#print axioms kills_of_iso
#print axioms kills_of_biprod_iso

end ABGV52
