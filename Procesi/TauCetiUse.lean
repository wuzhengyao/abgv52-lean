/-
  Procesi —— **外部件消费（TauCeti）**：`eq:procesi-S9` 限制到 `H` 后的**分式域分裂**

  **用户令**（2026-10-18）：「**TauCeti 库也利用好**」。本件是该移植件
  （`Procesi/External/TauCetiFractionRing.lean`，TauCeti 的 `nonempty_tensor_linearEquiv_prod_of_exact`）
  的**首次实际消费**：把「`R[G]`-格正合列在分式域上分裂」（＝分式域上的 Maschke）用于
  **Procesi 正合列**

      0 → M|_H → (U⊗U)|_H → I[Ω]|_H → 0        （论文 `eq:procesi-S9`，限制到 H）

  得：`((U⊗U)|_H ⊗ ℚ) ≃_{ℤ[H]} ((M|_H × I[Ω]|_H) ⊗ ℚ)`。

  **为何这是真的**：`H = C₃×C₃` 的阶 9 在 `ℤ` 中非零（`NeZero`，`card_Hp`），故 `ℚ` 上
  Maschke 成立；TauCeti 件把它做成 `R[G]`-线性同构（而不只是 `ℚ[G]`-线性）。

  **工艺（三处实测）**：
  ① `Representation.IntertwiningMap` 的字段是 `isIntertwining'`，且其型是**线性映射等式**
     （不是逐点式）⟹ 须 `LinearMap.ext`；
  ② 该结构的 `asModule` 是**类型副本**，一切搬运用 `Representation.asModuleEquiv`；
     逐点式恒等式（如 `fLin x = (asModuleEquiv x).1`）实测为 **`rfl`**；
  ③ `H` 在 `I[Ω] = ker ε` 上的作用由 `U|_H` 的作用限制（`augF_smul_H` 供稳定性）。

  **射程**：本件给**结构**分裂；数值秩账（81 = 73 + 8）的算术版已在 `Lattice.lean`
  （`rank_account_exact`），其**结构版**（由本分裂 ＋ `finrank_prod` 导出）登记为后续件
  （需 `finrank` 沿 `asModule` 与 `TensorProduct.prodLeft` 的两次搬运）。
-/
import Procesi.Lattice
import Procesi.External.TauCetiFractionRing
import Mathlib.RepresentationTheory.Intertwining

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

set_option maxHeartbeats 2400000

/-! ## §1 `H` 在 `I[Ω] = ker ε` 上的作用（由 `U|_H` 限制） -/

/-- `ε` 在 `U|_H`-作用下不变（`U_rho_theta` ＋ `G1b` 的 `augF_smul`）。 -/
theorem augF_smul_H (h : P.Hp 3) (f : G.ZOm 3) :
    G.augF 3 ((G.UH 3).ρ h f) = G.augF 3 f := by
  rw [← G.U_rho_theta 3 h]
  exact G.augF_smul 3 (G.thetaH 3 h) f

theorem mem_iOmega_iff (f : G.ZOm 3) : f ∈ G.IOmega 3 ↔ G.augF 3 f = 0 := Iff.rfl

/-- `H` 在 `I[Ω]` 上的作用（子模稳定，`augF_smul_H` 供）。 -/
def Iact (h : P.Hp 3) (z : ↥(G.IOmega 3)) : ↥(G.IOmega 3) :=
  ⟨(G.UH 3).ρ h z.1, by rw [mem_iOmega_iff]; rw [augF_smul_H]; exact z.2⟩

instance instDistribMulActionIOmega : DistribMulAction (P.Hp 3) ↥(G.IOmega 3) where
  smul h z := Iact h z
  one_smul z := by
    apply Subtype.ext
    show (G.UH 3).ρ 1 z.1 = z.1
    rw [map_one]; rfl
  mul_smul a b z := by
    apply Subtype.ext
    show (G.UH 3).ρ (a * b) z.1 = (G.UH 3).ρ a ((G.UH 3).ρ b z.1)
    rw [map_mul]; rfl
  smul_zero h := Subtype.ext (map_zero _)
  smul_add h x y := Subtype.ext (map_add _ _ _)

instance uniqueSums_iOmega : UniqueSums ↥(G.IOmega 3) :=
  UniqueSums.of_injective_addHom
    { toFun := fun z => (z.1 : G.ZOm 3), map_add' := fun _ _ => rfl }
    Subtype.val_injective inferInstance

/-- `I[Ω]` 作为 `Rep ℤ (Hp 3)`。 -/
def Irep : Rep ℤ (P.Hp 3) :=
  Rep.ofDistribMulAction ℤ (P.Hp 3) ↥(G.IOmega 3)

/-! ## §2 正合列 `0 → M|_H → (U⊗U)|_H → I[Ω]|_H → 0` 的 `ℤ[H]`-线性形 -/

/-- 包含 `M|_H ↪ (U⊗U)|_H`（交错映射）。 -/
def incInter :
    Representation.IntertwiningMap (G.Mres 3).ρ (G.tensorDiagRepr 3) where
  toLinearMap := (LinearMap.ker (G.phiFun 3)).subtype
  isIntertwining' _ := rfl

/-- `φ` 以 `I[Ω]` 为靶（交错映射；等变性 = `phiFun_equivariant` ∘ `U_rho_theta`）。 -/
def phiInter :
    Representation.IntertwiningMap (G.tensorDiagRepr 3) (Irep).ρ where
  toLinearMap := (G.phiFun 3).codRestrict (G.IOmega 3)
    (fun x => (G.range_phiFun_eq 3) ▸ LinearMap.mem_range_self (G.phiFun 3) x)
  isIntertwining' h := by
    refine LinearMap.ext fun x => ?_
    apply Subtype.ext
    show G.phiFun 3 (TensorProduct.map ((G.UH 3).ρ h) ((G.UH 3).ρ h) x)
      = (G.UH 3).ρ h (G.phiFun 3 x)
    rw [← G.U_rho_theta 3 h]
    exact G.phiFun_equivariant 3 (G.thetaH 3 h) x

/-- `ℤ[H]`-线性的包含 `M|_H → (U⊗U)|_H`。 -/
def fLin : (G.Mres 3).ρ.asModule →ₗ[MonoidAlgebra ℤ (P.Hp 3)]
    (G.tensorDiagRepr 3).asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ incInter

/-- `ℤ[H]`-线性的 `φ : (U⊗U)|_H → I[Ω]|_H`。 -/
def gLin : (G.tensorDiagRepr 3).asModule →ₗ[MonoidAlgebra ℤ (P.Hp 3)]
    (Irep).ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _ phiInter

/-- **单射**（子模包含）。 -/
theorem fLin_injective : Function.Injective fLin := by
  intro x y h
  have h2 : (Representation.asModuleEquiv (G.Mres 3).ρ x).1
      = (Representation.asModuleEquiv (G.Mres 3).ρ y).1 := by
    rw [← show fLin x = (Representation.asModuleEquiv (G.Mres 3).ρ x).1 from rfl,
      ← show fLin y = (Representation.asModuleEquiv (G.Mres 3).ρ y).1 from rfl, h]
  exact (Representation.asModuleEquiv (G.Mres 3).ρ).injective (Subtype.ext h2)

/-- **满射到 `I[Ω]`**（`range φ = I[Ω]`，`G1b` 的 `range_phiFun_eq`）。 -/
theorem gLin_surjective : Function.Surjective gLin := by
  intro y
  obtain ⟨w, hw⟩ := (G.range_phiFun_eq 3).ge
    (Representation.asModuleEquiv (Irep).ρ y).2
  refine ⟨(Representation.asModuleEquiv (G.tensorDiagRepr 3)).symm w, ?_⟩
  apply (Representation.asModuleEquiv (Irep).ρ).injective
  apply Subtype.ext
  show G.phiFun 3 w = (Representation.asModuleEquiv (Irep).ρ y).1
  rw [hw]

/-- **正合性** `ker φ = M|_H`（两方向）。 -/
theorem fg_exact : Function.Exact fLin gLin := by
  intro y
  constructor
  · intro hy
    have hy' : (Representation.asModuleEquiv (Irep).ρ (gLin y)).1 = 0 := by
      rw [hy]; rfl
    have h0 : G.phiFun 3 (Representation.asModuleEquiv (G.tensorDiagRepr 3) y) = 0 := by
      rw [← show (Representation.asModuleEquiv (Irep).ρ (gLin y)).1
          = G.phiFun 3 (Representation.asModuleEquiv (G.tensorDiagRepr 3) y) from rfl]
      exact hy'
    refine ⟨(Representation.asModuleEquiv (G.Mres 3).ρ).symm
      ⟨Representation.asModuleEquiv (G.tensorDiagRepr 3) y, h0⟩, ?_⟩
    apply (Representation.asModuleEquiv (G.tensorDiagRepr 3)).injective
    rfl
  · rintro ⟨x, rfl⟩
    have hx : G.phiFun 3 (Representation.asModuleEquiv (G.Mres 3).ρ x).1 = 0 :=
      (Representation.asModuleEquiv (G.Mres 3).ρ x).2
    apply (Representation.asModuleEquiv (Irep).ρ).injective
    apply Subtype.ext
    show G.phiFun 3 (Representation.asModuleEquiv (G.tensorDiagRepr 3) (fLin x)) = 0
    rw [show Representation.asModuleEquiv (G.tensorDiagRepr 3) (fLin x)
        = (Representation.asModuleEquiv (G.Mres 3).ρ x).1 from rfl]
    exact hx

/-- ★★★ **`eq:procesi-S9` 的分式域分裂（TauCeti 件的首次消费）**：
`((U⊗U)|_H) ⊗ ℚ ≃_{ℤ[H]} ((M|_H × I[Ω]|_H) ⊗ ℚ)`。

**读法**：`0 → M → U⊗U → I[Ω] → 0` 在 `ℚ` 上分裂（Maschke），且分裂是 **`ℤ[H]`-线性**的
（不是仅 `ℚ[H]`-线性）——这正是 TauCeti 件相对"直接对 `ℚ[G]` 用半单性"的增量。 -/
theorem procesi_splitting :
    Nonempty (((G.tensorDiagRepr 3).asModule ⊗[ℤ] ℚ) ≃ₗ[MonoidAlgebra ℤ (P.Hp 3)]
      (((G.Mres 3).ρ.asModule × (Irep).ρ.asModule) ⊗[ℤ] ℚ)) :=
  TauCeti.IsFractionRing.nonempty_tensor_linearEquiv_prod_of_exact
    (R := ℤ) (Q := ℚ) (G := P.Hp 3)
    (M := (G.Mres 3).ρ.asModule) (N := (G.tensorDiagRepr 3).asModule)
    (P := (Irep).ρ.asModule) (f := fLin) (g := gLin)
    fg_exact fLin_injective gLin_surjective

/-! ## §3 公理闸门 -/

#print axioms augF_smul_H
#print axioms Iact
#print axioms instDistribMulActionIOmega
#print axioms uniqueSums_iOmega
#print axioms Irep
#print axioms incInter
#print axioms phiInter
#print axioms fLin
#print axioms gLin
#print axioms fLin_injective
#print axioms gLin_surjective
#print axioms fg_exact
#print axioms procesi_splitting

end

end Procesi
