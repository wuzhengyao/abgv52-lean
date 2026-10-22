/-
  Procesi —— **第一层：格层**（lattice layer，论文 §"The Procesi Lattice"）

  源的六件（`raw/ABGV-5.2-resolution.pre44.tex:664–733` 逐字）：
    (1) `U = ℤ[Ω]`（`Ω = S₉/S₈`，秩 9）；
    (2) `φ : U ⊗ U → ℤ[Ω]`，`φ(e_α ⊗ e_β) = e_α − e_β`，`S₉`-等变；
    (3) `im φ = I[Ω] = ker ε`（增广理想，秩 8）；
    (4) `M := ker φ`（秩 73）＋正合列 `eq:procesi-S9`；
    (5) `M` 是 `ℤ`-自由（PID 上自由模的子模）；
    (6) 秩表 `9 / 81 / 8 / 73`；
    (7) 限制 `U|_H ≅ ℤ[H]`（`eq:U-restrict`）＋ `prop:U-restrict-canonical`。

  **本件不复刻证明**：上述全部在 `ABGV52`（同 pin 工具链）已机检
  （`G1b` 的 `phiFun`／`range_phiFun_eq`；`ProcLat` 的秩；`G1c` 的 `eL`；`GThm` 的
  `gThm_restrict_canonical`）。本件做**三件新事**（L47 库内优先 ＋ 本工作区的型锁职责）：
    * **`Module.Free ℤ M`**（第 (5) 件）：库内**没有**——本件用
      `Submodule.basisOfPid` 在张积的显式基上现造（`tensorBasis` ＋ `mBasis`）；
    * **`finrank ℚ (I[Ω] ⊗ ℚ) = 8`**（第 (3) 件的秩）：库内**没有**——本件用
      「ℚ 平坦于 ℤ ⟹ 正合性保持」＋ 两次 rank-nullity 现算；
    * **秩账闭合**：`73 + 9 = 82` 与 `81 − 73 = 8 = 9 − 1` 的**机器算术**。

  口径：`M` 在本工作区沿用 `Procesi.M = G.MRep 3`（`S₉`-层）；限制到 `H` 的
  「`H`-层 `M`」是 `G.MresOf`／`P.M_rep`（见 §4）。
-/
import ABGV52.ProcLat_ABGV52
import ABGV52.G2p_ABGV52
import ABGV52.GThm_ABGV52
import ABGV52.BR_ABGV52
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

/-! ## §1 正合性：`im φ = I[Ω] = ker ε` -/

/-- `I[Ω]` 就是 `augF` 的核（`rfl`；`IOmega` 是 `def`，故须显式给等式的方向）。 -/
theorem iOmega_eq_ker : G.IOmega 3 = LinearMap.ker (G.augF 3) := rfl

/-- ★ **`eq:procesi-S9` 的 ℤ-侧正合性**：`ker ε = im φ`
（论文 `:690`：`im φ = I[Ω] = ker(ε : ℤ[Ω] ⇉ ℤ)`）。 -/
theorem ker_augF_eq_range :
    LinearMap.ker (G.augF 3) = LinearMap.range (G.phiFun 3) := by
  rw [← iOmega_eq_ker]
  exact (G.range_phiFun_eq 3).symm

/-- 正合性（`φ`／`ε` 形，即 `eq:procesi-S9` 的映射层）：`Function.Exact φ ε`。 -/
theorem exact_phiFun_augF : Function.Exact (G.phiFun 3) (G.augF 3) :=
  LinearMap.exact_iff.mpr ker_augF_eq_range

/-! ## §2 `M = ker φ` 的 `ℤ`-自由性（第 (5) 件；库内没有） -/

/-- `ℤ[Ω] ⊗ ℤ[Ω]` 的显式 `ℤ`-基（`Ω × Ω` 索引）。 -/
def tensorBasis :
    Module.Basis (G.OmegaP 3 × G.OmegaP 3) ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3) :=
  (MonoidAlgebra.basis (G.OmegaP 3) ℤ).tensorProduct
    (MonoidAlgebra.basis (G.OmegaP 3) ℤ)

/-- **`M` 的 `ℤ`-基**：PID 上自由模的子模自由（`Submodule.basisOfPid`）。 -/
def mBasis : Σ n, Module.Basis (Fin n) ℤ ↥(LinearMap.ker (G.phiFun 3)) :=
  Submodule.basisOfPid (tensorBasis) (LinearMap.ker (G.phiFun 3))

/-- ★ **`M` 是 `ℤ`-自由模**（论文 `:716`：「`M` is `ℤ`-free: it is a `ℤ`-submodule of the
free `ℤ`-module `U ⊗ U`, and every submodule of a free `ℤ`-module is free (PID)」）。

**库内缺口**：`ABGV52` 有 `M` 的秩（`finrank_ker_phiFun`）但**没有**自由性——本件补。 -/
instance m_free : Module.Free ℤ ↥(LinearMap.ker (G.phiFun 3)) :=
  Module.Free.of_basis mBasis.2

/-! ## §3 秩表（第 (6) 件）与秩账 -/

/-- `rk U = 9`。 -/
theorem finrank_U : Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3) = 9 :=
  ProcLat.finrank_tensorU_three

/-- `rk (U ⊗ U) = 81`。 -/
theorem finrank_UU :
    Module.finrank ℚ (ℚ ⊗[ℤ] (G.ZOm 3 ⊗[ℤ] G.ZOm 3)) = 81 := by
  rw [ProcLat.finrank_tensorUU]

/-- ★ **`rk I[Ω] = 8`**（库内没有）：ℚ 平坦于 ℤ（正合性保持）＋ 两次 rank-nullity
——与 `ProcLat.finrank_ker_phiFun` 的 (0)–(3) 步同法，止于增广核。 -/
theorem finrank_I :
    Module.finrank ℚ (↥(G.IOmega 3) ⊗[ℤ] ℚ) = 8 := by
  have hQ : Function.Exact (AlgebraTensorModule.lTensor ℚ ℚ (G.phiFun 3))
      (AlgebraTensorModule.lTensor ℚ ℚ (G.augF 3)) :=
    Module.Flat.lTensor_exact ℚ exact_phiFun_augF
  have hsurj : Function.Surjective (AlgebraTensorModule.lTensor ℚ ℚ (G.augF 3)) :=
    LinearMap.lTensor_surjective ℚ (fun n =>
      ⟨MonoidAlgebra.single (G.omega0 3) n, G.augF_single 3 (G.omega0 3) n⟩)
  have hrange1 : Module.finrank ℚ
      (LinearMap.range (AlgebraTensorModule.lTensor ℚ ℚ (G.augF 3))) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top ℚ (ℚ ⊗[ℤ] ℤ),
      LinearEquiv.finrank_eq (AlgebraTensorModule.rid ℤ ℚ ℚ), Module.finrank_self]
  have hker1 : Module.finrank ℚ
      (LinearMap.ker (AlgebraTensorModule.lTensor ℚ ℚ (G.augF 3))) = 3 * 3 - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (AlgebraTensorModule.lTensor ℚ ℚ (G.augF 3))
    rw [hrange1, finrank_U] at h
    omega
  calc Module.finrank ℚ (↥(G.IOmega 3) ⊗[ℤ] ℚ)
      = Module.finrank ℚ (ℚ ⊗[ℤ] ↥(LinearMap.ker (G.augF 3))) := by
        rw [iOmega_eq_ker]
        exact LinearEquiv.finrank_eq (BR.commUpgrade ↥(LinearMap.ker (G.augF 3)))
    _ = Module.finrank ℚ
          ↥(LinearMap.ker (AlgebraTensorModule.lTensor ℚ ℚ (G.augF 3))) :=
        LinearEquiv.finrank_eq (LinearMap.tensorKerEquiv ℚ ℚ (G.augF 3))
    _ = 3 * 3 - 1 := hker1
    _ = 8 := by norm_num

/-- `rk M = 73`。 -/
theorem finrank_M :
    Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ) = 73 :=
  ProcLat.finrank_ker_phiFun_three

/-- `rk (M ⊕ U) = 82`。 -/
theorem finrank_Mp2 : Module.finrank ℚ (ProcLat.Mp2 3 ⊗[ℤ] ℚ) = 82 :=
  ProcLat.finrank_Mp2_three

/-- ★ **秩表**（论文 `:723–726` 的 `9 / 81 / 8 / 73` ＋ `M ⊕ U` 的 82）。 -/
theorem rank_table :
    Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3) = 9 ∧
    Module.finrank ℚ (ℚ ⊗[ℤ] (G.ZOm 3 ⊗[ℤ] G.ZOm 3)) = 81 ∧
    Module.finrank ℚ (↥(G.IOmega 3) ⊗[ℤ] ℚ) = 8 ∧
    Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ) = 73 ∧
    Module.finrank ℚ (ProcLat.Mp2 3 ⊗[ℤ] ℚ) = 82 :=
  ⟨finrank_U, finrank_UU, finrank_I, finrank_M, finrank_Mp2⟩

/-- ★ **秩账闭合（甲）**：`rk M + rk U = rk (M ⊕ U)`，即 `73 + 9 = 82`
——`AGPR2020` `cor:14.4.5` 的 `n²+1`（`n = 9`）与 Procesi 格的秩账在此**机器闭合**。 -/
theorem rank_account_add :
    Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ)
      + Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3)
      = Module.finrank ℚ (ProcLat.Mp2 3 ⊗[ℤ] ℚ) := by
  rw [finrank_M, finrank_U, finrank_Mp2]

/-- ★ **秩账闭合（乙）**：`rk (U ⊗ U) − rk M = rk I[Ω]`，即 `81 − 73 = 8`
（正合列 `eq:procesi-S9` 的秩收支）。 -/
theorem rank_account_exact :
    Module.finrank ℚ (ℚ ⊗[ℤ] (G.ZOm 3 ⊗[ℤ] G.ZOm 3))
      - Module.finrank ℚ (↥(LinearMap.ker (G.phiFun 3)) ⊗[ℤ] ℚ)
      = Module.finrank ℚ (↥(G.IOmega 3) ⊗[ℤ] ℚ) := by
  rw [finrank_UU, finrank_M, finrank_I]

/-- ★ **秩账闭合（丙）**：`rk I[Ω] = rk U − 1`，即 `8 = 9 − 1`（增广理想）。 -/
theorem rank_account_aug :
    Module.finrank ℚ (↥(G.IOmega 3) ⊗[ℤ] ℚ)
      = Module.finrank ℚ (ℚ ⊗[ℤ] G.ZOm 3) - 1 := by
  rw [finrank_I, finrank_U]

/-! ## §4 限制到 `H = C₃ × C₃`（`eq:U-restrict` ＋ `prop:U-restrict-canonical`） -/

/-- ★ **`eq:U-restrict` 的机器形**：`U|_H → ℤ[H]`（`e_{h·ω₀} ↦ h`）是
**`ℤ[H]`-模同构**——即 `eL` 把 `U|_H` 的作用换到 `ℤ[H]` 的**左乘**作用。

**逐字源**（论文 `:711`）：`U|_H ≅ ℤ[H]`，`e_{h·ω₀} ↦ h`，由 `H` 在 `Ω` 上
**正则**（`|H| = |Ω|` ＋ 传递）得来。 -/
theorem eq_U_restrict (h : P.Hp 3) (f : G.ZOm 3) :
    G.eL 3 ((G.UH 3).ρ h f) = P.lmul 3 h (G.eL 3 f) :=
  G.eL_lmul 3 h f

/-- ★ **`prop:U-restrict-canonical`**（论文 `:624`）：**任意**基点 `e : H ≃ Ω`
给出的限制都与正则模型 `M_rep` 同构——故 `M|_H` 的同构类与基点无关。 -/
theorem prop_U_restrict_canonical (e : P.Hp 3 ≃ G.OmegaP 3) :
    Nonempty (G.MresOf 3 e ≅ P.M_rep 3) :=
  G.gThm_restrict_canonical 3 e

/-- **`prop:embedding-independence`**（论文 `:644`）：两基点给出的限制同构。 -/
theorem prop_embedding_independence (e₁ e₂ : P.Hp 3 ≃ G.OmegaP 3) :
    Nonempty (G.MresOf 3 e₁ ≅ G.MresOf 3 e₂) :=
  G.gThm_embedding_independence 3 e₁ e₂

/-! ## §4b **`ℤ`-秩**（论文 `rk_ℤ` 的逐字口径） -/

/-- `ker φ` 的有限性（由 `mBasis` 的有限基）。 -/
instance m_finite : Module.Finite ℤ ↥(LinearMap.ker (G.phiFun 3)) :=
  Module.Finite.of_basis mBasis.2

/-- `ℤ[Ω] ⊗ ℤ[Ω]` 的自由性（由 `tensorBasis`）。 -/
instance tensorU_free : Module.Free ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3) :=
  Module.Free.of_basis tensorBasis

/-- `ℤ[Ω] ⊗ ℤ[Ω]` 的有限性。 -/
instance tensorU_finite : Module.Finite ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3) :=
  Module.Finite.of_basis tensorBasis

/-- 桥：`finrank ℤ X = finrank ℚ (ℚ ⊗ X)`（`Module.finrank_baseChange` 的逆向）。 -/
theorem finrankZ_eq {X : Type} [AddCommGroup X] [Module ℤ X] [Module.Free ℤ X] :
    Module.finrank ℤ X = Module.finrank ℚ (ℚ ⊗[ℤ] X) :=
  (Module.finrank_baseChange (R := ℚ) (S := ℤ) (M' := X)).symm

/-- 桥（`X ⊗ ℚ` 口径，与 `finrank_*` 的写法一致）。 -/
theorem finrankZ_eq' {X : Type} [AddCommGroup X] [Module ℤ X] [Module.Free ℤ X] :
    Module.finrank ℤ X = Module.finrank ℚ (X ⊗[ℤ] ℚ) := by
  rw [finrankZ_eq, ← LinearEquiv.finrank_eq (BR.commUpgrade X)]

/-- ★ **`rk_ℤ U = 9`**（论文 `:727–731` 的 `rk_ℤ U = 9`）。 -/
theorem finrank_Z_U : Module.finrank ℤ (G.ZOm 3) = 9 := by
  rw [finrankZ_eq, finrank_U]

/-- ★ **`rk_ℤ (U ⊗ U) = 81`**。 -/
theorem finrank_Z_UU : Module.finrank ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3) = 81 := by
  rw [finrankZ_eq, finrank_UU]

/-- ★ **`rk_ℤ I[Ω] = 8`**。 -/
theorem finrank_Z_I : Module.finrank ℤ ↥(G.IOmega 3) = 8 := by
  rw [finrankZ_eq', finrank_I]

/-- ★ **`rk_ℤ M = 73`**。 -/
theorem finrank_Z_M : Module.finrank ℤ ↥(LinearMap.ker (G.phiFun 3)) = 73 := by
  rw [finrankZ_eq', finrank_M]

/-- ★★ **`rk_ℤ (M ⊕ U) = 82`（结构版秩账）**：由 `Module.finrank_prod` 直接得
`73 + 9 = 82`（比 `rank_account_add` 的**算术**核对更强：此处走的是乘法性引理）。 -/
theorem finrank_Z_Mp2 : Module.finrank ℤ (ProcLat.Mp2 3) = 82 := by
  have h := Module.finrank_prod (R := ℤ)
    (M := ↥(LinearMap.ker (G.phiFun 3))) (M' := G.ZOm 3)
  rw [finrank_Z_M, finrank_Z_U] at h
  exact h

/-- **`ℤ`-秩表**（论文 `eq:procesi-S9` 段的 `rk_ℤ` 口径：四项 ＋ `M ⊕ U`）。 -/
theorem rank_table_Z :
    Module.finrank ℤ (G.ZOm 3) = 9 ∧
    Module.finrank ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3) = 81 ∧
    Module.finrank ℤ ↥(G.IOmega 3) = 8 ∧
    Module.finrank ℤ ↥(LinearMap.ker (G.phiFun 3)) = 73 ∧
    Module.finrank ℤ (ProcLat.Mp2 3) = 82 :=
  ⟨finrank_Z_U, finrank_Z_UU, finrank_Z_I, finrank_Z_M, finrank_Z_Mp2⟩

/-- ★★ **秩账闭合（乙′，结构版，`ℤ` 口径）**：`rk_ℤ (U ⊗ U) = rk_ℤ M + rk_ℤ I[Ω]`
（即 `81 = 73 + 8`）。

**与（乙）的差别**：`rank_account_exact` 由三条秩的**算术**改写得到；本件走**结构**路线——
`eq:procesi-S9` 的正合性（`exact_phiFun_augF` ＋ `iOmega_eq_ker`）＋ **秩-零化度**
（`LinearMap.finrank_range_add_finrank_ker`，`HasRankNullity ℤ` 由 `IsDomain.hasRankNullity` 给）。
这就是 TauCeti 分裂数值对接所需的 `finrank` 结构件（`ℤ` 口径，与论文 `rk_ℤ` 同口径）。 -/
theorem rank_account_exact_Z :
    Module.finrank ℤ (G.ZOm 3 ⊗[ℤ] G.ZOm 3)
      = Module.finrank ℤ ↥(LinearMap.ker (G.phiFun 3))
        + Module.finrank ℤ ↥(G.IOmega 3) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.phiFun 3)
  have hEx : LinearMap.ker (G.augF 3) = LinearMap.range (G.phiFun 3) :=
    LinearMap.exact_iff.mp exact_phiFun_augF
  rw [← hEx, ← iOmega_eq_ker] at h
  omega

/-! ## §5 公理闸门 -/

#print axioms iOmega_eq_ker
#print axioms ker_augF_eq_range
#print axioms exact_phiFun_augF
#print axioms tensorBasis
#print axioms mBasis
#print axioms m_free
#print axioms finrank_U
#print axioms finrank_UU
#print axioms finrank_I
#print axioms finrank_M
#print axioms finrank_Mp2
#print axioms rank_table
#print axioms rank_account_add
#print axioms rank_account_exact
#print axioms rank_account_exact_Z
#print axioms rank_account_aug
#print axioms eq_U_restrict
#print axioms prop_U_restrict_canonical
#print axioms m_finite
#print axioms tensorU_free
#print axioms tensorU_finite
#print axioms finrankZ_eq
#print axioms finrankZ_eq'
#print axioms finrank_Z_U
#print axioms finrank_Z_UU
#print axioms finrank_Z_I
#print axioms finrank_Z_M
#print axioms finrank_Z_Mp2
#print axioms rank_table_Z
#print axioms prop_embedding_independence

end

end Procesi
