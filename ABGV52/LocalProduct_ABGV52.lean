import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# (乙) 有限维交换代数 ⟹ **局部积分解**（第 365 轮，2026-10-15）

**所攻问句**：设 `K` 为域、`L` 为交换 `K`-代数、`Module.Finite K L` —— `L` 能否**规范地**写成
**有限个局部环之积**？

**答案** ✓（**全部用 mathlib 现成件** ✓，本文件只做**装配** ✓）：
`IsArtinianRing.of_finite` ⟹ `IsArtinianRing L` ⟹
`IsArtinianRing.instDiscreteTopologyPrimeSpectrum` ⟹ `DiscreteTopology (PrimeSpectrum L)` ⟹
**`MaximalSpectrum.toPiLocalizationEquiv L : L ≃ₐ[L] ∏_{I ∈ MaxSpec L} L_I`** ✓
（`MaximalSpectrum.PiLocalization L = Π I : MaximalSpectrum L, Localization.AtPrime I.1` ✓），
每个因子**局部** ✓（`IsLocalization.AtPrime.isLocalRing` ✓）、指标集**有限** ✓
（`IsArtinianRing.instFiniteMaximalSpectrum` ✓）。

**⚠ 与侦察的关系** ✓：这正是 [[proj-lean-external-recon-protocol]] §4 表 2 所记的**第二次假阻断**
（此前记为「mathlib 无，须外部理论」✗）；本轮把它**落成库件** ✓。
**⚠ 不声称** ✗：本件**不含** `C_p`-作用的**传递性论证**（(丙) ✓）与**分量同构** ✗ —— 那是下一段；
亦**不含** (甲)（`Module.Finite K L` 本身 ✗）。 -/

namespace ABGV52.LocalProduct

variable (K L : Type*) [Field K] [CommRing L] [Algebra K L]

/-- **(乙) 第 ① 步** ✓：`L` 在域 `K` 上有限 ⟹ `L` 是 Artin 环。 -/
theorem isArtinianRing_of_finite [Module.Finite K L] : IsArtinianRing L :=
  IsArtinianRing.of_finite K L

/-- **(乙) 第 ② 步** ✓：指标集（极大谱）**有限**。 -/
theorem finite_maximalSpectrum_of_finite [Module.Finite K L] :
    Finite (MaximalSpectrum L) := by
  haveI : IsArtinianRing L := isArtinianRing_of_finite K L
  infer_instance

/-- **(乙) 主件** ✓：**局部积分解** `L ≃ₐ[L] ∏_{I ∈ MaxSpec L} L_I`（规范同构 ✓）。
**读法** ✓：右端每个因子是 `L` 在极大理想处的局部化 ✓ ⟹ 局部环 ✓（见 `factor_isLocalRing` ✓）。

**⚠ 语境** ✗：右端的 `L`-代数结构**本身**依赖 `DiscreteTopology (PrimeSpectrum L)` ✓
（故本件在 `[IsArtinianRing L]` 下陈述 ✓ —— 该实例由 `IsArtinianRing.instDiscreteTopologyPrimeSpectrum` 供给 ✓）。
**由 `Module.Finite K L` 到此** ✓：先 `haveI : IsArtinianRing L := isArtinianRing_of_finite K L` ✓（第 ① 步 ✓）。 -/
noncomputable def localProductEquiv [IsArtinianRing L] :
    L ≃ₐ[L] MaximalSpectrum.PiLocalization L :=
  MaximalSpectrum.toPiLocalizationEquiv L

/-- **(乙) 第 ③ 步** ✓：每个因子**是局部环** ✓。 -/
theorem factor_isLocalRing (I : MaximalSpectrum L) :
    IsLocalRing (Localization.AtPrime I.1) :=
  IsLocalization.AtPrime.isLocalRing (Localization.AtPrime I.1) I.1

/-- **(乙) 打包形**（消费入口 ✓）：`L ≅ ∏` 且指标集有限、因子皆局部 ✓。 -/
theorem exists_local_product_decomposition [IsArtinianRing L] :
    Finite (MaximalSpectrum L) ∧
      Nonempty (L ≃ₐ[L] MaximalSpectrum.PiLocalization L) ∧
      (∀ I : MaximalSpectrum L, IsLocalRing (Localization.AtPrime I.1)) :=
  ⟨inferInstance, ⟨localProductEquiv L⟩, factor_isLocalRing L⟩

#print axioms isArtinianRing_of_finite
#print axioms finite_maximalSpectrum_of_finite
#print axioms localProductEquiv
#print axioms factor_isLocalRing
#print axioms exists_local_product_decomposition

end ABGV52.LocalProduct
