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

/-! ## (丙) `C_p` 作用的**组合核心**（第 367 轮，2026-10-15）

**所攻问句** ✓：素数阶群 `C_p = Multiplicative (ZMod p)` 作用在集合 `α` 上 —— 轨道能有多大？
**答案** ✓：**只能 1 或 p** ✓（轨道大小整除群阶 ✓，而素数只有 1 与自身两个因子 ✓）。
**推论** ✓：若作用**传递**，则 `card α ∈ {1, p}` ✓。
**⚠ 语境** ✗：轨道与其稳定化子的**有限性实例不会自动合成**（实测 ✗）⟹ 两条引理**要求调用方供给** ✓
（在二分的使用场景里 `α = MaxSpec L` 有限 ✓，实例由 `L` 的有限性给出 ✓）。
**⚠ 不声称** ✗：本件**不含**「`G` 在 `MaxSpec L` 上传递」本身（那要用 `L^G = K` ＋ 幂等元论证 ✗）——
也不含「p 个因子时 `L ≅ K^p`」的代数结论 ✗。 -/

section CpAction

/-- **(丙) ①** ✓：`C_p` 作用的轨道大小**只能是 1 或 p** ✓。
**证明** ✓：`card (orbit x) * card (stabilizer x) = card C_p = p` ✓ ⟹ `card (orbit x) ∣ p` ✓ ⟹ 素数因子只有 1 与 p ✓。 -/
theorem card_orbit_eq_one_or_eq_prime {p : ℕ} (hp : p.Prime)
    {α : Type*} [MulAction (Multiplicative (ZMod p)) α] (x : α)
    [Fintype (ZMod p)]
    [Fintype (MulAction.orbit (Multiplicative (ZMod p)) x)]
    [Fintype ↥(MulAction.stabilizer (Multiplicative (ZMod p)) x)] :
    Fintype.card (MulAction.orbit (Multiplicative (ZMod p)) x) = 1 ∨
      Fintype.card (MulAction.orbit (Multiplicative (ZMod p)) x) = p := by
  have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by
    simp [ZMod.card]
  have hmul :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Multiplicative (ZMod p)) x
  rw [hcard] at hmul
  have hdvd : Fintype.card (MulAction.orbit (Multiplicative (ZMod p)) x) ∣ p :=
    ⟨_, hmul.symm⟩
  exact hp.eq_one_or_self_of_dvd _ hdvd

/-- **(丙) ②（传递推论）** ✓：`C_p` 作用**传递** ⟹ `card α ∈ {1, p}` ✓。
**证明** ✓：取 `x` ✓，传递性 ⟹ 轨道 ＝ 全集 ✓ ⟹ `card α = card (orbit x)` ✓ 再用 ① ✓。 -/
theorem card_eq_one_or_eq_prime_of_pretransitive {p : ℕ} (hp : p.Prime)
    {α : Type*} [Fintype α] [MulAction (Multiplicative (ZMod p)) α]
    [MulAction.IsPretransitive (Multiplicative (ZMod p)) α] (x : α)
    [Fintype (ZMod p)]
    [Fintype (MulAction.orbit (Multiplicative (ZMod p)) x)]
    [Fintype ↥(MulAction.stabilizer (Multiplicative (ZMod p)) x)] :
    Fintype.card α = 1 ∨ Fintype.card α = p := by
  have hset : MulAction.orbit (Multiplicative (ZMod p)) x = (Set.univ : Set α) :=
    MulAction.orbit_eq_univ _ _
  have horbit : Fintype.card (MulAction.orbit (Multiplicative (ZMod p)) x) =
      Fintype.card α :=
    (Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by rw [hset]))).trans
      (Fintype.card_congr (Equiv.Set.univ α))
  rcases card_orbit_eq_one_or_eq_prime hp x with h | h
  · exact Or.inl (by rw [← horbit, h])
  · exact Or.inr (by rw [← horbit, h])

/-- **(丙) ③（幂等元核心）** ✓：若 `L` 的 **`G`-不变元都落在 `K` 的像**里（即 `L^G ⊆ K` ✓）
而 `K` 是**域** ✓，则 **`G`-不变幂等元只有 `0` 与 `1`** ✓。

**用途** ✓（(丙) 代数部分第 ① 步的引擎 ✓）：设 `L ≅ ∏_{i∈ι} L_i` ✓ 且 `G` 置换各因子 ✓。
若 `G` 在 `ι` 上**不传递** ✗，取一个非空真 `G`-稳定子集 `S` ✓，则 `e_S := Σ_{i∈S} e_i` 是
**`G`-不变幂等元**且 `≠ 0, 1` ✗ —— 与本条矛盾 ✓ ⟹ **作用必传递** ✓。
**⚠ 不声称** ✗：本件**只给引擎**（幂等元二分 ✓）；「因子置换 ＋ `e_S` 构造」与「传递 ⟹ `card ι ∈ {1,p}`」
的**拼接**仍待落 ✗（后者已由第 367 轮 `card_eq_one_or_eq_prime_of_pretransitive` ✓ 备好）。 -/
theorem fixed_idempotent_eq_zero_or_one [FaithfulSMul K L]
    {G : Type*} [Group G] [MulSemiringAction G L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → ∃ k : K, algebraMap K L k = x)
    (e : L) (he : IsIdempotentElem e) (hge : ∀ g : G, g • e = e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨k, hk⟩ := hfix e hge
  have hkidem : IsIdempotentElem k := by
    rw [isIdempotentElem_iff] at he ⊢
    exact FaithfulSMul.algebraMap_injective K L (by rw [map_mul, hk, he])
  rw [isIdempotentElem_iff] at hkidem
  have hzero : k * (k - 1) = 0 := by rw [mul_sub, mul_one, hkidem, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact Or.inl (by rw [← hk, h, map_zero])
  · exact Or.inr (by rw [← hk, sub_eq_zero.mp h, map_one])

#print axioms fixed_idempotent_eq_zero_or_one
#print axioms card_orbit_eq_one_or_eq_prime
#print axioms card_eq_one_or_eq_prime_of_pretransitive

end CpAction

end ABGV52.LocalProduct
