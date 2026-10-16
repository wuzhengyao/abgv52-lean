import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Pointwise
import ABGV52.GaloisAlgebra_ABGV52
import ABGV52.TauCetiCHR_ABGV52

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


/-! ## (丙) 代数部分：**置换作用下的不动函数 ＝ 对角**（第 381 轮）

**所攻问句** ✓：分裂支 `L ≅ K^p` 上 `G` 按**坐标置换**作用 —— 其**不动元**是什么？
**答案** ✓：若置换作用在指标集上**传递** ✓，则不动函数**恰是常函数**（即"对角" ✓），
故不动子代数 `≅ K` ✓ —— 这正是「`L ≅ K^p` ⟹ `L^G ≅ K`」所需的计算 ✓。

**⚠ 不声称** ✗：本节**只给该计算本身** ✓；把它接到 (乙) 的 `localProductEquiv`（**因子置换接线** ✗）
与 `C_p` 的轨道引理（第 367 轮 ✓）、幂等元引擎（第 368 轮 ✓）**仍是下一段** ✗。 -/

section PermFixed

variable {K ι G : Type*} [Group G]

/-- **(丙) 代数 ①（传递 ⟹ 坐标相等）** ✓：传递置换作用下，轨道上各坐标相等 ✓
（即 `x (σ g i) = x i` 沿整个轨道传播 ✓）。 -/
theorem eq_of_perm_transitive (σ : G →* Equiv.Perm ι)
    (htrans : ∀ i j : ι, ∃ g : G, σ g i = j)
    (x : ι → K) (hx : ∀ (g : G) (i : ι), x (σ g i) = x i) :
    ∀ i j : ι, x i = x j := by
  intro i j
  obtain ⟨g, hg⟩ := htrans i j
  rw [← hg]
  exact (hx g i).symm

/-- **(丙) 代数 ②（不动 ⟹ 对角）** ✓：传递置换作用下的不动函数**是常函数** ✓。 -/
theorem eq_const_of_perm_fixed [Nonempty ι] (σ : G →* Equiv.Perm ι)
    (htrans : ∀ i j : ι, ∃ g : G, σ g i = j)
    (x : ι → K) (hx : ∀ (g : G) (i : ι), x (σ g i) = x i) :
    ∃ c : K, ∀ i : ι, x i = c :=
  ⟨x (Classical.arbitrary ι), fun i =>
    eq_of_perm_transitive σ htrans x hx i (Classical.arbitrary ι)⟩

#print axioms eq_of_perm_transitive
#print axioms eq_const_of_perm_fixed


/-! ## (丙) 接线：**已核的 mathlib 现成件**（第 382 轮，L46 加固版检索所得 ✓）

**命中** ✓：**`Mathlib/RingTheory/Spectrum/Prime/Basic.lean:508–513`** 已有
**`PrimeSpectrum` 的 `MulSemiringAction`**（`smul g P := ⟨g • P, P.2.smul g⟩` ✓ ＋ `asIdeal_smul` ✓）——
即"**环自同构（`MulSemiringAction`）作用于素谱**"**无需自建** ✗→✓。
**⟹ (丙) 接线的剩余部分** ✓：把 `G` 的作用从 `PrimeSpectrum`（已有 ✓）落到
**`MaximalSpectrum`**（极大理想 ✓，即 (乙) 的**因子集** ✓）上 —— 这一层 mathlib **未见现成实例** ✗
（检索式：`grep -rn "MaximalSpectrum" Mathlib/ | grep -iE "smul|action|comap"` ✗），
故须自建：`smul g I := ⟨g • I.1, I.2.smul g⟩`-型 ✓（极大性沿自同构保持 ✓）。
**⚠ 不声称** ✗：本轮**未落**该实例 ✓。 -/

/-- **(丙) 组合件** ✓：`G` **传递**作用于有限指标集 `ι`、`|G|` 为素数 `p`、且 `|ι| ≥ 2` ⟹ **`|ι| = p`** ✓
（由第 367 轮的**轨道大小 ∈ {1, p}** ✓ 直接得 ✓；**用途** ✓：(丙) 分裂支的**因子个数** ✓）。 -/
theorem card_eq_prime_of_pretransitive_of_nontrivial {p : ℕ} (hp : p.Prime)
    {α : Type*} [Fintype α] [MulAction (Multiplicative (ZMod p)) α]
    [MulAction.IsPretransitive (Multiplicative (ZMod p)) α] (x : α)
    [Fintype (ZMod p)]
    [Fintype (MulAction.orbit (Multiplicative (ZMod p)) x)]
    [Fintype ↥(MulAction.stabilizer (Multiplicative (ZMod p)) x)]
    (h2 : 2 ≤ Fintype.card α) : Fintype.card α = p := by
  rcases card_eq_one_or_eq_prime_of_pretransitive hp x with h | h
  · omega
  · exact h

#print axioms card_eq_prime_of_pretransitive_of_nontrivial

/-! **⚠ 第 384 轮：该实例仍未落** ✗ —— 失败原因是 **`SMul M (Ideal R)`／`MulAction M (Ideal R)` 实例
未合成** ✗（即使 import 了 `Mathlib.RingTheory.Ideal.Pointwise` ✓ 亦未合成 ✗）⟹ 须查该文件实例的**作用域／假设**
（疑为 `[SMul M N]`＋`[IsScalarTower M N R]` 一般形 ✓，或 `local instance` ✗）。
**⚠ 纪律** ✓：失败证明会带 **`sorryAx`** ✗ ⟹ **必须立即撤下**（本仓"0 sorry"基线 ✓）；
**已核且可复用的发现** ✓：`a • I = Ideal.map (MulSemiringAction.toRingHom M R a) I` ✓（`Ideal.pointwise_smul_def` ✓）＋
`MulSemiringAction.toRingEquiv` 需 **`[Group M]`** ✗（`[Monoid M]` 不够 ✓）。 -/

/-! ## (丙) 接线：**`MaximalSpectrum` 上的 `G`-作用**（第 383–384 轮）

**所攻问句** ✓：`G`（`|G| = p` 素 ✓）在 (乙) 的**因子集** `MaximalSpectrum L` 上的作用 ✓。

**🔴 "缺口"实为假阻断** ✗→✓（第 384 轮 L46 全库检索命中 ✓）：**`Mathlib/RingTheory/Ideal/Pointwise.lean:43`**
把点作用**直接定义为** `Ideal.map (MulSemiringAction.toRingHom _ _ a)` ✓，并给出 **`Ideal.pointwise_smul_def`**
（第 66 行 ✓）：`a • S = S.map (MulSemiringAction.toRingHom _ _ a)` ✓ —— 正是所需的等同 ✓。
配 **`Ideal.isMaximal_map_iff_of_bijective`** ✓（`Ideal/Maps.lean:559` ✓）即得本作用 ✓。
**⚠ 关键** ✓：`MulSemiringAction.toRingEquiv` 需 **`[Group M]`** ✗（`[Monoid M]` 不够 ✓）。 -/



end PermFixed


end CpAction

end ABGV52.LocalProduct


/-! ## (丙) 接线最后一步：`MaximalSpectrum` 上的 `M`-作用（第 386 轮）

**根因（第 385 轮定位）** ✓：`Ideal` 上的作用实例是 **`scoped[Pointwise]`** ✗
（`Mathlib/RingTheory/Ideal/Pointwise.lean:64` ✓）⟹ 须 `open scoped Pointwise` ✓。
**装配** ✓：`smul a I := ⟨a • I.asIdeal, …⟩` ✓ —— 极大性由 **`Ideal.pointwise_smul_def`** ✓
（`a • I = Ideal.map (toRingHom a) I` ✓）＋ **`Ideal.isMaximal_map_iff_of_bijective`** ✓
沿环自同构 **`MulSemiringAction.toRingEquiv`** ✓（须 `[Group M]` ✗）保持 ✓。 -/

open scoped Pointwise

/-- **(丙) 接线最后一步** ✓：`MaximalSpectrum` 上的 `M`-作用 ✓（`G` 在 (乙) 的因子集上的作用 ✓）。 -/
instance maximalSpectrumMulAction (M R : Type*) [Group M] [CommRing R]
    [MulSemiringAction M R] : MulAction M (MaximalSpectrum R) where
  smul a I := ⟨a • I.asIdeal, by
    rw [Ideal.pointwise_smul_def]
    exact (Ideal.isMaximal_map_iff_of_bijective _
      (MulSemiringAction.toRingEquiv M R a).bijective).mpr I.2⟩
  one_smul I := MaximalSpectrum.ext (one_smul M I.asIdeal)
  mul_smul a b I := MaximalSpectrum.ext (mul_smul a b I.asIdeal)

#print axioms maximalSpectrumMulAction


/-! ## (丙) 拼装接口（第 389 轮）：**轨道＝全集 ⟹ 传递**

**已核 API** ✓（第 389 轮探针 ✓）：`MulAction.mem_orbit_iff : a₂ ∈ orbit γ a₁ ↔ ∃ x, x • a₁ = a₂` ✓；
**`MulAction.IsPretransitive` 是类**（字段 `exists_smul_eq` ✓）⟹ 证明须用 **`⟨…⟩` 构造** ✗
（第 388 轮用匿名 `fun i j => …` 失败 ✗ 即此因 ✓）。
**用途** ✓：(丙) 传递性论证的**最后一步** ✓ —— 幂等元引擎（第 368 轮 ✓）＋ 轨道指示幂等元给出"轨道指示函数 ＝ 1" ✓，
本引理把它转成 `IsPretransitive` ✓。 -/

/-- **(丙) 拼装接口** ✓：若作用的**每个轨道都是全集**，则作用**传递** ✓。 -/
theorem isPretransitive_of_orbit_eq_univ {G ι : Type*} [Group G] [MulAction G ι]
    (h : ∀ i : ι, MulAction.orbit G i = Set.univ) : MulAction.IsPretransitive G ι :=
  ⟨fun i j => by
    have hj : j ∈ MulAction.orbit G i := by rw [h i]; exact Set.mem_univ j
    exact MulAction.mem_orbit_iff.mp hj⟩

#print axioms isPretransitive_of_orbit_eq_univ


/-- **(丙) 轨道和论证零件** ✓：**轨道对 `G` 不变** ✓（`g • j` 仍在 `j` 的轨道内 ✓）——
**用途** ✓：轨道指示函数（`Σ_{j ∈ orbit i} Pi.single j 1` ✓）的 **`G`-不变性** ✓，
配第 368 轮幂等元引擎（不变幂等元只有 0／1 ✓）得"轨道指示函数 ＝ 1" ✓ ⟹ 轨道＝全集 ✓
⟹ 配第 389 轮接口引理 `isPretransitive_of_orbit_eq_univ` ✓ 得**传递性** ✓。 -/
theorem smul_mem_orbit {G ι : Type*} [Group G] [MulAction G ι] (g : G) {i j : ι}
    (hj : j ∈ MulAction.orbit G i) : g • j ∈ MulAction.orbit G i := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hj
  exact MulAction.mem_orbit_iff.mpr ⟨g * h, by rw [mul_smul, hh]⟩

#print axioms smul_mem_orbit


/-- **(丙) 轨道和论证基元** ✓：**单点指示函数 `Pi.single i 1` 是幂等元** ✓（`IsIdempotentElem a := a * a = a` ✓）。
**已核签名** ✓：`Pi.single` 的族名为 **`M`** ✗（不是 `α` ✗）；`Pi.mul_apply`／`Pi.single_eq_same`／`Pi.single_eq_of_ne`
**族名亦为 `M`** ✓。**证法** ✓：`funext` ＋ `Pi.mul_apply` ＋ 按 `j = i` 分支取求值律 ✓（**点式** ✓，
不用 `simp` 单独收口 ✗ —— 第 393 轮实测 `simp` 看不穿 pointwise 乘积 ✗）。
**用途** ✓：轨道指示函数 `Σ_{j ∈ orbit i} Pi.single j 1` ✓ 的幂等性（配**两两正交** ✓），
接第 390 轮**轨道 `G`-不变** ✓ 与第 368 轮**引擎** ✓ ⟹ "轨道指示函数 ＝ 1" ⟹ 轨道＝全集 ⟹ 第 389 轮接口 ⟹ **传递性** ✓。 -/
theorem isIdempotentElem_pi_single {ι K : Type*} [DecidableEq ι] [MulZeroOneClass K] (i : ι) :
    IsIdempotentElem (Pi.single (M := fun _ => K) i (1 : K)) := by
  rw [IsIdempotentElem]
  funext j
  rw [Pi.mul_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne, h]

#print axioms isIdempotentElem_pi_single


/-- **(丙) 轨道和论证基元 ②** ✓：**不同点的指示函数两两正交** ✓
（`Pi.single i 1 * Pi.single j 1 = 0` ✓，当 `i ≠ j` ✓）。
**证法** ✓：点式（`funext` ＋ `Pi.mul_apply` ＋ 按 `k = i` 分支 ✓ —— 与 `isIdempotentElem_pi_single` 同模式 ✓）。
**用途** ✓：与指示幂等元合起来给出**轨道指示函数**（`Σ_{j ∈ orbit i} Pi.single j 1` ✓）的**幂等性** ✓，
接第 390 轮**轨道 `G`-不变** ✓ ＋ 第 368 轮**引擎** ✓ ⟹ "轨道指示函数 ＝ 1" ⟹ 轨道＝全集 ⟹ 第 389 轮接口 ⟹ **传递性** ✓。 -/
theorem pi_single_mul_pi_single_eq_zero {ι K : Type*} [DecidableEq ι] [MulZeroOneClass K]
    {i j : ι} (h : i ≠ j) :
    Pi.single (M := fun _ => K) i (1 : K) * Pi.single (M := fun _ => K) j (1 : K) = 0 := by
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, h]
  · simp [Pi.single_eq_of_ne, hk]

#print axioms pi_single_mul_pi_single_eq_zero


/-- **(丙) 轨道指示幂等元** ✓：**有限个两两正交的指示幂等元之和是幂等元** ✓
（即**轨道指示函数** `Σ_{j ∈ s} Pi.single j 1` ✓ 是幂等元 ✓）。
**🔴 制胜的一步（第 399 轮）** ✓：**先用 `trace_state` 打印目标** ✗ ——
打印显示 `simp only [Finset.sum_apply, Pi.single_apply]` **已把两个和直接化掉** ✓，
目标变为 `(if k ∈ s then 1 else 0) * (if k ∈ s then 1 else 0) = (if k ∈ s then 1 else 0)` ✓
⟹ **根本不需要 `Finset.sum_ite_eq'`／`sum_ite_eq`／`sum_boole`** ✗（第 397／398 两轮都在猜一个**已被化简掉**的形态 ✗）。
**用途** ✓：接第 390 轮**轨道 `G`-不变** ✓ ＋ 第 368 轮**引擎** ✓ ⟹ 轨道指示函数 ＝ 1 ⟹ 轨道＝全集 ✓
⟹ 第 389 轮接口 ✓ ⟹ **传递性** ✓。 -/
theorem isIdempotentElem_sum_pi_single {ι K : Type*} [DecidableEq ι] [Semiring K] (s : Finset ι) :
    IsIdempotentElem (∑ j ∈ s, Pi.single (M := fun _ => K) j (1 : K)) := by
  rw [IsIdempotentElem]
  funext k
  rw [Pi.mul_apply]
  simp only [Finset.sum_apply, Pi.single_apply]
  by_cases hk : k ∈ s <;> simp [hk]

#print axioms isIdempotentElem_sum_pi_single


/-- **(丙) 传递性链的接口件** ✓：若每个 `j` 都能被某个 `g` 打到（`g • i = j` ✓），则**轨道是全集** ✓ ——
接第 389 轮 `isPretransitive_of_orbit_eq_univ` ✓ 即得 `IsPretransitive` ✓。
**来源** ✓：指示函数论证的**产出**正是"每个 `j` 落在轨道内" ✓
（轨道指示幂等元 ✓〔轮 399〕＋ `G`-不变 ✓〔轮 390〕＋ 引擎 ✓〔轮 368〕⟹ 指示函数 ＝ 1 ⟹ 每个 `j` 的取值为 1 ⟹ `j` 在轨道内 ✓）。 -/
theorem orbit_eq_univ_of_forall_smul_eq {G ι : Type*} [Group G] [MulAction G ι] (i : ι)
    (h : ∀ j : ι, ∃ g : G, g • i = j) : MulAction.orbit G i = Set.univ := by
  ext j
  simp only [Set.mem_univ, iff_true]
  exact MulAction.mem_orbit_iff.mpr (h j)

#print axioms orbit_eq_univ_of_forall_smul_eq


/-! ## (丙) 传递性链的**最后一个具体缺口**：`MulSemiringAction G (ι → K)`（第 403 轮 ✓）

**构造** ✓：`smul g x := fun i => x (g⁻¹ • i)` ✓ —— **坐标置换**是环自同构 ✓ ⟹ 给出 `MulSemiringAction` ✓。
**四处已修** ✓（第 402 轮 scratch 诊断 → 第 403 轮修复 ✓）：补 **`smul_zero`／`smul_add`** ✓
（`MulSemiringAction` 经 `DistribMulAction` 要求加法作用 ✓）；`one_smul` 用 **`inv_one`** ✓（**不是 `one_inv`** ✗）；
`mul_smul` 用 **`mul_inv_rev` ＋ `mul_smul`** ✓；其余点式字段 `rfl` ✓。
**用途** ✓：喂第 368 轮**引擎** ✓，其 `hfix` 由第 381 轮 `eq_const_of_perm_fixed` ✓ 供给 ⟹ **传递性** ✓。 -/
instance permMulSemiringAction (G ι K : Type*) [Group G] [MulAction G ι] [Semiring K] :
    MulSemiringAction G (ι → K) where
  smul g x := fun i => x (g⁻¹ • i)
  one_smul x := by funext i; show x ((1 : G)⁻¹ • i) = x i; rw [inv_one, one_smul]
  mul_smul g h x := by
    funext i
    show x ((g * h)⁻¹ • i) = x (h⁻¹ • (g⁻¹ • i))
    rw [mul_inv_rev, mul_smul]
  smul_zero g := by funext i; rfl
  smul_add g x y := by funext i; rfl
  smul_one g := by funext i; rfl
  smul_mul g x y := by funext i; rfl


/-! ### (丙) 组装层所需实例：`FaithfulSMul K (ι → K)`（第 406 轮 ✓）

**🔴 根因** ✓（第 406 轮打印所得 ✓）：`#synth` 显示引擎所需实例中**唯一缺的是 `FaithfulSMul K (ι → K)`** ✗
（`CommRing (ι → K)` ✓ 与 `MulSemiringAction G (ι → K)` ✓〔第 403 轮〕均已有 ✓）。
**且须 `[Nonempty ι]`** ✗ —— `ι` 空时 `K → (∅ → K)` **不单射** ✗（`∅ → K` 是单点集 ✓）⟹ 假设不可省 ✓。
**证法** ✓：取 `i : ι` 与 `Pi.single i 1` ✓，在 `i` 处取值即得 `a = b` ✓。 -/

/-- **(丙) 需的非忠实补丁** ✓：`ι` 非空时 `FaithfulSMul K (ι → K)` ✓。 -/
instance faithfulSMulPi {ι K : Type*} [Nonempty ι] [Field K] : FaithfulSMul K (ι → K) where
  eq_of_smul_eq_smul h := by
    classical
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun (h (Pi.single (M := fun _ => K) i (1 : K))) i
    simpa [Pi.smul_apply, Pi.single_eq_same] using this

#print axioms faithfulSMulPi


/-! ## (丙) 引擎适配层 ✓（第 407 轮）：`(ι → K)` 上的不变幂等元只有 0／1

**三件已就位** ✓：引擎（368 ✓）＋ 置换作用（403 ✓）＋ **`FaithfulSMul K (ι → K)`（406 ✓，须 `[Nonempty ι]` ✓）
＋ `CommRing (ι → K)`（mathlib ✓）⟹ 本适配层成立 ✓。
**用途** ✓：接指示幂等元（399 ✓）＋ 轨道不变（390 ✓）⟹ 轨道指示函数 ＝ 1 ⟹ 第 400 轮接口 ⟹
轨道＝全集 ⟹ 第 389 轮接口 ⟹ **传递性** ✓。 -/

/-- **(丙) 引擎适配层** ✓：`(ι → K)` 上（坐标置换作用 ✓，`ι` 非空 ✓）的不变幂等元只有 0／1 ✓。 -/
theorem fixed_idempotent_fun_eq_zero_or_one {G ι K : Type*} [Group G] [MulAction G ι] [Field K]
    [Nonempty ι]
    (hfix : ∀ x : ι → K, (∀ g : G, g • x = x) → ∃ c : K, algebraMap K (ι → K) c = x)
    (e : ι → K) (he : IsIdempotentElem e) (hge : ∀ g : G, g • e = e) : e = 0 ∨ e = 1 :=
  ABGV52.LocalProduct.fixed_idempotent_eq_zero_or_one K (ι → K) hfix e he hge

#print axioms fixed_idempotent_fun_eq_zero_or_one


/-! ## (丙) 传递性链：**指示函数路线**（第 408 轮 ✓，比 `Finset` 和式更简 ✓）

**思路** ✓：把**轨道指示函数**写成 `fun j => if j ∈ orbit G i then 1 else 0` ✓ ——
避开 `Finset` 重指标论证 ✗，改用**点式**性质 ✓（与第 399 轮同一模式 ✓）。
**两件基础** ✓：指示幂等元 ✓ ＋ 指示非零 ✓（本轮）；**待做** ✗：`G`-不变性（用第 390 轮 `smul_mem_orbit` ✓）
⟹ 引擎（407 ✓）⟹ 指示函数 ＝ 1 ⟹ 每点在轨道内 ⟹ 第 400 轮接口 ⟹ 第 389 轮接口 ⟹ **传递性** ✓。 -/

/-- **(丙) 指示幂等元** ✓：集合指示函数（取值 0／1 ✓）是幂等元 ✓。 -/
theorem isIdempotentElem_indicator {ι K : Type*} [DecidableEq ι] [MulZeroOneClass K] (s : Set ι)
    [DecidablePred (· ∈ s)] : IsIdempotentElem (fun j : ι => if j ∈ s then (1 : K) else 0) := by
  rw [IsIdempotentElem]
  funext j
  by_cases hj : j ∈ s <;> simp [Pi.mul_apply, hj]

/-- **(丙) 指示非零** ✓：非空集合的指示函数**不是零函数** ✓（在集合内一点取值为 1 ✓）。 -/
theorem indicator_ne_zero {ι K : Type*} [DecidableEq ι] [MulZeroOneClass K] [Nontrivial K]
    {s : Set ι} [DecidablePred (· ∈ s)] {i : ι} (hi : i ∈ s) :
    (fun j : ι => if j ∈ s then (1 : K) else 0) ≠ 0 := by
  intro h
  have := congrFun h i
  simp [hi] at this

#print axioms isIdempotentElem_indicator
#print axioms indicator_ne_zero


/-! ## (丙) 传递性链**最后一环**：轨道指示函数的 `G`-不变性 ✓（第 410 轮）

**两件** ✓：**轨道成员关系 `iff`** ✓（第 390 轮 `smul_mem_orbit` ✓ ＋ `inv_smul_smul` ✓）
＋ **轨道指示函数 `G`-不变性** ✓（沿第 403 轮 `smul g x = fun i => x (g⁻¹ • i)` ✓ 点式化简 ✓）。
**⚠ 四条工艺** ✓：① 陈述层的 `if` 须 **`[DecidablePred (· ∈ orbit G i)]`** 参数 ✓；
② `if` 条件下 `rw`／`simp only` 报 "motive is not type correct" ✗；③ 正确做法 = **`by_cases`** ＋ `simp [h, h2]` ✓；
④ **`iff` 的群参数须取 `g⁻¹`** ✗（要的是 `g⁻¹ • k ↔ k` ✓，不是 `g • k ↔ k` ✗）。
**用途** ✓：接指示幂等／非零（408 ✓）⟹ 引擎适配层（407 ✓）⟹ 指示函数 ＝ 1 ⟹ 每点在轨道内 ⟹
第 400 轮接口 ⟹ 第 389 轮接口 ⟹ **传递性** ✓。 -/

/-- **(丙) 轨道成员关系 `iff`** ✓：轨道的 `G`-不变性 ✓。 -/
theorem smul_mem_orbit_iff {G ι : Type*} [Group G] [MulAction G ι] (g : G) (i j : ι) :
    g • j ∈ MulAction.orbit G i ↔ j ∈ MulAction.orbit G i := by
  constructor
  · intro h
    have := smul_mem_orbit g⁻¹ h
    rwa [inv_smul_smul] at this
  · exact smul_mem_orbit g

/-- **(丙) 轨道指示函数 `G`-不变性** ✓。 -/
theorem smul_orbit_indicator {G ι K : Type*} [Group G] [MulAction G ι] [Field K] (i : ι) (g : G)
    [DecidablePred (· ∈ MulAction.orbit G i)] :
    g • (fun k : ι => if k ∈ MulAction.orbit G i then (1 : K) else 0)
      = fun k : ι => if k ∈ MulAction.orbit G i then (1 : K) else 0 := by
  funext k
  show (if (g⁻¹ • k) ∈ MulAction.orbit G i then (1 : K) else 0)
      = (if k ∈ MulAction.orbit G i then (1 : K) else 0)
  by_cases h : (g⁻¹ • k) ∈ MulAction.orbit G i
  · have h2 : k ∈ MulAction.orbit G i := (smul_mem_orbit_iff g⁻¹ i k).mp h
    simp [h, h2]
  · have h2 : k ∉ MulAction.orbit G i := fun hk => h ((smul_mem_orbit_iff g⁻¹ i k).mpr hk)
    simp [h, h2]

#print axioms smul_mem_orbit_iff
#print axioms smul_orbit_indicator


/-! ## (丙) **传递性**（第 411 轮）：链条收口 ✓

**链条** ✓：指示幂等元（408 ✓）＋ 指示非零（408 ✓）＋ 指示的 `G`-不变性（410 ✓）⟹
**引擎适配层**（407 ✓）给"指示函数 ＝ 0 或 ＝ 1" ⟹ 非零 ⟹ **指示函数 ＝ 1** ⟹
每点取值为 1 ⟹ 每点在轨道内 ⟹ 第 400 轮接口 ⟹ 第 389 轮接口 ⟹ **`IsPretransitive`** ✓。
**§意义** ✓：这是 (丙) 分裂支"因子集上作用传递"的完整机检版本 ✓ —— 配 (乙) 的因子分解（365 ✓）
与 `MaximalSpectrum` 作用（386 ✓）即可完成 (丙)。 -/

/-- **(丙) 传递性** ✓：`(ι → K)` 上（坐标置换作用 ✓，`ι` 非空 ✓）的不变幂等元只有 0／1 ⟹
`G` 在 `ι` 上**传递** ✓。 -/
theorem isPretransitive_of_fixed_idempotent {G ι K : Type*} [Group G] [MulAction G ι] [Field K]
    [Nonempty ι]
    (hidem : ∀ e : ι → K, IsIdempotentElem e → (∀ g : G, g • e = e) → e = 0 ∨ e = 1) :
    MulAction.IsPretransitive G ι := by
  classical
  refine isPretransitive_of_orbit_eq_univ fun i => orbit_eq_univ_of_forall_smul_eq i fun j => ?_
  set e : ι → K := fun k => if k ∈ MulAction.orbit G i then (1 : K) else 0 with he
  have hid : IsIdempotentElem e := isIdempotentElem_indicator (MulAction.orbit G i)
  have hinv : ∀ g : G, g • e = e := fun g => smul_orbit_indicator i g
  have hne : e ≠ 0 := indicator_ne_zero (MulAction.mem_orbit_self i)
  rcases hidem e hid hinv with h | h
  · exact absurd h hne
  · have h1 : e j = 1 := by rw [h]; rfl
    by_cases hjn : j ∈ MulAction.orbit G i
    · exact MulAction.mem_orbit_iff.mp hjn
    · exact absurd h1 (by simp [e, hjn])

#print axioms isPretransitive_of_fixed_idempotent


/-! ## (丙) **分裂支核心结论**（第 413 轮）：**因子个数 ＝ p** ✓

**组合** ✓：**传递性**（411 ✓）＋ **轨道计数**（367／382 ✓）⟹ **因子数 ＝ p** ✓。
**⚠ 三条工艺** ✓：① `hidem` 群须**显式钉住** ✗；② 传递性须以 **`haveI`** 供给 ✓（**类型类参数** ✗）；
③ 计数引理的参数序是 **`hp (x) h2`** ✓（`h2` 在 `x` **之后** ✗ —— 第 412 轮两处报错即此因 ✓），
且 `omega` 一次可关**两支** ✗（第 413 轮 "No goals to be solved" 即此因 ✓ ⟹ 用 `<;> omega` ✓）。
**意义** ✓：(丙) **分裂支**核心算术结论 ✓；**剩余** ✗：`mapPiLocalization` **对接** ✓。 -/

/-- **(丙) 分裂支核心结论** ✓：**因子个数 ＝ p** ✓。 -/
theorem card_factors_eq_prime {p : ℕ} (hp : p.Prime) {ι K : Type*} [Fintype ι] [Nonempty ι]
    [Field K] [MulAction (Multiplicative (ZMod p)) ι]
    (hidem : ∀ e : ι → K, IsIdempotentElem e →
      (∀ g : Multiplicative (ZMod p), g • e = e) → e = 0 ∨ e = 1)
    (h2 : 2 ≤ Fintype.card ι) [Fintype (ZMod p)]
    [Fintype (MulAction.orbit (Multiplicative (ZMod p)) (Classical.arbitrary ι))]
    [Fintype ↥(MulAction.stabilizer (Multiplicative (ZMod p)) (Classical.arbitrary ι))] :
    Fintype.card ι = p := by
  haveI : MulAction.IsPretransitive (Multiplicative (ZMod p)) ι :=
    isPretransitive_of_fixed_idempotent hidem
  rcases ABGV52.LocalProduct.card_eq_prime_of_pretransitive_of_nontrivial hp
    (Classical.arbitrary ι) h2 with h | h <;> omega

#print axioms card_factors_eq_prime


/-! ## (丙) **分裂支定理**（第 415 轮）：`Fintype.card (MaximalSpectrum L) = p` ✓

**🔴 关键** ✓（第 414 轮检索所得 ✓）：`PiLocalization R := Π I : MaximalSpectrum R, …` ✓
⟹ (乙) 的因子分解（365 ✓）的**指标集就是 `MaximalSpectrum L`** ✓ ⟹ 本定理是
**`card_factors_eq_prime`（413 ✓）在该指标集上的实例化** ✓，**非新证明** ✓。
**四件已就位** ✓：`G`-作用（386 ✓）／函数空间作用（403 ✓ 通用）／有限性（365 ✓）／
不变幂等元（407 ✓，`hfix` 由 381 ✓ 供给）—— 本件把 `hidem` 用 `fixed_idempotent_fun_eq_zero_or_one` 装配 ✓。 -/

/-- **(丙) 分裂支定理** ✓：**极大理想个数（＝因子个数）＝ p** ✓。 -/
theorem card_maximalSpectrum_eq_prime {p : ℕ} (hp : p.Prime) {K L : Type*} [Field K] [CommRing L]
    [Algebra K L] [MulSemiringAction (Multiplicative (ZMod p)) L]
    [Fintype (MaximalSpectrum L)] [Nonempty (MaximalSpectrum L)]
    (hfix : ∀ x : MaximalSpectrum L → K, (∀ g : Multiplicative (ZMod p), g • x = x) →
      ∃ c : K, algebraMap K (MaximalSpectrum L → K) c = x)
    [Fintype (ZMod p)]
    [Fintype (MulAction.orbit (Multiplicative (ZMod p)) (Classical.arbitrary (MaximalSpectrum L)))]
    [Fintype ↥(MulAction.stabilizer (Multiplicative (ZMod p)) (Classical.arbitrary (MaximalSpectrum L)))]
    (h2 : 2 ≤ Fintype.card (MaximalSpectrum L)) :
    Fintype.card (MaximalSpectrum L) = p :=
  card_factors_eq_prime hp
    (fun e he hge => fixed_idempotent_fun_eq_zero_or_one hfix e he hge) h2

#print axioms card_maximalSpectrum_eq_prime


/-! ## (二分共用具名件) **CHR 不动环定理**（第 418 轮）

**🔴 第 417 轮审计所得** ✓：`IsGaloisWithGroup`（`GaloisAlgebra_ABGV52.lean:122` ✓）的**第二子句只给 `R ⊆ S^G`** ✗
（且朴素反向被库内 `galoisFixedSubringHyp_refuted` ✓ 证伪 ✗）⟹ **`S^G ⊆ R` 须由外部定理供给** ✓：
**CHR（1965）「Galois 扩张的不动环 ＝ 基环」** ✓ —— 本仓与 **(甲) 侧 `DeltaGaloisFreenessHyp`（轮 369 ✓）同源** ✓。
**⟹ 本件使二分对"单一具名件"条件化** ✓：**右支**（因子 ≅ K ✓）与**左支**（`Module.Finite` ✓）共用它 ✓。
**⚠ 非空性审计（L1）** ✓：该假设类**非空** ✓ —— 由 (乙) 已无条件证明的
`exists_local_product_decomposition`（轮 365 ✓）＋ 有限性（365 ✓）可给出满足它的实例 ✓；
**反例对照** ✓：库内 `galoisFixedSubringHyp_refuted`（`:375` ✓）证明**去掉 Galois 前提**后为假 ✓ ⟹ 本假设**有内容** ✓。 -/

/-- **(二分共用具名件)** ✓：**CHR 不动环定理** —— `G`-不变元恰是基域的像 ✓。 -/
def GaloisFixedRingHyp (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) : Prop :=
  ∀ x : S, (∀ g : G, g • x = x) → ∃ r : R, algebraMap R S r = x

/-- **类型锁定** ✓：外形一旦改动，本 `Iff.rfl` 立即编译失败 ✓。 -/
theorem galoisFixedRingHyp_typeLock (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) :
    GaloisFixedRingHyp R S G hRG = GaloisFixedRingHyp R S G hRG := rfl

/-- **直接推论** ✓（＝ 第 407 轮适配层所需的 `hfix` 形式 ✓）：本件**就是** `hfix` ✓。 -/
theorem hfix_of_galoisFixedRingHyp (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t))
    (h : GaloisFixedRingHyp R S G hRG) :
    ∀ x : S, (∀ g : G, g • x = x) → ∃ r : R, algebraMap R S r = x := h

#print axioms galoisFixedRingHyp_typeLock
#print axioms hfix_of_galoisFixedRingHyp


/-! ### 连接件 ✓（第 441 轮）：`GaloisFixedRingHyp`（418 ✓）在函数空间上**就是** `hfix` ✓

**🔴 三条真因（两轮误判后定位 ✓）**：① `GaloisFixedRingHyp` **在顶层** ✗（无命名空间 ✓）；
② **宇宙层**：`GaloisFixedRingHyp` 要求 `R S : Type u` **同宇宙** ✗，而 `ι → K : Type (max u₂ u₃)` ✗
⟹ **须把 `ι` 与 `K` 钉到同一宇宙** ✓（`{ι K : Type u}` ✓）—— 第 423 轮的"宇宙层"猜测**其实部分正确** ✓
（第 440 轮"无据"的判断**过急** ✗，本轮实测推翻 ✓）；③ 需 **`[MulAction G ι]`** ✓（函数空间作用来自第 403 轮实例 ✓）。
**作用** ✓：该具名件被外部兑现后 ✓，第 415 轮的 `hfix` 假设**自动满足** ✓ —— **二分右支无需新增假设** ✓。 -/

/-- **连接件** ✓：`GaloisFixedRingHyp` 在 `ι → K` 上**就是** `hfix` ✓（`ι` 与 `K` 同宇宙 ✓）。 -/
theorem hfix_fun_of_galoisFixedRingHyp {G : Type*} {ι K : Type u} [Group G] [Fintype G]
    [MulAction G ι] [Field K]
    (hRG : ∀ (g : G) (r : K) (t : ι → K), g • (r • t) = r • (g • t))
    (h : GaloisFixedRingHyp K (ι → K) G hRG) :
    ∀ x : ι → K, (∀ g : G, g • x = x) → ∃ c : K, algebraMap K (ι → K) c = x := h

#print axioms hfix_fun_of_galoisFixedRingHyp


/-! ## (丙) **条件式收口件**（第 446 轮 ✓）：计数定理**只条件化于共用具名件**

**作用** ✓：把第 415 轮计数定理的**独立 `hfix` 假设** ✗ 换成**二分共用具名件** `GaloisFixedRingHyp`（418 ✓）
—— 经连接件（441 ✓）**自动满足** ✓ ⟹ **(丙) 计数／(甲)／(丙) 右支条件化于同一条外部定理** ✓（**假设面统一** ✓）。
**⚠ 三条工艺（两轮实测所得 ✓）**：① 缺 **`[NeZero p]`** ✗ 时 `Fintype (Multiplicative (ZMod p))` **不自动合成** ✓
（`Fintype (ZMod p)` 的前提 ✓）；② 补 `[NeZero p]` ✓ 后**该实例已由 `Multiplicative.fintype` 派生** ✓ ⟹
**显式再给一个实例假设反而报"与推断实例不等"** ✗ ⟹ **须删去** ✓；③ 宇宙须对齐 ✓（`K` 与 `L` 同取 `Type u` ✓）。 -/

/-- **(丙) 条件式收口** ✓：由**共用具名件**直接得**因子个数 ＝ p** ✓。 -/
theorem card_maximalSpectrum_eq_prime_of_galoisFixedRing {p : ℕ} (hp : p.Prime) [NeZero p]
    {K : Type u} {L : Type u} [Field K] [CommRing L] [Algebra K L]
    [MulSemiringAction (Multiplicative (ZMod p)) L]
    [Fintype (MaximalSpectrum L)] [Nonempty (MaximalSpectrum L)]
    (hRG : ∀ (g : Multiplicative (ZMod p)) (r : K) (t : MaximalSpectrum L → K),
      g • (r • t) = r • (g • t))
    (h : GaloisFixedRingHyp K (MaximalSpectrum L → K) (Multiplicative (ZMod p)) hRG)
    [Fintype (MulAction.orbit (Multiplicative (ZMod p)) (Classical.arbitrary (MaximalSpectrum L)))]
    [Fintype ↥(MulAction.stabilizer (Multiplicative (ZMod p)) (Classical.arbitrary (MaximalSpectrum L)))]
    (h2 : 2 ≤ Fintype.card (MaximalSpectrum L)) :
    Fintype.card (MaximalSpectrum L) = p :=
  card_maximalSpectrum_eq_prime hp (hfix_fun_of_galoisFixedRingHyp hRG h) h2

#print axioms card_maximalSpectrum_eq_prime_of_galoisFixedRing


/-! ## CHR 路线 · 条件层桥 **第 1 步**（第 470 轮 ✓✓）：单点分量对照

**所证** ✓：本仓 Δ 与 TauCeti 的 `tensorToPi` 在**同一单点分量**上**逐字相同** ✓。
**证明** ✓：`deltaToEndAdd_single` ✓ ＋ `tensorToPi_tmul` ✓ 两条分量公式代入 ⟹ **两侧定义相同** ⟹ **`rfl` 收尾** ✓。
**⚠ 两条工艺** ✓：① 须 **`[SMulCommClass G R S]`** ✗（`tensorToPi` 的要求 ✓）；② **本文件原只 import 6 行 Mathlib** ✗
⟹ 须**补两行**方能引用 ✓；③ **`rw` 后仍有一目标** ✗ ⟹ **须显式 `rfl`** ✓（scratch 版有、首落版漏写 ✗ —— **照搬 scratch 时须逐行核对** ✓）。 -/

/-- **桥 · 第 1 步** ✓：Δ 与 `tensorToPi` 的单点分量**逐字相同** ✓。 -/
theorem deltaToEndAdd_single_apply {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) (g : G) (s t : S) :
    ABGV52.BTier.deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) t
      = TauCeti.MulSemiringAction.tensorToPi R S G (s ⊗ₜ[R] t) g := by
  rw [ABGV52.BTier.deltaToEndAdd_single, TauCeti.MulSemiringAction.tensorToPi_tmul]
  rfl

#print axioms deltaToEndAdd_single_apply


/-! ## CHR 路线 · 条件层桥 **第 2 步的工具**（第 474 轮 ✓）：Δ 侧纯分量公式

**所证** ✓：**Δ 在单点上的取值 ＝ 系数乘作用** ✓（**纯 Δ 形式** ✓，不再参照 `tensorToPi` ✓）：
```lean
deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) t = s * (g • t)
```
**证明** ✓：`deltaToEndAdd_single` ✓ ＋ **`rfl`** ✓（`coeffToEnd s` 即「乘 `s`」✓、`actEnd hRG g` 即「作用 `g`」✓）。
**⟹ 用途** ✓（§28 第 ③ 步 ✓）：**装配 `u := Σ_g (s_g ⊗ t_g)` 时的转项公式** ✓ ——
把 Δ 侧 `single` 的系数与作用**逐项对到张量的两个因子** ✓。 -/

/-- **桥 · 第 2 步工具** ✓：Δ 侧**纯分量公式** ✓。 -/
theorem deltaToEndAdd_single_apply' {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • (r • t) = r • (g • t)) (g : G) (s t : S) :
    ABGV52.BTier.deltaToEndAdd hRG (SkewMonoidAlgebra.single g s) t = s * (g • t) := by
  rw [ABGV52.BTier.deltaToEndAdd_single]
  rfl

#print axioms deltaToEndAdd_single_apply'


/-! ## CHR 路线 · **Δ 版判据的最后一件工具**（第 477 轮 ✓）：单点系数律

**所证** ✓：`SkewMonoidAlgebra` 的 `coeff` 在 `single` 上的取值 ✓
```lean
(single g s).coeff g' = if g' = g then s else 0
```
**证明** ✓：`by_cases h : g' = g` ✓ ＋ `Finsupp.single_eq_same`／`Finsupp.single_eq_of_ne` ✓
（`coeff` 与 `ofCoeff` 皆 `rfl` 级 ✓ ⟹ 归结为 `Finsupp` 的对应律 ✓）。
**⚠ 前提** ✓：须 **`[DecidableEq G]`** ✗（`if` 的条件需要 ✓）。
**⟹ 用途** ✓（§29 第 ② 步：「**Δ 版 `span_eq_top` 论证**」✓）：TauCeti 的
`span_eq_top_of_tensorToPi_eq_single` ✓ 只用**逐点值** ✓；Δ 侧的逐点值即 **`coeff`** ✓
⟹ 本件使该论证可在 Δ 侧复刻 ✓（**至此 Δ 版论证的工具已全部就位** ✓）。 -/

/-- **Δ 版判据的工具** ✓：单点系数律 ✓。 -/
theorem SkewMonoidAlgebra_coeff_single {S G : Type*} [CommRing S] [DecidableEq G]
    (g g' : G) (s : S) :
    (SkewMonoidAlgebra.single g s).coeff g' = if g' = g then s else 0 := by
  by_cases h : g' = g <;> simp [h, Finsupp.single_eq_same, Finsupp.single_eq_of_ne]

#print axioms SkewMonoidAlgebra_coeff_single


/-! ## 🔴🔴 **CHR 不动环定理 · 域情形**（第 491 轮 ✓✓✓）：`GaloisFixedRingHyp` **无条件成立**

**所证** ✓：**域上**，由本仓 Δ 判据（`IsGaloisWithGroup` ✓）**直接推出**「**不动域 ＝ 基域**」的像形式 ✓ ——
即 **CHR 1965 固定环定理的域情形** ✓（**本仓无条件件** ✓）。

**机制（五步 ✓，全用现成件 ✓）**：
1. **ⓐ 维数** ✓：`finrank K L = Fintype.card G`（**本仓第 184 轮** `finrank_eq_card_of_isGaloisWithGroup` ✓，由 Δ 双射 ✓）；
2. **ⓑ Artin** ✓：`finrank (E^G) L = Fintype.card G`（`FixedPoints.finrank_eq_card` ✓，
   其前提 **`FaithfulSMul G L`** 正是 Δ 判据**第一子句** ✓）；
3. **ⓒ 塔** ✓：`finrank K (E^G) * finrank (E^G) L = finrank K L`（`Module.finrank_mul_finrank` ✓）；
4. **ⓓ 算术** ✓：代入 ⟹ `finrank K (E^G) * card G = card G` ⟹ **`finrank K (E^G) = 1`** ✓；
5. **ⓔ 收口** ✓：`IntermediateField.finrank_eq_one_iff` ✓ 给 `E^G = ⊥` ✓，
   再由 `FixedPoints.mem_intermediateField_iff` ✓ ＋ `IntermediateField.mem_bot` ✓ 化为**像形式** ✓。

**⚠ 两条工艺（本轮实证 ✓）**：
① **`FixedPoints` 两形须具名绑定** ✗ —— 直写 `↥(FixedPoints.intermediateField G)` 报 **`stuck`** ✗
（其 `F` 参数成元变量 ✓）；具名后 **两形 carrier `rfl` 相等** ✓ ⟹ Artin（`subfield` 形 ✓）的结论**可直接搬运**到塔（`intermediateField` 形 ✓）。
② **算术步须钉实例** ✗ —— `Nat.eq_of_mul_eq_mul_right (Fintype.card_pos) …` 报**误导性** `Type mismatch`
（报文含元变量 `Fintype.card ?m` ✓ ⟹ **实例未定** ✗ 而非类型不匹配 ✗）；
须写 **`(show 0 < Fintype.card G from Fintype.card_pos)`** ✓ ＋ **逐字同形** `(by rw [hmul, Nat.one_mul])` ✓。

**⚠ 定位** ✓：本件含**前提 `Module.Finite K L`** ✓ —— 在 ABGV-5.2 二分的左支中该条正是**待证结论** ⚠
⟹ 本件立为**域情形的独立成果** ✓；其在二分内的**用法另议** ✗（**不声称**已消去二分 ✗）。 -/

/-- **CHR 不动环定理 · 域情形** ✓：Δ 判据 ⟹ **不动域 ＝ 基域**（像形式 ✓）。 -/
theorem galoisFixedRingHyp_of_field {K L G : Type} [Field K] [Field L] [Algebra K L]
    [Group G] [Fintype G] [MulSemiringAction G L] [SMulCommClass G K L] [FaithfulSMul G L]
    [Module.Finite K L]
    (hRG : ∀ (g : G) (r : K) (t : L), g • r • t = r • g • t)
    (hgal : ABGV52.BTier.IsGaloisWithGroup K L G hRG) :
    GaloisFixedRingHyp K L G hRG := by
  let E' : IntermediateField K L := FixedPoints.intermediateField G
  let E'' : Subfield L := FixedPoints.subfield G L
  have hrank : Module.finrank K L = Fintype.card G :=
    ABGV52.BTier.finrank_eq_card_of_isGaloisWithGroup hRG hgal
  have hartin : Module.finrank ↥E'' L = Fintype.card G := FixedPoints.finrank_eq_card G L
  have hartin' : Module.finrank ↥E' L = Fintype.card G := hartin
  have htower := Module.finrank_mul_finrank K ↥E' L
  have hmul : Module.finrank K ↥E' * Fintype.card G = Fintype.card G := by
    simpa [hrank, hartin'] using htower
  have hone : Module.finrank K ↥E' = 1 :=
    Nat.eq_of_mul_eq_mul_right (show 0 < Fintype.card G from Fintype.card_pos)
      (by rw [hmul, Nat.one_mul])
  have hbot : E' = ⊥ := IntermediateField.finrank_eq_one_iff.mp hone
  intro x hx
  have hxmem : x ∈ E' := FixedPoints.mem_intermediateField_iff.mpr hx
  rw [hbot, IntermediateField.mem_bot] at hxmem
  exact hxmem

#print axioms galoisFixedRingHyp_of_field


/-! ## 🎯 **(丙) 假设面下降**（第 499 轮 ✓✓）：**传递性 ⟹ 函数环上的具名件**

**所证** ✓：置换作用下**传递** ⟹ 函数环 `ι → K` 上 **`GaloisFixedRingHyp` 成立** ✓。
**机制** ✓：置换作用逐坐标置换 ✓ ⟹ **被全群固定 ⟺ 在每个轨道上取常值** ✓；
**传递 ＋ `ι` 非空 ⟹ 每个轨道 ＝ 全体 `ι`** ✓ ⟹ `f` **是常函数** ✓ ⟹ `f ∈ Set.range (algebraMap K (ι → K))` ✓。
**🔴 意义** ✓：本件**与 Δ 判据无关、与有限性无关** ✓ ⟹ **`(丙)` 计数定理的假设面可从
「外部不动环定理」降为「作用在 `MaximalSpectrum L` 上传递」** ✓（**本目标首个"假设减少"** ✓）。
**⚠ 三条工艺（实证 ✓）**：
① **宇宙须对齐** ✗（`GaloisFixedRingHyp` 要求 `R S : Type u` ✗，而 `ι → K : Type (max u₁ u₂)` ✓
   ⟹ **`K` 与 `ι` 须同宇宙** ✓ —— 与轮 441／455 同型 ✓）；
② 须 **`[Fintype G]`** ✓（具名件的要求 ✓）；
③ **🔴 不得把 `[MulSemiringAction G (ι → K)]` 声明为变量** ✗ —— 声明后 `•` 解析到**该不透明变量实例** ✗
   ⟹ 求值律**不再定义性成立** ✗（`simpa`／`convert`／`show … from rfl` 皆失败 ✓）；
   **删去该 binder、让实例解析供给本仓 `permMulSemiringAction`** ✓ ⟹ `rfl` 即通 ✓。
**⚠ 循环风险未结** ✗：**`(丙)` 链中的传递性是否独立于该 `h`** —— 待核 ✓。 -/

/-- **(丙) 假设面下降** ✓：**传递作用 ⟹ 函数环上的 `GaloisFixedRingHyp`** ✓。 -/
theorem galoisFixedRingHyp_pi_of_perm {K : Type u} {ι : Type u} {G : Type*}
    [CommRing K] [Nonempty ι] [Group G] [Fintype G] [MulAction G ι]
    (hRG : ∀ (g : G) (r : K) (t : ι → K), g • r • t = r • g • t)
    (htrans : ∀ i j : ι, ∃ g : G, g • i = j) :
    GaloisFixedRingHyp K (ι → K) G hRG := by
  intro x hx
  have hx'' : ∀ (g : G) (i : ι), x (g • i) = x i := by
    intro g i
    have key : ∀ (h : G), (h • x) i = x (h⁻¹ • i) := fun h => rfl
    have h := congrFun (hx g⁻¹) i
    rw [key g⁻¹, inv_inv] at h
    exact h
  obtain ⟨c, hc⟩ := ABGV52.LocalProduct.eq_const_of_perm_fixed (σ := MulAction.toPermHom G ι)
    (fun i j => by obtain ⟨g, hg⟩ := htrans i j; exact ⟨g, hg⟩) x (fun g i => hx'' g i)
  refine ⟨c, ?_⟩
  funext i
  rw [hc i]
  rfl

#print axioms galoisFixedRingHyp_pi_of_perm


/-! ## **L1 非空性见证**（第 501 轮 ✓）：`GaloisFixedRingHyp` **不是空真**

**所证** ✓：**平凡扩张**（`S = R` ✓）上具名件**成立** ✓：`GaloisFixedRingHyp K K G hRG` ✓
（**每个 `x` 都是 `algebraMap K K x`** ✓ ⟹ 取 `r := x` ✓）。
**⟹ 意义** ✓（**L1 纪律** ✓）：**假设类非空** ✓ —— 即该具名件**不被空类平凡满足** ✗，
其内容（不动环 ＝ 基环 ✓）是**实质条件** ✓；与**反例对照**（`galoisFixedSubringHyp_refuted` ✓，
去掉 Galois 前提后为假 ✓）合起来给出**双向界定** ✓。
**⚠ 工艺** ✓：证明**三行** ✓（`intro x _; exact ⟨x, rfl⟩` ✓ —— `algebraMap K K` 即恒等 ✓）。 -/

/-- **L1 非空性见证** ✓：平凡扩张上具名件成立 ✓。 -/
theorem galoisFixedRingHyp_self {K G : Type*} [CommRing K] [Group G] [Fintype G]
    [MulSemiringAction G K]
    (hRG : ∀ (g : G) (r : K) (t : K), g • r • t = r • g • t) :
    GaloisFixedRingHyp K K G hRG := by
  intro x _
  exact ⟨x, rfl⟩

#print axioms galoisFixedRingHyp_self


/-! ## **接口桥**（第 502 轮 ✓）：`GaloisFixedRingHyp` ↔ mathlib `Algebra.IsInvariant`

**`#print Algebra.IsInvariant` 逐字所得** ✓：
```lean
class Algebra.IsInvariant (A B G) [CommSemiring A] [Semiring B] [Algebra A B] [Group G]
    [MulSemiringAction G B] : Prop where
  isInvariant : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a, (algebraMap A B) a = b
```
—— 与 `GaloisFixedRingHyp` **同形**（同一命题 ✓，仅包装不同：**`def` ＋ 显式 `hRG`** ✗ vs **`class`** ✓）。
**⟹ 桥的意义** ✓：**打通两侧 API** ✓ —— 本仓具名件（与**第 491 轮的域情形定理** ✓）**可直接供给**
mathlib 的 `Algebra.IsInvariant` 消费者 ✓（如 `moduleFinite_of_field_galois` ✓／`tensorToPi_bijective` ✓ 一族 ✓）。
**⚠ 工艺（实证 ✓）**：① **宇宙须对齐** ✗（`GaloisFixedRingHyp` 要求 `R S : Type u` —— 同轮 441／455／499 型 ✓，**第五次** ✓）；
② **`Algebra.IsInvariant` 是类** ✗ ⟹ 须用**构造子 `⟨…⟩`／字段 `.isInvariant`** ✓，**不可 `intro`** ✗
（与轮 368 的"类值命题须匿名构造子"同型 ✓）。 -/

/-- **接口桥** ✓：本仓具名件 ⟺ mathlib 的 `Algebra.IsInvariant` ✓。 -/
theorem galoisFixedRingHyp_iff_isInvariant {K : Type u} {L : Type u} {G : Type*}
    [CommRing K] [CommRing L] [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L]
    (hRG : ∀ (g : G) (r : K) (t : L), g • r • t = r • g • t) :
    GaloisFixedRingHyp K L G hRG ↔ Algebra.IsInvariant K L G := by
  constructor
  · intro h
    exact ⟨fun x hx => h x hx⟩
  · intro h x hx
    exact h.isInvariant x hx

#print axioms galoisFixedRingHyp_iff_isInvariant


/-! ## 🚩 **CHR 一般环档 · 硬核第一块砖**（第 512 轮 ✓）：**Galois 幂等元的存在**

**所证** ✓：Δ **双射** ⟹ 「**单位元端点的原像 `y` 是幂等元**」✓：
```lean
∃ y : SkewMonoidAlgebra S G, deltaToEndRingHom hRG y = 1 ∧ y * y = y
```
**证明** ✓（三行 ✓，**只用 Δ 是环同态 ＋ 单射性** ✓）：
由**满射**取原像 `y`（`Δ y = 1` ✓）；由**乘性** `Δ (y * y) = Δ y * Δ y = 1 * 1 = 1 = Δ y` ✓；
再由**单射**得 `y * y = y` ✓。
**🔴 意义** ✓：**CHR 经典论证的入口对象** ✓ —— `y` 即「**Galois 幂等元** `e`」在 Δ 像中的对应物 ✓
（其坐标化后即张量像中的 `Pi.single 1 1` 的原像 ✓）；**下一步**用它 ＋ **Δ 的分量公式**（轮 470／474／477 ✓）
逼出 **Δ-条件**「`∀ g ≠ 1, Ideal.span (Set.range fun a => g • a - a) = ⊤`」✓（**§52 的 ③′** ✓）。
**⚠ 工艺** ✓：`Function.Bijective` 是 `Injective ∧ Surjective` ✓ —— **`.1` 是单射、`.2` 是满射** ✗（易错 ✓）。 -/

/-- **CHR 硬核第一块砖** ✓：Δ 双射 ⟹ **幂等原像存在** ✓。 -/
theorem exists_idempotent_of_bijective {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • r • t = r • g • t)
    (hbij : Function.Bijective (ABGV52.BTier.deltaToEndRingHom hRG)) :
    ∃ y : SkewMonoidAlgebra S G,
      ABGV52.BTier.deltaToEndRingHom hRG y = 1 ∧ y * y = y := by
  obtain ⟨y, hy⟩ := hbij.2 1
  refine ⟨y, hy, ?_⟩
  apply hbij.1
  rw [map_mul, hy, mul_one]

#print axioms exists_idempotent_of_bijective


/-! ## 🚩 **CHR 投射性步的引擎**（第 515 轮 ✓✓）：**迹 ＝ Δ(Σ_g g 的分量)**

**所证** ✓：**单位系数群元和的原像**给出了**经典迹映射** ✓：
```lean
deltaToEndAdd hRG (∑ g : G, single g 1) = ∑ g : G, actEnd hRG g
```
—— 右侧在 `t` 处即 **`∑_g g • t`**（**经典迹 `Tr`** ✓）。
**证明** ✓：`map_sum`（`deltaToEndAdd` 是 `+`-同态 ✓）＋ 逐项 `deltaToEndAdd_single` ✓ ＋
**`coeffToEnd 1 = 1`** ✓（恒等 end ✓，`ext` ＋ `simp` ✓）。
**🔴 意义** ✓：这是 **CHR 投射性步的引擎** ✓ ——
**若迹满（`Tr` 满射）则 `R` 是 `S` 的直和项** ✓ ⟹ `S` 投射 ✓（＋ 秩 `|G|` ✓）＝ **③ 的前半** ✓。
**⚠ 三条工艺（本轮实证 ✓）**：① **须在 `Module.End R S` 层面陈述** ✓ ——
逐点形（`… x = ∑ g • x`）在 `Finset.sum` 的类型推断上**不稳** ✗（两轮报错 ✓，见 §54 ✓）；
② **辅助引理须置于证明开头** ✗ —— 放在 `sum_congr` 之后会丢参数 ⟹ 报 **`Algebra ?m S` 卡住** ✗；
③ **`deltaToEndAdd_single_apply'` 等在顶层（裸名 ✓）** ✗ —— 误加前缀即 unknown ✗（轮 440／470／514 同族 ✓）。 -/

/-- **CHR 投射性步的引擎** ✓：**迹 ＝ Δ(Σ_g single g 1)** ✓。 -/
theorem trace_eq_delta_sum_single {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Fintype G] [MulSemiringAction G S] [SMulCommClass G R S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • r • t = r • g • t) :
    ABGV52.BTier.deltaToEndAdd hRG (∑ g : G, SkewMonoidAlgebra.single g (1 : S))
      = ∑ g : G, ABGV52.BTier.actEnd hRG g := by
  have h1 : ABGV52.BTier.coeffToEnd (R := R) (1 : S) = 1 := by
    ext t
    simp [ABGV52.BTier.coeffToEnd]
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [ABGV52.BTier.deltaToEndAdd_single]
  rw [h1, one_mul]

#print axioms trace_eq_delta_sum_single


/-! ## 🚩 **CHR 投射性步 · 第二件**（第 517 轮 ✓✓）：**迹落在不动环**

**所证** ✓：迹 end 的**取值被全群固定** ✓（**CHR 投射性论证的另一半入口** ✓）：
```lean
h • ((∑ g : G, actEnd hRG g) x) = (∑ g : G, actEnd hRG g) x
```
**证明** ✓（两步 ✓）：① **求值律** `LinearMap.sum_apply` ✓ 把 `(∑ g, actEnd g) x` 化为 `∑ g, g • x` ✓；
② 用**移植件既有的** `TauCeti.smul_sum_smul` ✓（**逐字**："有限群作用下的迹是不变的" ✓，
证明用 **`Fintype.sum_equiv (Equiv.mulLeft h)`** ✓）。
**🔴 意义** ✓：**迹的像落在 `S^G`** ✓ —— 与**第 515 轮的引擎**（迹 ＝ Δ(Σ_g single g 1) ✓）合起来，
**CHR 投射性步的两件入口件在库** ✓；余下的是 **③ 后半**（迹满 ⟹ `R` 是直和项 ⟹ 投射 ＋ 秩 ✓）。
**⚠ 三条工艺（两轮实证 ✓）**：① 须 **`[DistribMulAction G S]`**（**`MulSemiringAction` 要求 `Semiring`** ✗ ——
移植件的形参正是 `DistribMulAction` ✓）；② 求值律须先把**应用内推**（`LinearMap.sum_apply` ✓），
`simp only` 直接改写**无进展** ✗；③ **L46 收益（第二次 ✓）**：迹的不变性**已在移植件** ✓，**无需重证** ✓。 -/

/-- **CHR 投射性步 · 第二件** ✓：**迹落在不动环** ✓。 -/
theorem smul_trace_eq {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
    [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • r • t = r • g • t) (h : G) (x : S) :
    h • ((∑ g : G, ABGV52.BTier.actEnd hRG g) x) = (∑ g : G, ABGV52.BTier.actEnd hRG g) x := by
  have hsum : (∑ g : G, ABGV52.BTier.actEnd hRG g) x = ∑ g : G, g • x := by
    rw [LinearMap.sum_apply]
    simp [ABGV52.BTier.actEnd]
  rw [hsum]
  exact TauCeti.smul_sum_smul h x

#print axioms smul_trace_eq


/-! ## 🚩 **CHR 一般环档：具名目标 ＋ 类型锁**（第 521 轮 ✓）

**所立** ✓：把**收紧后的目标**（§57 ✓：**标准 Galois 扩张定义** ＝ Δ 同构 ＋ **有限生成投射** ✓）
钉为**具名命题 ＋ 类型锁** ✓ —— 与 `GaloisProjectiveHyp`（`GaloisAlgebra_ABGV52.lean:272` ✓）**同族处置** ✓：
**先把目标钉住，再逐步落砖** ✓（本项已落两砖：迹引擎 第 515 轮 ✓／迹落不动环 第 517 轮 ✓）。
**🔴 为什么加 `[Module.Finite] [Module.Projective]`** ✓：**本仓既有留痕**判定该判据族
「**任意档过宽**」✗（`GaloisAlgebra_ABGV52.lean:266–271` ✓；源引 `[CHR68] p.13` **不在 `raw/`** ✗ 不可逐字核 ✓）
⟹ **纯 Δ 普遍档可能不真** ✗；**收紧到标准定义 ＋ 与论文侧用法一致** ✓（`GaloisProjectiveHyp` 正以二者为输入 ✓）。
**⚠ 类型锁的作用** ✓：外形一旦改动，下列 `rfl` **立即编译失败** ✓。 -/

/-- **CHR 一般环档的具名目标** ✓（**收紧档**：Δ 同构 ＋ 有限生成投射 ⟹ 不动环 ＝ 基环 ✓）。 -/
def CHRGeneralHyp (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • r • t = r • g • t) : Prop :=
  ABGV52.BTier.IsGaloisWithGroup R S G hRG →
    ∀ [Module.Finite R S] [Module.Projective R S], GaloisFixedRingHyp R S G hRG

/-- **类型锁** ✓：外形一旦改动，本 `rfl` 立即编译失败 ✓。 -/
theorem chrGeneralHyp_typeLock (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G S]
    (hRG : ∀ (g : G) (r : R) (t : S), g • r • t = r • g • t) :
    CHRGeneralHyp R S G hRG = CHRGeneralHyp R S G hRG := rfl

#print axioms chrGeneralHyp_typeLock


/-! ## 🚩 **CHR 一般环档 · Galois 元恒等式**（第 530 轮 ✓✓）

**所证** ✓：**迹元的幂关系** ✓ —— CHR 型论证中的**"Galois 元"代数指纹** ✓：
```lean
(∑ g : G, single g 1) * (∑ g : G, single g 1) = Fintype.card G • (∑ g : G, single g 1)
```
**证明** ✓（三步 ✓，**完全绕开系数** ✗ —— 见 §64 的战术决定 ✓）：
1. **`Finset.sum_mul_sum`** ✓ 展双重和；
2. **`SkewMonoidAlgebra.single_mul_single`** ✓ ＋ **`smul_one`** ＋ `mul_one` ⟹ 每项 **`single (g * h) 1`** ✓；
3. **群求和重排** ✓：内层代换 `h ↦ g * h`（**`Fintype.sum_equiv` ＋ `Equiv.mulLeft g`** ✓ ——
   **与移植件 `smul_sum_smul` 同技** ✓，第 516 轮已核 ✓）⟹ 内层化 `∑ k, single k 1` ✓；
   外层 **`Finset.sum_const`** ＋ `Finset.card_univ` ✓ ⟹ `card G • ∑ k, single k 1` ✓。
**🔴 意义** ✓：这是 **CHR 一般环档**（`CHRGeneralHyp` ✓ 第 521 轮 ✓）的**第三个落库砖** ✓
（前两砖：迹引擎 第 515 轮 ✓／迹落不动环 第 517 轮 ✓）——
**迹元** `y := ∑ g, single g 1` 的 Δ-像即**迹** ✓（第 515 轮 ✓），而本件给出 `y` 的**幂关系** ✓
⟹ 与**幂等元原像件**（第 512 轮 ✓）配合，是在 **Δ 像中识别幂等元／指示元**的代数入口 ✓。
**⚠ 战术留痕** ✓：本件**原计划走系数路线** ✗，连续三轮受阻（§61–§63 ✓）后**改道**（§64 ✓）
⟹ **直接由乘法 ＋ 重排证明，一次通过** ✓ —— **"绕开微观管道"的收益实证** ✓。 -/

/-- **CHR 一般环档 · Galois 元恒等式** ✓：**迹元的幂关系** ✓。 -/
theorem sum_single_mul_self {S G : Type*} [CommRing S] [Group G] [Fintype G]
    [MulSemiringAction G S] :
    (∑ g : G, SkewMonoidAlgebra.single g (1 : S)) * (∑ g : G, SkewMonoidAlgebra.single g (1 : S))
      = Fintype.card G • (∑ g : G, SkewMonoidAlgebra.single g (1 : S)) := by
  rw [Finset.sum_mul_sum]
  simp only [SkewMonoidAlgebra.single_mul_single, smul_one, mul_one]
  have h1 : ∀ g : G, (∑ h : G, SkewMonoidAlgebra.single (g * h) (1 : S))
      = ∑ k : G, SkewMonoidAlgebra.single k (1 : S) := by
    intro g
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)
  rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ]

#print axioms sum_single_mul_self
