/-
  ABGV-5.2 —— 论文 2026-10-11 版 §4：`thm:retract-criterion`（4.12）的**具名假设接口**

  论文原文（4.12）：设 `G` 有限、`M` 忠实 `ℤ[G]`-格、`char F = 0`，则 `F(M)^G` 在 `F` 上
  retract rational **当且仅当** flasque 类 `ρ(M)` 是可逆格的类。论文随后明说：文献中的
  判据是对**扭转**不变量域 `Q(L/K,M)` 陈述的（Saltman 1984 Thm 3.14(a)），而 `F(M)^G`
  这一支**按假设使用**（"for it the criterion is an assumption rather than a quotation of
  a proved result"）⟹ 本件按 `EM_ABGV52`／`Saltman_ABGV52` 的工艺给出**具名假设**：

    * `RetractCriterionHyp` —— 判据的**定义外形**（对给定的 flasque 消解
      `R : FlasqueResolution H M`，其右端项 `R.F` 的相似类即 `ρ(M)`；域 `K` 的角色是
      `F(M)^G`；抽象谓词 `RRat` 的角色是「在 `F` 上 retract rational」，由调用方以
      `IsRetractRational F` 填入）；
    * **类型锁定断言**（`rfl`）：外形一旦改动立即编译失败；
    * **接线定理**：正方向（`RRat K ⟹ R.F` 可逆）与**负方向**（4.13 实际使用的
      `¬ R.F` 可逆 `⟹ ¬ RRat K`）；
    * **非空洞探针**（L1）：假设类**非空**——取 `RRat := fun _ => IsInvertible H R.F`
      即得实例（同义反复型见证），并且负方向接线对任意 `R` 可点火；
    * 公理闸门 `#print axioms`。

  与「类」这一层的接口约定：论文写的是「`ρ(M)` **是**可逆格**的类**」；本件把接口钉在
  **给定代表元** `R.F` 上（避免引入 `D(G)/S(G)` 商类型）。代表元无关性由 `Flasque_ABGV52`
  的 `FlasqueClassWellDefinedHyp`（CTS77 §1 Lemme 5）承担，见该件 §3。

  **无 sorry、无自造公理**。
-/
import ABGV52.Flasque_ABGV52
import ABGV52.SaltDef_ABGV52

open CategoryTheory CategoryTheory.Limits

namespace ABGV52

/-! ## §0 **已登记：本件假设的「论文实例」被文献反证**（R785，勿反复试填）

⚠ `RetractCriterionHyp M R K RRat` 在**论文的实例**上
（`RRat := fun _ => IsRetractRational F K`、`K := F(M)^G`、`M` 忠实、`char F = 0`）
**不是定理**：其（⟹）方向（retract rational ⟹ `ρ(M)` 是可逆格的类）在文献中**为假**。

**反例（拼装，来源已逐字核）**：`G = C₂ × C₂`、`F = ℚ`、`M = M₂(G)`：
1. `M` 忠实 —— `raw/Saltman1987.tex:335`「An exercise shows that `M` is `G` faithful」；
2. `F(M,G)` 是 Amitsur–Snider 通用叉积之中心（同处逐字）且**在 ℚ 上有理**
   —— Snider 定理，经 `raw/OfirDavid2016.tex:233–237`；
3. `η(M₂(G)) = η(J_G) ≠ 0` —— `raw/Saltman1984.tex` Thm 2.6（取 `N = 1` 得 `f = id`）
   ＋ Thm 2.7(a)；
4. `η(M) = 0 ⟺ IsInvertible H R.F`（本件 §4 `etaVanishes_iff_isInvertible`，已机检）。

⟹ 有理 ⟹ retract rational（第 2 条）而 `ρ(M)` **不可逆**（第 3、4 条）。

**且 §0 的「3.14(a) 特化」判读不成立**：3.14 的（⟹）证明承重步
「Tensoring by `L` we have `G` preserving `F` algebra maps `φ′ : L[M] → L[N]`」
（`raw/Saltman1984.tex:617`）依赖 **Speiser／半线性下降**（`G` 半线性作用于 `L[M]`）；
`L = F` 时作用为 `F`-线性、半线性前提消失 ⟹ 该步不可用。全库检索：未扭变侧（⟹）
**无任何已发表证明**（`raw/Kang2009.tex:342`／`:283`、`raw/OfirDavid2016.tex:1122` 均单向）。

**可证的替代**（见 `wiki/proj-ABGV52-retract-criterion-refutation.md` §3）：
`eta(M) = 0` ⟹（`F(M,G)` retract rational ⟺ `F(G)` retract rational）（Saltman1987
Cor 1.4 ＋ Prop 1.7 ＋ Lem 1.1 ＋ Cor 1.6）；twisted 判据 3.14(a) 本体为真。
-/

/-- **文献反证的登记锚**（本库 `..._gap_registered` 惯例）：**不得**把本件 `hCrit` 当作可证命题；
填入 `IsRetractRational` 实例即得假陈述（§0 反例）。 -/
theorem retractCriterionHyp_paper_instance_refuted_registered : True := trivial

/-! ## §1 具名假设外形 ＋ 类型锁定 -/

/-- **`thm:retract-criterion`（4.12）的具名假设**：`M` 的 flasque 消解 `R`（`R.F` 的相似类
即 `ρ(M)`）与域 `K`（角色 = `F(M)^G`）之下，`RRat K`（角色 = `K` 在 `F` 上 retract
rational）成立 **当且仅当** `R.F` 可逆（是置换格的直和项）。 -/
def RetractCriterionHyp (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) (RRat : Type → Prop) : Prop :=
  RRat K ↔ IsInvertible H R.F

/-- **类型锁定断言**：`RetractCriterionHyp` 的外形一旦被改动，本 `rfl` 立即编译失败。 -/
example (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M) (K : Type) (RRat : Type → Prop) :
    RetractCriterionHyp M R K RRat ↔ (RRat K ↔ IsInvertible H R.F) :=
  Iff.rfl

/-! ## §2 接线（正方向与负方向） -/

/-- **接线（正方向）**：`RRat K` 与「`ρ(M)` 可逆」等价的正向——由判据假设得 `R.F` 可逆。 -/
theorem retractCriterion_mp {M : Rep.{0,0,0} ℤ H} {R : FlasqueResolution H M}
    {K : Type} {RRat : Type → Prop} (h : RetractCriterionHyp M R K RRat)
    (hRR : RRat K) : IsInvertible H R.F :=
  h.mp hRR

/-- **接线（负方向，`thm:not-retract-rational`（4.13）实际使用的方向）**：
若 `ρ(M)` 的代表元 `R.F` **不**可逆，则 `RRat K` 不成立。 -/
theorem retractCriterion_not {M : Rep.{0,0,0} ℤ H} {R : FlasqueResolution H M}
    {K : Type} {RRat : Type → Prop} (h : RetractCriterionHyp M R K RRat)
    (hInv : ¬ IsInvertible H R.F) : ¬ RRat K :=
  fun hRR => hInv (h.mp hRR)

/-! ## §3 非空洞探针（L1） -/

/-- **探针 1（假设类非空）**：把 `RRat` 取为「`R.F` 可逆」这一命题本身，判据的同义反复
实例成立——假设类不是空类，`RetractCriterionHyp` 的外形可被真实填入。 -/
theorem retractCriterionHyp_satisfiable (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) : RetractCriterionHyp M R K (fun _ => IsInvertible H R.F) :=
  Iff.rfl

/-- **探针 2（负方向接线可点火）**：在探针 1 的实例上，只要 `R.F` 不可逆，
`retractCriterion_not` 即给出否定结论——接线不是空转。 -/
theorem retractCriterion_not_probe (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M)
    (K : Type) (hInv : ¬ IsInvertible H R.F) :
    ¬ (fun _ => IsInvertible H R.F) K :=
  retractCriterion_not (retractCriterionHyp_satisfiable M R K) hInv

/-! ## §4 M1：`eta(M) = 0` 的等价形态（源 `raw/Saltman1984.tex` 印 189「To summarize」句）

**源逐字** ✓（`:224` 前后，印 189）：
「`eta (M) = [0]` if and only if there is an exact sequence `0 -> M -> P -> I -> 0`
where `P` is a permutation module and `I` is invertible.」

**本节的落点** ✓：论文 4.12 的右手边「`rho(M)` 是**可逆格**的**类**」写成**给定代表元**上的
`IsInvertible H R.F`（`Flasque_ABGV52:153`）；本节把它与「存在 flasque 消解其右端项可逆」
（`EtaVanishes`）证成**等价**，代表元无关性由 `FlasqueClassWellDefinedHyp`（`Flasque_ABGV52:225`）
承担。**这一步不依赖** Saltman §2 的 `eta'` 函子与 `thm2.3`。
-/

/-- **相似保持可逆** ✓：`M ~ N` 且 `M` 可逆 ⟹ `N` 可逆。

源（`Saltman1984` §2）：可逆 ＝ 置换模的直和项；相似 ＝ 两边各添一个置换模后同构。
链：`M + N' = P`（`P` 置换）、`M + A = N + B`（`A B` 置换）⟹
`N + (N' + B) = (N + B) + N' = (M + A) + N' = P + A`，右端是置换格的直和
（`isPermutationLattice_biprod`）✓。 -/
theorem isInvertible_of_isSimilar {G : Type} [Group G] {M N : Rep.{0,0,0} ℤ G}
    (h : IsSimilar G M N) (hM : IsInvertible G M) : IsInvertible G N := by
  obtain ⟨A, B, hA, hB, ⟨e⟩⟩ := h
  obtain ⟨N', P, hP, ⟨f⟩⟩ := hM
  refine ⟨N' ⊞ B, P ⊞ A, isPermutationLattice_biprod hP hA, ⟨?_⟩⟩
  exact (biprod.associator N N' B).symm ≪≫
    biprod.mapIso (biprod.braiding N N') (Iso.refl B) ≪≫
    biprod.associator N' N B ≪≫
    biprod.mapIso (Iso.refl N') e.symm ≪≫
    (biprod.associator N' M A).symm ≪≫
    biprod.mapIso (biprod.braiding N' M) (Iso.refl A) ≪≫
    biprod.mapIso f (Iso.refl A)

/-- **相似保持可逆（双向）** ✓：`IsSimilar` 是等价关系（`isSimilar_equivalence`）⟹ 可逆性是类函数。 -/
theorem isInvertible_iff_of_isSimilar {G : Type} [Group G] {M N : Rep.{0,0,0} ℤ G}
    (h : IsSimilar G M N) : IsInvertible G M ↔ IsInvertible G N :=
  ⟨isInvertible_of_isSimilar h, isInvertible_of_isSimilar (isSimilar_symm h)⟩

/-- **稳定置换 ⟹ 可逆** ✓（定义级桥）：`M + P = Q`（`P Q` 置换）取 `N := P`、补项 `Q`。

⚠ **注意单向** ✗：逆命题**不**成立（可逆的补项 `N` **任意**，不要求置换）。这一单向性正是
Saltman 1987 Thm 1.3 的 (b)（稳定有理：`Q` 置换）与 (c)（retract 有理：`Q` 仅可逆）**不同**
的代数来源——故 `EtaVanishes` **不得**读作「`M` 稳定置换」。 -/
theorem isInvertible_of_isStablyPermutation {G : Type} [Group G] {M : Rep.{0,0,0} ℤ G}
    (h : EM.IsStablyPermutation G M) : IsInvertible G M := by
  obtain ⟨P, Q, _hP, hQ, ⟨e⟩⟩ := h
  exact ⟨P, Q, hQ, ⟨e⟩⟩

/-- **`eta(M) = 0`**（源 `raw/Saltman1984.tex` 印 189「To summarize」句的本工程编码）：
存在一条 flasque 消解 `0 -> M -> P -> I -> 0`（`P` 置换、`I` flasque，`FlasqueResolution`）
使右端项 `I` **可逆**。

⚠ **与源的字面差**（登记，不掩盖）：源只要求 `I` 可逆、**不**要求 `I` flasque；本定义取
flasque 消解形（`FlasqueResolution` 自带 `flasque` 字段）。两形的等价需「可逆 ⟹ flasque」
（Swan, Lemma 8.4；亦见 `Kang2009` §2「an invertible lattice is necessarily a flabby lattice」），
本工程**未建**（见 §5 缺口表）。**4.12 的右手边是对给定 flasque 消解的 `IsInvertible`**，
故本形对主线**已够用** ✓。 -/
def EtaVanishes (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) : Prop :=
  ∃ R : FlasqueResolution G M, IsInvertible G R.F

/-- **外形锁定** ✓：`EtaVanishes` 一旦改形，本 `Iff.rfl` 立即编译失败。 -/
example (G : Type) [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G) :
    EtaVanishes G M ↔ ∃ R : FlasqueResolution G M, IsInvertible G R.F :=
  Iff.rfl

/-- **M1 主定理** ✓：`eta(M) = 0` ⟺ 给定 flasque 消解 `R` 的右端项 `R.F` 可逆。

`⟸` 取同一条消解（`⟨R, h⟩`）。`⟹` 用 `FlasqueClassWellDefinedHyp`（CTS77 §1 Lemme 5：
`rho(M)` 的代表元无关）把两条消解的右端项连成**相似**（`M ~ M` 由 `isSimilar_refl`），
再沿相似搬运可逆性（`isInvertible_of_isSimilar`）。 -/
theorem etaVanishes_iff_isInvertible {G : Type} [Group G] [Fintype G]
    (hWD : FlasqueClassWellDefinedHyp G) (M : Rep.{0,0,0} ℤ G)
    (R : FlasqueResolution G M) : EtaVanishes G M ↔ IsInvertible G R.F := by
  refine ⟨?_, fun h => ⟨R, h⟩⟩
  rintro ⟨R', hR'⟩
  have hsim : IsSimilar G R.F R'.F := hWD M M R R' (isSimilar_refl G M)
  exact isInvertible_of_isSimilar (isSimilar_symm hsim) hR'

/-- **L1 探针（结论类非空）** ✓：`EtaVanishes` 成立时其结论（存在可逆右端项）被某条消解见证。 -/
theorem etaVanishes_witness {G : Type} [Group G] [Fintype G] (M : Rep.{0,0,0} ℤ G)
    (h : EtaVanishes G M) : ∃ R : FlasqueResolution G M, IsInvertible G R.F := h

/-- **M1 在论文的群 `H` 上的实例**（`H = C_3 × C_3`，`Hyp_ABGV52:28`）。 -/
theorem etaVanishes_iff_isInvertible_H (hWD : FlasqueClassWellDefinedHyp H)
    (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M) :
    EtaVanishes H M ↔ IsInvertible H R.F :=
  etaVanishes_iff_isInvertible hWD M R

/-- **判据的 `EtaVanishes` 外形** ✓（右手边换成 `EtaVanishes`，与 `RetractCriterionHyp` 同构）。 -/
def RetractCriterionEtaHyp (M : Rep.{0,0,0} ℤ H) (K : Type)
    (RRat : Type → Prop) : Prop :=
  RRat K ↔ EtaVanishes H M

/-- **外形锁定**（`RetractCriterionEtaHyp`）。 -/
example (M : Rep.{0,0,0} ℤ H) (K : Type) (RRat : Type → Prop) :
    RetractCriterionEtaHyp M K RRat ↔ (RRat K ↔ EtaVanishes H M) :=
  Iff.rfl

/-- **两种判据外形互换** ✓：由 M1 主定理（代表元无关）把 `RetractCriterionHyp` 换成
`RetractCriterionEtaHyp`。 -/
theorem retractCriterionHyp_iff_eta (hWD : FlasqueClassWellDefinedHyp H)
    (M : Rep.{0,0,0} ℤ H) (R : FlasqueResolution H M) (K : Type)
    (RRat : Type → Prop) :
    RetractCriterionHyp M R K RRat ↔ RetractCriterionEtaHyp M K RRat := by
  have h := etaVanishes_iff_isInvertible hWD M R
  unfold RetractCriterionHyp RetractCriterionEtaHyp
  rw [h]

/-- **负方向接线**（4.13 实际使用的方向，`EtaVanishes` 版）：`eta(M) != 0` ⟹ `RRat K` 不成立。 -/
theorem retractCriterionEta_not {M : Rep.{0,0,0} ℤ H} {K : Type} {RRat : Type → Prop}
    (h : RetractCriterionEtaHyp M K RRat) (hE : ¬ EtaVanishes H M) : ¬ RRat K :=
  fun hRR => hE (h.mp hRR)

/-! ## §4.1 `IsInvertible` 的封闭性（`⊞`／直和项／同构）—— 为 `eta` 的可加性铺路

源（`raw/Saltman1984.tex` §2「An invertible module is a direct summand of a permutation
module」）⟹ 可逆性对 `⊞` 封闭、对直和项封闭、沿同构不变。三者是 `eta` 可加性与
「相似类不变」的**代数目录**（Saltman1987 Prop 1.7／`proj-ABGV52-retract-criterion-refutation` §3）。
-/

/-- **可逆被 `⊞` 保持**：`M ⊕ M' = P`、`N ⊕ N' = Q` ⟹ `(M⊕N) ⊕ (M'⊕N') = P ⊕ Q`（置换）。 -/
theorem isInvertible_biprod {G : Type} [Group G] {M N : Rep.{0,0,0} ℤ G}
    (hM : IsInvertible G M) (hN : IsInvertible G N) : IsInvertible G (M ⊞ N) := by
  obtain ⟨M', P, hP, ⟨e₁⟩⟩ := hM
  obtain ⟨N', Q, hQ, ⟨e₂⟩⟩ := hN
  refine ⟨M' ⊞ N', P ⊞ Q, isPermutationLattice_biprod hP hQ, ⟨?_⟩⟩
  exact (biprod.associator M N (M' ⊞ N')) ≪≫
    biprod.mapIso (Iso.refl M)
      ((biprod.associator N M' N').symm ≪≫
       biprod.mapIso (biprod.braiding N M') (Iso.refl N') ≪≫
       biprod.associator M' N N') ≪≫
    (biprod.associator M M' (N ⊞ N')).symm ≪≫
    biprod.mapIso e₁ e₂

/-- **可逆的直和项可逆**：`M ⊕ N` 可逆 ⟹ `M` 可逆（补项取 `N ⊕ N'`）。 -/
theorem isInvertible_of_isInvertible_biprod {G : Type} [Group G] {M N : Rep.{0,0,0} ℤ G}
    (h : IsInvertible G (M ⊞ N)) : IsInvertible G M := by
  obtain ⟨N', P, hP, ⟨e⟩⟩ := h
  exact ⟨N ⊞ N', P, hP, ⟨(biprod.associator M N N').symm ≪≫ e⟩⟩

/-- **可逆性沿同构搬运**。 -/
theorem isInvertible_of_iso {G : Type} [Group G] {M N : Rep.{0,0,0} ℤ G}
    (e : M ≅ N) (h : IsInvertible G M) : IsInvertible G N := by
  obtain ⟨M', P, hP, ⟨f⟩⟩ := h
  exact ⟨M', P, hP, ⟨biprod.mapIso e.symm (Iso.refl M') ≪≫ f⟩⟩

/-- **右直和项可逆**（左引理的交换形）。 -/
theorem isInvertible_of_isInvertible_biprod_right {G : Type} [Group G]
    {M N : Rep.{0,0,0} ℤ G} (h : IsInvertible G (M ⊞ N)) : IsInvertible G N :=
  isInvertible_of_isInvertible_biprod (M := N) (N := M)
    (isInvertible_of_iso (biprod.braiding M N) h)

section ZeroWitness

-- `0 : Rep ℤ G` 的 `Zero` 实例是 `scoped[ZeroObject]`（`Flasque_ABGV52` §4.6 的工艺读数 39）
open scoped ZeroObject

/-- **L19 判别力（非退化，正例）**：`IsInvertible` 在 `⊞` 下确实非空——
由 `isInvertible_zero` 与 `isInvertible_biprod` 得 `0 ⊞ 0` 可逆（不是空类上的断言）。 -/
theorem isInvertible_zero_biprod (G : Type) [Group G] :
    IsInvertible G ((0 : Rep.{0,0,0} ℤ G) ⊞ 0) :=
  isInvertible_biprod (isInvertible_zero G) (isInvertible_zero G)

end ZeroWitness

/-! ## §4.2 相似关系对 `⊞` 同余（`η`／`ρ` 演算的代数基础）

`IsSimilar` 是等价关系（`isSimilar_equivalence`）对 `⊞` 同余 —— 这是「相似类的加法」
（Saltman1984 §2 的 `[E₁] + [E₂] := [E₁ ⊕ E₂]`、CTS77 `lem:1.7` 的 ρ 算术）的载体层。
-/

/-- **四元重排**：`(M ⊞ N) ⊞ (A ⊞ C) ≅ (M ⊞ A) ⊞ (N ⊞ C)`（把 `N` 与 `A` 换位）。 -/
noncomputable def biprod_shuffle (M N A C : Rep.{0,0,0} ℤ H) :
    (M ⊞ N) ⊞ (A ⊞ C) ≅ (M ⊞ A) ⊞ (N ⊞ C) :=
  (biprod.associator M N (A ⊞ C)) ≪≫
  biprod.mapIso (Iso.refl M)
    ((biprod.associator N A C).symm ≪≫
     biprod.mapIso (biprod.braiding N A) (Iso.refl C) ≪≫
     biprod.associator A N C) ≪≫
  (biprod.associator M A (N ⊞ C)).symm

/-- **相似关系对 `⊞` 同余**：`M ~ M′`、`N ~ N′` ⟹ `M ⊞ N ~ M′ ⊞ N′`。

证明：`M ⊕ A ≅ M′ ⊕ B`、`N ⊕ C ≅ N′ ⊕ D`（`A B C D` 置换）⟹ 取补项 `A ⊞ C`、`B ⊞ D`
（`isPermutationLattice_biprod`），并用 `biprod_shuffle` 把两侧对齐到 `(M⊞A) ⊞ (N⊞C)` 与
`(M′⊞B) ⊞ (N′⊞D)`。 -/
theorem isSimilar_biprod {M M' N N' : Rep.{0,0,0} ℤ H}
    (h : IsSimilar H M M') (k : IsSimilar H N N') :
    IsSimilar H (M ⊞ N) (M' ⊞ N') := by
  obtain ⟨A, B, hA, hB, ⟨e⟩⟩ := h
  obtain ⟨C, D, hC, hD, ⟨f⟩⟩ := k
  refine ⟨A ⊞ C, B ⊞ D, isPermutationLattice_biprod hA hC,
    isPermutationLattice_biprod hB hD, ⟨?_⟩⟩
  exact biprod_shuffle M N A C ≪≫
    biprod.mapIso e f ≪≫
    (biprod_shuffle M' N' B D).symm

/-- **相似类的「加法」良定义**（推论）：相似类之间的 `+` 由 `⊞` 诱导且不依赖代表元。 -/
theorem isSimilar_add_congr {M M' N N' : Rep.{0,0,0} ℤ H}
    (h : IsSimilar H M M') (k : IsSimilar H N N') : IsSimilar H (M ⊞ N) (M' ⊞ N') :=
  isSimilar_biprod h k

/-! ## §5 缺口登记（M1 段的诚实边界）

| 缺口 | 内容 | 状态 |
|---|---|---|
| `invertible_imp_flasque` | 「可逆 ⟹ flasque」（Swan Lemma 8.4）⟹ `EtaVanishes` 与源的字面形（不要求 `I` flasque）等价 | ❌ 未建：需 `Ĥ^{-1}` 侧 Shapiro（`SubgroupPerm_ABGV52` 现只有 `coh^1` 侧），与 `Flasque_ABGV52` §1 登记的 flasque 侧缺口同源 |
| `EtaVanishes` 的具体见证 | 需要一个 `IsFlasque` 的**具体**实例（如置换格）才能给出非空洞见证 | ❌ 同上（依赖 `Ĥ^{-1}` 侧 Shapiro）；**不影响**主线（主线是给定 `R` 的等价） |
| `FlasqueResolutionHyp` | flasque 消解**存在性**（CTS77 §1 Lemme 3） | 具名假设（`Flasque_ABGV52:203`） |

⟹ `EtaVanishes` 与本节的等价**不声称**「存在度」；存在性由 `FlasqueResolutionHyp` 承担。
-/

/-! ## §6 公理闸门 -/

#print axioms retractCriterion_mp
#print axioms retractCriterion_not
#print axioms retractCriterionHyp_satisfiable
#print axioms retractCriterion_not_probe
#print axioms isInvertible_of_isSimilar
#print axioms isInvertible_iff_of_isSimilar
#print axioms isInvertible_of_isStablyPermutation
#print axioms etaVanishes_iff_isInvertible
#print axioms etaVanishes_witness
#print axioms etaVanishes_iff_isInvertible_H
#print axioms retractCriterionHyp_iff_eta
#print axioms retractCriterionEta_not
#print axioms isInvertible_biprod
#print axioms isInvertible_of_isInvertible_biprod
#print axioms isInvertible_of_iso
#print axioms isInvertible_of_isInvertible_biprod_right
#print axioms isInvertible_zero_biprod
#print axioms biprod_shuffle
#print axioms isSimilar_biprod
#print axioms isSimilar_add_congr
#print axioms retractCriterionHyp_paper_instance_refuted_registered

end ABGV52
