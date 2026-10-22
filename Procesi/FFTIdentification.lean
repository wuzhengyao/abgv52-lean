/-
  Procesi —— **FFT 第 5 步 识别 ①**：`(End V)^{⊗m} ≃ₗ End(V^{⊗m})`（第 501 轮）

  ## 这是什么

  **识别 ①**（[[proj-abgv52-fft-step5-identifications-2026-10-20]] §2）：
  ```
  (End V)^{⊗m}  ≃ₗ  End (V^{⊗m})
  ```
  它是 AGPR2020 `lem:12.1.2`（`:13862`，多线性不变量由 `T_σ` 张成）证明的**第一步**：
  该证明把 `End(V)^{⊗m}` 的**对偶**与 `End(V)^{⊗m}` 本身等同（迹配对），再把不变元
  与 `End(V^{⊗m})` 的 `GL`-等变自同态等同——后者由 Schur–Weyl 双中心化子（已入仓的
  `TauCetiSymmetricTensorActionGeneralLinear`）给出。

  ## 载体（内容式侦察的读数，L46）

  **v24 §3.1 把本项记为"自建（3 步搬运）"，实测只有 1 行**：
  `PiTensorProduct.piTensorHomEquiv`（`Procesi/External/TauCetiPiTensorProductHom.lean`，
  TauCeti 逐字搬运件）就是本识别，且其文件头逐字说明这正是 Schur–Weyl 双中心化子计算
  所需要的那座桥（"the endomorphisms of a tensor power commuting with the permutations of
  the factors are the invariants of the permutation action on the tensor power of the
  endomorphism algebra"）。取**常值族** `M i = N i = V` 即得。

  ⟹ 原计划的 `End V ≃ₗ V^* ⊗ V`（`Mathlib.LinearAlgebra.Contraction` 的
  `dualTensorHomEquivOfBasis`，须基参数）**整段不必做**：本条不需要对偶、不需要基。

  ## 件

  | 件 | 内容 |
  |---|---|
  | ★★★★★ `tensorPowerEndEquiv` | **识别 ① 本体**：`(End V)^{⊗m} ≃ₗ End(V^{⊗m})` |
  | `tensorPowerEndEquiv_tprod` | 纯张量上的计算律：`⊗^m f_i ↦ ⨂^m f_i`（`PiTensorProduct.map`） |
  | `tensorPowerEndEquiv_symm_map` | 逆的计算律 |
  | `tensorPowerEndEquiv_tprod_comp` | **乘性**：`⊗^m (f_i ∘ g_i) ↦ (⊗^m f_i) ∘ (⊗^m g_i)` |
  | ★★★★ `tensorPowerEndEquiv_conj` | **共轭穿桥**：`⊗^m (B f_i B') ↦ (⊗^m B) ∘ (⊗^m f_i) ∘ (⊗^m B')` |
  | ★★★★★ `trace_map_tensorPower` | **② 的引擎**：`m` 因子迹公式 `tr(⊗^m f_i) = ∏ tr f_i` |
  | ★★★★★ `trace_tensorPowerEnd_comp` | **AGPR 迹配对**：`tr((⊗^m a_i) ∘ (⊗^m b_i)) = ∏ tr(a_i b_i)` |

  `_conj` 是**不变性运输**（识别 ②）要用的那一格：`GL` 在 `(End V)^{⊗m}` 上的作用逐因子共轭，
  故"`x` 是 `GL`-不变元"经 ① 变成"`End(V^{⊗m})` 中的自同态与 `⊗^m B` 交换"，
  而那正是 Schur–Weyl 双中心化子的用武之地。

  `trace_map_tensorPower`／`trace_tensorPowerEnd_comp` 是 AGPR2020 `lem:12.1.2` 证明里那条配对的
  机器件（源文逐字：`⟨A₁⊗⋯⊗A_m | B₁⊗⋯⊗B_m⟩ = tr(A₁⋯A_m ∘ B₁⋯B_m) = ∏ tr(AᵢBᵢ)`），
  多线性不变量与 `GL`-不变元的等同（识别 ②）就靠它。

  ## 射程（勿夸大）

  本件只做识别 ①（含其计算律）与 ② 的**迹配对半边**。识别 ② 的其余部分
  （迹配对的**非退化性** ⟹ 对偶 ≅ 自身；`MultilinearMap` 侧的转写）与识别 ③
  （置换算子 ↔ `T_σ`，即 `eq:12.3` 的轮换展开）**未做**；AGPR2020 `lem:12.1.2` 本身、
  FFT 难半（`S^{PGL} ⊆ C`）、`SFixedLeZ`／`Z` 半／H2 **仍不是定理**。
-/

import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Procesi.External.TauCetiPiTensorProductHom
import Procesi.External.TauCetiSymmetricTensorActionGeneralLinear

open scoped TensorProduct

namespace Procesi

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
  [Module.Free k V] [Module.Finite k V] (m : ℕ)

/-- ★★★★★ **识别 ①**（`(End V)^{⊗m} ≃ₗ End(V^{⊗m})`）。

载体 = `PiTensorProduct.piTensorHomEquiv`（常值族 `M i = N i = V`）：把 `⨂ᵢ (Mᵢ →ₗ Nᵢ)`
与 `(⨂ᵢ Mᵢ) →ₗ (⨂ᵢ Nᵢ)` 等同。有限自由性是该件唯一的假设（本处由
`[Module.Free k V] [Module.Finite k V]` 提供）。

**用途**：AGPR2020 `lem:12.1.2`（`:13862`）的证明把 `End(V)^{⊗m}` 的 `GL`-不变元
识别为 `End(V^{⊗m})` 的 `GL`-等变自同态，再用 Schur–Weyl 双中心化子。本条给那座桥。 -/
noncomputable def tensorPowerEndEquiv :
    TensorPower k m (Module.End k V) ≃ₗ[k] Module.End k (TensorPower k m V) :=
  PiTensorProduct.piTensorHomEquiv k (fun _ : Fin m => V) (fun _ : Fin m => V)

#print axioms tensorPowerEndEquiv

/-- **纯张量上的计算律**：`⊗^m f_i` 经识别 ① 落成 `PiTensorProduct.map f`
（即 `⨂ᵢ aᵢ ↦ ⨂ᵢ fᵢ aᵢ`）。 -/
theorem tensorPowerEndEquiv_tprod (f : Fin m → Module.End k V) :
    tensorPowerEndEquiv k V m (PiTensorProduct.tprod k f)
      = PiTensorProduct.map f :=
  PiTensorProduct.piTensorHomEquiv_tprod f

#print axioms tensorPowerEndEquiv_tprod

/-- **逆的计算律**：`PiTensorProduct.map f` 经 ①⁻¹ 回到纯张量 `⊗^m f_i`。 -/
theorem tensorPowerEndEquiv_symm_map (f : Fin m → Module.End k V) :
    (tensorPowerEndEquiv k V m).symm (PiTensorProduct.map f)
      = PiTensorProduct.tprod k f :=
  PiTensorProduct.piTensorHomEquiv_symm_map f

#print axioms tensorPowerEndEquiv_symm_map

/-- ★★★★ **乘性**（因子逐项复合 ＝ 像的复合）：`⊗^m (f_i ∘ g_i) ↦ (⊗^m f_i) ∘ (⊗^m g_i)`。

**为何需要**：识别 ① 之后 `(End V)^{⊗m}` 上的代数结构（"逐因子相乘"）必须与
`End(V^{⊗m})` 的**复合**相容，否则"`GL`-不变**子代数**"无法运输。 -/
theorem tensorPowerEndEquiv_tprod_comp (f g : Fin m → Module.End k V) :
    tensorPowerEndEquiv k V m (PiTensorProduct.tprod k (fun i => f i ∘ₗ g i))
      = (tensorPowerEndEquiv k V m (PiTensorProduct.tprod k f))
        ∘ₗ (tensorPowerEndEquiv k V m (PiTensorProduct.tprod k g)) :=
  PiTensorProduct.piTensorHomEquiv_tprod_comp_tprod f g

#print axioms tensorPowerEndEquiv_tprod_comp

/-- ★★★★ **共轭穿桥**：`⊗^m (B ∘ f_i ∘ B') ↦ (⊗^m B) ∘ (⊗^m f_i) ∘ (⊗^m B')`。

**为何需要**：`GL(V)` 在 `(End V)^{⊗m}` 上的作用是**逐因子共轭** `f ↦ B ∘ f ∘ B'`。
本律把它翻译成 `End(V^{⊗m})` 侧与 `PiTensorProduct.map (fun _ => B)` 的**两侧复合**——
识别 ②（不变性运输）就靠这一格接上 Schur–Weyl 双中心化子。

**证明**：`PiTensorProduct.map_comp` 两次（逐点复合的 `map` ＝ `map` 的复合）。 -/
theorem tensorPowerEndEquiv_conj (B B' : Module.End k V) (f : Fin m → Module.End k V) :
    tensorPowerEndEquiv k V m (PiTensorProduct.tprod k (fun i => B ∘ₗ f i ∘ₗ B'))
      = (PiTensorProduct.map (fun _ : Fin m => B))
        ∘ₗ (tensorPowerEndEquiv k V m (PiTensorProduct.tprod k f))
        ∘ₗ (PiTensorProduct.map (fun _ : Fin m => B')) := by
  rw [tensorPowerEndEquiv_tprod, tensorPowerEndEquiv_tprod]
  have h1 : PiTensorProduct.map (fun i : Fin m => B ∘ₗ f i ∘ₗ B')
      = PiTensorProduct.map (fun _ : Fin m => B) ∘ₗ PiTensorProduct.map f
        ∘ₗ PiTensorProduct.map (fun _ : Fin m => B') := by
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  rw [h1]

#print axioms tensorPowerEndEquiv_conj

/-! ## §2 **识别 ② 的迹配对半边**：`m` 因子迹公式（第 502 轮）

AGPR2020 `lem:12.1.2`（`:13862`）的证明第一步逐字：

> the dual of `End(V)^{⊗m}` can be identified, in a `GL(V)` equivariant way, to `End(V)^{⊗m}`
> by the pairing formula `⟨A₁⊗⋯⊗A_m | B₁⊗⋯⊗B_m⟩ := tr(A₁⋯A_m ∘ B₁⋯B_m) = ∏ tr(AᵢBᵢ)`.

本节把**其中可计算的等式**做成机器件：`tr(⊗^m fᵢ) = ∏ tr fᵢ`（`m` 因子版；mathlib 只有
两因子版 `LinearMap.trace_tensorProduct'`），以及配对公式的纯张量形态
`tr((⊗^m aᵢ) ∘ (⊗^m bᵢ)) = ∏ tr(aᵢbᵢ)`。

**证明**（基计算）：取 `V` 的基 `b`，张量幂的基 `B = Basis.piTensorProduct (fun _ => b)`；
`tr = ∑ p, B.repr (M (B p)) p`，逐项用
`Basis.piTensorProduct_apply`＋`PiTensorProduct.map_tprod`＋`Basis.piTensorProduct_repr_tprod_apply`
化到 `∏ i, b.repr (f i (b (p i))) (p i)`，再用 `Finset.prod_univ_sum` 把 `∑_p ∏_i` 因子化成
`∏ i ∑_j`（`Fintype.piFinset_univ` 收尾），最后每因子回读为 `LinearMap.trace`。 -/

/-- ★★★★★ **`m` 因子迹公式**：`tr(⊗^m fᵢ) = ∏ tr fᵢ`（`PiTensorProduct.map` 形态）。

**为何需要**：AGPR2020 `lem:12.1.2` 的配对公式 `⟨A|B⟩ = ∏ tr(AᵢBᵢ)` 的右端就是它；
识别 ②（多线性不变量 ↔ `(End V)^{⊗m}` 的 `GL`-不变元）绕不过这一步。 -/
theorem trace_map_tensorPower (f : Fin m → Module.End k V) :
    LinearMap.trace k (TensorPower k m V) (PiTensorProduct.map f)
      = ∏ i : Fin m, LinearMap.trace k V (f i) := by
  classical
  set b := Module.Free.chooseBasis k V with hb
  set B : Module.Basis (Fin m → Module.Free.ChooseBasisIndex k V) k (TensorPower k m V) :=
    Basis.piTensorProduct (fun _ : Fin m => b) with hB
  rw [LinearMap.trace_eq_matrix_trace (R := k) (M := TensorPower k m V) B]
  rw [show (LinearMap.toMatrix B B (PiTensorProduct.map f)).trace
      = ∑ p, B.repr ((PiTensorProduct.map f) (B p)) p from by
    simp [Matrix.trace, LinearMap.toMatrix_apply]]
  have hterm : ∀ p : Fin m → Module.Free.ChooseBasisIndex k V,
      B.repr ((PiTensorProduct.map f) (B p)) p
        = ∏ i : Fin m, b.repr (f i (b (p i))) (p i) := by
    intro p
    rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
      Basis.piTensorProduct_repr_tprod_apply]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  have hsplit : (∑ p : Fin m → Module.Free.ChooseBasisIndex k V,
        ∏ i : Fin m, b.repr (f i (b (p i))) (p i))
      = ∏ i : Fin m, ∑ j : Module.Free.ChooseBasisIndex k V, b.repr (f i (b j)) j := by
    have h := Finset.prod_univ_sum
      (fun _ : Fin m => (Finset.univ : Finset (Module.Free.ChooseBasisIndex k V)))
      (fun i j => b.repr (f i (b j)) j)
    rw [Fintype.piFinset_univ] at h
    exact h.symm
  rw [hsplit]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [LinearMap.trace_eq_matrix_trace (R := k) (M := V) b (f i)]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

#print axioms trace_map_tensorPower

/-- ★★★★★ **AGPR 迹配对公式（纯张量形态）**：
`tr((⊗^m aᵢ) ∘ (⊗^m bᵢ)) = ∏ tr(aᵢ bᵢ)`。

经识别 ① 把两侧都送进 `End(V^{⊗m})`：左边 ＝ `tr(map (fun i => aᵢ ∘ bᵢ))`，再用
`trace_map_tensorPower`。**这正是** AGPR2020 `:13870` 那条配对的纯张量情形。 -/
theorem trace_tensorPowerEnd_comp (a b : Fin m → Module.End k V) :
    LinearMap.trace k (TensorPower k m V)
        ((tensorPowerEndEquiv k V m (PiTensorProduct.tprod k a))
          ∘ₗ (tensorPowerEndEquiv k V m (PiTensorProduct.tprod k b)))
      = ∏ i : Fin m, LinearMap.trace k V (a i ∘ₗ b i) := by
  rw [← tensorPowerEndEquiv_tprod_comp, tensorPowerEndEquiv_tprod]
  exact trace_map_tensorPower k V m (fun i => a i ∘ₗ b i)

#print axioms trace_tensorPowerEnd_comp

/-! ## §3 **识别 ② 的非退化半边**：迹配对非退化（第 503 轮）

AGPR2020 `lem:12.1.2`（`:13862`）的第一步要的是**同构**（对偶 ≅ 自身），不只是等式：
`End(V^{⊗m}) × End(V^{⊗m}) → k`，`(A,B) ↦ tr(A ∘ B)` 必须**非退化**。本节把非退化做成机器件
（`零检验形态`：`∀ B, tr(A ∘ B) = 0 ⟹ A = 0`；配上有限维即得同构）。

**证明**（基与秩一映射）：取基 `b`。秩一映射 `φ.smulRight v : w ↦ φ w • v` 的迹是 `φ v`
（`trace_smulRight`：`∑ i, φ(b i)·(b.repr v) i = φ(∑ i, (b.repr v) i • b i) = φ v`）；
且 `A ∘ (φ.smulRight v) = φ.smulRight (A v)`（`comp_smulRight`）。于是
`tr(A ∘ ((b.coord i).smulRight (b j))) = b.coord i (A (b j))`——**每个矩阵元**都是该配对的读数；
所有读数皆零 ⟹ `A = 0`（`Basis.ext_elem`）。 -/

section TraceNondegenerate

/-- `A ∘ₗ (φ.smulRight v) = φ.smulRight (A v)`（秩一映射与复合的交换律）。 -/
theorem comp_smulRight (A : Module.End k V) (φ : Module.Dual k V) (v : V) :
    A ∘ₗ (φ.smulRight v) = φ.smulRight (A v) := by
  ext w
  simp [LinearMap.smulRight_apply]

#print axioms comp_smulRight

/-- ★★★★ **秩一映射的迹**：`tr(w ↦ φ w • v) = φ v`。 -/
theorem trace_smulRight {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
    (φ : Module.Dual k V) (v : V) : LinearMap.trace k V (φ.smulRight v) = φ v := by
  rw [LinearMap.trace_eq_matrix_trace (R := k) (M := V) b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    LinearMap.smulRight_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have h2 : φ v = ∑ i, φ (b i) * (b.repr v) i := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum φ (fun i => (b.repr v) i • b i) Finset.univ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [h2]

#print axioms trace_smulRight

/-- ★★★★★ **迹配对非退化（零检验形态）**：若 `∀ B, tr(A ∘ B) = 0` 则 `A = 0`。

**用途**：这就是 AGPR `lem:12.1.2` 第一步所需的「不可见 ⟹ 为零」判据；配 `finrank`
相等即得 `End(W) ≅ End(W)^*` 的 `GL`-等变同构（对偶 ≅ 自身）。 -/
theorem trace_pairing_eq_zero_imp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (A : Module.End k V)
    (h : ∀ B : Module.End k V, LinearMap.trace k V (A ∘ₗ B) = 0) : A = 0 := by
  refine b.ext (fun j => ?_)
  refine b.ext_elem (fun i => ?_)
  have h1 := h ((b.coord i).smulRight (b j))
  rw [comp_smulRight, trace_smulRight k V b] at h1
  simpa [Module.Basis.coord_apply] using h1

#print axioms trace_pairing_eq_zero_imp

/-- ★★★★★ **迹配对非退化（无基形态）**：`∀ B, tr(A ∘ B) = 0 ⟹ A = 0`，无需显式给基。 -/
theorem trace_pairing_eq_zero (A : Module.End k V)
    (h : ∀ B : Module.End k V, LinearMap.trace k V (A ∘ₗ B) = 0) : A = 0 := by
  classical
  exact trace_pairing_eq_zero_imp k V (Module.Free.chooseBasis k V) A h

#print axioms trace_pairing_eq_zero

end TraceNondegenerate

/-! ## §4 **识别 ② 完成：迹配对的对偶等价与多线性识别**（第 504 轮）

AGPR2020 `lem:12.1.2` 第一步要的是**同构**（对偶 ≅ 自身），不只是「不可见 ⟹ 为零」。
本节把 `§2` 的等式与 `§3` 的非退化拼成同构：

```
End W ≃ₗ Dual k (End W)                     （endTraceDualEquiv，A ↦ (B ↦ tr(A ∘ B))）
⨂^m (End V) ≃ₗ Dual k (⨂^m (End V))          （tensorPowerTraceDualEquiv，经识别 ① 运输）
MultilinearMap k (Fin m → End V) k ≃ₗ ⨂^m (End V)   （multilinearMapTensorPowerEquiv）
```

最后一件就是**识别 ② 的同构形态**：「`m` 个 `End V` 的多线性函数」与「`(End V)^{⊗m}`」等同；
其纯张量计算律 `tensorPowerTraceDualEquiv_tprod` 就是 AGPR 的
`⟨A₁⊗⋯⊗A_m | B₁⊗⋯⊗B_m⟩ = ∏ tr(Aᵢ ∘ Bᵢ)`（源文 `:13870` 逐字）。

**⚠ 载体读数（L44／L46）**：`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` 在**当前 pin 上可建**
（第 504 轮实测 `lake build` 成功，1677 jobs）——v24 §4⑤ 记的「`FiniteDimensional` 是 bad import」
**只对伞件 `Mathlib.LinearAlgebra.FiniteDimensional` 成立**，`…Lemmas` 可直接引。
`BilinForm.toDual` 就在该件里，这正是本节的钥匙。 -/

section TraceDuality

/-- **迹配对形式**：`⟨A, B⟩ = tr(A ∘ B)`。 -/
noncomputable def endTraceForm : LinearMap.BilinForm k (Module.End k V) :=
  LinearMap.mk₂ k (fun A B => LinearMap.trace k V (A ∘ₗ B))
    (fun A₁ A₂ B => by simp [LinearMap.add_comp, map_add])
    (fun c A B => by simp [LinearMap.smul_comp, map_smul])
    (fun A B₁ B₂ => by simp [LinearMap.comp_add, map_add])
    (fun c A B => by simp [LinearMap.comp_smul, map_smul])

#print axioms endTraceForm

theorem endTraceForm_apply (A B : Module.End k V) :
    endTraceForm k V A B = LinearMap.trace k V (A ∘ₗ B) := rfl

#print axioms endTraceForm_apply

/-- ★★★★ **迹配对形式非退化**（左分离来自 §3 的非退化；右分离由 `tr(A∘B) = tr(B∘A)`）。 -/
theorem endTraceForm_nondegenerate : (endTraceForm k V).Nondegenerate := by
  constructor
  · intro A hA
    exact trace_pairing_eq_zero k V A fun B => hA B
  · intro B hB
    exact trace_pairing_eq_zero k V B fun A => by
      rw [LinearMap.trace_comp_comm' A B]
      exact hB A

#print axioms endTraceForm_nondegenerate

/-- ★★★★★ **迹对偶等价**：`End W ≃ₗ Dual k (End W)`，`A ↦ (B ↦ tr(A ∘ B))`。

**用途**：AGPR `lem:12.1.2` 把「多线性不变量」与「`(End V)^{⊗m}` 的 `GL`-不变元」等同，靠的就是
「对偶 ≅ 自身」这一步；本件给 `W = End V`（及其张量幂，见下）的形态。 -/
noncomputable def endTraceDualEquiv :
    Module.End k V ≃ₗ[k] Module.Dual k (Module.End k V) :=
  (endTraceForm k V).toDual (endTraceForm_nondegenerate k V)

#print axioms endTraceDualEquiv

theorem endTraceDualEquiv_apply (A B : Module.End k V) :
    endTraceDualEquiv k V A B = LinearMap.trace k V (A ∘ₗ B) := by
  rw [endTraceDualEquiv, LinearMap.BilinForm.toDual_def, endTraceForm_apply]

#print axioms endTraceDualEquiv_apply

/-- **张量幂上的迹配对形式**：经识别 ① 把 `⨂^m (End V)` 送进 `End(V^{⊗m})` 再取 `tr(A ∘ B)`。 -/
noncomputable def tensorPowerTraceForm :
    LinearMap.BilinForm k (TensorPower k m (Module.End k V)) :=
  LinearMap.BilinForm.congr (tensorPowerEndEquiv k V m).symm
    (endTraceForm k (TensorPower k m V))

#print axioms tensorPowerTraceForm

theorem tensorPowerTraceForm_apply (x y : TensorPower k m (Module.End k V)) :
    tensorPowerTraceForm k V m x y =
      LinearMap.trace k (TensorPower k m V)
        (tensorPowerEndEquiv k V m x ∘ₗ tensorPowerEndEquiv k V m y) := by
  rw [tensorPowerTraceForm, LinearMap.BilinForm.congr_apply, endTraceForm_apply]
  rfl

#print axioms tensorPowerTraceForm_apply

/-- ★★★★ **张量幂的迹配对形式非退化**（沿识别 ① 从 `End(V^{⊗m})` 运输）。 -/
theorem tensorPowerTraceForm_nondegenerate : (tensorPowerTraceForm k V m).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.congr (tensorPowerEndEquiv k V m).symm
    (endTraceForm_nondegenerate k (TensorPower k m V))

#print axioms tensorPowerTraceForm_nondegenerate

/-- ★★★★★ **张量幂的迹对偶等价**：`⨂^m (End V) ≃ₗ Dual k (⨂^m (End V))`。 -/
noncomputable def tensorPowerTraceDualEquiv :
    TensorPower k m (Module.End k V) ≃ₗ[k]
      Module.Dual k (TensorPower k m (Module.End k V)) :=
  (tensorPowerTraceForm k V m).toDual (tensorPowerTraceForm_nondegenerate k V m)

#print axioms tensorPowerTraceDualEquiv

/-- ★★★★★ **AGPR 配对公式（对偶形态）**：纯张量上的读数是 `∏ tr(aᵢ ∘ bᵢ)`。

源文 `:13870` 逐字：`⟨A₁⊗⋯⊗A_m | B₁⊗⋯⊗B_m⟩ = tr(A₁⋯A_m ∘ B₁⋯B_m) = ∏ tr(AᵢBᵢ)`。 -/
theorem tensorPowerTraceDualEquiv_tprod (a b : Fin m → Module.End k V) :
    tensorPowerTraceDualEquiv k V m (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k b)
      = ∏ i : Fin m, LinearMap.trace k V (a i ∘ₗ b i) := by
  rw [tensorPowerTraceDualEquiv, LinearMap.BilinForm.toDual_def,
    tensorPowerTraceForm_apply]
  exact trace_tensorPowerEnd_comp k V m a b

#print axioms tensorPowerTraceDualEquiv_tprod

/-- ★★★★★★ **识别 ② 的同构形态**：`m` 个 `End V` 的**多线性函数** ≅ `(End V)^{⊗m}`。

`(PiTensorProduct.lift)` 给「多线性函数 ≅ `(⨂^m End V) →ₗ k`」（张量积的万有色性），
再沿迹对偶等价换成 `⨂^m (End V)`。**这就是** AGPR `lem:12.1.2` 第一步的
「多线性不变量 ↔ `(End V)^{⊗m}` 的 `GL`-不变元」的**载体侧**。 -/
noncomputable def multilinearMapTensorPowerEquiv :
    MultilinearMap k (fun _ : Fin m => Module.End k V) k ≃ₗ[k]
      TensorPower k m (Module.End k V) :=
  (PiTensorProduct.lift).trans (tensorPowerTraceDualEquiv k V m).symm

#print axioms multilinearMapTensorPowerEquiv

/-- **其求值律**：`Θ` 的像在迹对偶下的读数，在纯张量 `⊗^m b` 上就是 `Θ b`。 -/
theorem multilinearMapTensorPowerEquiv_apply_dual
    (Θ : MultilinearMap k (fun _ : Fin m => Module.End k V) k)
    (b : Fin m → Module.End k V) :
    (tensorPowerTraceDualEquiv k V m (multilinearMapTensorPowerEquiv k V m Θ))
      (PiTensorProduct.tprod k b)
      = Θ b := by
  simp [multilinearMapTensorPowerEquiv]

#print axioms multilinearMapTensorPowerEquiv_apply_dual

end TraceDuality

/-! ## §5 **识别 ② 的群作用层（第一步）**：共轭穿桥对**任意** `x`（第 505 轮）

`§1` 的 `tensorPowerEndEquiv_conj` 只对**纯张量**成立；群作用层要的是对 `⨂^m (End V)` 的
**每个**元素成立——因为「`x` 是 `GL`-不变元」是 `x` 本体的条件，不是生成元的条件。
本节把上一行推广到全体 `x`：

```
x ↦ ⨂^m (B ∘ - ∘ B')   ≃    Φx ↦ (⊗^m B) ∘ Φx ∘ (⊗^m B')
```

于是「`x` 被逐因子共轭固定」经识别 ① 变成「`Φx` 与 `⊗^m B` 交换」——这正是已入仓的
Schur–Weyl 双臂双中心化子（`TauCetiSymmetricTensorActionGeneralLinear`）的输入形状。

**证明**：`PiTensorProduct.induction_on`（标量张量 ＋ 加法），纯张量情形用 `§1` 的 `_conj`，
加法情形用两侧的线性。 -/

section ConjTransport

/-- 逐因子共轭 `f ↦ B ∘ f ∘ B'`，作为 `End V` 的线性自同态。 -/
noncomputable def conjEnd (B B' : Module.End k V) : Module.End k V →ₗ[k] Module.End k V where
  toFun f := B ∘ₗ f ∘ₗ B'
  map_add' f g := by
    ext v
    simp [map_add]
  map_smul' c f := by
    ext v
    simp

#print axioms conjEnd

theorem conjEnd_apply (B B' : Module.End k V) (f : Module.End k V) :
    conjEnd k V B B' f = B ∘ₗ f ∘ₗ B' := rfl

#print axioms conjEnd_apply

/-- ★★★★★ **不变性运输（任意 `x`）**：逐因子共轭经识别 ① 变成两侧复合。

**为何需要**：AGPR `lem:12.1.2` 第二步的「`(End V)^{⊗m}` 的 `GL`-不变元」是 `x` 本体的条件；
本件把它翻译成 `End(V^{⊗m})` 侧「与 `⊗^m B` 交换」，双中心化子才可用。 -/
theorem tensorPowerEndEquiv_map_conj (B B' : Module.End k V)
    (x : TensorPower k m (Module.End k V)) :
    tensorPowerEndEquiv k V m
        (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B') x)
      = (PiTensorProduct.map (fun _ : Fin m => B))
        ∘ₗ (tensorPowerEndEquiv k V m x)
        ∘ₗ (PiTensorProduct.map (fun _ : Fin m => B')) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, PiTensorProduct.map_tprod, conjEnd_apply,
      tensorPowerEndEquiv_conj, LinearMap.smul_comp, LinearMap.comp_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, LinearMap.comp_add, LinearMap.add_comp]

#print axioms tensorPowerEndEquiv_map_conj

end ConjTransport

/-! ## §6 **识别 ② 双中心化子对接**（第 506 轮）：AGPR `lem:12.1.2` 的群论核心

本节把 §5 的运输接到已入仓的双臂双中心化子上，得到识别 ② 的**主结论**：

```
x ∈ ⨂^m (End (kⁿ)) 被所有可逆对的逐因子共轭固定
  ⟹  Φx ∈ range permTensorActionAlgHom   （＝ k[S_m]-作用的像 ＝ "置换算子张成"）
```

**桥**：`TauCeti.tensorPowerRep k n m g = ⨂^m (stdRep k n g)`（`Representation.tensorPower_apply`），
于是 §5 给出「`GL`-不变 ⟹ `Φx` 与 `⊗^m B` 交换」，再用
`TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep`
（「`x` 属 `k[S_m]`-像 ⟺ 与所有 `tensorPowerRep g` 交换」）。

**射程**：本件给的是**载体的两侧对接**；`T_σ`（迹单项式）的**逐字识别**（`eq:12.3`）仍未做，
故 AGPR `lem:12.1.2` 的**陈述**尚未作为一条定理写出（本件是其证明的两个引擎之一）。
`SFixedLeZ`／`Z` 半／H2 **仍不是定理**。 -/

section DoubleCentralizerBridge

open TauCeti

variable [Infinite k]

/-- **桥**：TauCeti 的 `tensorPowerRep` 是 `PiTensorProduct.map` 的常值族。 -/
theorem tensorPowerRep_eq_map (g : GL (Fin n) k) :
    TauCeti.tensorPowerRep k n m g
      = PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g) := by
  rw [TauCeti.tensorPowerRep, Representation.tensorPower_apply]

#print axioms tensorPowerRep_eq_map

/-- ★★★★★★ **AGPR `lem:12.1.2` 的群论核心**：逐因子共轭不变 ⟹ 属 `k[S_m]`-像。

**输入**：`x ∈ ⨂^m (End (kⁿ))` 被**所有**可逆对 `(B, B')` 的逐因子共轭
`⊗^m (B ∘ - ∘ B')` 固定。
**输出**：`Φx`（`End((kⁿ)^{⊗m})` 的元素）属置换作用的像。 -/
theorem mem_range_permTensorActionAlgHom_of_fixed [NeZero (Nat.factorial m : k)]
    (x : TensorPower k m (Module.End k (Fin n → k)))
    (hx : ∀ (B B' : Module.End k (Fin n → k)), B ∘ₗ B' = 1 → B' ∘ₗ B = 1 →
      PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') x = x) :
    tensorPowerEndEquiv k (Fin n → k) m x ∈ (TauCeti.permTensorActionAlgHom k n m).range := by
  classical
  rw [TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute_tensorPowerRep]
  intro g
  rw [tensorPowerRep_eq_map]
  have h1 : TauCeti.stdRep k n g ∘ₗ TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k)) = 1 := by
    have h : TauCeti.stdRep k n g * TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k)) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact h
  have h2 : TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k)) ∘ₗ TauCeti.stdRep k n g = 1 := by
    have h : TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k)) * TauCeti.stdRep k n g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    exact h
  have hfix := hx _ _ h1 h2
  have key : (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
      ∘ₗ (tensorPowerEndEquiv k (Fin n → k) m x)
      ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k))))
      = tensorPowerEndEquiv k (Fin n → k) m x := by
    rw [← tensorPowerEndEquiv_map_conj k (Fin n → k) m _ _ x, hfix]
  have hcomp : (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k))))
      ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g)) = 1 := by
    rw [← PiTensorProduct.map_comp, h2]
    exact PiTensorProduct.map_id
  have key' : (tensorPowerEndEquiv k (Fin n → k) m x)
        ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
      = (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
          ∘ₗ (tensorPowerEndEquiv k (Fin n → k) m x) := by
    calc (tensorPowerEndEquiv k (Fin n → k) m x)
          ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
        = ((PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
            ∘ₗ (tensorPowerEndEquiv k (Fin n → k) m x)
            ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k)))))
            ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g)) := by
          rw [key]
      _ = (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
            ∘ₗ (tensorPowerEndEquiv k (Fin n → k) m x)
            ∘ₗ ((PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n ((g⁻¹ : GL (Fin n) k))))
                ∘ₗ (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))) := by
          rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
      _ = (PiTensorProduct.map (fun _ : Fin m => TauCeti.stdRep k n g))
            ∘ₗ (tensorPowerEndEquiv k (Fin n → k) m x) := by
          rw [hcomp]
          exact LinearMap.comp_id ((PiTensorProduct.map
            (fun _ : Fin m => TauCeti.stdRep k n g)) ∘ₗ tensorPowerEndEquiv k (Fin n → k) m x)
  exact key'

#print axioms mem_range_permTensorActionAlgHom_of_fixed

end DoubleCentralizerBridge

/-! ## §7 **GL-不变性的一半：迹配对在同时共轭下不变**（第 507 轮）

识别 ② 把「多线性不变量」与「`(End V)^{⊗m}` 的 `GL`-不变元」等同，但**配对本身**必须是
`GL`-等变的：`tr((UAU')(UBU')) = tr(AB)`。本节补上这一格。

**证明**（纯结合律 ＋ 迹的交换性）：`(UAU')(UBU') = U(AB)U'`（用 `U'U = 1`），
再 `tr(U(AB)U') = tr((AB)U'U) = tr(AB)`（`LinearMap.trace_comp_comm'`）。

`trace_tensorPower_pairing_conj` 是张量幂侧形态：沿识别 ①（§5 的 `_map_conj`）运输。 -/

section TracePairingInvariance

/-- ★★★★ **常值族的复合律**：`⊗^m B' * ⊗^m B = 1`（当 `B' * B = 1`）。

**载体**：`PiTensorProduct.map_comp`（`map (g ∘ f) = map g ∘ map f`）＋ `map_id`。
**用途**：`GL`-作用是同时共轭，其逆给出 `⊗^m B' * ⊗^m B = 1`——这是「迹在共轭下不变」
（§7）与「`T_σ` 的 `GL`-不变性」（§12）共用的那一格。 -/
theorem map_const_mul_eq_one (m : ℕ) (B B' : Module.End k V) (hB'B : B' * B = 1) :
    (PiTensorProduct.map (fun _ : Fin m => B'))
        * (PiTensorProduct.map (fun _ : Fin m => B)) = 1 := by
  show (PiTensorProduct.map (fun _ : Fin m => B'))
      ∘ₗ (PiTensorProduct.map (fun _ : Fin m => B)) = 1
  rw [← PiTensorProduct.map_comp,
    show (fun i : Fin m => B' ∘ₗ B) = (fun _ => 1) from by funext i; exact hB'B]
  exact PiTensorProduct.map_id

#print axioms map_const_mul_eq_one

/-- ★★★★★ **迹配对在同时共轭下不变**：`tr((U A U')(U B U')) = tr(A B)`（`U' U = 1`）。

**用途**：AGPR `lem:12.1.2` 的配对 `⟨A|B⟩ = tr(A ∘ B)` 要成为 `GL`-等变的配对（对偶 ≅ 自身
在 `GL`-模意义下），靠的就是这一条。 -/
theorem trace_pairing_conj (A B U U' : Module.End k V) (hU'U : U' * U = 1) :
    LinearMap.trace k V ((U * A * U') * (U * B * U'))
      = LinearMap.trace k V (A * B) := by
  have key : (U * A * U') * (U * B * U') = U * (A * B) * U' := by
    simp only [mul_assoc]
    rw [← mul_assoc U' U (B * U'), hU'U, one_mul]
  rw [key]
  show LinearMap.trace k V (U ∘ₗ (A * B * U')) = LinearMap.trace k V (A * B)
  rw [LinearMap.trace_comp_comm' (A * B * U') U]
  show LinearMap.trace k V ((A * B * U') * U) = LinearMap.trace k V (A * B)
  simp only [mul_assoc]
  rw [hU'U, mul_one]

#print axioms trace_pairing_conj

/-- ★★★★★ **张量幂侧**：沿识别 ①（§5）运输后的迹配对在逐因子共轭下不变。 -/
theorem trace_tensorPower_pairing_conj (m : ℕ) (B B' : Module.End k V)
    (x y : TensorPower k m (Module.End k V)) (hB'B : B' * B = 1) :
    LinearMap.trace k (TensorPower k m V)
        ((tensorPowerEndEquiv k V m
            (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B') x))
          ∘ₗ (tensorPowerEndEquiv k V m
            (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B') y)))
      = LinearMap.trace k (TensorPower k m V)
          (tensorPowerEndEquiv k V m x ∘ₗ tensorPowerEndEquiv k V m y) := by
  rw [tensorPowerEndEquiv_map_conj, tensorPowerEndEquiv_map_conj]
  have hcomp := map_const_mul_eq_one k V m B B' hB'B
  exact trace_pairing_conj k (TensorPower k m V)
    (tensorPowerEndEquiv k V m x) (tensorPowerEndEquiv k V m y)
    (PiTensorProduct.map (fun _ : Fin m => B)) (PiTensorProduct.map (fun _ : Fin m => B')) hcomp

#print axioms trace_tensorPower_pairing_conj

end TracePairingInvariance

/-! ## §8 **识别 ③ 的第一格**：置换算子在纯张量上的计算律（第 508 轮）

识别 ③ 要把「置换算子」与「`T_σ`（迹单项式）」逐字对上。第一格是让 `permTensorAction`
在纯张量上**可算**：

```
permTensorAction k n m σ (⊗^m vᵢ) = ⊗^m (v_{σ⁻¹ i})
```

即它与 `PiTensorProduct.reindex` 的 `tprod` 计算律一致（`reindex_tprod`）。有了它，
`tr(σ⁻¹ ∘ ⊗Xᵢ)`（AGPR `eq:12.2` 的右端）才可逐项展开——这是 `eq:12.3` 轮换展开的入口。

**射程**：本件只给 `permTensorAction` 的 `tprod` 计算律；`T_σ` 的**逐字识别**与
`eq:12.3`（`σ` 的轮换分解给出迹的乘积）**均未做**。 -/

section PermActionOnTprod

/-- ★★★★ **置换算子的纯张量计算律**：`permTensorAction σ (⊗ v) = ⊗ (v ∘ σ.symm)`。 -/
theorem permTensorAction_tprod (σ : Equiv.Perm (Fin m)) (v : Fin m → (Fin n → k)) :
    TauCeti.permTensorAction k n m σ (PiTensorProduct.tprod k v)
      = PiTensorProduct.tprod k (fun i => v (σ.symm i)) :=
  PiTensorProduct.reindex_tprod (R := k) (s := fun _ : Fin m => Fin n → k) σ v

#print axioms permTensorAction_tprod

end PermActionOnTprod

/-! ## §9 **两作用交换（Schur–Weyl 易半）＋ 识别 ③ 的算子侧接口**（第 509 轮）

§8 给了 `permTensorAction` 在纯张量上的计算律；本节给它的**算子侧**：`⊗^m B` 与置换重标号**交换**。
即 AGPR 引用的 `GL(V)`-作用与 `S_m`-作用的两两交换性（双中心化子的先决条件），
在我们自己的 `PiTensorProduct.map` 接口里：

```
(⊗^m B) * reindex σ = reindex σ * (⊗^m B)
```

**证明**：`PiTensorProduct.map_comp_reindex_eq` 在**常值族** `f = fun _ => B` 上的特化
（此时 `f ∘ σ.symm = f`）。 -/

section ActionsCommute

/-- ★★★★ **两作用交换**：`⊗^m B` 与置换重标号交换（`*` 是 `Module.End` 的复合）。 -/
theorem map_const_commute_reindex (m : ℕ) (B : Module.End k V)
    (σ : Equiv.Perm (Fin m)) :
    (PiTensorProduct.map (fun _ : Fin m => B))
        * (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
      = (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        * (PiTensorProduct.map (fun _ : Fin m => B)) :=
  PiTensorProduct.map_comp_reindex_eq (R := k) (s := fun _ : Fin m => V)
    (t := fun _ : Fin m => V) (f := fun _ : Fin m => B) (e := σ)

#print axioms map_const_commute_reindex

/-- ★★★★ TauCeti 接口形态：`⊗^m B` 与 `permTensorAction σ` 交换。 -/
theorem map_const_commute_permTensorAction (n m : ℕ) (B : Module.End k (Fin n → k))
    (σ : Equiv.Perm (Fin m)) :
    (PiTensorProduct.map (fun _ : Fin m => B)) * TauCeti.permTensorAction k n m σ
      = TauCeti.permTensorAction k n m σ * (PiTensorProduct.map (fun _ : Fin m => B)) :=
  map_const_commute_reindex k (Fin n → k) m B σ

#print axioms map_const_commute_permTensorAction

end ActionsCommute

/-! ## §10 **`T_σ` 的载体定义**（AGPR `eq:12.2`；第 510 轮）

AGPR `lem:12.1.2` 的 `eq:12.2` 逐字：

> `T_σ(X₁,…,X_m) := tr(σ⁻¹ ∘ X₁ ⊗ X₂ ⊗ ⋯ ⊗ X_m)`，`σ ∈ S_m`.

本节把 `T_σ` 在**我们的接口**里定义出来：`x ↦ tr(P_σ ∘ Φx)`，其中 `P_σ` 是置换重标号、
`Φ` 是识别 ①。纯张量上的计算律 `tSigma_tprod` 给出 `T_σ(⊗^m a) = tr(P_σ ∘ ⨂^m a)`。

**射程**：`T_σ` 的 `GL`-不变性与 `eq:12.3`（轮换分解给出迹的乘积）**均未做**；
`lem:12.1.2` 的「`T_σ` 张成多线性不变量」尚未成陈述。 -/

section TSigma

/-- ★★★★★ **`T_σ`（AGPR `eq:12.2`）**：`x ↦ tr(σ⁻¹ ∘ Φ x)`。 -/
noncomputable def tSigma (σ : Equiv.Perm (Fin m)) (x : TensorPower k m (Module.End k V)) : k :=
  LinearMap.trace k (TensorPower k m V)
    ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
      * tensorPowerEndEquiv k V m x)

#print axioms tSigma

/-- 纯张量上的计算律：`T_σ(⊗^m a) = tr(P_σ ∘ ⨂^m a)`。 -/
theorem tSigma_tprod (σ : Equiv.Perm (Fin m)) (a : Fin m → Module.End k V) :
    tSigma k V m σ (PiTensorProduct.tprod k a)
      = LinearMap.trace k (TensorPower k m V)
          ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
            * PiTensorProduct.map a) := by
  rw [tSigma, tensorPowerEndEquiv_tprod]

#print axioms tSigma_tprod

end TSigma

/-! ## §11 **`T_σ` 作为线性泛函**（第 511 轮）

`lem:12.1.2` 说「多线性不变量**线性张成**于 `T_σ`」——故 `T_σ` 必须是**可线性组合的对象**。
本节把 §10 的 `tSigma` 打包成 `Module.Dual` 的元素。 -/

section TSigmaLinear

/-- ★★★★★ **`T_σ` 的线性泛函形态**（`T_σ ∈ Dual k (⨂^m (End V))`）。 -/
noncomputable def tSigmaLinear (σ : Equiv.Perm (Fin m)) :
    Module.Dual k (TensorPower k m (Module.End k V)) where
  toFun := tSigma k V m σ
  map_add' x y := by
    simp only [tSigma, map_add, mul_add, add_mul]
  map_smul' c x := by
    simp only [tSigma, map_smul, mul_smul_comm, RingHom.id_apply]

#print axioms tSigmaLinear

/-- 纯张量上的值：`T_σ(⊗^m a) = tr(P_σ ∘ ⨂^m a)`。 -/
theorem tSigmaLinear_tprod (σ : Equiv.Perm (Fin m)) (a : Fin m → Module.End k V) :
    tSigmaLinear k V m σ (PiTensorProduct.tprod k a)
      = LinearMap.trace k (TensorPower k m V)
          ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
            * PiTensorProduct.map a) :=
  tSigma_tprod k V m σ a

#print axioms tSigmaLinear_tprod

end TSigmaLinear

/-! ## §12 **`T_σ` 的 `GL`-不变性**（AGPR `lem:12.1.2` 证明的第一句；第 512 轮）

`lem:12.1.2` 的证明第一句是「多线性不变量 ＝ `End(V)^{⊗m}` 的 `GL`-不变元」。
要成为不变量，`T_σ`（§10）必须在同时共轭下不变：

```
T_σ(B X₁ B', …, B X_m B') = T_σ(X₁, …, X_m)      （B' B = 1）
```

载体形态：`T_σ x = tr(P_σ * Φ x)`，故不变性 ＝ **迹的循环性**（与 §7 同款）
＋ **`⊗^m B'` 与 `P_σ` 交换**（§9）。四步：

1. 展开：`tr(P_σ * (⊗^m B * Φ x * ⊗^m B'))`（§5 的 `tensorPowerEndEquiv_map_conj`）；
2. 循环性把 `⊗^m B'` 移到最左（`LinearMap.trace_mul_comm`）；
3. 交换律（§9）把 `⊗^m B'` 穿过 `P_σ`；
4. `⊗^m B' * ⊗^m B = 1`（`map_const_mul_eq_one`，§7）消去。

**射程**：本件只给 `T_σ` 的**不变性**（即「`T_σ` 属于不变量」这一半）；
`eq:12.3` 的轮换展开、`lem:12.1.2` 的「张成」陈述、FFT 难半 **均未做**。 -/

section TSigmaGlInvariant

/-- ★★★★★ **四因子迹恒等式**：若 `X * Y = 1` 且 `X` 与 `P` 交换，则 `tr(P * Y * A * X) = tr(P * A)`。

**证明**：`tr(P*Y*A*X) = tr(X*P*Y*A)`（循环性）`= tr(P*X*Y*A)`（交换性）
`= tr(P*A)`（`X*Y = 1`）。`Module.End` 的结合律是**定义相等**的（`∘ₗ` 的结合律为 `rfl`），
故中间的换组无需 `simp only [mul_assoc]`。 -/
theorem trace_mul_conj_right (W : Type*) [AddCommGroup W] [Module k W]
    [Module.Free k W] [Module.Finite k W] (P X Y A : Module.End k W)
    (hXY : X * Y = 1) (hPX : X * P = P * X) :
    LinearMap.trace k W (P * (Y * A * X)) = LinearMap.trace k W (P * A) := by
  have hP : X * P * Y = P := by
    rw [hPX, mul_assoc, hXY, mul_one]
  calc LinearMap.trace k W (P * (Y * A * X))
      = LinearMap.trace k W ((P * Y * A) * X) := rfl
    _ = LinearMap.trace k W (X * (P * Y * A)) := by
          rw [LinearMap.trace_mul_comm]
    _ = LinearMap.trace k W (X * P * Y * A) := rfl
    _ = LinearMap.trace k W (P * A) := by rw [hP]

#print axioms trace_mul_conj_right

/-- ★★★★★ **`T_σ` 的 `GL`-不变性（张量形态）**：逐因子共轭不改变 `T_σ` 的值。 -/
theorem tSigma_map_conj (m : ℕ) (σ : Equiv.Perm (Fin m)) (B B' : Module.End k V)
    (hB'B : B' * B = 1) (x : TensorPower k m (Module.End k V)) :
    tSigma k V m σ (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B') x)
      = tSigma k V m σ x := by
  rw [tSigma, tensorPowerEndEquiv_map_conj]
  have hcomp := map_const_mul_eq_one k V m B B' hB'B
  have hcomm : (PiTensorProduct.map (fun _ : Fin m => B'))
      * (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
      = (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        * (PiTensorProduct.map (fun _ : Fin m => B')) :=
    map_const_commute_reindex k V m B' σ
  show LinearMap.trace k (TensorPower k m V)
      ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        * ((PiTensorProduct.map (fun _ : Fin m => B))
          * (tensorPowerEndEquiv k V m x)
          * (PiTensorProduct.map (fun _ : Fin m => B'))))
    = LinearMap.trace k (TensorPower k m V)
      ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        * tensorPowerEndEquiv k V m x)
  exact trace_mul_conj_right k (TensorPower k m V) _ _ _ _ hcomp hcomm

#print axioms tSigma_map_conj

/-- ★★★★★ **`T_σ` 的 `GL`-不变性（多线性形态）**——AGPR `eq:12.2` 的逐字语义：
`T_σ(B X₁ B', …, B X_m B') = T_σ(X₁, …, X_m)`。 -/
theorem tSigma_tprod_map_conj (m : ℕ) (σ : Equiv.Perm (Fin m)) (B B' : Module.End k V)
    (hB'B : B' * B = 1) (f : Fin m → Module.End k V) :
    tSigma k V m σ (PiTensorProduct.tprod k (fun i => B ∘ₗ f i ∘ₗ B'))
      = tSigma k V m σ (PiTensorProduct.tprod k f) := by
  have h : PiTensorProduct.tprod k (fun i => B ∘ₗ f i ∘ₗ B')
      = PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B')
          (PiTensorProduct.tprod k f) := by
    rw [PiTensorProduct.map_tprod]
    rfl
  rw [h, tSigma_map_conj k V m σ B B' hB'B]

#print axioms tSigma_tprod_map_conj

end TSigmaGlInvariant

/-! ## §13 **`eq:12.3` 的两端**：`σ = 1` 情形 ＋ 左端的**标准形**（第 513 轮）

AGPR `eq:12.3`（`raw/AGPR2020.tex:13868`）说：若 `σ` 的轮换分解是
`(i₁…i_h)⋯(s₁…s_t)`，则

```
T_σ(X₁,…,X_m) = tr(X_{i₁}⋯X_{i_h}) ⋯ tr(X_{s₁}⋯X_{s_t})。
```

本节做**两端**，把该等式化成一个纯组合问题：

| 端 | 件 | 形态 |
|---|---|---|
| 右端（`σ = 1`，全是不动点） | ★★★★★ `tSigma_one_tprod` | `T_1(⊗^m Xᵢ) = ∏ tr Xᵢ` |
| **左端（任意 `σ`）** | ★★★★★ `tSigma_tprod_eq_sum` | `T_σ(⊗^m Xᵢ) = Σ_p ∏ i, (Xᵢ)_{p i, p(σ i)}` |

**为何左端标准形是关键**：它把「置换算子的迹」换成**多指标和**，而右端的每一项也是同类的
多指标和 ⟹ `eq:12.3` 变成「两组多指标和相等」的组合恒等式。取 `Xᵢ` 为**矩阵单位**时两端都退化成
Kronecker 张量积，且**与轮换结构无关**（左端 `∏ i, [aᵢ = b_{σ⁻¹i}]`、右端同一条件集的轮换重排）。

**证明（左端）**：把 §10 的 `tSigma_tprod` 送进基 `Basis.piTensorProduct`，逐项用
`Module.End.mul_apply`（`(f*g) x = f (g x)`）＋ `Basis.piTensorProduct_apply` ＋
`PiTensorProduct.map_tprod` ＋ `reindex_tprod`（此处须以 `.toLinearMap` 形态写出——
`↑(reindex σ)` 与 `reindex σ` 的 `rw` 匹配失败，见 v25 教训 3 同族）＋
`Basis.piTensorProduct_repr_tprod_apply`，最后把 `∏ i, F (σ.symm i) i` 重标号为
`∏ j, F j (σ j)`（`Finset.prod_bij`，双射取 `i ↦ σ.symm i`）。

**射程**：本节只给**两端**。`eq:12.3` 的等式本身（矩阵单位上的 δ 计算 ＋ 「只需查矩阵单位」
的多线性延拓）**未做**；`lem:12.1.2` 的「张成」陈述、FFT 难半、`SFixedLeZ`／`Z` 半／H2 **仍不是定理**。 -/

section Eq123Ends

/-- ★★★★★ **`T_1 = tr ∘ Φ`**：`eq:12.3` 的右端在「全不动点」情形（`P_1 = id`）。 -/
theorem tSigma_one (m : ℕ) (x : TensorPower k m (Module.End k V)) :
    tSigma k V m 1 x
      = LinearMap.trace k (TensorPower k m V) (tensorPowerEndEquiv k V m x) := by
  rw [tSigma]
  have hP : PiTensorProduct.reindex k (fun _ : Fin m => V) (1 : Equiv.Perm (Fin m))
      = LinearEquiv.refl k (TensorPower k m V) := by
    have h1 : (1 : Equiv.Perm (Fin m)) = Equiv.refl (Fin m) := rfl
    rw [h1, PiTensorProduct.reindex_refl]
  rw [hP]
  show LinearMap.trace k (TensorPower k m V)
      ((LinearMap.id : Module.End k (TensorPower k m V)) ∘ₗ (tensorPowerEndEquiv k V m x))
      = LinearMap.trace k (TensorPower k m V) (tensorPowerEndEquiv k V m x)
  rw [LinearMap.id_comp]

#print axioms tSigma_one

/-- ★★★★★ **`eq:12.3` 的 `σ = 1` 情形**：`T_1(⊗^m Xᵢ) = ∏ tr Xᵢ`（右端全是不动点的一次轮换）。 -/
theorem tSigma_one_tprod (m : ℕ) (X : Fin m → Module.End k V) :
    tSigma k V m 1 (PiTensorProduct.tprod k X)
      = ∏ i : Fin m, LinearMap.trace k V (X i) := by
  rw [tSigma_one, tensorPowerEndEquiv_tprod]
  exact trace_map_tensorPower k V m X

#print axioms tSigma_one_tprod

/-- ★★★★★ **`eq:12.3` 左端的标准形**（任意 `σ`、任意基 `b`）：`T_σ(⊗^m Xᵢ)` 是基下的多指标和
`Σ_p ∏ i, (Xᵢ)_{p i, p (σ i)}`。

**用途**：右端（轮换分解的迹乘积）也是同类的多指标和 ⟹ 等式 `eq:12.3` 归约为组合恒等式；
取矩阵单位时两端都退化为 Kronecker 张量积（见 §14 的 `tSigma_tprod_matUnit`）。

**基参数**（第 514 轮加）：原形态硬编码 `Module.Free.chooseBasis`，使 §14 的矩阵单位
**无法与同一基对齐**；本形态对任意 `b` 成立，原形态是其特化。 -/
theorem tSigma_tprod_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (b : Module.Basis ι k V)
    (σ : Equiv.Perm (Fin m)) (X : Fin m → Module.End k V) :
    tSigma k V m σ (PiTensorProduct.tprod k X)
      = ∑ p : Fin m → ι, ∏ i : Fin m, b.repr (X i (b (p i))) (p (σ i)) := by
  classical
  set B : Module.Basis (Fin m → ι) k (TensorPower k m V) :=
    Basis.piTensorProduct (fun _ : Fin m => b) with hB
  rw [tSigma_tprod]
  rw [LinearMap.trace_eq_matrix_trace (R := k) (M := TensorPower k m V) B]
  rw [show (LinearMap.toMatrix B B
        ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
          * PiTensorProduct.map X)).trace
      = ∑ p, B.repr (((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
          * PiTensorProduct.map X) (B p)) p from by
    simp [Matrix.trace, LinearMap.toMatrix_apply]]
  have hterm : ∀ p : Fin m → ι,
      B.repr (((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
          * PiTensorProduct.map X) (B p)) p
        = ∏ i : Fin m,
            b.repr (X (σ.symm i) (b (p (σ.symm i)))) (p i) := by
    intro p
    rw [Module.End.mul_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
    have hre : (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        ((PiTensorProduct.tprod k) (fun i => X i (b (p i))))
        = (PiTensorProduct.tprod k) (fun i => X (σ.symm i) (b (p (σ.symm i)))) :=
      PiTensorProduct.reindex_tprod (R := k) (s := fun _ : Fin m => V) σ
        (fun i => X i (b (p i)))
    rw [hre, Basis.piTensorProduct_repr_tprod_apply]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine Finset.prod_bij (fun i _ => σ.symm i) (fun i _ => Finset.mem_univ _)
    (fun i _ j _ hij => σ.symm.injective hij)
    (fun j _ => ⟨σ j, Finset.mem_univ _, by simp⟩) ?_
  intro i _
  simp

#print axioms tSigma_tprod_eq_sum

end Eq123Ends

/-! ## §14 **矩阵单位上的 `T_σ`**（`eq:12.3` 的判别性读数；第 514 轮）

§13 把 `eq:12.3` 的左端化成了多指标和。本节取**矩阵单位** `Xᵢ = E_{aᵢcᵢ}` 求出闭式：

```
T_σ(⊗^m E_{aᵢ cᵢ}) = ∏ i, [aᵢ = c_{σ i}]
```

**这同时是一条定案的方向读数**。AGPR `eq:12.2`（`raw/AGPR2020.tex:13864`）逐字是
`T_σ := tr(σ⁻¹ ∘ X₁⊗⋯⊗X_m)`，而我们 §10 的 `tSigma σ = tr(P_σ ∘ Φ x)`，其中 `P_σ = reindex σ`
在纯张量上是 `tprod v ↦ tprod (v ∘ σ.symm)`（§8 的 `permTensorAction_tprod`，即 `S_m` 的**标准左作用**
以 `σ` 作用在 `V^{⊗m}` 上）。故

```
我们的 tSigma σ  =  AGPR 的 T_{σ⁻¹}
```

⟹ `eq:12.3` 在本仓接口里必须写成**逆序**轮换积（等价地：写成 `σ⁻¹` 的轮换上的正序积）：

```
T_σ(X) = ∏_{c ∈ cycleFactors(σ)} tr(X_{i_h} ⋯ X_{i_1}),     σ = (i₁i₂⋯i_h)⋯
```

**为何这不伤战役**：`lem:12.1.2` 的「张成」陈述只用到**族** `{T_σ : σ ∈ S_m}`，而
`σ ↦ σ⁻¹` 是 `S_m` 的双射 ⟹ 该族不变。方向只影响 `eq:12.3` 的**写法**，不影响张成性。
（CLAUDE.md 规则 2：引入源中没有的记号/方向时须显式声明等价关系——本节即该声明。）

**证明**：§13 的标准形 ＋ `matUnit_entry`（`(E_{ac})_{xy} = [x=c][y=a]`）＋
`Finset.sum_eq_single`（多指标和里只有 `p = c` 一项非零）。

**射程**：本节只做**矩阵单位**这一层。`eq:12.3` 的等式本身仍需
（i）右端的轮换积载体（`cycleTrace`）与（ii）「只需查矩阵单位」的多线性延拓；**均未做**。 -/

section MatrixUnit

/-- `E_{a c}`（行 `a`、列 `c`）：`w ↦ (b.coord c w) • b a`。 -/
noncomputable def matUnit {ι : Type*} (b : Module.Basis ι k V) (a c : ι) : Module.End k V :=
  (b.coord c).smulRight (b a)

#print axioms matUnit

/-- ★★★★ **矩阵单位的矩阵元**：`(E_{a c})_{x y} = [x = c] · [y = a]`。 -/
theorem matUnit_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (a c x y : ι) :
    b.repr (matUnit k V b a c (b x)) y
      = (if x = c then (1 : k) else 0) * (if a = y then 1 else 0) := by
  simp only [matUnit, LinearMap.smulRight_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

#print axioms matUnit_entry

/-- ★★★★★ **矩阵单位上的 `T_σ`**：`T_σ(⊗^m E_{aᵢ cᵢ}) = ∏ i, [aᵢ = c_{σ i}]`。

**方向读数是定案读数**：右端是 `c (σ i)`（不是 `c (σ⁻¹ i)`）⟹ `eq:12.3` 须写成逆序轮换积
（见本节的节标说明）。 -/
theorem tSigma_tprod_matUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (b : Module.Basis ι k V) (σ : Equiv.Perm (Fin m)) (a c : Fin m → ι) :
    tSigma k V m σ (PiTensorProduct.tprod k (fun i => matUnit k V b (a i) (c i)))
      = ∏ i : Fin m, (if a i = c (σ i) then (1 : k) else 0) := by
  classical
  have hsum := tSigma_tprod_eq_sum (k := k) (V := V) (m := m) (ι := ι) b σ
    (fun i => matUnit k V b (a i) (c i))
  rw [hsum]
  simp only [matUnit_entry]
  rw [Finset.sum_eq_single (fun i => c i)]
  · simp
  · intro p _ hp
    obtain ⟨i₀, hi₀⟩ : ∃ i, p i ≠ c i := by
      by_contra h
      refine hp (funext fun i => ?_)
      by_contra hne
      exact h ⟨i, hne⟩
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    simp [hi₀]
  · intro h
    exact absurd (Finset.mem_univ (fun i => c i)) h

#print axioms tSigma_tprod_matUnit

end MatrixUnit

/-! ## §15 **`eq:12.3` 右端的引擎**：peel 引理 ＋ 单轮换因子（第 515 轮）

§14 给出了矩阵单位上的**闭式**：`T_σ(⊗^m E_{aᵢcᵢ}) = ∏ i, [aᵢ = c_{σ i}]`。本节给出右端的
**归纳引擎**，即「沿轮换每剥一个矩阵单位就得到一个矩阵元」：

```
tr(E_{a c} * M) = M_{c a} = b.repr (M (b a)) c          （peel 引理）
tr(E_{a c} * E_{a' c'}) = [c = a'] · [a = c']             （h = 2 的轮换积）
```

**★★ 方向由这两条**合起来**定死**：列表条件为 `c_k = a_{k+1}`（peel 的读数），而 §14 的 δ 条件为
`∀ j, a_j = c_{σ j}`；两者相等 ⟺ 遍历沿 `σ⁻¹`（**逆序**）。故 `cycleTrace` 用 `c.symm` 的迭代。

**射程**：本节的 `cycleTrace` 只是**载体**（有对象、方向正确）；`eq:12.3` 的等式本身仍需
（i）任意长度的 peel 归纳（`∏_k [c_k = a_{k+1}]`）与（ii）按轮换分解的乘积重排 ＋ 不动点因子、
（iii）「只需查矩阵单位」的多线性延拓。**三者均未做。** -/

section Eq123CycleEngine

/-- ★★★★★ **peel 引理**：`tr(E_{a c} * M) = M_{c a} = b.repr (M (b a)) c`。

**证明**：迹 ＝ 矩阵迹 ＋ `toMatrix_mul`，双层和里只有 `i = a`、`j = c` 一项非零
（`matUnit_entry` 给出 `[i = a][j = c]`）。 -/
theorem trace_matUnit_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (a c : ι) (M : Module.End k V) :
    LinearMap.trace k V (matUnit k V b a c * M) = b.repr (M (b a)) c := by
  classical
  rw [LinearMap.trace_eq_matrix_trace (R := k) (M := V) b, LinearMap.toMatrix_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, LinearMap.toMatrix_apply,
    matUnit_entry]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ c) h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [show a ≠ i from fun h => hi h.symm]
  · intro h
    exact absurd (Finset.mem_univ a) h

#print axioms trace_matUnit_mul

/-- ★★★★★ **两矩阵单位的迹**（`h = 2` 的 `eq:12.3` 右端因子）：`tr(E_{a c} E_{a' c'}) = [c=a'][a=c']`。

**方向读数**：列表条件 `c_k = a_{k+1}` 的第一格即 `c = a'`（不是 `a' = c` 之外的东西）——
把它与 §14 的 `[aᵢ = c_{σ i}]` 对比即得「遍历沿 `σ⁻¹`」。 -/
theorem trace_matUnit_matUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (a c a' c' : ι) :
    LinearMap.trace k V (matUnit k V b a c * matUnit k V b a' c')
      = (if c = a' then (1 : k) else 0) * (if a = c' then 1 else 0) := by
  rw [trace_matUnit_mul, matUnit_entry]
  by_cases h : a' = c
  · subst h; simp
  · simp [h, Ne.symm h]

#print axioms trace_matUnit_matUnit

/-- ★★★★ **`eq:12.3` 右端的单轮换因子**：沿 `c⁻¹` 的迭代顺序取 `X` 之积的迹。

`((c.symm)^t) i` 遍历 `i, c⁻¹ i, c⁻² i, …`（**逆序**）；`orderOf c = c.support.card` 对轮换成立。
取 `i = c.support.min' _` 作代表点（`trace` 的循环不变性使之与基点无关——此独立性**未证**）。 -/
noncomputable def cycleTrace (X : Fin m → Module.End k V) (c : Equiv.Perm (Fin m))
    (i : Fin m) : k :=
  LinearMap.trace k V ((List.range (orderOf c)).map (fun t => X (((c.symm) ^ t) i))).prod

#print axioms cycleTrace

end Eq123CycleEngine

/-! ## §16 **`T_σ` 的迹对偶向量**（`lem:12.1.2` 的「张成」陈述的桥；第 516 轮）

AGPR `lem:12.1.2` 的证明第二句：把 `End(V)^{⊗m}` 的**对偶**与它自身等同（迹配对）后，
「多线性不变量」就变成「`End(V)^{⊗m}` 的 `GL`-不变元」。§4 已给出该对偶等价
（`tensorPowerTraceDualEquiv`），本节给出**对象的运输**：

```
tSigmaVec σ := Φ⁻¹(P_σ)          （P_σ = 置换重标号算子）
⟹  ⟨tSigmaVec σ, y⟩ = T_σ y                 （tensorPowerTraceForm_tSigmaVec）
⟹  tensorPowerTraceDualEquiv (tSigmaVec σ) = tSigmaLinear σ
⟹  tSigmaVec σ 是 GL-固定向量               （map_conj_tSigmaVec）
```

**为何这是缺口 #3 的桥**：`lem:12.1.2` 说「多线性不变量**线性张成**于 `T_σ`」。
经上面的运输，它等价于「`⨂^m (End V)` 的 `GL`-不变元在 `span{tSigmaVec σ}` 里」——
后者正是 Schur–Weyl 双中心化子的**向量形态**（§6 已入仓的 TauCeti 双臂件给的是算子形态）。

**射程**：本节只做**运输**（`T_σ` ↔ 固定向量）。「`span{tSigmaVec σ}` ＝ 全部固定元」这个
**反向包含**（＝ `lem:12.1.2` 的「张成」陈述）**未做**；`eq:12.3` 的等式、FFT 难半、
`(A)→(B)` 均未做。 -/

section TSigmaVector

/-- ★★★★★ **`T_σ` 的迹对偶向量**：`tSigmaVec σ := Φ⁻¹(P_σ)`。 -/
noncomputable def tSigmaVec (σ : Equiv.Perm (Fin m)) :
    TensorPower k m (Module.End k V) :=
  (tensorPowerEndEquiv k V m).symm
    ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap)

#print axioms tSigmaVec

/-- ★★★★★ **配对读数**：`⟨tSigmaVec σ, y⟩ = T_σ y`。 -/
theorem tensorPowerTraceForm_tSigmaVec (σ : Equiv.Perm (Fin m))
    (y : TensorPower k m (Module.End k V)) :
    tensorPowerTraceForm k V m (tSigmaVec k V m σ) y = tSigma k V m σ y := by
  rw [tensorPowerTraceForm_apply, tSigma, tSigmaVec, LinearEquiv.apply_symm_apply]
  rfl

#print axioms tensorPowerTraceForm_tSigmaVec

/-- ★★★★★ **对偶等价把向量送到泛函**：`tensorPowerTraceDualEquiv (tSigmaVec σ) = tSigmaLinear σ`。

AGPR `lem:12.1.2` 那句「under this isomorphism the multilinear invariants of matrices are
identified with the `GL(V)` invariants of `End(V)^{⊗m}`」的**对象级形态**。 -/
theorem tensorPowerTraceDualEquiv_tSigmaVec (σ : Equiv.Perm (Fin m)) :
    tensorPowerTraceDualEquiv k V m (tSigmaVec k V m σ) = tSigmaLinear k V m σ := by
  refine LinearMap.ext fun y => ?_
  show tensorPowerTraceForm k V m (tSigmaVec k V m σ) y = tSigmaLinear k V m σ y
  rw [tensorPowerTraceForm_tSigmaVec]
  rfl

#print axioms tensorPowerTraceDualEquiv_tSigmaVec

/-- ★★★★★ **`tSigmaVec σ` 是 `GL`-固定向量**：逐因子共轭固定它（`B B' = 1`）。

**机制**：`Φ(逐因子共轭 · v) = (⊗^m B) ∘ Φ v ∘ (⊗^m B')`（§5 的 `_map_conj`）；把 `Φ v = P_σ` 代入，
用 §9 的两作用交换把 `⊗^m B` 与 `⊗^m B'` 移到一起，再用 `⊗^m B * ⊗^m B' = 1`（§7 的
`map_const_mul_eq_one`）消去。 -/
theorem map_conj_tSigmaVec (σ : Equiv.Perm (Fin m)) (B B' : Module.End k V)
    (hBB' : B * B' = 1) :
    PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B') (tSigmaVec k V m σ)
      = tSigmaVec k V m σ := by
  refine (tensorPowerEndEquiv k V m).injective ?_
  simp only [tSigmaVec]
  rw [LinearEquiv.apply_symm_apply, tensorPowerEndEquiv_map_conj,
    LinearEquiv.apply_symm_apply]
  have hcomp : (PiTensorProduct.map (fun _ : Fin m => B))
      * (PiTensorProduct.map (fun _ : Fin m => B')) = 1 :=
    map_const_mul_eq_one k V m B' B hBB'
  have hcomm : (PiTensorProduct.map (fun _ : Fin m => B'))
      * (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
      = (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        * (PiTensorProduct.map (fun _ : Fin m => B')) :=
    map_const_commute_reindex k V m B' σ
  calc (PiTensorProduct.map (fun _ : Fin m => B))
        * (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
        * (PiTensorProduct.map (fun _ : Fin m => B'))
      = (PiTensorProduct.map (fun _ : Fin m => B))
          * ((PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap
            * (PiTensorProduct.map (fun _ : Fin m => B'))) := rfl
    _ = (PiTensorProduct.map (fun _ : Fin m => B))
          * ((PiTensorProduct.map (fun _ : Fin m => B'))
            * (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap) := by
          rw [← hcomm]
    _ = ((PiTensorProduct.map (fun _ : Fin m => B))
          * (PiTensorProduct.map (fun _ : Fin m => B')))
          * (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap := rfl
    _ = (PiTensorProduct.reindex k (fun _ : Fin m => V) σ).toLinearMap := by
          rw [hcomp, one_mul]

#print axioms map_conj_tSigmaVec

end TSigmaVector

/-! ## §17 ★ **`lem:12.1.2` 的「张成」陈述（机检）**（第 517 轮）

AGPR `lem:12.1.2`（`raw/AGPR2020.tex:13862`）前半逐字：

> The space `T_n(m)` of multilinear invariants of `m` matrices is identified with
> `End_{GL(V)}(V^{⊗m})`, and it is linearly spanned by the functions `T_σ`, `σ ∈ S_m`.

本节把它的**向量形态**做成双向机检件（经 §16 的运输：`T_σ ↔ tSigmaVec σ`）：

```
x ∈ span{ tSigmaVec σ : σ ∈ S_m }   ⟺   x 被所有逐因子共轭固定（B ∘ B' = 1 = B' ∘ B）
```

**两个方向各自的来源**：

* **⇐（反向包含，真正的数学）**：§6 的 `mem_range_permTensorActionAlgHom_of_fixed`
  （TauCeti 双臂双中心化子）＋ `permTensorActionAlgHom_eq_sum`（`k[S_m]`-作用 ＝ 置换作用
  的系数加权和）⟹ `Φx = Σ_σ (coeff σ) • permTensorAction σ` ⟹ 施 `Φ⁻¹` 得
  `x = Σ_σ (coeff σ) • tSigmaVec σ`。
* **⇒（正向包含）**：§16 的 `map_conj_tSigmaVec`（每个 `tSigmaVec σ` 都是固定向量）
  ＋ `Submodule.span_le` ＋ `LinearMap.eqLocus`。

**假设（诚实登记）**：`[Infinite k]`（TauCeti 双中心化子所需）与
`[NeZero (Nat.factorial m : k)]`（`m!` 可逆，即特征 `0` 或 `> m`）。
AGPR 同一条路线也是「We prove this in characteristic 0」（`raw/AGPR2020.tex:13847`）。

**射程**：本节给的是**向量形态**的「张成」。`T_n(m)`（多线性**不变量**空间）与
`End_GL(V)(V^{⊗m})` 的**等同本身**（即 `lem:12.1.2` 的第一句）经 §4 的对偶等价运输后
与本节的 iff 等价，但**尚未**打包成一条以 `T_n(m)` 为名的陈述。
`eq:12.3` 的等式、FFT 难半（`thm:12.1.3`）、`(A)→(B)` **均未做**。 -/

section Lem1212Span

/-- 识别：`tSigmaVec σ` 就是 `Φ⁻¹(permTensorAction σ)`。 -/
theorem tSigmaVec_permTensorAction [Infinite k] (σ : Equiv.Perm (Fin m)) :
    tSigmaVec k (Fin n → k) m σ
      = (tensorPowerEndEquiv k (Fin n → k) m).symm (TauCeti.permTensorAction k n m σ) := rfl

#print axioms tSigmaVec_permTensorAction

/-- ★★★★★★ **反向包含**：`GL`-固定向量在 `span{tSigmaVec σ}` 里。 -/
theorem mem_span_tSigmaVec_of_fixed [Infinite k] [NeZero (Nat.factorial m : k)]
    (x : TensorPower k m (Module.End k (Fin n → k)))
    (hx : ∀ (B B' : Module.End k (Fin n → k)), B ∘ₗ B' = 1 → B' ∘ₗ B = 1 →
      PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') x = x) :
    x ∈ Submodule.span k
      (Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ)) := by
  classical
  have hmem := mem_range_permTensorActionAlgHom_of_fixed (k := k) (n := n) (m := m) x hx
  rw [AlgHom.mem_range] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [TauCeti.permTensorActionAlgHom_eq_sum] at ha
  have hx' : x = ∑ σ : Equiv.Perm (Fin m),
      a.coeff σ • tSigmaVec k (Fin n → k) m σ := by
    conv_lhs => rw [← LinearEquiv.symm_apply_apply (tensorPowerEndEquiv k (Fin n → k) m) x]
    rw [← ha, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [map_smul, tSigmaVec_permTensorAction]
  rw [hx']
  refine Submodule.sum_mem _ (fun σ _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨σ, rfl⟩

#print axioms mem_span_tSigmaVec_of_fixed

/-- ★★★★ **正向包含**：`span{tSigmaVec σ}` 的每个元都被逐因子共轭固定。 -/
theorem map_conj_eq_of_mem_span_tSigmaVec [Infinite k]
    (x : TensorPower k m (Module.End k (Fin n → k)))
    (hx : x ∈ Submodule.span k
      (Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ)))
    (B B' : Module.End k (Fin n → k)) (hBB' : B ∘ₗ B' = 1) :
    PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') x = x := by
  have hspan : Submodule.span k
        (Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ))
      ≤ LinearMap.eqLocus (PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B'))
          LinearMap.id := by
    rw [Submodule.span_le]
    rintro y ⟨σ, rfl⟩
    exact map_conj_tSigmaVec k (Fin n → k) m σ B B' hBB'
  exact hspan hx

#print axioms map_conj_eq_of_mem_span_tSigmaVec

/-- ★★★★★★★ **`lem:12.1.2` 的「张成」陈述（向量形态，双向机检）**：

`x ∈ span{T_σ}` **⟺** `x` 被所有逐因子共轭固定（`B ∘ B' = 1 = B' ∘ B`）。 -/
theorem mem_span_tSigmaVec_iff_fixed [Infinite k] [NeZero (Nat.factorial m : k)]
    (x : TensorPower k m (Module.End k (Fin n → k))) :
    x ∈ Submodule.span k (Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ))
      ↔ ∀ (B B' : Module.End k (Fin n → k)), B ∘ₗ B' = 1 → B' ∘ₗ B = 1 →
          PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') x = x := by
  refine ⟨fun hx B B' h1 _ => ?_, fun hx => ?_⟩
  · exact map_conj_eq_of_mem_span_tSigmaVec (x := x) (hx := hx) (B := B) (B' := B')
      (hBB' := h1)
  · exact mem_span_tSigmaVec_of_fixed (x := x) (hx := hx)

#print axioms mem_span_tSigmaVec_iff_fixed

end Lem1212Span

/-! ## §18 **任意长度矩阵单位乘链的迹**（`eq:12.3` 右端的一般引擎；第 518 轮）

§15 给了 `h = 2` 的因子与 peel 引理。本节把它推到**任意长度**，做成一条**无循环指标簿记**的形式：

```
chainCond []        x y = [x = y]
chainCond ((a,c)::l) x y = [x = a] * chainCond l c y          （链条件的递归定义）
tr(E_p * ∏_{q ∈ l} E_q) = chainCond l p.2 p.1                 （一般长度的迹公式）
```

**为何这样能避开循环**：把**首元单独拿出**（`p` 是参数而不是列表的第一个），链条件交给
`chainCond` 的递归；「闭合」留给调用处（取 `l` 为轮换的其余元时，递归末端给出首尾相接的那一格）。

**技术路线（本轮的侦察结论）**：矩阵单位在 **`Matrix` 世界**里是 `Matrix.single`，
其乘法是 `single_mul_single_same` / `single_mul_mul_single`，`Matrix.single_apply` 是 `rfl` 级引理；
故先在 `Matrix` 层做归纳（`mul_prod_single_apply`），再沿 `LinearMap.toMatrix` 抬回
（`toMatrix_matUnit` ＋ `LinearMap.toMatrix_mul`）。另附 `endBasis`：`End V` 的**矩阵单位基**
（`Matrix.stdBasis` 沿 `toMatrix` 运回），它是下一轮「只需查矩阵单位」那一步的载体。

**射程**：本节只给**矩阵单位**上的乘链读数。`eq:12.3` 的等式本身仍缺
（i）按轮换分解的乘积重排 ＋ 不动点因子，（ii）「只需查矩阵单位」的多线性延拓。**均未做。** -/

section MatUnitChain

/-- 矩阵单位的**链条件**：`chainCond l x y` ＝ 沿链 `x → p₀.1/p₀.2 = p₁.1 → ⋯ → y` 的 0/1 条件积。 -/
def chainCond {ι : Type*} [DecidableEq ι] : List (ι × ι) → ι → ι → k
  | [], x, y => if x = y then (1 : k) else 0
  | p :: l, x, y => if x = p.1 then chainCond l p.2 y else 0

#print axioms chainCond

/-- ★★★★ **矩阵单位乘链的矩阵元**：`(∏_{q ∈ l} single q) x y = chainCond l x y`。 -/
theorem mul_prod_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (ι × ι)) (x y : ι) :
    ((l.map (fun q => Matrix.single q.1 q.2 (1 : k))).prod) x y = chainCond k l x y := by
  induction l generalizing x with
  | nil => simp [chainCond, Matrix.one_apply]
  | cons q l ih =>
    rw [List.map_cons, List.prod_cons, chainCond, Matrix.mul_apply]
    by_cases hx : x = q.1
    · rw [if_pos hx]
      refine (Finset.sum_eq_single q.2 ?_ ?_).trans ?_
      · intro z _ hz
        have h1 : ¬ (q.1 = x ∧ q.2 = z) := fun ⟨_, h2⟩ => hz h2.symm
        rw [Matrix.single_apply, if_neg h1, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ q.2) h
      · have h1 : q.1 = x ∧ q.2 = q.2 := ⟨hx.symm, rfl⟩
        rw [Matrix.single_apply, if_pos h1, one_mul]
        exact ih q.2
    · rw [if_neg hx]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      have h1 : ¬ (q.1 = x ∧ q.2 = z) := fun ⟨h, _⟩ => hx h.symm
      rw [Matrix.single_apply, if_neg h1, zero_mul]

#print axioms mul_prod_single_apply

/-- `toMatrix` 把 `matUnit` 送到矩阵单位 `Matrix.single`。 -/
theorem toMatrix_matUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (a c : ι) :
    LinearMap.toMatrix b b (matUnit k V b a c) = Matrix.single a c (1 : k) := by
  ext i j
  rw [LinearMap.toMatrix_apply, matUnit_entry, Matrix.single_apply]
  by_cases h1 : a = i
  · by_cases h2 : c = j
    · simp [h1, h2]
    · simp [h1, h2, Ne.symm h2]
  · simp [h1]

#print axioms toMatrix_matUnit

/-- ★★★★★ **任意长度矩阵单位乘链的迹**：`tr(E_p * ∏_{q ∈ l} E_q) = chainCond l p.2 p.1`。

`eq:12.3` 右端的**一般长度引擎**：首元单独拿出，链条件由 `chainCond` 给出（无循环指标簿记）。 -/
theorem trace_matUnit_mul_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (p : ι × ι) (l : List (ι × ι)) :
    LinearMap.trace k V (matUnit k V b p.1 p.2
        * (l.map (fun q => matUnit k V b q.1 q.2)).prod) = chainCond k l p.2 p.1 := by
  classical
  rw [trace_matUnit_mul]
  have hmat : ∀ l : List (ι × ι),
      LinearMap.toMatrix b b ((l.map (fun q => matUnit k V b q.1 q.2)).prod)
        = (l.map (fun q => Matrix.single q.1 q.2 (1 : k))).prod := by
    intro l
    induction l with
    | nil => simp
    | cons q l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, LinearMap.toMatrix_mul,
        toMatrix_matUnit, ih]
  rw [← LinearMap.toMatrix_apply, hmat, mul_prod_single_apply]

#print axioms trace_matUnit_mul_prod

/-- `End V` 的**矩阵单位基**（把 `Matrix.stdBasis` 沿 `toMatrix` 运回）。 -/
noncomputable def endBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) : Module.Basis (ι × ι) k (Module.End k V) :=
  (Matrix.stdBasis k ι ι).map (LinearMap.toMatrix b b).symm

#print axioms endBasis

/-- 基向量就是矩阵单位：`endBasis b (a, c) = matUnit b a c`。 -/
theorem endBasis_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (a c : ι) :
    endBasis k V b (a, c) = matUnit k V b a c := by
  have h1 : (LinearMap.toMatrix b b).symm (Matrix.single a c (1 : k)) = matUnit k V b a c := by
    have h2 := toMatrix_matUnit (k := k) (V := V) b a c
    rw [← h2, LinearEquiv.symm_apply_apply]
  rw [endBasis, Module.Basis.map_apply, Matrix.stdBasis_eq_single, h1]

#print axioms endBasis_apply

end MatUnitChain

/-! ## §19 ★ **AGPR `lem:12.1.2` 的「等同」**：`T_n(m) = span{T_σ}`（第 519 轮）

AGPR `def:12.1.1`（`raw/AGPR2020.tex:13855`）定义 `T_n(m)` ＝ `m` 个 `n×n` 矩阵的**多线性不变量**空间；
`lem:12.1.2`（`:13862`）说它「is identified with `End_GL(V)(V^{⊗m})`, and it is linearly spanned by
the functions `T_σ`」。§17 已把「张成」做成固定向量形态；本节把它**打包成论文自己的形状**：

```
T_n(m) = span{ T_σ : σ ∈ S_m }
```

**路线（三段，全部机检）**：
1. **⊇**：每个 `T_σ` 都是不变量（§12 的 `tSigma_map_conj` 重述为泛函层）⟹ 张成落在 `T_n(m)` 里。
2. **⊆**：`φ` 不变量 ⟹ 其**对偶向量** `v = E⁻¹φ` 是固定向量（用 §7 配对的 `GL`-等变性
   `⟨g x, g y⟩ = ⟨x,y⟩` ＋ 迹配对非退化把 `g⁻¹v = v` 抬成 `g v = v`）⟹ 由 §17 得
   `v ∈ span{tSigmaVec}` ⟹ 施 `E` 得 `φ ∈ span{E(tSigmaVec)} = span{tSigmaLinear}`（§16）。
3. **附属件**：`conjEnd_comp`／`map_conjEnd_comp`（共轭作用的可逆性）、`dual_eq_of_matUnit`
   （泛函若在矩阵单位纯张量上相同则相等 —— `endBasis` ＋ `Basis.piTensorProduct`）。

**假设诚实登记**：`[Infinite k]` ＋ `[NeZero (Nat.factorial m : k)]`（`m!` 可逆；AGPR 同路线亦限特征 0）。

**射程**：本节给的是**不变量空间**的等同（`lem:12.1.2` 全句）。`eq:12.3` 的等式、
FFT 难半（`thm:12.1.3`）、`(A)→(B)` **均未做**。 -/

section Lem1212Equality

variable (n : ℕ)

/-- AGPR `def:12.1.1` 的 `T_n(m)`：**多线性不变量**（在 `GL_n` 的同时共轭下不变的线性泛函）。 -/
def tnm [Infinite k] : Submodule k
    (Module.Dual k (TensorPower k m (Module.End k (Fin n → k)))) where
  carrier := {φ | ∀ (B B' : Module.End k (Fin n → k)), B ∘ₗ B' = 1 → B' ∘ₗ B = 1 →
    ∀ y, φ (PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') y) = φ y}
  zero_mem' := by
    intro B B' h1 h2 y
    simp
  add_mem' := by
    intro φ ψ hφ hψ B B' h1 h2 y
    simp only [LinearMap.add_apply, hφ B B' h1 h2 y, hψ B B' h1 h2 y]
  smul_mem' := by
    intro c φ hφ B B' h1 h2 y
    simp only [LinearMap.smul_apply, hφ B B' h1 h2 y]

#print axioms tnm

/-- `T_σ` 是**不变量**（§12 的不变性重述为泛函层）。 -/
theorem tSigmaLinear_mem_tnm [Infinite k] (σ : Equiv.Perm (Fin m)) :
    tSigmaLinear k (Fin n → k) m σ ∈ tnm (k := k) (m := m) (n := n) := by
  intro B B' h1 h2 y
  exact tSigma_map_conj k (Fin n → k) m σ B B' h2 y

#print axioms tSigmaLinear_mem_tnm

/-- **两个泛函若在矩阵单位纯张量上相同则相等**（`Basis.piTensorProduct` ＋ `Basis.ext`）。 -/
theorem dual_eq_of_matUnit [Infinite k]
    (F G : Module.Dual k (TensorPower k m (Module.End k (Fin n → k))))
    (h : ∀ p : Fin m → (Fin n × Fin n),
      F (PiTensorProduct.tprod k (fun i => endBasis k (Fin n → k) (Pi.basisFun k (Fin n)) (p i)))
        = G (PiTensorProduct.tprod k (fun i => endBasis k (Fin n → k) (Pi.basisFun k (Fin n)) (p i)))) : F = G := by
  refine (Basis.piTensorProduct (fun _ : Fin m => endBasis k (Fin n → k)
    (Pi.basisFun k (Fin n)))).ext ?_
  intro p
  simpa only [Basis.piTensorProduct_apply] using h p

#print axioms dual_eq_of_matUnit

/-- 逐因子共轭的复合是恒等：`conjEnd B B' ∘ conjEnd B' B = id`（`B B' = 1 = B' B`）。 -/
theorem conjEnd_comp (B B' : Module.End k V) (h1 : B ∘ₗ B' = 1) :
    conjEnd k V B B' ∘ₗ conjEnd k V B' B = LinearMap.id := by
  have h1' : ∀ y, B (B' y) = y := fun y => by
    have h := congrArg (fun g : Module.End k V => g y) h1
    simpa using h
  ext x
  simp only [LinearMap.comp_apply, conjEnd_apply, LinearMap.id_apply, h1']

#print axioms conjEnd_comp

/-- 置换张量幂上的作用是**可逆**的：`map (conj B B') * map (conj B' B) = 1`。 -/
theorem map_conjEnd_comp (m : ℕ) (B B' : Module.End k V) (h1 : B ∘ₗ B' = 1) :
    (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B'))
      * (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B' B)) = 1 := by
  show (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B B'))
      ∘ₗ (PiTensorProduct.map (fun _ : Fin m => conjEnd k V B' B)) = 1
  rw [← PiTensorProduct.map_comp,
    show (fun i : Fin m => conjEnd k V B B' ∘ₗ conjEnd k V B' B)
      = (fun _ => LinearMap.id) from by
      funext i; exact conjEnd_comp k V B B' h1]
  exact PiTensorProduct.map_id

#print axioms map_conjEnd_comp

/-- ★★★★★★ **`lem:12.1.2` 的「等同」（⊆ 方向）**：每个多线性不变量都在 `span{T_σ}` 里。 -/
theorem tnm_le_span [Infinite k] [NeZero (Nat.factorial m : k)]
    {φ : Module.Dual k (TensorPower k m (Module.End k (Fin n → k)))}
    (hφ : φ ∈ tnm (k := k) (m := m) (n := n)) :
    φ ∈ Submodule.span k (Set.range (fun σ : Equiv.Perm (Fin m) =>
      tSigmaLinear k (Fin n → k) m σ)) := by
  classical
  set E := tensorPowerTraceDualEquiv k (Fin n → k) m with hE
  set v := E.symm φ with hv
  have hEv : E v = φ := by rw [hv, LinearEquiv.apply_symm_apply]
  have hcoe : ∀ y, φ y = tensorPowerTraceForm k (Fin n → k) m v y := by
    intro y
    have h := congrArg (fun f => f y) hEv
    simpa only [hE, tensorPowerTraceDualEquiv, LinearMap.BilinForm.toDual_def] using h.symm
  have hfix : ∀ (B B' : Module.End k (Fin n → k)), B ∘ₗ B' = 1 → B' ∘ₗ B = 1 →
      PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') v = v := by
    intro B B' h1 h2
    set g := PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B B') with hg
    set g' := PiTensorProduct.map (fun _ : Fin m => conjEnd k (Fin n → k) B' B) with hg'
    have hgg' : g (g' v) = v := by
      rw [hg, hg', ← Module.End.mul_apply, map_conjEnd_comp (k := k) (V := Fin n → k) m B B' h1]
      simp
    have hleft : ∀ w, tensorPowerTraceForm k (Fin n → k) m v (g w)
        = tensorPowerTraceForm k (Fin n → k) m v w := by
      intro w
      rw [← hcoe (g w), ← hcoe w]
      exact hφ B B' h1 h2 w
    have hadj : ∀ w, tensorPowerTraceForm k (Fin n → k) m (g' v) w
        = tensorPowerTraceForm k (Fin n → k) m v (g w) := by
      intro w
      have hspec := trace_tensorPower_pairing_conj k (Fin n → k) m B B' (g' v) w h2
      rw [hg, hg', tensorPowerTraceForm_apply, tensorPowerTraceForm_apply, ← hspec, hgg']
    have hg'v : g' v = v := by
      refine sub_eq_zero.mp ((tensorPowerTraceForm_nondegenerate k (Fin n → k) m).1
        (g' v - v) (fun w => ?_))
      simp only [LinearMap.sub_apply, map_sub]
      rw [hadj w, hleft w, sub_self]
    calc g v = g (g' v) := by rw [hg'v]
      _ = v := hgg'
  have hspan : v ∈ Submodule.span k
      (Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ)) :=
    (mem_span_tSigmaVec_iff_fixed (k := k) (m := m) (x := v)).mpr hfix
  have hset : (tensorPowerTraceDualEquiv k (Fin n → k) m) ''
      (Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ))
      = Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaLinear k (Fin n → k) m σ) := by
    ext x
    constructor
    · rintro ⟨y, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, (tensorPowerTraceDualEquiv_tSigmaVec (k := k) (V := (Fin n → k)) (m := m) σ).symm⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨_, ⟨σ, rfl⟩, tensorPowerTraceDualEquiv_tSigmaVec (k := k) (V := (Fin n → k)) (m := m) σ⟩
  have hmono : Submodule.span k (Set.range (fun σ : Equiv.Perm (Fin m) =>
        tSigmaVec k (Fin n → k) m σ))
      ≤ Submodule.comap (tensorPowerTraceDualEquiv k (Fin n → k) m).toLinearMap
          (Submodule.span k ((tensorPowerTraceDualEquiv k (Fin n → k) m) ''
            Set.range (fun σ : Equiv.Perm (Fin m) => tSigmaVec k (Fin n → k) m σ))) := by
    rw [Submodule.span_le]
    rintro y ⟨σ, rfl⟩
    exact Submodule.subset_span ⟨tSigmaVec k (Fin n → k) m σ, ⟨σ, rfl⟩, rfl⟩
  have hmem := hmono hspan
  rw [hset] at hmem
  rw [← hEv]
  exact hmem

#print axioms tnm_le_span

/-- ⊇ 方向：每个 `T_σ` 都是不变量，故张成落在 `T_n(m)` 里。 -/
theorem span_tSigmaLinear_le_tnm [Infinite k] :
    Submodule.span k (Set.range (fun σ : Equiv.Perm (Fin m) =>
      tSigmaLinear k (Fin n → k) m σ)) ≤ tnm (k := k) (m := m) (n := n) := by
  rw [Submodule.span_le]
  rintro y ⟨σ, rfl⟩
  exact tSigmaLinear_mem_tnm (k := k) (m := m) (n := n) σ

#print axioms span_tSigmaLinear_le_tnm

/-- ★★★★★★★ **AGPR `lem:12.1.2`（`T_n(m) = span{T_σ}`，逐字形态）**：

多线性不变量空间 `T_n(m)`（`def:12.1.1`）**恰是** `{T_σ : σ ∈ S_m}` 的线性张成。 -/
theorem tnm_eq_span [Infinite k] [NeZero (Nat.factorial m : k)] :
    tnm (k := k) (m := m) (n := n) = Submodule.span k (Set.range (fun σ : Equiv.Perm (Fin m) =>
      tSigmaLinear k (Fin n → k) m σ)) :=
  le_antisymm (fun _ hφ => tnm_le_span (k := k) (m := m) (hφ := hφ))
    (span_tSigmaLinear_le_tnm (k := k) (m := m) (n := n))

#print axioms tnm_eq_span


end Lem1212Equality

/-! ## §20 **`chainCond` 的显式求值**（`eq:12.3` 全循环情形的那一格；第 521 轮）

§18 把任意长度的矩阵单位乘链的迹压成 `chainCond`（递归定义）。本节把它**算成显式 δ 积**：

```
chainCond ((a 0,c 0),…,(a m,c m)) x y = [x = a 0] · ∏_{t<m} [c t = a (t+1)] · [c m = y]
Σ_x chainCond ((a 0,c 0),…,(a m,c m)) x x = (∏_{t<m} [c t = a (t+1)]) · [c m = a 0]
```

**为何是这一格**：`eq:12.3` 的右端是**轮换积的迹**，而轮换积在矩阵单位上给出**首尾相接**的 δ 链；
上面第二条正是「首尾相接后对自由指标求和」的读数（闭合条件 `[c m = a 0]` 自动出现），
即全循环情形所需的那一步。**无划分需求**（全循环只有一块），故这是 §3.1 三格中最便宜的一格。

**射程**：本节只做 δ 链的**求值**。`eq:12.3` 的等式本身仍需（i）多线性延拓（把矩阵单位结论抬到
任意 `X`）与（ii）一般的轮换分解重排；**均未做**。 -/

section ChainCondEval

/-- ★★★★★ **`chainCond` 在 `List.range` 上的求值**（显式连续 δ 积）。 -/
theorem chainCond_range {ι : Type*} [DecidableEq ι] (m : ℕ) (a c : ℕ → ι) (x y : ι) :
    chainCond k ((List.range (m + 1)).map (fun t => (a t, c t))) x y
      = (if x = a 0 then (1 : k) else 0)
        * (Finset.prod (Finset.range m) fun t => (if c t = a (t + 1) then (1 : k) else 0))
        * (if c m = y then 1 else 0) := by
  induction m generalizing x a c with
  | zero =>
    simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil,
      Finset.range_zero, Finset.prod_empty, mul_one, chainCond]
    by_cases h1 : x = a 0 <;> by_cases h2 : c 0 = y <;> simp [h1, h2]
  | succ m ih =>
    have hrange : List.range (m + 1 + 1) = 0 :: (List.range (m + 1)).map (fun t => t + 1) := by
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, List.range_succ_eq_map]
    rw [hrange]
    have hmap : List.map (fun t => (a t, c t)) (List.map (fun t => t + 1) (List.range (m + 1)))
        = List.map (fun t => (a (t + 1), c (t + 1))) (List.range (m + 1)) := by
      rw [List.map_map]
      rfl
    simp only [List.map_cons, hmap, chainCond]
    rw [ih (x := c 0) (a := fun t => a (t + 1)) (c := fun t => c (t + 1)),
      Finset.prod_range_succ', Nat.zero_add]
    by_cases h : x = a 0 <;> simp [h]

#print axioms chainCond_range

/-- ★★★★★ **对角求和 ＝ 闭合的循环 δ 积**：把链的首尾相接（`x = y`）并对 `x` 求和，
闭合条件 `[c m = a 0]` 自动出现。这是全循环情形取迹的那一格。 -/
theorem sum_chainCond_range_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (a c : ℕ → ι) :
    (∑ x : ι, chainCond k ((List.range (m + 1)).map (fun t => (a t, c t))) x x)
      = (Finset.prod (Finset.range m) fun t => (if c t = a (t + 1) then (1 : k) else 0))
        * (if c m = a 0 then 1 else 0) := by
  classical
  rw [Finset.sum_congr rfl (fun x _ => chainCond_range k m a c x x)]
  rw [Finset.sum_eq_single (a 0)]
  · simp
  · intro x _ hx
    have : ¬ (x = a 0) := hx
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ (a 0)) h

#print axioms sum_chainCond_range_diag

end ChainCondEval

/-! ## §21 **全循环的迹公式 ＋ 多线性延拓原理**（`eq:12.3` 的最后一格；第 522 轮）

§20 把矩阵单位的乘链算成了 δ 积。本节补两件，使 `eq:12.3` 的**全循环情形**可以收口：

```
tr(∏_{q∈l} E_q) = Σ_x chainCond l x x                              （迹 ＝ 对角和）
tr(E_{a₀c₀}⋯E_{a_hc_h}) = (∏_{t<h} [cₜ = a_{t+1}]) · [c_h = a₀]     （全循环 δ 积，闭合）
R 多线性、F 线性，若在 ⊗ᵢ E_{pᵢ} 上一致 ⟹ 处处一致                  （多线性延拓原理）
```

**最后一条是「只需查矩阵单位」的机器件**：`R` 取 `X ↦ tr(X₀⋯X_{h-1})`、`F` 取 `tSigma σ`，
即把矩阵单位的读数抬到任意 `X`。证明用 `MultilinearMap.map_sum`（各槽展开成多指标和）
＋ `map_smul_univ`（提出系数积），`F` 一侧用 `Basis.sum_repr` 沿 `Basis.piTensorProduct` 展开，
两侧落到**同一个**多指标和。

**射程**：本节给了全循环情形所需的**全部零件**，但 `eq:12.3` 的**等式本身仍未陈述**（差把
`tSigma σ` 与 `tr(∏ X)` 在矩阵单位上的读数对上、并选对 `σ` 与列表序的对应）；一般轮换分解的
重排亦未做。FFT 难半、`(A)→(B)` 未做。 -/

section FullyCycleTrace

/-- ★★★★★ **矩阵单位乘链的迹 ＝ `chainCond` 的对角和**。 -/
theorem trace_prod_matUnit_list {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (l : List (ι × ι)) :
    LinearMap.trace k V ((l.map (fun q => matUnit k V b q.1 q.2)).prod)
      = ∑ x : ι, chainCond k l x x := by
  classical
  have hmat : LinearMap.toMatrix b b ((l.map (fun q => matUnit k V b q.1 q.2)).prod)
      = (l.map (fun q => Matrix.single q.1 q.2 (1 : k))).prod := by
    induction l with
    | nil => simp
    | cons q l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, LinearMap.toMatrix_mul,
        toMatrix_matUnit, ih]
  rw [LinearMap.trace_eq_matrix_trace (R := k) (M := V) b, hmat, Matrix.trace]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.diag_apply, mul_prod_single_apply]

#print axioms trace_prod_matUnit_list

/-- ★★★★★ **全循环的矩阵单位迹公式**（闭合的循环 δ 积）：

`tr(E_{a₀c₀} ⋯ E_{a_h c_h}) = (∏_{t<h} [cₜ = a_{t+1}]) · [c_h = a₀]`。 -/
theorem trace_prod_matUnit_cyclic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (h : ℕ) (a c : ℕ → ι) :
    LinearMap.trace k V (((List.range (h + 1)).map
        (fun t => matUnit k V b (a t) (c t))).prod)
      = (Finset.prod (Finset.range h) fun t => (if c t = a (t + 1) then (1 : k) else 0))
        * (if c h = a 0 then 1 else 0) := by
  rw [show (List.map (fun t => matUnit k V b (a t) (c t)) (List.range (h + 1)))
      = List.map (fun q : ι × ι => matUnit k V b q.1 q.2)
          (List.map (fun t => (a t, c t)) (List.range (h + 1))) from by
    rw [List.map_map]
    rfl]
  rw [trace_prod_matUnit_list, sum_chainCond_range_diag]

#print axioms trace_prod_matUnit_cyclic

/-- ★★★★★★ **多线性延拓原理（「只需查矩阵单位」）**：多线性泛函 `R` 与线性泛函 `F` 若在
**矩阵单位纯张量** `⊗ᵢ E_{pᵢ}` 上一致，则处处一致。 -/
theorem multilinear_eq_dual_of_matUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V)
    (R : MultilinearMap k (fun _ : Fin m => Module.End k V) k)
    (F : Module.Dual k (TensorPower k m (Module.End k V)))
    (h : ∀ p : Fin m → ι × ι, R (fun i => endBasis k V b (p i))
      = F (PiTensorProduct.tprod k (fun i => endBasis k V b (p i))))
    (X : Fin m → Module.End k V) :
    R X = F (PiTensorProduct.tprod k X) := by
  classical
  have hX : X = fun i => ∑ q : ι × ι, (endBasis k V b).repr (X i) q • endBasis k V b q :=
    funext fun i => ((endBasis k V b).sum_repr (X i)).symm
  have hR : R X = ∑ p : Fin m → ι × ι,
      (∏ i, (endBasis k V b).repr (X i) (p i)) •
        R (fun i => endBasis k V b (p i)) := by
    conv_lhs => rw [hX]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [MultilinearMap.map_smul_univ]
  have hB : PiTensorProduct.tprod k X = ∑ p : Fin m → ι × ι,
      (∏ i, (endBasis k V b).repr (X i) (p i)) •
        PiTensorProduct.tprod k (fun i => endBasis k V b (p i)) := by
    conv_lhs => rw [← (Basis.piTensorProduct (fun _ : Fin m => endBasis k V b)).sum_repr
      (PiTensorProduct.tprod k X)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Basis.piTensorProduct_apply, Basis.piTensorProduct_repr_tprod_apply]
  rw [hR, hB, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul, h p]

#print axioms multilinear_eq_dual_of_matUnit

end FullyCycleTrace

/-! ## §22 **乘链泛函**（`X ↦ tr(X₀⋯X_{m-1})` 作为多线性泛函；第 523 轮）

§21 的延拓原理需要 `R` 是**多线性**泛函。本节把 `X ↦ tr(X₀ * ⋯ * X_{m-1})` 造成 `MultilinearMap`：

```
cycleProdMap := (LinearMap.trace k V).compMultilinearMap (MultilinearMap.mkPiAlgebraFin k m (End V))
⟹  cycleProdMap X = tr((List.ofFn X).prod) = tr(X₀ * ⋯ * X_{m-1})
```

**载体（本轮侦察读数）**：`MultilinearMap.mkPiAlgebraFin`（`Multilinear/Basic.lean:1215`）是
**非交换版**的「全坐标乘积」多线性映射（值为 `(List.ofFn m).prod`），`compMultilinearMap`
（`:796`）把结果过一道线性映射（此处是迹）。**注意 `mkPiAlgebra`（`:1192`）是交换版，不能用于
`Module.End`**。

**射程**：本节只给**对象**。全循环的 `eq:12.3` 收口还需把 §20／§21 的 `List.range`-形态读数
换成 `List.ofFn`／`List.finRange` 形态（`List.ofFn_eq_map` 给的是 `finRange` 而非 `range`，
两者之间**无现成桥**）。 -/

section CycleProdMap

/-- ★★★★★ **乘链泛函**：`X ↦ tr(X₀ * X₁ * ⋯ * X_{m-1})`，作为**多线性**泛函。 -/
noncomputable def cycleProdMap : MultilinearMap k (fun _ : Fin m => Module.End k V) k :=
  (LinearMap.trace k V).compMultilinearMap
    (MultilinearMap.mkPiAlgebraFin k m (Module.End k V))

#print axioms cycleProdMap

/-- 计算律：`cycleProdMap X = tr((List.ofFn X).prod)`。 -/
theorem cycleProdMap_apply (X : Fin m → Module.End k V) :
    cycleProdMap k V m X = LinearMap.trace k V ((List.ofFn X).prod) := rfl

#print axioms cycleProdMap_apply

end CycleProdMap

/-! ## §23 **`chainCond` 的 `Fin`-指标求值**（`cycleProdMap` 形态的桥；第 524 轮）

§22 的 `cycleProdMap` 走 `List.ofFn`（`Fin`-指标），而 §20 的读数是 `List.range`（`ℕ`-指标）。
mathlib **无**现成桥（`List.ofFn_eq_map` 给的是 `finRange`，其 API 很薄），故本节自建：

```
chainCond (l ++ [p]) x y = chainCond l x p.1 · [p.2 = y]                     （拼接律）
chainCond (ofFn g) x y = [x = a₀] · ∏_{i<n} [cᵢ = a_{i+1}] · [cₙ = y]        （Fin-指标求值）
```

**路线**：`List.ofFn_succ'`（末尾追加）＋ 拼接律 ＋ `Fin.prod_univ_castSucc`（末项分离）＋ 归纳。

**射程**：本节只给**求值**。全循环的 `eq:12.3` 收口还需最后一步：把本节的 δ 积与 §14 的
`∏ i, [aᵢ = c_{σ i}]` 在 `Fin`-积上对齐（`σ = finRotate⁻¹`，方向由 §14／§21 共同定死）。 -/

section ChainCondOfFn

/-- ★★★★ **`chainCond` 的拼接律**：末尾追加一个元素 ＝ 旧链终点接新元素行指标，再乘列指标与 `y` 的 δ。 -/
theorem chainCond_concat {ι : Type*} [DecidableEq ι] (l : List (ι × ι)) (p : ι × ι)
    (x y : ι) :
    chainCond k (l ++ [p]) x y
      = chainCond k l x p.1 * (if p.2 = y then (1 : k) else 0) := by
  induction l generalizing x with
  | nil =>
    by_cases h1 : x = p.1 <;> by_cases h2 : p.2 = y <;> simp [chainCond, h1, h2]
  | cons q l ih =>
    simp only [List.cons_append, chainCond]
    rw [ih]
    by_cases h1 : x = q.1 <;> simp [h1]

#print axioms chainCond_concat

/-- ★★★★★ **`chainCond` 在 `List.ofFn` 上的求值**（`Fin`-指标形态）：

`chainCond (ofFn ((a₀,c₀),…,(aₙ,cₙ))) x y = [x = a₀] · ∏_{i<n} [cᵢ = a_{i+1}] · [cₙ = y]`。 -/
theorem chainCond_ofFn {ι : Type*} [DecidableEq ι] {n : ℕ} (g : Fin (n + 1) → ι × ι)
    (x y : ι) :
    chainCond k (List.ofFn g) x y
      = (if x = (g 0).1 then (1 : k) else 0)
        * (Finset.prod Finset.univ fun i : Fin n =>
            (if (g (Fin.castSucc i)).2 = (g i.succ).1 then (1 : k) else 0))
        * (if (g (Fin.last n)).2 = y then 1 else 0) := by
  induction n generalizing y with
  | zero =>
    have hofn : List.ofFn g = [g 0] := by
      have h := List.ofFn_succ' (n := 0) g
      simpa using h
    rw [hofn]
    simp only [chainCond, Finset.univ_eq_empty, Finset.prod_empty, mul_one, Fin.last_zero]
    by_cases h1 : x = (g 0).1 <;> by_cases h2 : (g 0).2 = y <;> simp [h1, h2]
  | succ n ih =>
    have hofn : List.ofFn g
        = (List.ofFn fun i : Fin (n + 1) => g (Fin.castSucc i)).concat (g (Fin.last (n + 1))) :=
      List.ofFn_succ' (n := n + 1) g
    rw [hofn, List.concat_eq_append, chainCond_concat,
      ih (fun i : Fin (n + 1) => g (Fin.castSucc i)) (y := (g (Fin.last (n + 1))).1),
      Fin.prod_univ_castSucc]
    simp only [Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last]
    by_cases h1 : x = (g 0).1 <;> by_cases h2 : (g (Fin.last n).castSucc).2
      = (g (Fin.last (n + 1))).1 <;> simp [h1, h2]

#print axioms chainCond_ofFn

end ChainCondOfFn

/-! ## §24 **`cycleProdMap` 的矩阵单位读数**（`eq:12.3` 全循环的最后两块；第 525 轮）

§23 给了 `Fin`-指标的 `chainCond` 求值。本节把它接到 `cycleProdMap`（§22）与迹上：

```
Σ_x chainCond (ofFn g) x x = (∏_{i<n} [cᵢ = a_{i+1}]) · [cₙ = a₀]        （对角闭合，Fin 形态）
cycleProdMap (fun i => E_{aᵢcᵢ}) = (∏_{i<n} [cᵢ = a_{i+1}]) · [cₙ = a₀]  （RHS 的矩阵单位读数）
```

**这正是 `eq:12.3` 右端在矩阵单位上的读数**（全循环、闭合）。与 §14 的
`tSigma σ (⊗ E_{aᵢcᵢ}) = ∏ i, [aᵢ = c_{σ i}]` 对比：本节的 δ 链是
`∀ i, cᵢ = a_{i+1}`（后继沿 `Fin` 的 `castSucc ↦ succ`、末项回绕到 `0`），
而 §14 是 `∀ i, aᵢ = c_{σ i}` ⟹ 取 `σ = (finRotate (n+1))⁻¹` 即两者一致
（方向由 §14／§21 的读数定死，见 §2.3 的方向定案）。

**射程**：本节只给**两块读数**。`eq:12.3` 全循环的**等式本身**仍差最后一步：把上述
`σ = finRotate⁻¹` 的对应在 `Fin`-积上对齐（需 `finRotate⁻¹ (j.succ) = j.castSucc` 与
`finRotate⁻¹ 0 = last` 两条 `Fin` 引理）。 -/

section CycleProdMatUnit

/-- ★★★★★ **`Fin`-形态的对角闭合**：把 `List.ofFn` 链首尾相接并对 `x` 求和，
闭合条件 `[cₙ = a₀]` 自动出现。 -/
theorem sum_chainCond_ofFn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (g : Fin (n + 1) → ι × ι) :
    (∑ x : ι, chainCond k (List.ofFn g) x x)
      = (Finset.prod Finset.univ fun i : Fin n =>
          (if (g (Fin.castSucc i)).2 = (g i.succ).1 then (1 : k) else 0))
        * (if (g (Fin.last n)).2 = (g 0).1 then 1 else 0) := by
  classical
  rw [Finset.sum_congr rfl (fun x _ => chainCond_ofFn k g x x)]
  rw [Finset.sum_eq_single (g 0).1]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ (g 0).1) h

#print axioms sum_chainCond_ofFn_diag

/-- ★★★★★ **`cycleProdMap` 在矩阵单位上的读数**：
`tr(∏_{i} E_{aᵢcᵢ}) = (∏_{i<n} [cᵢ = a_{i+1}]) · [cₙ = a₀]`（`Fin`-指标、闭合）。 -/
theorem cycleProdMap_matUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (b : Module.Basis ι k V) (a c : Fin (n + 1) → ι) :
    cycleProdMap k V (n + 1) (fun i => matUnit k V b (a i) (c i))
      = (Finset.prod Finset.univ fun i : Fin n =>
          (if c (Fin.castSucc i) = a i.succ then (1 : k) else 0))
        * (if c (Fin.last n) = a 0 then 1 else 0) := by
  classical
  rw [cycleProdMap_apply]
  have hofn : List.ofFn (fun i : Fin (n + 1) => matUnit k V b (a i) (c i))
      = List.map (fun q : ι × ι => matUnit k V b q.1 q.2)
          (List.ofFn (fun i : Fin (n + 1) => (a i, c i))) :=
    List.ofFn_comp' (fun i : Fin (n + 1) => (a i, c i))
      (fun q : ι × ι => matUnit k V b q.1 q.2)
  rw [hofn, trace_prod_matUnit_list, sum_chainCond_ofFn_diag]

#print axioms cycleProdMap_matUnit

end CycleProdMatUnit

/-! ## §25 ★★ **`eq:12.3` 的「全循环」情形（机检）**（第 526 轮）

AGPR `eq:12.3`（`raw/AGPR2020.tex:13868`）把一个 `T_σ` 拆成**按轮换分解的迹之积**。
本节机检它在「`σ` 是**一个全长轮换**」时的取值——右端是**单个**迹单项式：

```
T_{(finRotate (n+1))⁻¹}(X₀,…,Xₙ) = tr(X₀ * X₁ * ⋯ * Xₙ)
```

**这是 `eq:12.3` 的第一个完整机检实例**，也把 §13–§24 的整条链收口：

| 环节 | 件 |
|---|---|
| LHS 的态射 | `tSigmaLinear σ : Dual k (⨂^m (End V))`（§10／§11／§16） |
| LHS 的矩阵单位读数 | `tSigma_tprod_matUnit`：`∏ i, [aᵢ = c_{σ i}]`（§14） |
| RHS 的态射 | `cycleProdMap : MultilinearMap`（§22，`mkPiAlgebraFin` 非交换版） |
| RHS 的矩阵单位读数 | `cycleProdMap_matUnit`（§24，经 §23 的 `Fin`-指标 `chainCond` 求值与 §21 的迹-对角和） |
| 两侧对接 | `multilinear_eq_dual_of_matUnit`（§21 延拓原理） |
| 方向 | `σ = (finRotate (n+1))⁻¹`；由 `finRotate_symm_succ`／`_zero` 给出其作用 |

**方向说明（与 §2.3 的定案一致）**：RHS 的 δ 链是 `∀ i, cᵢ = a_{i+1}`（沿 `castSucc ↦ succ`、
末项回绕到 `0`），§14 的是 `∀ i, aᵢ = c_{σ i}` ⟹ `σ` 必须取**逆旋转**。

**射程**：本节只做**全循环**情形。`eq:12.3` 的一般情形（`σ` 有多个轮换）仍需按
`σ.cycleFactorsFinset` 的 support 划分做乘积重排 ＋ 不动点因子；**未做**。
FFT 难半（`thm:12.1.3`）、`(A)→(B)` 亦未做。 -/

section Eq123FullCycle

/-- `(finRotate (n+1))⁻¹ (j.succ) = j.castSucc`。 -/
theorem finRotate_symm_succ {n : ℕ} (j : Fin n) :
    (finRotate (n + 1))⁻¹ (j.succ) = j.castSucc := by
  change (finRotate (n + 1)).symm (j.succ) = j.castSucc
  rw [Equiv.symm_apply_eq]
  have key := finRotate_of_lt (n := n) (k := j.val) j.isLt
  rw [show j.castSucc = (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) from Fin.ext rfl, key]
  exact Fin.ext rfl

#print axioms finRotate_symm_succ

/-- `(finRotate (n+1))⁻¹ 0 = Fin.last n`。 -/
theorem finRotate_symm_zero {n : ℕ} :
    (finRotate (n + 1))⁻¹ (0 : Fin (n + 1)) = Fin.last n := by
  change (finRotate (n + 1)).symm (0 : Fin (n + 1)) = Fin.last n
  rw [Equiv.symm_apply_eq]
  exact finRotate_last.symm

#print axioms finRotate_symm_zero

/-- ★★★★★★★ **`eq:12.3` 的全循环情形（机检）**：
`T_{(finRotate (n+1))⁻¹}(X₀,…,Xₙ) = tr(X₀ ⋯ Xₙ)`。 -/
theorem tSigma_finRotate_inv_tprod {n : ℕ} (X : Fin (n + 1) → Module.End k V) :
    tSigma k V (n + 1) (finRotate (n + 1))⁻¹ (PiTensorProduct.tprod k X)
      = LinearMap.trace k V ((List.ofFn X).prod) := by
  classical
  refine Eq.symm ?_
  refine multilinear_eq_dual_of_matUnit (k := k) (V := V)
    (b := Module.Free.chooseBasis k V) (m := n + 1)
    (R := cycleProdMap k V (n + 1))
    (F := tSigmaLinear k V (n + 1) (finRotate (n + 1))⁻¹) (X := X) ?_
  intro p
  rw [show (fun i => endBasis k V (Module.Free.chooseBasis k V) (p i))
      = (fun i => matUnit k V (Module.Free.chooseBasis k V) (p i).1 (p i).2) from
    funext fun i => endBasis_apply k V (Module.Free.chooseBasis k V) (p i).1 (p i).2]
  rw [cycleProdMap_matUnit]
  show (Finset.prod Finset.univ fun i : Fin n =>
        (if (p (Fin.castSucc i)).2 = (p i.succ).1 then (1 : k) else 0))
      * (if (p (Fin.last n)).2 = (p 0).1 then 1 else 0)
      = tSigma k V (n + 1) (finRotate (n + 1))⁻¹
          (PiTensorProduct.tprod k fun i =>
            matUnit k V (Module.Free.chooseBasis k V) (p i).1 (p i).2)
  rw [tSigma_tprod_matUnit, Fin.prod_univ_succ, finRotate_symm_zero, mul_comm]
  congr 1
  · simp only [eq_comm]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [finRotate_symm_succ]
    simp only [eq_comm]

#print axioms tSigma_finRotate_inv_tprod

/-- **`eq:12.3` 全循环情形的「多线性形态」**：右端就是「乘积的迹」。 -/
theorem tSigma_finRotate_inv_apply {n : ℕ} (X : Fin (n + 1) → Module.End k V) :
    LinearMap.trace k V ((List.ofFn X).prod)
      = tSigma k V (n + 1) (finRotate (n + 1))⁻¹ (PiTensorProduct.tprod k X) :=
  (tSigma_finRotate_inv_tprod k V X).symm

#print axioms tSigma_finRotate_inv_apply

end Eq123FullCycle

/-! ## §26 **`eq:12.3` 一般情形的两块前置**（第 527 轮）

§25 做了全循环情形。一般情形（`σ` 有多个轮换）的两块前置记录在本节：

**(甲) 归纳骨架（侦察读数，代替原计划的 `cycleFactorsFinset` 机械）**：
mathlib 有现成的**轮换归纳原理** `Equiv.Perm.cycle_induction_on`（`GroupTheory/Perm/Cycle/Factors.lean:790`）：

```
P 1 → (∀ σ, σ.IsCycle → P σ) → (∀ σ τ, Disjoint σ τ → IsCycle σ → P σ → P τ → P (σ * τ)) → P σ
```

⟹ `eq:12.3` 的一般情形**不需要**自建 `Fin m ≃ Σ c, c.support` 型的划分机械，只需三格：
① `σ = 1`（**已机检**：§13 `tSigma_one_tprod`）；
② `σ` 是单个轮换（含其外的不动点）；
③ 两个**不交**的轮换之积（乘性）。

**(乙) ★ 结构性判读（决定 ②③ 的形状）**：右端必须把**平凡轮换（1-循环）也计入**——
即右端 ＝ `∏_{i ∈ fixed} tr(Xᵢ) × ∏_{非平凡轮换 c} tr(∏_{i∈c} Xᵢ)`。因为只有如此
右端才在 `σ ↦ στ`（不交）下**乘性**：`cycles(στ) = cycles(σ) ⊔ cycles(τ)` ✓。
若把不动点排除在积之外，乘性会因「不动点集合在加轮换时缩小」而失效。

**(丙) 本轮件**：`prod_delta_split`——δ 条件积按 `σ.support`／补集分裂，补集上 `σ` 是恒等。
这是 (乙) 在**矩阵单位层**的对应事实（左端 `∏ i, [aᵢ = c_{σ i}]` 按不动点因子化）。

**射程**：本节只给 (甲)(乙) 的判读与 (丙) 一件。②③ 两格**均未做**——它们都需要
「按 support 的两块分解」（`Equiv.piEquivPiSubtypeProd`，`Logic/Equiv/Prod.lean:479`）与
`T` 在该分解下的乘性。FFT 难半、`(A)→(B)` 未做。 -/

section Eq123GeneralPrep

/-- ★★★★ **固定点因子分离**：δ 条件积在 `σ.support` 与其补集上分裂；补集上 `σ i = i`。 -/
theorem prod_delta_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm (Fin m)) (a c : Fin m → ι) :
    (∏ i, (if a i = c (σ i) then (1 : k) else 0))
      = (Finset.prod σ.support (fun i => if a i = c (σ i) then (1 : k) else 0))
        * (Finset.prod σ.supportᶜ (fun i => if a i = c i then (1 : k) else 0)) := by
  classical
  rw [← Finset.prod_mul_prod_compl σ.support
    (fun i => if a i = c (σ i) then (1 : k) else 0)]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Finset.mem_compl] at hi
  have hfix : σ i = i := by
    by_contra hne
    exact hi ((Equiv.Perm.mem_support).mpr hne)
  rw [hfix]

#print axioms prod_delta_split

end Eq123GeneralPrep

/-! ## §27 **乘积按轮换重排**（`eq:12.3` 一般情形的核心组合件；第 528 轮）

一般情形要把 `∏ i, f i` 按 `σ` 的**轮换分解**分组：轮换内的因子归各自轮换，不动点单独成积。

```
σ.cycleFactorsFinset.biUnion (·.support) = σ.support                    （support 覆盖）
∏ i, f i = (∏_{c ∈ cycleFactors} ∏_{i ∈ c.support} f i) · ∏_{fixed} f i  （重排）
```

**证明路线**：`⊆` 用 `mem_cycleFactorsFinset_support_le`；`⊇` 用「被移动的点 `a` 落在
`cycleOf σ a` 的 support 里，而后者属 `cycleFactorsFinset`」（`cycleOf_ne_one_iff_mem_cycleFactorsFinset`
＋ `cycleOf_apply_self`）。重排用 `Finset.prod_biUnion`（其 `PairwiseDisjoint` 由
`cycleFactorsFinset_pairwise_disjoint` 给出：两轮换不交 ⟹ support 不交）＋ `Finset.prod_mul_prod_compl`。

**用途**：这是 `eq:12.3` 在**矩阵单位层**所需的重排——两边的 δ 条件积都按 `σ` 的轮换分组后比较。
对一般 `σ` 的等式本身，还需 `T` 在 support 两块分解下的乘性（`Equiv.piEquivPiSubtypeProd`）。

**射程**：本节只给**组合件**。`eq:12.3` 一般情形（②③ 两格）**未做**；
FFT 难半、`(A)→(B)` 未做。 -/

section CycleRegroup

/-- ★★★★ **轮换 support 的并 ＝ `σ` 的 support**。 -/
theorem biUnion_support_cycleFactorsFinset {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) :
    σ.cycleFactorsFinset.biUnion (fun c => c.support) = σ.support := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro a ha
    obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
    exact Equiv.Perm.mem_cycleFactorsFinset_support_le hc hac
  · intro a ha
    rw [Equiv.Perm.mem_support] at ha
    refine Finset.mem_biUnion.mpr ⟨σ.cycleOf a, ?_, ?_⟩
    · rw [← Equiv.Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset]
      intro h
      rw [Equiv.Perm.cycleOf_eq_one_iff] at h
      exact ha h
    · rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
      exact ha

#print axioms biUnion_support_cycleFactorsFinset

/-- ★★★★★ **乘积按轮换重排**：
`∏ i, f i = (∏_{c ∈ cycleFactors} ∏_{i ∈ c.support} f i) · ∏_{不动点} f i`。 -/
theorem prod_eq_prod_cycles {α : Type*} [DecidableEq α] [Fintype α] (k : Type*) [Field k]
    (σ : Equiv.Perm α) (f : α → k) :
    (∏ i, f i) = (∏ c ∈ σ.cycleFactorsFinset, Finset.prod c.support f)
      * Finset.prod σ.supportᶜ f := by
  classical
  have step1 : (∏ i, f i) = Finset.prod σ.support f * Finset.prod σ.supportᶜ f :=
    (Finset.prod_mul_prod_compl σ.support f).symm
  have step2 : Finset.prod σ.support f
      = ∏ c ∈ σ.cycleFactorsFinset, Finset.prod c.support f := by
    rw [← biUnion_support_cycleFactorsFinset σ]
    refine Finset.prod_biUnion (f := f) ?_
    intro c hc c' hc' hne
    have h1 : Equiv.Perm.Disjoint c c' :=
      Equiv.Perm.cycleFactorsFinset_pairwise_disjoint (f := σ) hc hc' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Equiv.Perm.mem_support] at ha ha'
    rcases h1 a with h | h
    · exact ha h
    · exact ha' h
  rw [step1, step2]

#print axioms prod_eq_prod_cycles

end CycleRegroup

/-! ## §28 ★ **张量幂按子集的两块分解**（`eq:12.3` 一般情形的关键基础设施；第 529 轮）

一般情形的 ②③ 两格都要把 `V^{⊗m}` 按 `σ` 的一个轮换的 support `S` 拆成两块：

```
tensorPowerSplit S : (⨂_{i : Fin m} V) ≃ₗ (⨂_{i ∈ S} V) ⊗ (⨂_{i ∉ S} V)
tensorPowerSplit S (⊗_i v_i) = (⊗_{i∈S} v_i) ⊗ (⊗_{i∉S} v_i)
```

**载体（本轮侦察读数，推翻 v26 §3.1 的旧判读）**：mathlib **有** `⨂` 对 `Sum`-指标的分解——
`PiTensorProduct.tmulEquiv : (⨂ i, M) ⊗ (⨂ i₂, M) ≃ₗ ⨂ (i : ι ⊕ ι₂), M`
（`LinearAlgebra/PiTensorProduct/Basic.lean:896`，附 `tmulEquiv_apply`／`tmulEquiv_symm_apply`），
配 `Equiv.Set.sumCompl`（`Logic/Equiv/Set.lean:307`）与其 `_symm_apply_of_mem`／`_of_notMem` 规格。

**⟹ 修正记录**：v26 §3.1 曾把「自建 `⨂` 对 `Σ`-指标的分块分解」记为本缺口**唯一的真实成本**
（第 512 轮侦察时只看了 `PiTensorProduct/Basic.lean` 的 `def` 列表，漏了 `tmulEquiv` 所在的
`section tmulEquiv`）。实测**两行**即可组出。这是本仓第 5 次「按名字／按文件版式判死」造成的假阻断
（规则 23／L46 的同型），**教训 24**。

**roadmap**：本节只给**分解本身**。②③ 还需：
① `P_σ` 在分解下的形态（`S`-不变时 `P_σ = P_{σ|_S} ⊗ 1`）；
② `tr(A ⊗ B) = tr A · tr B`（`LinearMap.trace_tensorProduct'` 在仓）把它们拼起来。 -/

section TensorPowerSplit

/-- ★★★★★ **张量幂按子集的两块分解**：`⨂_{Fin m} V ≃ ⨂_{i∈S} V ⊗ ⨂_{i∉S} V`。 -/
noncomputable def tensorPowerSplit (S : Finset (Fin m)) :
    TensorPower k m V ≃ₗ[k]
      ((⨂[k] _ : ↥(↑S : Set (Fin m)), V) ⊗[k]
        (⨂[k] _ : ↥((↑S : Set (Fin m))ᶜ), V)) :=
  (PiTensorProduct.reindex k
      (fun _ : ↥(↑S : Set (Fin m)) ⊕ ↥((↑S : Set (Fin m))ᶜ) => V)
      (Equiv.Set.sumCompl (↑S : Set (Fin m)))).symm.trans
    (PiTensorProduct.tmulEquiv k V).symm

#print axioms tensorPowerSplit

/-- ★★★★★ **分解在纯张量上的计算律**。 -/
theorem tensorPowerSplit_tprod (S : Finset (Fin m)) (X : Fin m → V) :
    tensorPowerSplit k V m S (PiTensorProduct.tprod k X)
      = (PiTensorProduct.tprod k (fun i : ↥(↑S : Set (Fin m)) => X i))
        ⊗ₜ[k] (PiTensorProduct.tprod k (fun i : ↥((↑S : Set (Fin m))ᶜ) => X i)) := by
  have hfun : ∀ i : Fin m, Sum.elim (fun i : ↥(↑S : Set (Fin m)) => X i)
      (fun i : ↥((↑S : Set (Fin m))ᶜ) => X i)
      ((Equiv.Set.sumCompl (↑S : Set (Fin m))).symm i) = X i := by
    intro i
    by_cases hi : i ∈ (↑S : Set (Fin m))
    · rw [Equiv.Set.sumCompl_symm_apply_of_mem hi]; rfl
    · rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi]; rfl
  rw [tensorPowerSplit, LinearEquiv.trans_apply]
  have h1 : (PiTensorProduct.reindex k
      (fun _ : ↥(↑S : Set (Fin m)) ⊕ ↥((↑S : Set (Fin m))ᶜ) => V)
      (Equiv.Set.sumCompl (↑S : Set (Fin m)))).symm (PiTensorProduct.tprod k X)
      = PiTensorProduct.tprod k (Sum.elim (fun i : ↥(↑S : Set (Fin m)) => X i)
          (fun i : ↥((↑S : Set (Fin m))ᶜ) => X i)) := by
    rw [LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
    congr 1
    funext i
    exact (hfun i).symm
  rw [h1, PiTensorProduct.tmulEquiv_symm_apply]
  simp

#print axioms tensorPowerSplit_tprod

end TensorPowerSplit

/-! ## §29 **置换算子在块分解下的形态**（`eq:12.3` 一般情形的倒数第二步；第 530 轮）

§28 给了 `V^{⊗m} ≅ V^{⊗S} ⊗ V^{⊗Sᶜ}`。本节给 `P_σ` 在它下面的形态：

```
若 σ 在 S 外逐点恒等，则 tensorPowerSplit S (P_σ (⊗X))
   = (⊗_{i∈S} X (σ⁻¹ i)) ⊗ (⊗_{i∈Sᶜ} X i)
```

即 **`Sᶜ` 那一块不动**（因为 `σ` 固定它），`S` 那一块按 `σ` 重标号。这是把 `P_σ` 拆成
`P_{σ|_S} ⊗ 1` 的机器形态（不必显式定义 `σ|_S`）。

**roadmap（只剩一步）**：接 `LinearMap.trace_tensorProduct'`（`tr(A ⊗ B) = tr A · tr B`）即得
「迹在块分解下乘积化」；再对 `σ` 的轮换逐个用 `cycle_induction_on` 归纳，即得一般 `eq:12.3`。
其中 ② 格（单轮换）还需「任一单轮换与其 `finRotate` 形态共轭」这一层（**未做**）。

**射程**：本节只给**形态**。②③ 两格与一般 `eq:12.3` **均未做**；FFT 难半、`(A)→(B)` 未做。 -/

section SplitReindex

/-- ★★★★★ **置换算子在块分解下的形态**：`σ` 固定 `Sᶜ` ⟹ `Sᶜ` 块不动、`S` 块按 `σ` 重标号。 -/
theorem tensorPowerSplit_reindex (S : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (hσ : ∀ i, i ∉ (↑S : Set (Fin m)) → σ i = i) (X : Fin m → V) :
    tensorPowerSplit k V m S
        (PiTensorProduct.reindex k (fun _ : Fin m => V) σ (PiTensorProduct.tprod k X))
      = (PiTensorProduct.tprod k (fun i : ↥(↑S : Set (Fin m)) => X (σ.symm ↑i)))
        ⊗ₜ[k] (PiTensorProduct.tprod k (fun i : ↥((↑S : Set (Fin m))ᶜ) => X ↑i)) := by
  rw [PiTensorProduct.reindex_tprod, tensorPowerSplit_tprod]
  congr 1
  congr 1
  funext i
  have hi : (↑i : Fin m) ∉ (↑S : Set (Fin m)) := i.2
  have hfix : σ.symm (↑i) = ↑i := by
    rw [Equiv.symm_apply_eq]
    exact (hσ ↑i hi).symm
  rw [hfix]

#print axioms tensorPowerSplit_reindex

end SplitReindex

/-! ## §30 **迹在块分解下的乘积化**（`eq:12.3` 一般情形的接线；第 531 轮）

§28 给了块分解、§29 给了 `P_σ` 在它下面的形态。本节把它们与迹乘法接起来：

```
tr_{V^{⊗m}} ( e⁻¹ ∘ (A₁ ⊗ A₂) ∘ e ) = tr A₁ · tr A₂        （e = tensorPowerSplit S）
```

**证明**：`LinearMap.trace_conj'`（迹在共轭下不变）＋ `LinearMap.trace_tensorProduct'`
（`tr(A ⊗ B) = tr A · tr B`）——两件都在仓，本节只是**接线**。

**roadmap（剩余）**：
① 还需 `Φ`（识别 ①）与块分解的相容性，即 `Φ_m` 在两边块分解下 ＝ `Φ_S ⊗ Φ_{Sᶜ}`；
② ② 格（单轮换）需「任一单轮换与其 `finRotate` 形态共轭」；
③ 再由 `cycle_induction_on` 归纳。

**射程**：本节只给**接线**。一般 `eq:12.3` **未做**；FFT 难半、`(A)→(B)` 未做。 -/

section SplitTrace

/-- ★★★★★ **迹在块分解下的乘积化**：`tr(e⁻¹ ∘ (A₁ ⊗ A₂) ∘ e) = tr A₁ · tr A₂`。 -/
theorem trace_tensorPowerSplit_map (S : Finset (Fin m))
    (A₁ : Module.End k (⨂[k] _ : ↥(↑S : Set (Fin m)), V))
    (A₂ : Module.End k (⨂[k] _ : ↥((↑S : Set (Fin m))ᶜ), V)) :
    LinearMap.trace k (TensorPower k m V)
        ((tensorPowerSplit k V m S).symm.toLinearMap
          ∘ₗ (TensorProduct.map A₁ A₂)
          ∘ₗ (tensorPowerSplit k V m S).toLinearMap)
      = LinearMap.trace k _ A₁ * LinearMap.trace k _ A₂ := by
  show LinearMap.trace k (TensorPower k m V)
      ((tensorPowerSplit k V m S).symm.conj (TensorProduct.map A₁ A₂)) = _
  rw [LinearMap.trace_conj', LinearMap.trace_tensorProduct']

#print axioms trace_tensorPowerSplit_map

end SplitTrace

/-! ## §31 **识别 ① 的任意有限指标版**（块分解与 `Φ` 的对接入口；第 532 轮）

§1 的 `tensorPowerEndEquiv` 只对 `Fin m`。块分解后 `S`／`Sᶜ` 是**子类型**指标，
故 ①（`Φ` 与块分解的相容性）需要任意 `Fintype` 指标的版本——同一载体
`PiTensorProduct.piTensorHomEquiv` 的常值族特化，**一行**：

```
piTensorEndEquiv : (⨂_{i∈ι} End V) ≃ₗ End(⨂_{i∈ι} V)   （任意 [Fintype ι]）
piTensorEndEquiv (⊗ᵢ fᵢ) = PiTensorProduct.map f
```

另附块分解在 `V := End V` 上的特化（纯张量形态），这是 ① 对接的入口。

**roadmap（剩余）**：① 的实体＝相容性
`Φ_m ∘ (split End)⁻¹ = (split V)⁻¹ ∘ TensorProduct.map (Φ_S ·) (Φ_{Sᶜ} ·)`
（**未做**）；② 单轮换的共轭层（未做）；③ `cycle_induction_on` 归纳（未做）。

**射程**：本节只给**载体**。一般 `eq:12.3` **未做**；FFT 难半、`(A)→(B)` 未做。 -/

section PiTensorEndEquivGeneral

/-- ★★★★★ **识别 ①（任意有限指标版）**：`(⨂_{i∈ι} End V) ≃ₗ End(⨂_{i∈ι} V)`。 -/
noncomputable def piTensorEndEquiv {ι : Type*} [Fintype ι] :
    (⨂[k] _ : ι, Module.End k V) ≃ₗ[k] Module.End k (⨂[k] _ : ι, V) :=
  PiTensorProduct.piTensorHomEquiv k (fun _ : ι => V) (fun _ : ι => V)

#print axioms piTensorEndEquiv

/-- 纯张量上的计算律：`⊗ᵢ fᵢ ↦ PiTensorProduct.map f`。 -/
theorem piTensorEndEquiv_tprod {ι : Type*} [Fintype ι] (f : ι → Module.End k V) :
    piTensorEndEquiv k V (PiTensorProduct.tprod k f) = PiTensorProduct.map f :=
  PiTensorProduct.piTensorHomEquiv_tprod f

#print axioms piTensorEndEquiv_tprod

/-- 块分解在 `V := End V` 上的特化（纯张量形态）。 -/
theorem tensorPowerSplit_end_tprod (S : Finset (Fin m)) (f : Fin m → Module.End k V) :
    tensorPowerSplit k (Module.End k V) m S (PiTensorProduct.tprod k f)
      = (PiTensorProduct.tprod k (fun i : ↥(↑S : Set (Fin m)) => f ↑i))
        ⊗ₜ[k] (PiTensorProduct.tprod k (fun i : ↥((↑S : Set (Fin m))ᶜ) => f ↑i)) :=
  tensorPowerSplit_tprod k (Module.End k V) m S f

#print axioms tensorPowerSplit_end_tprod

end PiTensorEndEquivGeneral

/-! ## §32 **格 ③ 的反例：乘性 `T_{στ} = T_σ · T_τ` 不成立**（第 533 轮；v27 §3.1 计划修正）

v27 §3.1 把一般 `eq:12.3` 的骨架定在 `Equiv.Perm.cycle_induction_on` 上，其第三步要求
`Disjoint σ τ` 时 `T_{στ} = T_σ · T_τ`（v27 §3.1 的 ★ 判读、§16.2 的「1-循环必须计入」）。

本节给**反例**（机检）：取 `m = 4`、`σ = (0 1)`、`τ = (2 3)`——两者均为单轮换、互不交——
以及矩阵单位纯张量 `⊗ E_{aᵢcᵢ}`，其中 `a = (0,1,0,1)`、`c = (1,0,1,0)`。由 §14 的
`tSigma_tprod_matUnit`（`T_σ(⊗E_{aᵢcᵢ}) = ∏ i, [aᵢ = c_{σ i}]`）直接算出

```
T_σ = 0,   T_τ = 0,   T_{στ} = 1   ⟹   T_{στ} = 1 ≠ 0 = T_σ · T_τ
```

**根因（不动点因子）**：`σ` 固定 `2, 3`，故 `T_σ` 的 δ 积含 `[a₂ = c₂][a₃ = c₃]`；`τ` 固定 `0, 1`，
故 `T_τ` 含 `[a₀ = c₀][a₁ = c₁]`；而 `στ = (0 1)(2 3)` **没有**不动点，其 δ 积完全不含这四个条件。
把 1-循环计入右端（v27 §16.2 的判读）不救乘性，原因是 `fix(στ) = fix σ ∩ fix τ`，
而乘积给的是 `fix σ` 与 `fix τ` 上的因子**各自**出现。

**后果（只否定计划，不否定 `eq:12.3` 本身）**：一般情形**不能**用 `cycle_induction_on` 的乘性步。
正确结构有两条：(i) AGPR `lem:12.1.2` 证明所用的**多线性 ＋ 矩阵单位**路线
（`raw/AGPR2020.tex:13883` 逐字：「since the identity is multilinear, it is enough to prove it on
the decomposable tensors」；机器件已在仓：`multilinear_eq_dual_of_matUnit`、
`dual_eq_of_matUnit`、`tSigma_tprod_matUnit`）；(ii) **逐轮换剥离**（ground set 缩小的归纳，
用 `Equiv.Perm.decomposeFin`）。矩阵单位层的重排已由 §26／§27 的
`prod_delta_split`、`prod_eq_prod_cycles` 备好，故取 (i)。

**射程**：本节只给**反例**。`eq:12.3` 一般情形**未做**；FFT 难半、`(A)→(B)` 未做；
`S'^N ⊆ Z` 未证；`H2` 仍不是定理。 -/

section Grid3Counterexample

/-- ★★★ **格 ③ 不成立**（`Disjoint σ τ` 时 `T_{στ} ≠ T_σ · T_τ`）。

取 `σ = (0 1)`、`τ = (2 3)`（单轮换、互不交）与矩阵单位纯张量
`⊗ᵢ E_{aᵢ cᵢ}`，`a = (0,1,0,1)`、`c = (1,0,1,0)`：两侧分别为 `1` 与 `0 · 0`。
故 `cycle_induction_on` 的乘性步**不可用**于 `eq:12.3` 的一般情形。 -/
theorem tSigma_mul_ne_prod :
    ∃ (σ τ : Equiv.Perm (Fin 4)) (a c : Fin 4 → Fin 2),
      σ.IsCycle ∧ τ.IsCycle ∧ Equiv.Perm.Disjoint σ τ ∧
      tSigma ℚ (Fin 2 → ℚ) 4 (σ * τ)
          (PiTensorProduct.tprod ℚ (fun i => matUnit ℚ (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2))
            (a i) (c i)))
        ≠ tSigma ℚ (Fin 2 → ℚ) 4 σ
            (PiTensorProduct.tprod ℚ (fun i => matUnit ℚ (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2))
              (a i) (c i)))
          * tSigma ℚ (Fin 2 → ℚ) 4 τ
            (PiTensorProduct.tprod ℚ (fun i => matUnit ℚ (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2))
              (a i) (c i))) := by
  refine ⟨Equiv.swap 0 1, Equiv.swap 2 3, ![0, 1, 0, 1], ![1, 0, 1, 0],
    Equiv.Perm.isCycle_swap (by decide), Equiv.Perm.isCycle_swap (by decide), ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [Equiv.swap_apply_def]
  · intro hcontra
    have hσ : tSigma ℚ (Fin 2 → ℚ) 4 (Equiv.swap (0 : Fin 4) 1)
        (PiTensorProduct.tprod ℚ (fun i => matUnit ℚ (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2))
          (![0, 1, 0, 1] i) (![1, 0, 1, 0] i))) = 0 := by
      rw [tSigma_tprod_matUnit, Fin.prod_univ_four]
      simp [Equiv.swap_apply_def]
    have hτ : tSigma ℚ (Fin 2 → ℚ) 4 (Equiv.swap (2 : Fin 4) 3)
        (PiTensorProduct.tprod ℚ (fun i => matUnit ℚ (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2))
          (![0, 1, 0, 1] i) (![1, 0, 1, 0] i))) = 0 := by
      rw [tSigma_tprod_matUnit, Fin.prod_univ_four]
      simp [Equiv.swap_apply_def]
    have hστ : tSigma ℚ (Fin 2 → ℚ) 4 ((Equiv.swap (0 : Fin 4) 1) * (Equiv.swap 2 3))
        (PiTensorProduct.tprod ℚ (fun i => matUnit ℚ (Fin 2 → ℚ) (Pi.basisFun ℚ (Fin 2))
          (![0, 1, 0, 1] i) (![1, 0, 1, 0] i))) = 1 := by
      rw [tSigma_tprod_matUnit, Fin.prod_univ_four]
      simp [Equiv.swap_apply_def]
    rw [hσ, hτ, hστ] at hcontra
    norm_num at hcontra

#print axioms tSigma_mul_ne_prod

end Grid3Counterexample

/-! ## §33 **轮换枚举**（`eq:12.3` 一般情形右端的指标载体；第 533 轮）

一般情形右端每个轮换 `c` 的因子是「沿轮换次序的乘链之迹」。写下「轮换次序」需要一个枚举
`Fin h ≃ ↥c.support`（`h = #c.support`）。本节取

```
e k := (c⁻¹ ^ k) x₀          （x₀ ∈ c.support）
```

**方向（沿 `c⁻¹` 而非 `c`，§12.1 的判读）**：如此 `e` 的循环后继恰是 `c⁻¹`，故链条件写作
`[c_j = a_{c⁻¹ j}]`，重标号（`j ↦ c j`）后即 `[a_i = c_{c i}] = [a_i = c_{σ i}]`——与 §14 的
`tSigma_tprod_matUnit` 左端**逐字对齐**。所以 `cycEnum_step` 的形态是
`c⁻¹ (e k) = e ⟨(k+1) % #support⟩`（用 `%` 显式形态而不用 `finRotate`：后者会把
`c.support.card` 放进 `Fin` 的类型，触发依赖重写失败——本轮实测）。

**侦察读数（本 pin 逐条 `#check`，全部命中）**：`Equiv.Perm.mem_support`、
`coe_support_eq_set_support`、`IsCycle.isCycleOn`、`IsCycle.two_le_card_support`、
`isCycleOn_inv`、`IsCycleOn.injOn_pow_apply`、`IsCycleOn.range_pow`、
`IsCycleOn.pow_card_apply`、`IsCycleOn.pow_apply_eq_pow_apply`（`≡ [MOD #s]`）、`Nat.mod_modEq`。

**用途**：`cycEnum` 是右端泛函的指标载体（`cycleProdMap` 沿 `reindex`／`domDomCongr` 搬到
`↥c.support` 上时要它）；`cycEnum_step` 是矩阵单位上把链条件变成 `[a_i = c_{σ i}]` 的那一步。

**射程**：本节只给**枚举**。右端泛函的拼接（每轮换因子 ＋ 多块胶水）**未做**；
`eq:12.3` 一般情形未做；FFT 难半、`(A)→(B)` 未做。 -/

section CycleEnum

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `c.support` 在 `c⁻¹` 下封闭。 -/
theorem inv_mem_support {c : Equiv.Perm α} {a : α} (h : a ∈ c.support) : c⁻¹ a ∈ c.support := by
  rw [Equiv.Perm.mem_support] at h ⊢
  intro hh
  have h1 : c⁻¹ a = a := by rw [← hh]; simp
  exact h (by rw [← h1]; exact hh)

#print axioms inv_mem_support

/-- 沿 `c⁻¹` 迭代仍在 `c.support` 内。 -/
theorem pow_inv_mem_support {c : Equiv.Perm α} {x₀ : α} (hx₀ : x₀ ∈ c.support) (k : ℕ) :
    (c⁻¹ ^ k) x₀ ∈ c.support := by
  induction k with
  | zero => simpa using hx₀
  | succ k ih => rw [pow_succ']; exact inv_mem_support ih

#print axioms pow_inv_mem_support

/-- 枚举函数：`k ↦ (c⁻¹ ^ k) x₀`。 -/
def cycEnumFun (c : Equiv.Perm α) (x₀ : α) (hx₀ : x₀ ∈ c.support) :
    Fin c.support.card → ↥c.support :=
  fun k => ⟨(c⁻¹ ^ (k : ℕ)) x₀, pow_inv_mem_support hx₀ k⟩

#print axioms cycEnumFun

/-- `c⁻¹` 在 `c.support` 上是轮换。 -/
theorem isCycleOn_inv_support (c : Equiv.Perm α) (hc : c.IsCycle) :
    c⁻¹.IsCycleOn (↑c.support : Set α) := by
  rw [Equiv.Perm.coe_support_eq_set_support]
  exact Equiv.Perm.isCycleOn_inv.mpr hc.isCycleOn

#print axioms isCycleOn_inv_support

theorem cycEnumFun_injective (c : Equiv.Perm α) (hc : c.IsCycle) (x₀ : α)
    (hx₀ : x₀ ∈ c.support) : Function.Injective (cycEnumFun c x₀ hx₀) := by
  intro k l hkl
  have hs := isCycleOn_inv_support c hc
  have hinj := hs.injOn_pow_apply hx₀
  refine Fin.ext (hinj k.isLt l.isLt ?_)
  exact Subtype.ext_iff.mp hkl

#print axioms cycEnumFun_injective

theorem cycEnumFun_surjective (c : Equiv.Perm α) (hc : c.IsCycle) (x₀ : α)
    (hx₀ : x₀ ∈ c.support) : Function.Surjective (cycEnumFun c x₀ hx₀) := by
  intro y
  have hs := isCycleOn_inv_support c hc
  have hcard : 0 < c.support.card := lt_of_lt_of_le (by decide : 0 < 2) hc.two_le_card_support
  have hrange : Set.range (fun n : ℕ => (c⁻¹ ^ n) x₀) = (↑c.support : Set α) :=
    hs.range_pow c.support.finite_toSet hx₀
  have hy : (y : α) ∈ Set.range (fun n : ℕ => (c⁻¹ ^ n) x₀) := by
    rw [hrange]; exact y.2
  obtain ⟨n, hn⟩ := hy
  refine ⟨⟨n % c.support.card, Nat.mod_lt _ hcard⟩, ?_⟩
  apply Subtype.ext
  show (c⁻¹ ^ (n % c.support.card)) x₀ = (y : α)
  rw [← hn]
  exact (hs.pow_apply_eq_pow_apply hx₀).mpr (Nat.mod_modEq n c.support.card)

#print axioms cycEnumFun_surjective

/-- ★★★★★ **轮换枚举** `Fin #c.support ≃ ↥c.support`：`k ↦ (c⁻¹ ^ k) x₀`。 -/
noncomputable def cycEnum (c : Equiv.Perm α) (hc : c.IsCycle) (x₀ : α)
    (hx₀ : x₀ ∈ c.support) : Fin c.support.card ≃ ↥c.support :=
  Equiv.ofBijective (cycEnumFun c x₀ hx₀)
    ⟨cycEnumFun_injective c hc x₀ hx₀, cycEnumFun_surjective c hc x₀ hx₀⟩

#print axioms cycEnum

@[simp] theorem cycEnum_apply (c : Equiv.Perm α) (hc : c.IsCycle) (x₀ : α)
    (hx₀ : x₀ ∈ c.support) (k : Fin c.support.card) :
    (cycEnum c hc x₀ hx₀ k : α) = (c⁻¹ ^ (k : ℕ)) x₀ := rfl

#print axioms cycEnum_apply

/-- ★★★★★ **枚举与 `c⁻¹` 的相容（循环后继形态）**：`c⁻¹ (e k) = e ⟨(k+1) % #support⟩`。

这正是右端「沿轮换次序」的链条件：`j = e k` 时后继是 `c⁻¹ j`，故链条件为
`[c_j = a_{c⁻¹ j}]` ⟺ `[a_j = c_{c j}]`（§12.1 的方向判读）。用 `% #support` 的显式形态
（不用 `finRotate`）以避免 `c.support.card` 出现在类型的依赖重写。 -/
theorem cycEnum_step (c : Equiv.Perm α) (hc : c.IsCycle) (x₀ : α) (hx₀ : x₀ ∈ c.support)
    (k : Fin c.support.card) :
    c⁻¹ (cycEnum c hc x₀ hx₀ k)
      = cycEnum c hc x₀ hx₀
          ⟨((k : ℕ) + 1) % c.support.card,
            Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 2) hc.two_le_card_support)⟩ := by
  show c⁻¹ ((c⁻¹ ^ (k : ℕ)) x₀) = (c⁻¹ ^ (((k : ℕ) + 1) % c.support.card)) x₀
  rw [show c⁻¹ ((c⁻¹ ^ (k : ℕ)) x₀) = (c⁻¹ * c⁻¹ ^ (k : ℕ)) x₀ from rfl, ← pow_succ']
  exact (isCycleOn_inv_support c hc).pow_apply_eq_pow_apply hx₀ |>.mpr
    (Nat.mod_modEq ((k : ℕ) + 1) c.support.card).symm

#print axioms cycEnum_step

end CycleEnum

/-! ## §34 **轮换因子的两件**：support 上 `σ = c` ＋ 全循环矩阵单位的迹（第 535 轮）

`eq:12.3` 右端每个轮换因子的矩阵单位读数是「沿轮换次序的乘链之迹」。本节补两件：

```
σ x = c x                          （x ∈ c.support，c ∈ σ.cycleFactorsFinset）—— 一行
tr(∏_{k<n+1} E_{g k}) = ∏_{i<n} [cᵢ = a_{i+1}] · [c_n = a₀]      （闭合循环的 δ 积）
```

第一件用 mathlib 的 `Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff`
（`GroupTheory/Perm/Cycle/Factors.lean:717`：`c = g.cycleOf x ↔ x ∈ c.support`）＋
`cycleOf_apply_self`；第二件用 §21 的 `trace_prod_matUnit_list`（迹 ＝ 对角和）＋
§23 的 `chainCond_ofFn`（`Fin`-指标求值）＋ 对 `x` 的和只取 `x = (g 0).1` 一项。

**用途**：第一件把 §33 的枚举给出的链条件 `[c_j = a_{c⁻¹ j}]` 换成 `[a_i = c_{σ i}]`；
第二件给出右端因子在矩阵单位上的闭式。两者合起来即「右端在矩阵单位上 ＝ §14 的左端」。

**射程**：本节只给**两件**。右端泛函的拼接（每轮换因子乘起来成 `⊗^m(End V)` 上一个泛函）
**未做**；`eq:12.3` 一般情形未做；FFT 难半、`(A)→(B)` 未做。 -/

section CycleFactorMatUnit

/-- ★★★★★ **轮换因子在其 support 上等于 `σ`**：`x ∈ c.support`，`c ∈ σ.cycleFactorsFinset` ⟹ `σ x = c x`。 -/
theorem apply_eq_of_mem_cycleFactorsFinset {α : Type*} [DecidableEq α] [Fintype α]
    {σ c : Equiv.Perm α} (hc : c ∈ σ.cycleFactorsFinset) {x : α} (hx : x ∈ c.support) :
    σ x = c x := by
  have h1 : c = σ.cycleOf x :=
    (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c hc x).mpr hx
  rw [h1, Equiv.Perm.cycleOf_apply_self]

#print axioms apply_eq_of_mem_cycleFactorsFinset

/-- ★★★★★ **全循环矩阵单位乘链的迹**（`Fin (n+1)` 形态）：闭合循环的 δ 积
`∏_{i<n} [cᵢ = a_{i+1}] · [c_n = a₀]`。 -/
theorem trace_prod_matUnit_ofFn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) {n : ℕ} (g : Fin (n + 1) → ι × ι) :
    LinearMap.trace k V ((List.ofFn g).map (fun q => matUnit k V b q.1 q.2)).prod
      = (∏ i : Fin n, (if (g i.castSucc).2 = (g i.succ).1 then (1 : k) else 0))
        * (if (g (Fin.last n)).2 = (g 0).1 then (1 : k) else 0) := by
  rw [trace_prod_matUnit_list]
  simp only [chainCond_ofFn]
  rw [Finset.sum_eq_single (g 0).1]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

#print axioms trace_prod_matUnit_ofFn

end CycleFactorMatUnit

/-! ## §35 **A′ 的块划分（载体 1/2）**（第 536 轮）

`eq:12.3` 一般情形的右端是「按 `σ` 的轮换分组」的乘积：非平凡轮换各一块（块内沿轮换次序
求乘链之迹），不动点各自一块（因子 `tr Xᵢ`）。本节给这块划分的**指标载体**：

```
BlockIdx σ := ↥σ.cycleFactorsFinset ⊕ ↥(σ.supportᶜ)      （轮换块 ＋ 不动点块）
blockBeta σ (inl c) := ↥c.support,   blockBeta σ (inr i) := Unit
slotVal    : (Σ x, blockBeta σ x) → Fin n,   ⟨inl c, j⟩ ↦ ↑j,  ⟨inr i, ()⟩ ↦ ↑i
slotVal_injective : 单射（用 cycleFactorsFinset_pairwise_disjoint ＋ support_le ＋ mem_compl）
```

**★ 侦察读数（决定 A′ 便宜，L46／L47）**：mathlib 有**多线性映射的复合**
`MultilinearMap.compMultilinearMap`（`LinearAlgebra/Multilinear/Basic.lean:415`）：
给定 `g : MultilinearMap R M₁ M₂` 与每槽一个多线性映射 `f i : MultilinearMap R (N i) (M₁ i)`，
得**指标类型为 `Σ i, β i`** 的多线性映射 `m ↦ g (f₁ m₁⋯) (f₂ m₂⋯) ⋯`。配 `domDomCongr`
（`:674`，`toFun v = m (v ∘ σ)`）即可把「每轮换一个 `cycleProdMap`（§22）＋ 外层 `mkPiAlgebra`
（`:1215` 的交换版 `:1192` 已 `#check`：`mkPiAlgebra` 要求 `CommSemiring A`——取 `A = k` 故可用）」拼成
`Fin m` 上的**一个**多线性泛函。**⟹ A′ 不需要任何张量幂的多块分解**（v27 §3.1 格 ① 与 §28 的
`tensorPowerSplit` 都不在路径上）。

**射程**：本节只给**指标载体与单射**。满射／`Σ`-型到 `Fin m` 的等价、`blockMap`（每块的多线性因子）、
以及 `R_σ` 本体的拼接**未做**；`eq:12.3` 一般情形未做；FFT 难半、`(A)→(B)` 未做。 -/

section BlockPartition

open Equiv.Perm

/-- 块指标：`inl c` ＝ 一个非平凡轮换，`inr i` ＝ 一个不动点。 -/
abbrev BlockIdx {n : ℕ} (σ : Equiv.Perm (Fin n)) : Type :=
  ↥σ.cycleFactorsFinset ⊕ ↥(σ.supportᶜ)

#print axioms BlockIdx

/-- 块的槽类型：轮换块是 `↥c.support`，不动点块是 `Unit`。 -/
def blockBeta {n : ℕ} (σ : Equiv.Perm (Fin n)) : BlockIdx σ → Type
  | Sum.inl c => ↥(c.1.support)
  | Sum.inr _ => Unit

#print axioms blockBeta

/-- 槽到 `Fin n` 的值映射。 -/
def slotVal {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Σ x : BlockIdx σ, blockBeta σ x) → Fin n
  | ⟨Sum.inl c, j⟩ => ↑(show ↥(c.1.support) from j)
  | ⟨Sum.inr i, _⟩ => ↑i

#print axioms slotVal

theorem slotVal_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (slotVal σ) := by
  rintro ⟨x, j⟩ ⟨y, j'⟩ h
  match x, y with
  | Sum.inl c, Sum.inl c' =>
    have hj : (↑(show ↥(c.1.support) from j) : Fin n) = ↑(show ↥(c'.1.support) from j') := h
    have h1 : (↑(show ↥(c.1.support) from j) : Fin n) ∈ c.1.support :=
      (show ↥(c.1.support) from j).2
    have h2 : (↑(show ↥(c'.1.support) from j') : Fin n) ∈ c'.1.support :=
      (show ↥(c'.1.support) from j').2
    have hcc : c = c' := by
      by_contra hne
      have hdisj : Disjoint c.1 c'.1 :=
        cycleFactorsFinset_pairwise_disjoint σ c.2 c'.2 (fun hceq => hne (Subtype.ext hceq))
      have hne1 : c.1 (↑(show ↥(c.1.support) from j)) ≠ ↑(show ↥(c.1.support) from j) :=
        mem_support.mp h1
      have hne2 : c'.1 (↑(show ↥(c.1.support) from j)) ≠ ↑(show ↥(c.1.support) from j) := by
        rw [hj]; exact mem_support.mp h2
      rcases hdisj (↑(show ↥(c.1.support) from j)) with hh | hh
      · exact hne1 hh
      · exact hne2 hh
    subst hcc
    have : (show ↥(c.1.support) from j) = (show ↥(c.1.support) from j') := Subtype.ext hj
    obtain rfl : j = j' := this
    rfl
  | Sum.inl c, Sum.inr i =>
    have h1 : (↑(show ↥(c.1.support) from j) : Fin n) ∈ σ.support :=
      mem_cycleFactorsFinset_support_le c.2 (show ↥(c.1.support) from j).2
    have hfin : (↑(show ↥(c.1.support) from j) : Fin n) = ↑i := h
    rw [hfin] at h1
    exact absurd h1 (Finset.mem_compl.mp i.2)
  | Sum.inr i, Sum.inl c =>
    have h1 : (↑(show ↥(c.1.support) from j') : Fin n) ∈ σ.support :=
      mem_cycleFactorsFinset_support_le c.2 (show ↥(c.1.support) from j').2
    have hfin : (↑i : Fin n) = ↑(show ↥(c.1.support) from j') := h
    rw [← hfin] at h1
    exact absurd h1 (Finset.mem_compl.mp i.2)
  | Sum.inr i, Sum.inr i' =>
    have : (i : Fin n) = (i' : Fin n) := h
    obtain rfl : i = i' := Subtype.ext this
    obtain rfl : j = j' := by
      have hs : Subsingleton (blockBeta σ (Sum.inr i)) :=
        ⟨fun a b => by cases a; cases b; rfl⟩
      exact @Subsingleton.elim _ hs _ _
    rfl

#print axioms slotVal_injective

end BlockPartition

/-! ## §36 **A′ 收口：`R_σ` 一个对象即成**（第 537 轮）

§35 给了块划分的指标载体；本节把它拼成**一个**多线性泛函（v27 §3.1 A′ 的实体）：

```
cycBlockMap  : MultilinearMap k (↥c.support → End V) k := (cycleProdMap k V #c.support).domDomCongr (cycEnum …)
traceSlotMap : MultilinearMap k (Unit → End V) k          := v ↦ tr (v ())
blockMap σ x : MultilinearMap k (blockBeta σ x → End V) k  （inl c ↦ cycBlockMap，inr i ↦ traceSlotMap）
blockEquiv σ : (Σ x : BlockIdx σ, blockBeta σ x) ≃ Fin n   （单射 §35 ＋ 满射 slotVal_surjective）
sigmaRMap σ  : MultilinearMap k (Fin n → End V) k
             := (compMultilinearMap (mkPiAlgebra k (BlockIdx σ) k) (blockMap σ)).domDomCongr (blockEquiv σ)
```

**值**（`sigmaRMap_apply`）：`sigmaRMap σ X = ∏ x : BlockIdx σ, blockMap σ x (fun b => X (slotVal σ ⟨x,b⟩))`
——即「按轮换分组的乘积」；`blockMap_inr_apply` 给出不动点块的读数 `tr (X i)`。

**★ 载体（侦察读数，L46／L47）**：`MultilinearMap.compMultilinearMap`（`Basic.lean:415`，
值律 `compMultilinearMap_apply : (g.compMultilinearMap f) m = g fun i => f i (Sigma.curry m i)`）、
`MultilinearMap.domDomCongr`（`:674`，`toFun v = m (v ∘ σ)`）、`MultilinearMap.mkPiAlgebra`（`:1192`
交换版，`A = k` 可用；`mkPiAlgebra_apply` 给乘积形态）。**⟹ 无任何张量幂多块分解。**

**射程**：本节只给**对象与值律**。轮换块的矩阵单位读数（`blockMap_inl_apply`）、与
`tSigma_tprod_matUnit` 的逐块比较（B′）、以及 `eq:12.3` 的收口（C′）**未做**。

**工艺读数**：`cycBlockMap` 的 `x₀` 取 `c.support.min' …`（`Finset.min'_mem`），其证明项会进入
`blockMap` 的定义；因此给轮换块的读数引理时**必须在陈述里写出同一组项**，不能用 `_` 让 Lean 猜
（本轮实测：`don't know how to synthesize placeholder`）。 -/

open Equiv.Perm

/-- 轮换块上的多线性因子：沿枚举次序的乘链之迹（`cycleProdMap` 搬到 `↥c.support` 上）。 -/
noncomputable def cycBlockMap {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (x₀ : Fin n)
    (hx₀ : x₀ ∈ c.support) :
    MultilinearMap k (fun _ : ↥c.support => Module.End k V) k :=
  (cycleProdMap k V c.support.card).domDomCongr (cycEnum c hc x₀ hx₀)

/-- 值：`cycBlockMap` 在切片上就是「沿枚举次序的乘链之迹」。 -/
theorem cycBlockMap_apply {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (x₀ : Fin n)
    (hx₀ : x₀ ∈ c.support) (v : ↥c.support → Module.End k V) :
    cycBlockMap k V c hc x₀ hx₀ v
      = LinearMap.trace k V ((List.ofFn (fun i : Fin c.support.card => v (cycEnum c hc x₀ hx₀ i))).prod) := by
  show (cycleProdMap k V c.support.card) (fun i => v (cycEnum c hc x₀ hx₀ i)) = _
  rw [cycleProdMap_apply]

#print axioms cycBlockMap
#print axioms cycBlockMap_apply

/-- 单槽迹因子（不动点块用）：`Unit`-槽的多线性映射 `v ↦ tr v`。 -/
noncomputable def traceSlotMap :
    MultilinearMap k (fun _ : Unit => Module.End k V) k where
  toFun v := LinearMap.trace k V (v ())
  map_update_add' := by
    intro _ m _ x y
    simp
  map_update_smul' := by
    intro _ m _ c x
    simp

theorem traceSlotMap_apply (v : Unit → Module.End k V) :
    traceSlotMap k V v = LinearMap.trace k V (v ()) := rfl

#print axioms traceSlotMap
#print axioms traceSlotMap_apply


/-- 每块的多线性因子：轮换块 ＝ 乘链之迹；不动点块 ＝ 单槽迹。 -/
noncomputable def blockMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : BlockIdx σ) :
    MultilinearMap k (fun _ : blockBeta σ x => Module.End k V) k :=
  match x with
  | Sum.inl c =>
    cycBlockMap k V c.1 (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
      (c.1.support.min' (Finset.card_pos.mp (by
        have h := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.two_le_card_support
        omega)))
      (Finset.min'_mem _ _)
  | Sum.inr _ => traceSlotMap k V

#print axioms blockMap

/-- `slotVal` 满射（每点或在某轮换的 support 内，或在 `σ.supportᶜ`）。 -/
theorem slotVal_surjective {n : ℕ} (σ : Equiv.Perm (Fin n)) : Function.Surjective (slotVal σ) := by
  intro x
  by_cases hx : x ∈ σ.support
  · rw [← biUnion_support_cycleFactorsFinset σ] at hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    exact ⟨⟨Sum.inl ⟨c, hc⟩, ⟨x, hxc⟩⟩, rfl⟩
  · exact ⟨⟨Sum.inr ⟨x, by rwa [Finset.mem_compl]⟩, ()⟩, rfl⟩

#print axioms slotVal_surjective

/-- ★★★★★ **块划分的等价**：`(Σ x : BlockIdx σ, blockBeta σ x) ≃ Fin n`。 -/
noncomputable def blockEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Σ x : BlockIdx σ, blockBeta σ x) ≃ Fin n :=
  Equiv.ofBijective (slotVal σ) ⟨slotVal_injective σ, slotVal_surjective σ⟩

#print axioms blockEquiv

/-- ★★★★★ **A′ 的产物**：右端（按轮换分组的乘积）作为 `Fin n` 上的**一个**多线性泛函。 -/
noncomputable def sigmaRMap {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MultilinearMap k (fun _ : Fin n => Module.End k V) k :=
  (MultilinearMap.compMultilinearMap (MultilinearMap.mkPiAlgebra k (BlockIdx σ) k)
    (fun x => blockMap k V σ x)).domDomCongr (blockEquiv σ)

#print axioms sigmaRMap

/-- ★★★★★ **`sigmaRMap` 的值**：按块展开成乘积。 -/
theorem sigmaRMap_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (X : Fin n → Module.End k V) :
    sigmaRMap k V σ X
      = ∏ x : BlockIdx σ, blockMap k V σ x (fun b => X (slotVal σ ⟨x, b⟩)) := by
  show (MultilinearMap.mkPiAlgebra k (BlockIdx σ) k)
      (fun x => blockMap k V σ x (fun b => X (slotVal σ ⟨x, b⟩))) = _
  rw [MultilinearMap.mkPiAlgebra_apply]

#print axioms sigmaRMap_apply

/-- 不动点块的读数：`tr (X i)`。 -/
theorem blockMap_inr_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ↥(σ.supportᶜ))
    (v : Unit → Module.End k V) :
    blockMap k V σ (Sum.inr i) v = LinearMap.trace k V (v ()) := rfl

#print axioms blockMap_inr_apply

/-! ## §37 **`cycleProdMap` 矩阵单位读数的「循环后继」形态**（第 538 轮）

§24 的 `cycleProdMap_matUnit` 给的是**分裂形态**：`∏_{i : Fin n}[c (castSucc i) = a i.succ] * [c (last n) = a 0]`
（末项单独拿出）。而 §33 的枚举给出的循环后继是 `(i+1) % (n+1)`，§36 的 `blockMap` 沿枚举喂槽，
故收口时两端形态**必须对齐**。本节给 `%` 形态：

```
cycleProdMap (⊗ 矩阵单位) = ∏ i : Fin (n+1), [c i = a ⟨(i+1) % (n+1)⟩]
```

**证明**：`cycleProdMap_matUnit` ＋ `Fin.prod_univ_castSucc`（末项分离）＋ 两条 `Fin` 指标算术
（`(castSucc j + 1) % (n+1) = j.succ`、`(last n + 1) % (n+1) = 0`，用 `Fin.ext` ＋ `Nat.mod_eq_of_lt`
＋ `Nat.mod_self`）。

**射程**：本节只给**形态对齐的一件**。`blockMap` 轮换块的矩阵单位读数（B′ 的实体）、
块乘积与 `Fin n` 乘积的桥（B″）、以及 `eq:12.3` 的收口（C′）**未做**。

**已登记的形态障碍（下一轮入口）**：`cycleProdMap_matUnit_mod` 仍是 `Fin (n+1)` 形（因为 §24 是），
而轮换 support 的 `card` 是任意 `h ≥ 2`；`cycBlockMap` 的槽类型是 `Fin h`。故 `cycBlockMap_matUnit`
需一次 `h ↔ n+1` 的**形状搬运**——建议做法：把 §24 的证明换成对 `h` 通用的形态（`List.ofFn_succ'`
＋`chainCond_concat`＋「和只取一项」），而不是在原形态上做 `finCongr` 传送。 -/

/-- ★★★★★ **`cycleProdMap_matUnit` 的 `%`（循环后继）形态**：
`cycleProdMap (⊗ 矩阵单位) = ∏_{i : Fin (n+1)} [c i = a ((i+1) % (n+1))]`。 -/
theorem cycleProdMap_matUnit_mod {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (b : Module.Basis ι k V) (a c : Fin (n + 1) → ι) :
    cycleProdMap k V (n + 1) (fun i => matUnit k V b (a i) (c i))
      = ∏ i : Fin (n + 1),
          (if c i = a ⟨((i : ℕ) + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ then (1 : k) else 0) := by
  classical
  rw [cycleProdMap_matUnit, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    have hidx : (⟨(((j.castSucc : Fin (n + 1)) : ℕ) + 1) % (n + 1),
        Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)) = j.succ := by
      ext
      show (((j.castSucc : Fin (n + 1)) : ℕ) + 1) % (n + 1) = (j.succ : ℕ)
      rw [Nat.mod_eq_of_lt]
      · simp
      · simp only [Fin.val_castSucc]
        have := j.isLt
        omega
    rw [hidx]
  · have hidx : (⟨(((Fin.last n : Fin (n + 1)) : ℕ) + 1) % (n + 1),
        Nat.mod_lt _ (by omega)⟩ : Fin (n + 1)) = 0 := by
      ext
      show (((Fin.last n : Fin (n + 1)) : ℕ) + 1) % (n + 1) = 0
      rw [Fin.val_last]
      exact Nat.mod_self (n + 1)
    rw [hidx]

#print axioms cycleProdMap_matUnit_mod

/-! ## §38 **乘积按块划分（B″）**（第 539 轮）

`sigmaRMap` 的值（§36 `sigmaRMap_apply`）是**按 `BlockIdx` 分块**的乘积，而 `tSigma` 的矩阵单位读数
（§14）是**按 `i : Fin n`** 的乘积。收口（C′）需要两者之间的桥：

```
∏_{i : Fin n} f i = (∏_{c : ↥σ.cycleFactorsFinset} ∏_{j : ↥c.support} f ↑j) * ∏_{j : ↥σ.supportᶜ} f ↑j
```

**与 §27 的关系**：`prod_eq_prod_cycles`（§27）是同一内容的 `Finset` 形态，但**限 `Field`**
（其陈述带 `[Field k]`）；本件对**任意 `CommMonoid`**，且用 `↥`-型乘积（正是 `BlockIdx` 的逐块读法所需）。

**证明**：`Finset.prod_mul_prod_compl`（按 `σ.support` 分裂）＋ `Finset.prod_coe_sort`（`↥`-型 ⟷ `∈`-型）
＋ `biUnion_support_cycleFactorsFinset`（§27）＋ `Finset.prod_biUnion`（`PairwiseDisjoint` 由
`cycleFactorsFinset_pairwise_disjoint` 给）。

**射程**：本节只给**乘积的桥**。轮换块的矩阵单位读数（B′ 的实体）、`sigmaRMap` 与 `tSigma` 的
矩阵单位比较（C′）**未做**；`eq:12.3` 一般情形未成定理。

**登记的下一轮障碍**：`sigmaRMap_matUnit_of_cycleValues`（C′ 的归约：若每块的读数已给则整体读数成立）
在 `rw [sigmaRMap_apply]` 后需把 `blockMap σ (inl c) (fun b => X (slotVal σ ⟨inl c, b⟩))` 与
`blockMap σ (inl c) (fun j => X ↑j)` 对齐；`slotVal` 的分支定义了但 `rw` 不匹配 ⟹ 须 `show`/`convert`。
（同族于 v27 教训 21／26 的「记法方向由机器定」。） -/

/-- ★★★★★ **乘积按块划分**：`∏_{i : Fin n} f i` ＝ 「轮换块之积 × 不动点之积」，用 `↥`-型乘积写。 -/
theorem prod_over_blocks {M : Type*} [CommMonoid M] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f : Fin n → M) :
    (∏ i : Fin n, f i)
      = (∏ c : ↥σ.cycleFactorsFinset, ∏ j : ↥(c.1.support), f ↑j)
        * (∏ j : ↥(σ.supportᶜ), f ↑j) := by
  classical
  rw [← Finset.prod_mul_prod_compl σ.support f]
  congr 1
  · rw [Finset.prod_coe_sort (s := σ.cycleFactorsFinset)
      (f := fun c => ∏ j : ↥(c.support), f ↑j)]
    rw [← biUnion_support_cycleFactorsFinset σ]
    rw [Finset.prod_biUnion]
    · refine Finset.prod_congr rfl (fun c _ => ?_)
      rw [← Finset.prod_coe_sort c.support f]
    · intro c hc c' hc' hne
      have h1 : Equiv.Perm.Disjoint c c' :=
        Equiv.Perm.cycleFactorsFinset_pairwise_disjoint (f := σ) hc hc' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro a ha ha'
      rw [Equiv.Perm.mem_support] at ha ha'
      rcases h1 a with h | h
      · exact ha h
      · exact ha' h
  · exact (Finset.prod_coe_sort σ.supportᶜ f).symm

#print axioms prod_over_blocks

/-! ## §39 **单个矩阵单位的迹 ＋ 轮换块的矩阵单位读数（进行中）**（第 540 轮）

§36 的不动点块读数是 `tr (X i)`。本节的 `trace_matUnit_single` 给它在矩阵单位上的值：

```
tr E_{ac} = [c = a]
```

证明 ＝ §21 `trace_prod_matUnit_list`（迹 ＝ 对角和）取单元素列表 ＋ `chainCond [(a,c)] x x` 的求值
（`Σ_x [x = a]·[c = x] = [c = a]`，`Finset.sum_eq_single`）。

**B′ 的进度与已登记障碍**：轮换块的读数需要「**任意长度 `h`** 的全循环矩阵单位公式」
（§24／§37 只给 `Fin (n+1)` 形，而 support 的 `card` 是任意 `h ≥ 2`）。本轮尝试的路线与卡点：

```
obtain ⟨n, hn⟩ : h = n+1
rw [cycleProdMap_apply, List.ofFn_congr hn, ← cycleProdMap_apply, cycleProdMap_matUnit_mod]
-- 剩：∏_{i' : Fin (n+1)} [β (cast i') = α (cast ⟨(i'+1)%(n+1)⟩)] = ∏_{i : Fin h} [β i = α ⟨(i+1)%h⟩]
--     用 Finset.prod_bij 沿 Fin.cast hn.symm 重标号
```

卡点＝**指标项比较里那条 `Fin` 等式**（`Fin.cast hn.symm ⟨…⟩ = ⟨…⟩`）：`ext; simp [Fin.val_cast]`
未能闭包（本轮实测）。**下一轮建议**：把该 `Fin` 等式**先单独证成具名引理**（用 `Fin.val_inj` 或
`Fin.ext` ＋ `Nat.mod_eq_of_lt` 显式给两条 `omega` 义务），而不是在 `prod_bij` 的项比较里内联。

**射程**：本节只给 `trace_matUnit_single`。B′ 的实体（轮换块读数）**未做**；C′、`eq:12.3`
一般情形未做；FFT 难半、`(A)→(B)` 未做。 -/

/-- 单个矩阵单位的迹：`tr E_{ac} = [c = a]`。 -/
theorem trace_matUnit_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (a c : ι) :
    LinearMap.trace k V (matUnit k V b a c) = (if c = a then (1 : k) else 0) := by
  classical
  have h := trace_prod_matUnit_list (k := k) (V := V) b [(a, c)]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [h, Finset.sum_eq_single a]
  · simp only [chainCond, if_true]
  · intro x _ hx
    simp only [chainCond, if_neg hx]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

#print axioms trace_matUnit_single

/-! ## §40 **形状搬运的指标等式**（第 541 轮）

B′ 需把 §24／§37 的 `Fin (n+1)` 形公式搬到任意长度 `h` 的轮换 support 上。搬运的最后一块是指标等式：

```
Fin.cast hn.symm ⟨(i+1) % (n+1)⟩ = ⟨(↑(Fin.cast hn.symm i) + 1) % h⟩        （hn : h = n+1）
```

本节把它**单独证成具名引理**（§39 节标登记的教训：不在 `prod_bij` 的项比较里内联）。
证明：`Fin.ext` ＋ `Fin.val_cast` ＋ `Fin.val_mk` ＋ `rw [hn]`（三行）。

**下一轮的障碍（本轮实测，已登记）**：把该引理用到 `cycleProdMap_matUnit_gen` 的
`Finset.prod_bij` 重标号时，**`prod_bij` 的隐式参数使四个 bullet 错位**
（第二个 bullet 报 `introN failed: no additional binders`，而 `rw`/`simp only [hidx]` 均报
"找不到模式"／"no progress"）。**下一轮改走**：`Fintype.prod_equiv`（或显式给 `prod_bij` 的
`f`/`g` 两参数），并把「项比较」与「重标号」拆成两个独立引理。

**射程**：本节只给指标等式。`cycleProdMap_matUnit_gen`（任意 `h` 的全循环公式）、B′ 实体、C′、
`eq:12.3` 一般情形**均未做**。 -/

/-- **形状搬运的指标等式**：`Fin.cast` 与「`% (n+1)` 循环后继」可交换。 -/
theorem fin_cast_mod_succ {h n : ℕ} (hn : h = n + 1) (i : Fin (n + 1)) :
    (Fin.cast hn.symm ⟨((i : ℕ) + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩ : Fin h)
      = ⟨(((Fin.cast hn.symm i : Fin h) : ℕ) + 1) % h, Nat.mod_lt _ (by omega)⟩ := by
  ext
  simp only [Fin.val_cast, Fin.val_mk]
  rw [hn]

#print axioms fin_cast_mod_succ

/-! ## §41 **B′ 的形状块：`Fin (d+1)` 形进定义**（第 542 轮）

§39／§40 两轮都在**每处引理各搬一次形状**（`Fin h` ⟷ `Fin (n+1)`），代价高且互相干扰。
本轮换做法：**把形状写进定义**——

```
cycBlockMapK c hc d hk x₀ hx₀ := (cycleProdMap k V (d+1)).domDomCongr ((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀))
                              （hk : c.support.card = d+1）
```

于是矩阵单位读数**直接**由 §37 的 `cycleProdMap_matUnit_mod` 给出，**零形状搬运**：

```
cycBlockMapK_matUnit : cycBlockMapK … (E_{a,w}) = ∏ i : Fin (d+1), [w (e i) = a (e ⟨(i+1) % (d+1)⟩)]
```

**工艺读数（本轮最省的一招）**：`domDomCongr_apply`（`(domDomCongr σ m) v = m (v ∘ σ)`）＋
`List.ofFn_congr`（§540 侦察命中）足以把「`Fin h` 与 `Fin (n+1)`」的搬运**一次做在定义里**，
之后所有读数引理都是 `rw [cycBlockMapK, domDomCongr_apply]` ＋ `exact 已有公式`。

**射程**：本节只给**形状块与其读数**。与 §36 的 `cycBlockMap` 的一致性（`cycBlockMap_eq_K`）、
枚举形 → 子类型形（`∏_{j ∈ c.support} [a j = w (σ j)]`）的两次重标号、C′ 收口**均未做**；
`eq:12.3` 一般情形未成定理。 -/

/-- 轮换块的因子（**显式 `d+1` 形**：形状进定义，避免每处引理各搬一遍）。 -/
noncomputable def cycBlockMapK {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (d : ℕ)
    (hk : c.support.card = d + 1) (x₀ : Fin n) (hx₀ : x₀ ∈ c.support) :
    MultilinearMap k (fun _ : ↥c.support => Module.End k V) k :=
  (cycleProdMap k V (d + 1)).domDomCongr
    ((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀))

#print axioms cycBlockMapK

/-- ★★★★★ **`cycBlockMapK` 的矩阵单位读数**（`Fin (d+1)` 形，直接由 §37 得，无形状搬运）。 -/
theorem cycBlockMapK_matUnit {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (d : ℕ)
    (hk : c.support.card = d + 1) (x₀ : Fin n) (hx₀ : x₀ ∈ c.support)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (a w : Fin n → ι) :
    cycBlockMapK k V c hc d hk x₀ hx₀ (fun j => matUnit k V b (a ↑j) (w ↑j))
      = ∏ i : Fin (d + 1),
          (if w ↑(((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i)
              = a ↑(((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀))
                  ⟨((i : ℕ) + 1) % (d + 1), Nat.mod_lt _ (by omega)⟩)
            then (1 : k) else 0) := by
  rw [cycBlockMapK, MultilinearMap.domDomCongr_apply]
  exact cycleProdMap_matUnit_mod (k := k) (V := V) b
    (fun i : Fin (d + 1) => a ↑(((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i))
    (fun i : Fin (d + 1) => w ↑(((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i))

#print axioms cycBlockMapK_matUnit

/-! ## §42 **B′ 的实体：轮换块的矩阵单位读数**（第 543 轮）

§41 给了 `cycBlockMapK` 的 `Fin (d+1)` 形读数。本节把它搬到**子类型形**（即 `↥c.support` 上的乘积）：

```
cycBlockMapK_step              : e ⟨(i+1) % (d+1)⟩ = c⁻¹ (e i)          （枚举的循环后继，Fin (d+1) 形）
cycBlockMapK_matUnit_support   : cycBlockMapK … (E_{a,w}) = ∏ j : ↥c.support, [w j = a (c⁻¹ j)]
```

**两件的载体**：`cycBlockMapK_step` ＝ §40 的 `fin_cast_mod_succ` ＋ §33 的 `cycEnum_step`（§40 那轮
单独具名化指标等式的投资在此兑现）；`_support` ＝ `Finset.prod_bij` 沿枚举重标号，项比较用 `_step`。

**★ 本轮根因虫（重要工艺读数）**：前两轮 `Finset.prod_bij` 反复失败的**真因**是**参数次序**——
其签名是 `prod_bij (i) (hi) (i_inj) (i_surj) (h)`，**项比较 `h` 在最后**；我此前按「i, hi, h, ...」
的顺序给，导致 bullet 错位并报 `introN failed`。另：`prod_bij` 的结论方向是
`s.prod f = t.prod g`，故**不要再加 `.symm`**。两条都记入教训。

**射程**：本节只给**轮换块读数（`c⁻¹` 形态）**。与 §36 `cycBlockMap` 的一致性、到
`∏ j, [a j = w (σ j)]`（`σ` 形态）的最后一次重标号、C′ 收口**均未做**；`eq:12.3` 一般情形未成定理。 -/

/-- 枚举的循环后继（`Fin (d+1)` 形）：`e ⟨(i+1)%(d+1)⟩ = c⁻¹ (e i)`。 -/
theorem cycBlockMapK_step {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (d : ℕ)
    (hk : c.support.card = d + 1) (x₀ : Fin n) (hx₀ : x₀ ∈ c.support) (i : Fin (d + 1)) :
    ((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀))
        ⟨((i : ℕ) + 1) % (d + 1), Nat.mod_lt _ (by omega)⟩
      = c⁻¹ (((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i) := by
  show cycEnum c hc x₀ hx₀ (Fin.cast hk.symm ⟨((i : ℕ) + 1) % (d + 1), _⟩)
      = c⁻¹ (cycEnum c hc x₀ hx₀ (Fin.cast hk.symm i))
  rw [fin_cast_mod_succ hk i, cycEnum_step c hc x₀ hx₀ (Fin.cast hk.symm i)]

#print axioms cycBlockMapK_step

/-- ★★★★★ **B′ 的实体（子类型形）**：轮换块在矩阵单位上的读数
`∏_{j ∈ c.support} [w j = a (c⁻¹ j)]`。 -/
theorem cycBlockMapK_matUnit_support {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (d : ℕ)
    (hk : c.support.card = d + 1) (x₀ : Fin n) (hx₀ : x₀ ∈ c.support)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (a w : Fin n → ι) :
    cycBlockMapK k V c hc d hk x₀ hx₀ (fun j => matUnit k V b (a ↑j) (w ↑j))
      = ∏ j : ↥c.support, (if w ↑j = a ↑(c⁻¹ ↑j) then (1 : k) else 0) := by
  classical
  rw [cycBlockMapK_matUnit]
  refine (Finset.prod_bij
    (f := fun i : Fin (d + 1) => (if w ↑(((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i)
        = a ↑(((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀))
            ⟨((i : ℕ) + 1) % (d + 1), Nat.mod_lt _ (by omega)⟩) then (1 : k) else 0))
    (g := fun j : ↥c.support => (if w ↑j = a ↑(c⁻¹ ↑j) then (1 : k) else 0))
    (fun i (_ : i ∈ Finset.univ) => ((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i)
    ?_ ?_ ?_ ?_)
  · intro i _; exact Finset.mem_univ _
  · intro a₁ _ a₂ _ heq
    exact ((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)).injective heq
  · intro j _
    exact ⟨((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)).symm j, Finset.mem_univ _,
      Equiv.apply_symm_apply _ _⟩
  · intro i _
    rw [cycBlockMapK_step c hc d hk x₀ hx₀ i]

#print axioms cycBlockMapK_matUnit_support

/-! ## §43 **收口第 ② 步：轮换块读数的 `σ` 形态**（第 545 轮）

§42 的读数是 `c⁻¹` 形态：`∏_{j ∈ c.support} [w j = a (c⁻¹ j)]`；而 §14 的左端是 `σ` 形态
`∏_{i} [a i = w (σ i)]`。本节把它们接上：

```
apply_mem_support       : x ∈ c.support → c x ∈ c.support        （§33 `inv_mem_support` 的对偶方向）
prod_cycle_support_eq   : ∏_{j ∈ c.support} [w j = a (c⁻¹ j)] = ∏_{j ∈ c.support} [a j = w (σ j)]
```

**两件的钉法（本轮把 §544 死胡同的两条教训都用上）**：
① **指标侧事实先具名化**——`apply_mem_support` 单独成件（`mem_support` ＋ 置换单射，三行），
不在 `prod_bij` 的内联 `?_` 里现证；
② `prod_bij` 按**正确参数次序** `(i) (hi) (i_inj) (i_surj) (h)`（§543 根因虫），且因 `h` 形如
`f a = g (i a)`，把待证等式**反向**陈述后取 `.symm`——避免 `f j` 与 `g (Φ j)` 索引不对齐。

**核心一步**：`mem_cycleFactorsFinset_iff.mp hc` 的第二分量给的是 **`c x = σ x`**（注意方向，
本轮实测该方向报错过一次），故 `c⁻¹ (σ j) = j` 要用 `← hσ` 反写。

**收口三步的进度**：① `cycBlockMap_eq_K` **未做**；② `prod_cycle_support_eq` ✓ **本件**；
③ C′（`sigmaRMap_matUnit_of_cycleValues` ⟹ `multilinear_eq_dual_of_matUnit`）**未做**。

**射程**：`eq:12.3` 一般情形**仍未成定理**；FFT 难半、`(A)→(B)` 未做。 -/

/-- `c.support` 对 `c` 封闭（§33 的 `inv_mem_support` 是 `c⁻¹` 方向）。 -/
theorem apply_mem_support {α : Type*} [DecidableEq α] [Fintype α] {c : Equiv.Perm α} {x : α}
    (h : x ∈ c.support) : c x ∈ c.support := by
  rw [Equiv.Perm.mem_support] at h ⊢
  intro hcon
  exact h (by simpa using congrArg (fun z => c⁻¹ z) hcon)

#print axioms apply_mem_support

/-- ★★★★★ **轮换块读数的 `σ` 形态**。 -/
theorem prod_cycle_support_eq {n : ℕ} (σ c : Equiv.Perm (Fin n))
    (hc : c ∈ σ.cycleFactorsFinset) {ι : Type*} [DecidableEq ι] (a w : Fin n → ι) :
    (∏ j : ↥c.support, (if w ↑j = a ↑(c⁻¹ ↑j) then (1 : k) else 0))
      = ∏ j : ↥c.support, (if a ↑j = w (σ ↑j) then (1 : k) else 0) := by
  classical
  have hσ : ∀ x ∈ c.support, c x = σ x :=
    fun x hx => (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 x hx
  refine (Finset.prod_bij
    (f := fun j : ↥c.support => (if a ↑j = w (σ ↑j) then (1 : k) else 0))
    (g := fun j : ↥c.support => (if w ↑j = a ↑(c⁻¹ ↑j) then (1 : k) else 0))
    (fun j (_ : j ∈ Finset.univ) => (⟨σ ↑j, by rw [← hσ ↑j j.2]; exact apply_mem_support j.2⟩ :
      ↥c.support)) ?_ ?_ ?_ ?_).symm
  · intro j _; exact Finset.mem_univ _
  · intro j₁ _ j₂ _ heq
    have h1 : σ ↑j₁ = σ ↑j₂ := Subtype.ext_iff.mp heq
    exact Subtype.ext (σ.injective h1)
  · intro j _
    refine ⟨⟨c⁻¹ ↑j, inv_mem_support j.2⟩, Finset.mem_univ _, ?_⟩
    refine Subtype.ext ?_
    show σ (c⁻¹ ↑j) = ↑j
    rw [← hσ _ (inv_mem_support j.2)]
    simp
  · intro j _
    show (if a ↑j = w (σ ↑j) then (1 : k) else 0)
      = (if w ↑(σ ↑j) = a ↑(c⁻¹ ↑(σ ↑j)) then (1 : k) else 0)
    have hstep : c⁻¹ (σ ↑j) = ↑j := by
      rw [← hσ ↑j j.2]
      simp
    rw [hstep]
    simp [eq_comm]

#print axioms prod_cycle_support_eq

/-! ## §44 **收口第 ① 步：`cycBlockMap` 与 `cycBlockMapK` 一致**（第 546 轮）

§36 的 `blockMap` 用的是 `cycBlockMap`（`Fin #c.support` 形），而 §41／§42 的读数建在
`cycBlockMapK`（`Fin (d+1)` 形）上。本节把两者接起来：

```
cycBlockMap_eq_K : cycBlockMap c hc x₀ hx₀ v = cycBlockMapK c hc d hk x₀ hx₀ v      （hk : #c.support = d+1）
```

**做法（兑现 §544 死胡同的教训）**：不在 `List.prod` 层做同余（`congrArg List.prod` 会报
`typeclass instance problem is stuck`），而是在 **`List` 层**先写下 `hlist`：

```
hlist : List.ofFn (v ∘ e) = List.ofFn (v ∘ ((finCongr hk.symm).trans e))
```

由 §540 侦察的 `List.ofFn_congr` ＋ `finCongr_apply` 得到（`simpa [finCongr_apply] using …`），
再 `rw [hlist]` 一次收口。

**收口三步进度**：① ✓ **本件**；② ✓ §43；③ C′（`sigmaRMap` 的矩阵单位读数 ⟹
`eq:12.3` 一般情形）**未做**——**这是 `eq:12.3` 的最后一格**。

**C′ 的精确配方（下一轮直接照做）**：
```
rw [sigmaRMap_apply, Fintype.prod_sum_type]
· 轮换块：blockMap (inl c) 的定义是 rfl 的 cycBlockMap ⟹ hfun(rfl) 展开 slotVal ⟹
  rw [cycBlockMap_eq_K (d := #c.support - 1) (hk := Nat.sub_add_cancel …)]
  ⟹ cycBlockMapK_matUnit_support ⟹ prod_cycle_support_eq
· 不动点块：blockMap_inr_apply ⟹ trace_matUnit_single ⟹ σ ↑i = ↑i（i ∈ supportᶜ）
⟹ prod_over_blocks（§38）反向收尾
```
**射程**：`eq:12.3` 一般情形**仍未成定理**（只差 C′）；FFT 难半、`(A)→(B)` 未做。 -/

/-- §36 的 `cycBlockMap` 与 §41 的 `cycBlockMapK` 一致（形状不同、值相同）。 -/
theorem cycBlockMap_eq_K {n : ℕ} (c : Equiv.Perm (Fin n)) (hc : c.IsCycle) (d : ℕ)
    (hk : c.support.card = d + 1) (x₀ : Fin n) (hx₀ : x₀ ∈ c.support)
    (v : ↥c.support → Module.End k V) :
    cycBlockMap k V c hc x₀ hx₀ v = cycBlockMapK k V c hc d hk x₀ hx₀ v := by
  rw [cycBlockMap, cycBlockMapK, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domDomCongr_apply, cycleProdMap_apply, cycleProdMap_apply]
  have hlist : (List.ofFn (fun i : Fin c.support.card => v (cycEnum c hc x₀ hx₀ i)))
      = List.ofFn (fun i : Fin (d + 1) =>
          v (((finCongr hk.symm).trans (cycEnum c hc x₀ hx₀)) i)) := by
    simpa [finCongr_apply] using
      List.ofFn_congr hk (fun i : Fin c.support.card => v (cycEnum c hc x₀ hx₀ i))
  rw [hlist]

#print axioms cycBlockMap_eq_K

/-! ## §45 ★★★★ **C′：`sigmaRMap` 的矩阵单位读数**（第 547 轮）——`eq:12.3` 的最后一格

```
sigmaRMap_matUnit : sigmaRMap σ (⊗ E_{aᵢwᵢ}) = ∏ i, [aᵢ = w_{σ i}]      （＝ §14 的 tSigma 读数）
```

**证明（AGPR 原证「多线性 ＋ 矩阵单位」的机器形态，`raw/AGPR2020.tex:13883`）**：
`sigmaRMap_apply`（§36）按块展开 ＋ `Fintype.prod_sum_type` 拆 `BlockIdx` ＝ `循环 ⊕ 不动点`；
- **轮换块**：`hfun`（`slotVal` 定义为 `↑b`，rfl）⟹ `cycBlockMap_eq_K`（§44，取 `d := #c.support - 1`，
  `hk` 由 `IsCycle.two_le_card_support`）⟹ `cycBlockMapK_matUnit_support`（§42，`c⁻¹` 形态）
  ⟹ `prod_cycle_support_eq`（§43，`c⁻¹` → `σ` 形态）；
- **不动点块**：`blockMap_inr_apply`（§36）⟹ `trace_matUnit_single`（§39/§40）⟹ `σ ↑i = ↑i`
  （`i ∈ σ.supportᶜ` ＋ `mem_compl`）；
- **收口**：`prod_over_blocks`（§38）反向。

⟹ **`eq:12.3` 一般情形的两端在矩阵单位上一致**（`tSigma_eq_sigmaRMap_matUnit`）。

**剩余一格**：`tSigma_eq_sigmaRMap`（把矩阵单位等式经 §21 延拓到任意 `X`）——本轮尝试只差
**参数方向一处**（`multilinear_eq_dual_of_matUnit` 的结论方向是 `R X = F (tprod X)`，目标相反，
需 `.symm`；本轮 `.symm` 后仍报 type mismatch，下一轮检查 `h` 的实参形态）。

**射程**：`eq:12.3` 一般情形**仍未成定理**（差最后一行延拓）；FFT 难半、`(A)→(B)` 未做。 -/

/-- ★★★★★★★ **AGPR `eq:12.3` 的右端在矩阵单位上的读数（C′）**：
`sigmaRMap σ` 在矩阵单位纯张量上 ＝ `∏ i, [a i = w (σ i)]`（即 §14 `tSigma` 的读数）。 -/
theorem sigmaRMap_matUnit {n : ℕ} (σ : Equiv.Perm (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (a w : Fin n → ι) :
    sigmaRMap k V σ (fun i => matUnit k V b (a i) (w i))
      = ∏ i : Fin n, (if a i = w (σ i) then (1 : k) else 0) := by
  classical
  rw [sigmaRMap_apply, Fintype.prod_sum_type]
  have hcyc : ∀ c : ↥σ.cycleFactorsFinset,
      blockMap k V σ (Sum.inl c)
          (fun b_1 => matUnit k V b (a (slotVal σ ⟨Sum.inl c, b_1⟩))
            (w (slotVal σ ⟨Sum.inl c, b_1⟩)))
        = ∏ j : ↥(c.1.support), (if a ↑j = w (σ ↑j) then (1 : k) else 0) := by
    intro c
    have hfun : (fun b_1 : blockBeta σ (Sum.inl c) => matUnit k V b
        (a (slotVal σ ⟨Sum.inl c, b_1⟩)) (w (slotVal σ ⟨Sum.inl c, b_1⟩)))
        = fun j : ↥(c.1.support) => matUnit k V b (a ↑j) (w ↑j) := rfl
    rw [hfun]
    show cycBlockMap k V c.1 _ _ _ (fun j => matUnit k V b (a ↑j) (w ↑j)) = _
    have hk : c.1.support.card = (c.1.support.card - 1) + 1 := by
      have h2 := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.two_le_card_support
      omega
    rw [cycBlockMap_eq_K (k := k) (V := V) c.1 _ (c.1.support.card - 1) hk _ _]
    rw [cycBlockMapK_matUnit_support]
    exact prod_cycle_support_eq (k := k) σ c.1 c.2 a w
  have hfix : ∀ i : ↥(σ.supportᶜ),
      blockMap k V σ (Sum.inr i)
          (fun b_1 => matUnit k V b (a (slotVal σ ⟨Sum.inr i, b_1⟩))
            (w (slotVal σ ⟨Sum.inr i, b_1⟩)))
        = (if a ↑i = w (σ ↑i) then (1 : k) else 0) := by
    intro i
    have hfun : (fun b_1 : blockBeta σ (Sum.inr i) => matUnit k V b
        (a (slotVal σ ⟨Sum.inr i, b_1⟩)) (w (slotVal σ ⟨Sum.inr i, b_1⟩)))
        = fun _ : Unit => matUnit k V b (a ↑i) (w ↑i) := rfl
    rw [hfun, blockMap_inr_apply, trace_matUnit_single]
    have hσi : σ ↑i = ↑i := by
      have hmem := i.2
      rw [Finset.mem_compl] at hmem
      by_contra hne
      exact hmem (Equiv.Perm.mem_support.mpr hne)
    rw [hσi]
    simp only [eq_comm]
  rw [Finset.prod_congr rfl (fun c (_ : c ∈ Finset.univ) => hcyc c),
    Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hfix i)]
  exact (prod_over_blocks σ (fun i => if a i = w (σ i) then (1 : k) else 0)).symm

#print axioms sigmaRMap_matUnit

/-- ★★★★★★★ **AGPR `eq:12.3`（矩阵单位形态，机检）**：
`T_σ(⊗ E_{aᵢcᵢ}) = ∏ i, [aᵢ = w_{σ i}]` 的两条路线一致。 -/
theorem tSigma_eq_sigmaRMap_matUnit {n : ℕ} (σ : Equiv.Perm (Fin n))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V) (a w : Fin n → ι) :
    tSigma k V n σ (PiTensorProduct.tprod k (fun i => matUnit k V b (a i) (w i)))
      = sigmaRMap k V σ (fun i => matUnit k V b (a i) (w i)) := by
  rw [sigmaRMap_matUnit, tSigma_tprod_matUnit]

#print axioms tSigma_eq_sigmaRMap_matUnit

/-! ## §46 ★★★★★★★★ **AGPR `eq:12.3` 一般情形（机检）**（第 548 轮）

```
tSigma_eq_sigmaRMap : T_σ(⊗ X) = sigmaRMap σ X
```

右端 ＝ 按 `σ` 的**轮换分解**分组、沿轮换次序取乘链之迹的乘积（§36 的 `sigmaRMap` 值律 ＋
§43 的 `σ` 形态重标号 ＋ §38 的乘积桥）。

**路线（AGPR 原证逐字，`raw/AGPR2020.tex:13883`）**：「since the identity is multilinear, it is enough
to prove it on the decomposable tensors」⟹ `multilinear_eq_dual_of_matUnit`（§21 多线性延拓原理）
把矩阵单位上的等式（§45 `tSigma_eq_sigmaRMap_matUnit`）抬到任意 `X`。

**工艺读数**：照 §25 `tSigma_finRotate_inv_tprod` 的已验证模式——先 `refine Eq.symm ?_` 把目标
翻成延拓原理的结论方向 `R X = F (tprod X)`，**再正着用**该原理；末端的矩阵单位等式要 `.symm`
（`tSigma_eq_sigmaRMap_matUnit` 的方向是 `tSigma = sigmaRMap`）。**两处 `Eq.symm` 一个都不能少、
且都不能多**——§547 的一处 type mismatch 就是只翻了外层、忘了内层。

**不变量**：无 `sorry`、无额外公理（`[propext, Classical.choice, Quot.sound]`）。

**⟹ v27 §3.1 的缺口 #2（`eq:12.3`）关闭。** 一般情形不再需要 `cycle_induction_on`
（§533 已证其乘性步不成立）、不需要 `Φ` 与块分解的相容性、不需要张量幂多块分解。

**射程**：`eq:12.3` 已机检，但**缺口 #4（FFT 难半 `thm:12.1.3`）未做**；`(A)→(B)` 未做；
`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★★★★ **AGPR `eq:12.3` —— 一般情形（机检）**：
`T_σ(⊗ X) = sigmaRMap σ X`（右端 ＝ 按 `σ` 的轮换分解分组、沿轮换次序取乘链之迹的乘积）。 -/
theorem tSigma_eq_sigmaRMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (X : Fin n → Module.End k V) :
    tSigma k V n σ (PiTensorProduct.tprod k X) = sigmaRMap k V σ X := by
  classical
  refine Eq.symm ?_
  refine multilinear_eq_dual_of_matUnit (k := k) (V := V)
    (b := Module.Free.chooseBasis k V) (m := n)
    (R := sigmaRMap k V σ) (F := tSigmaLinear k V n σ) (X := X) ?_
  intro p
  rw [show (fun i => endBasis k V (Module.Free.chooseBasis k V) (p i))
      = (fun i => matUnit k V (Module.Free.chooseBasis k V) (p i).1 (p i).2) from
    funext fun i => endBasis_apply k V (Module.Free.chooseBasis k V) (p i).1 (p i).2]
  exact (tSigma_eq_sigmaRMap_matUnit (k := k) (V := V) σ (Module.Free.chooseBasis k V)
    (fun i => (p i).1) (fun i => (p i).2)).symm

#print axioms tSigma_eq_sigmaRMap

/-! ## §47 **`T_σ` 的对偶层形态（缺口 #4 的 (B) 桥）**（第 552 轮）

§46 是 `tprod` 层的等式；缺口 #4 的 Aronhold 归纳需要对偶层（`Module.Dual`）的同一事实：

```
tSigmaLinear_eq_lift_sigmaRMap : tSigmaLinear σ = PiTensorProduct.lift (sigmaRMap σ)
```

⟹ `T_σ` 作为**线性泛函**就是「乘链迹之积」那个多线性形式的提升。

**载体（本轮先 `#check` 再写，兑现 §551 教训）**：`PiTensorProduct.ext`
（`φ₁.compMultilinearMap tprod = φ₂.compMultilinearMap tprod → φ₁ = φ₂`，即「纯张量上一致即相等」）
＋ `PiTensorProduct.lift.tprod`（`(lift φ) (tprod f) = φ f`）。§551 猜的两个名字
（`dualSect.injective`、`lift_symm_apply`）在本 pin **不存在**——故本轮改为先 `#check` 全部候选，
一次即通。

**射程**：本节只给**对偶层桥**。缺口 #4（`thm:12.1.3`）的环层（迹环 ≥ 不变量环 ＋ 极化／复原）
**未做**；`(A)→(B)` 未做；`S'^N ⊆ Z` 未证；H2 仍不是定理。 -/

/-- ★★★★★★ **`T_σ` 的泛函形态 ＝ `sigmaRMap σ` 的提升**（§46 的对偶层形态）。 -/
theorem tSigmaLinear_eq_lift_sigmaRMap {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    tSigmaLinear k V n σ
      = (PiTensorProduct.lift (sigmaRMap k V σ) :
          Module.Dual k (TensorPower k n (Module.End k V))) := by
  classical
  refine PiTensorProduct.ext ?_
  ext X
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    PiTensorProduct.lift.tprod]
  exact tSigma_eq_sigmaRMap k V σ X

#print axioms tSigmaLinear_eq_lift_sigmaRMap

end Procesi
