/-
  Procesi —— **切片泛函的 `End` 层运输**（搬运段 3 的第 4 块；第 630 轮）

  本文件把 `FFTRing` 的 `sliceForm`（多边形层，§43／§44）沿 `LinearMap.toMatrix'` 运到
  `Module.End F (Fin n → F)` 上，并证其**迹对偶泛函**落在 `FFTIdentification` 的
  `tnm`（＝ AGPR `def:12.1.1` 的 `T_n(d)`，同时共轭不变的多线性泛函空间）里。

  于是 **`tnm_eq_span`**（`FFTIdentification.lean:1563`，AGPR `lem:12.1.2` 的形级 Schur–Weyl：
  `T_n(d) = span{T_σ}`）**直接可用**——这是 `hAdBd` 正文（多线性块不变量 ⊆ `T_σ` 代数）
  在**泛函层**的最后一块拼图。

  **射程（诚实边界）**：本文件只做到"切片泛函 ∈ `tnm`"。**未做**：由 `tnm_eq_span` 取出系数
  `c_σ`、以及把这些系数**回推**成 `S` 层的多项式等式（`killLabelsK g w ∈ adjoin (range tSigmaPoly)`）。
  `hAdBd` 正文、`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；
  H2 仍不是定理。
-/
import Procesi.FFTRing
import Procesi.FFTIdentification

namespace Procesi

open scoped BigOperators

/-- 矩阵层共轭 `conjMat` 就是矩阵乘积 `A⁻¹ · M · A`（指标重排）。 -/
theorem conjMat_eq_mul (F : Type) [Field F] (n : ℕ) (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (M : Matrix (Fin n) (Fin n) F) :
    conjMat F n A M = (↑A⁻¹ : Matrix (Fin n) (Fin n) F) * M * (↑A : Matrix (Fin n) (Fin n) F) := by
  classical
  funext i l
  rw [conjMat, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]

#print axioms conjMat_eq_mul

/-- 由 `End` 的互逆对造矩阵单位。 -/
noncomputable def matUnitOfEnd (F : Type) [Field F] (n : ℕ)
    (B B' : Module.End F (Fin n → F)) (h1 : B ∘ₗ B' = 1) (h2 : B' ∘ₗ B = 1) :
    (Matrix (Fin n) (Fin n) F)ˣ where
  val := LinearMap.toMatrix' B'
  inv := LinearMap.toMatrix' B
  val_inv := by rw [← LinearMap.toMatrix'_comp, h2]; simp
  inv_val := by rw [← LinearMap.toMatrix'_comp, h1]; simp

#print axioms matUnitOfEnd

/-- `toMatrix'` 把逐因子共轭送成矩阵乘积夹逼。 -/
theorem toMatrix'_conjEnd (F : Type) [Field F] (n : ℕ)
    (B B' : Module.End F (Fin n → F)) (X : Module.End F (Fin n → F)) :
    LinearMap.toMatrix' (conjEnd F (Fin n → F) B B' X)
      = LinearMap.toMatrix' B * LinearMap.toMatrix' X * LinearMap.toMatrix' B' := by
  rw [conjEnd_apply, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, mul_assoc]

#print axioms toMatrix'_conjEnd

/-- `End` 层的切片泛函（`sliceForm` 沿 `toMatrix'` 运输）。 -/
noncomputable def sliceFormEnd (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    MultilinearMap F (fun _ : Fin d => Module.End F (Fin n → F)) F :=
  (sliceForm F r n d v g).compLinearMap
    (fun _ => (LinearMap.toMatrix' (m := Fin n) (n := Fin n) (R := F)).toLinearMap)

#print axioms sliceFormEnd

theorem sliceFormEnd_apply (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r)
    (Y : Fin d → Module.End F (Fin n → F)) :
    sliceFormEnd F r n d v g Y
      = sliceForm F r n d v g (fun j => LinearMap.toMatrix' (Y j)) := by
  rw [sliceFormEnd, MultilinearMap.compLinearMap_apply]
  rfl

#print axioms sliceFormEnd_apply

/-- `End` 层切片的共轭不变性。 -/
theorem sliceFormEnd_conj (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) w)
    (hw : IsBlockInvariant F r n d w) (B B' : Module.End F (Fin n → F))
    (h1 : B ∘ₗ B' = 1) (h2 : B' ∘ₗ B = 1) (Y : Fin d → Module.End F (Fin n → F)) :
    sliceFormEnd F r n d w g (fun j => conjEnd F (Fin n → F) B B' (Y j))
      = sliceFormEnd F r n d w g Y := by
  classical
  rw [sliceFormEnd_apply, sliceFormEnd_apply]
  rw [show (fun j => LinearMap.toMatrix' (conjEnd F (Fin n → F) B B' (Y j)))
      = fun j => conjMat F n (matUnitOfEnd F n B B' h1 h2) (LinearMap.toMatrix' (Y j)) from by
    funext j
    rw [toMatrix'_conjEnd, conjMat_eq_mul]
    rfl]
  exact sliceForm_eq_of_blockInvariant (F := F) (r := r) (n := n) (d := d) (g := g)
    (w := w) (Y := fun j => LinearMap.toMatrix' (Y j)) hv hw
    (matUnitOfEnd F n B B' h1 h2)

#print axioms sliceFormEnd_conj

/-- 切片泛函的**迹对偶**（`⨂^d (End V)` 上的线性泛函）。 -/
noncomputable def sliceDual (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    Module.Dual F (TensorPower F d (Module.End F (Fin n → F))) :=
  tensorPowerTraceDualEquiv F (Fin n → F) d
    (multilinearMapTensorPowerEquiv F (Fin n → F) d (sliceFormEnd F r n d v g))

#print axioms sliceDual

theorem sliceDual_tprod (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r)
    (b : Fin d → Module.End F (Fin n → F)) :
    sliceDual F r n d v g (PiTensorProduct.tprod F b)
      = sliceFormEnd F r n d v g b :=
  multilinearMapTensorPowerEquiv_apply_dual (k := F) (V := Fin n → F) (m := d)
    (sliceFormEnd F r n d v g) b

#print axioms sliceDual_tprod

/-- ★★★★★ **`AGPR lem:12.1.2` 的输入：切片泛函落在 `T_n(d)` 里**（同时共轭不变）。 -/
theorem sliceDual_mem_tnm (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) w)
    (hw : IsBlockInvariant F r n d w) :
    sliceDual F r n d w g ∈ tnm (k := F) (m := d) (n := n) := by
  classical
  intro B B' h1 h2 y
  have hfun_lin : (sliceDual F r n d w g).comp
        (PiTensorProduct.map (fun _ : Fin d => conjEnd F (Fin n → F) B B'))
      = sliceDual F r n d w g := by
    refine dual_eq_of_matUnit (k := F) (m := d) (n := n) _ _ ?_
    intro p
    rw [LinearMap.comp_apply, PiTensorProduct.map_tprod, sliceDual_tprod, sliceDual_tprod]
    exact sliceFormEnd_conj F r n d g hv hw B B' h1 h2 _
  calc sliceDual F r n d w g
        (PiTensorProduct.map (fun _ : Fin d => conjEnd F (Fin n → F) B B') y)
      = ((sliceDual F r n d w g).comp
          (PiTensorProduct.map (fun _ : Fin d => conjEnd F (Fin n → F) B B'))) y := by
        rw [LinearMap.comp_apply]
    _ = sliceDual F r n d w g y := by rw [hfun_lin]

#print axioms sliceDual_mem_tnm


/-! ## 切分第 46 步：★★★★★★★ **取系数：形级 Schur–Weyl 的收口**（第 631 轮）

§45 已给「切片泛函的迹对偶 ∈ `tnm`」。本节把它与 `tnm_eq_span`（AGPR `lem:12.1.2` 的形级
Schur–Weyl：`T_n(d) = span{T_σ}`）**接上**，取出系数：

```
∃ c : S_d → F,   Σ_σ c σ • T_σ  =  sliceFormEnd w g
```

**三段**：

* `sliceDual_mem_span`：`sliceDual ∈ span{T_σ}`（`sliceDual_mem_tnm` ＋ `tnm_eq_span`）；
* `dualToForm`：**"迹对偶泛函 → 多线性映射"的线性等价**（`(E).symm.trans (MTPE).symm`），
  并给两条读数：`dualToForm (tSigmaLinear σ) = tSigmaMap σ`、
  `dualToForm (sliceDual w g) = sliceFormEnd w g`；
* **`sliceFormEnd_eq_sum_tSigmaMap`**：由 `Finsupp.mem_span_range_iff_exists_finsupp` 取 `c₀`，
  沿 `dualToForm` 运输（`map_sum`／`map_smul`）即得显式线性组合。

**`tSigmaMap σ` 是什么**：`T_σ` 的**多线性映射形态**（`MTPE.symm (tSigmaVec σ)`），
其求值律 `tSigmaMap_apply : tSigmaMap σ b = T_σ(⊗^d b)` 就是 AGPR `eq:12.2` 的形级形态。

**射程（诚实边界）**：本节只到**泛函层的线性组合**。**未做**：把每个 `σ` 对应到**块标签 `g` 下的
`tSigmaPoly` 字表**（即 `vs(σ,g)` 的构造）与**回推多项式层**（`hAdBd` 正文的收口）。
`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `Finsupp.mem_span_range_iff_exists_finsupp` 给的是
`c.sum (fun i a => a • v i)`（**`Finsupp.sum`**）⟹ 用 `c.sum_fintype (g) (fun _ => zero_smul _ _)`
（**方法形态**，不是 `Finsupp.sum_fintype c g h`）转成 `Finset` 和，才能用 `map_sum`／`map_smul`；
② `LinearEquiv.symm_apply_apply` 不能直接消 `(E).symm (tSigmaLinear σ)`（不是 `E x` 形态）
⟹ 先用 `← tensorPowerTraceDualEquiv_tSigmaVec` 把它写成 `E (tSigmaVec σ)`。 -/

/-- `T_σ` 的**多线性映射形态**（`sliceForm` 的 Schur–Weyl 目标）。 -/
noncomputable def tSigmaMap (F : Type) [Field F] (n : ℕ) (d : ℕ)
    (σ : Equiv.Perm (Fin d)) :
    MultilinearMap F (fun _ : Fin d => Module.End F (Fin n → F)) F :=
  (multilinearMapTensorPowerEquiv F (Fin n → F) d).symm (tSigmaVec F (Fin n → F) d σ)

#print axioms tSigmaMap

/-- 求值律：`tSigmaMap σ b = T_σ(⊗^d b)`。 -/
theorem tSigmaMap_apply (F : Type) [Field F] (n d : ℕ) (σ : Equiv.Perm (Fin d))
    (b : Fin d → Module.End F (Fin n → F)) :
    tSigmaMap F n d σ b = tSigma F (Fin n → F) d σ (PiTensorProduct.tprod F b) := by
  have h := multilinearMapTensorPowerEquiv_apply_dual (k := F) (V := Fin n → F) (m := d)
    (tSigmaMap F n d σ) b
  rw [tSigmaMap, LinearEquiv.apply_symm_apply, tensorPowerTraceDualEquiv_tSigmaVec] at h
  rw [tSigmaMap, ← h]
  rfl

#print axioms tSigmaMap_apply

/-- 迹对偶把 `tSigmaMap σ` 送回 `tSigmaLinear σ`。 -/
theorem dual_tSigmaMap (F : Type) [Field F] (n d : ℕ) (σ : Equiv.Perm (Fin d)) :
    tensorPowerTraceDualEquiv F (Fin n → F) d
        (multilinearMapTensorPowerEquiv F (Fin n → F) d (tSigmaMap F n d σ))
      = tSigmaLinear F (Fin n → F) d σ := by
  rw [tSigmaMap, LinearEquiv.apply_symm_apply, tensorPowerTraceDualEquiv_tSigmaVec]

#print axioms dual_tSigmaMap

/-- 「迹对偶泛函 → 多线性映射」的线性等价（`sliceDual` 的逆）。 -/
noncomputable def dualToForm (F : Type) [Field F] (n d : ℕ) :
    Module.Dual F (TensorPower F d (Module.End F (Fin n → F)))
      ≃ₗ[F] MultilinearMap F (fun _ : Fin d => Module.End F (Fin n → F)) F :=
  (tensorPowerTraceDualEquiv F (Fin n → F) d).symm.trans
    (multilinearMapTensorPowerEquiv F (Fin n → F) d).symm

#print axioms dualToForm

theorem dualToForm_tSigmaLinear (F : Type) [Field F] (n d : ℕ) (σ : Equiv.Perm (Fin d)) :
    dualToForm F n d (tSigmaLinear F (Fin n → F) d σ) = tSigmaMap F n d σ := by
  rw [dualToForm, LinearEquiv.trans_apply, ← tensorPowerTraceDualEquiv_tSigmaVec,
    LinearEquiv.symm_apply_apply, tSigmaMap]

#print axioms dualToForm_tSigmaLinear

theorem dualToForm_sliceDual (F : Type) [Field F] (r n d : ℕ)
    (w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    dualToForm F n d (sliceDual F r n d w g) = sliceFormEnd F r n d w g := by
  rw [sliceDual, dualToForm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

#print axioms dualToForm_sliceDual

/-- 切片泛函经 `tnm_eq_span` 落在 `T_σ` 的张成里。 -/
theorem sliceDual_mem_span (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    [NeZero (Nat.factorial d : F)] (g : Fin d → Fin r)
    {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) w)
    (hw : IsBlockInvariant F r n d w) :
    sliceDual F r n d w g ∈ Submodule.span F
      (Set.range (fun σ : Equiv.Perm (Fin d) => tSigmaLinear F (Fin n → F) d σ)) := by
  rw [← tnm_eq_span (k := F) (m := d) (n := n)]
  exact sliceDual_mem_tnm F r n d g hv hw

#print axioms sliceDual_mem_span

/-- ★★★★★ **取系数**：切片泛函 ＝ `T_σ` 多线性映射的有限线性组合。 -/
theorem sliceFormEnd_eq_sum_tSigmaMap (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    [NeZero (Nat.factorial d : F)] (g : Fin d → Fin r)
    {w : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F}
    (hv : IsBlockMultilinear F d (Fin r × Fin n × Fin n) w)
    (hw : IsBlockInvariant F r n d w) :
    ∃ c : Equiv.Perm (Fin d) → F,
      (∑ σ, c σ • tSigmaMap F n d σ) = sliceFormEnd F r n d w g := by
  classical
  obtain ⟨c₀, hc₀⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (sliceDual_mem_span F r n d g hv hw)
  refine ⟨fun σ => c₀ σ, ?_⟩
  have hc : (∑ σ, c₀ σ • tSigmaLinear F (Fin n → F) d σ) = sliceDual F r n d w g := by
    rw [← hc₀]
    exact (c₀.sum_fintype (fun σ a => a • tSigmaLinear F (Fin n → F) d σ)
      (fun _ => zero_smul _ _)).symm
  rw [← dualToForm_sliceDual (w := w), ← hc, map_sum]
  exact Finset.sum_congr rfl (fun σ _ => by rw [map_smul, dualToForm_tSigmaLinear])

#print axioms sliceFormEnd_eq_sum_tSigmaMap


/-! ## 切分第 53 步：★★★★★ **`vs(σ, g)` 字表构造**（字表字典的入口；第 637 轮）

把 `σ` 的**循环分解**翻译成 §41 的**字表**形态 `List (List (Fin d × Fin r))`：

* `vsOfBlock σ x`：一个块（`BlockIdx σ` 的 `Sum.inl` 轮换 ／ `Sum.inr` 不动点）对应的字——
  沿 `cycEnum`（FFTIdentification 的循环枚举）取槽，逐个打上标签 `g j`；
* **`vsOf σ g`**：所有块的字拼起来（`Finset.univ` 上的列表）。

**为何用 `BlockIdx`／`cycEnum` 而不新造循环分解**（L47「库内已有优先于自建」）：`FFTIdentification`
的 `sigmaRMap`（AGPR `eq:12.3` 的机检件，`:3282`）**正是**按这同一套块结构展开的
（`sigmaRMap_apply` ＋ `cycBlockMap_apply` ＝ 沿 `cycEnum` 的乘链之迹），故两边**天然同构**，
主恒等式 `sliceForm (tSigmaPoly (vsOf σ g)) g = tSigmaMap σ` 只需对齐乘积次序。

**射程（诚实边界）**：本节只给**构造**（定义本身）。**未做**：`vsOf` 的槽覆盖性、label-g、
主恒等式、`hAdBd` 正文。`hZ` 未证；H2 仍不是定理。 -/

/-- 一个块（轮换或不动点）对应的**字**：`(槽, 矩阵标签)` 的列表。 -/
noncomputable def vsOfBlock (F : Type) [Field F] (r _n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (x : BlockIdx σ) : List (Fin d × Fin r) :=
  match x with
  | Sum.inl c =>
    (List.ofFn (fun i : Fin c.1.support.card =>
      slotVal σ ⟨Sum.inl c, cycEnum c.1 (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
        (c.1.support.min' (Finset.card_pos.mp (by
          have h := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.two_le_card_support
          omega)))
        (Finset.min'_mem _ _) i⟩)).map (fun j => (j, g j))
  | Sum.inr i => [(slotVal σ ⟨Sum.inr i, ()⟩, g (slotVal σ ⟨Sum.inr i, ()⟩))]

#print axioms vsOfBlock

/-- ★★★★★ **`σ` 的循环分解决定的字表**（字表字典的入口）。 -/
noncomputable def vsOf (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) : List (List (Fin d × Fin r)) :=
  ((Finset.univ : Finset (BlockIdx σ)).toList).map (fun x => vsOfBlock F r n d g σ x)

#print axioms vsOf


/-! ## 切分第 54 步：★★★★ **字表的标签一致性**（label-g 判据的第一步；第 638 轮）

`vsOfBlock` 的每个对子 `(j, k)` 都有 `k = g j`——这是 `tSigmaPoly (vsOf σ g)` 的 **label-g** 性质
（进入 §48 忠实性的第二前提）的组合基础。

**射程（诚实边界）**：本节只给**块级**标签一致性。**未做**：`vsOf` 整体的 label-g（需
`killLabelsK` 与迹的交换）、槽覆盖性、主恒等式、`hAdBd` 正文。`hZ` 未证；H2 仍不是定理。 -/

/-- `vsOfBlock` 的每个对子都带标签 `g`。 -/
theorem mem_vsOfBlock (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (x : BlockIdx σ) {p : Fin d × Fin r}
    (hp : p ∈ vsOfBlock F r n d g σ x) : p.2 = g p.1 := by
  cases x with
  | inl c =>
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    rfl
  | inr i =>
    simp only [vsOfBlock, List.mem_singleton] at hp
    rw [hp]
#print axioms mem_vsOfBlock

/-! ## 切分第 55 步：★★★★★★ **字表主恒等式 ＋ 槽覆盖 ＋ label-g**（第 639 轮）

§53 给了字表 `vs(σ,g)`（`vsOf`），§54 给了**块级**标签一致性。本节把它补成 §4.3 装配所需的
**三件输入** ＋ **主恒等式**：

* **主恒等式** `sliceForm_tSigmaPoly_vsOf`：`sliceForm (tSigmaPoly (vsOf σ g)) g Y = T_σ (toLin' ∘ Y)`。
  机制 = 两端都化成「沿 `BlockIdx σ` 的迹乘积」再**逐块对齐**（`block_word_eq`）：
  LHS 由 §44 `sliceForm_eq_evalBlock_expansion` ＋ §38 `evalBlock_tSigmaPoly` 得
  `∏_x tr(∏_{p ∈ vsOfBlock x} zeroFilled g Y p)`，其中 `zeroFilled g Y (j, g j) = Y j`（`zeroFilled_self`）；
  RHS 由 `tSigmaMap_apply` → `tSigma_eq_sigmaRMap`（`eq:12.3`）→ `sigmaRMap_apply` 得
  `∏_x blockMap x (fun b => toLin' (Y (slotVal ⟨x,b⟩)))`；逐块用 `cycBlockMap_apply`／
  `blockMap_inr_apply` 展开，再用 `trace_prod_toLin'`（矩阵迹 ↔ `End` 乘积迹）接上。
* **槽覆盖** `vsOf_slots_prod`：`∏_w ∏_{p∈w} λ_{p.1} = ∏_j λ_j`（每槽恰一次）——由
  `blockEquiv`（§36 的块划分等价）＋ `Fintype.prod_sigma` 得；配 §51 判据即
  `isBlockMultilinear_tSigmaPoly_vsOf`（**主恒等式的 `hv` 前提由本节自供**）。
* **label-g** `killLabelsK_tSigmaPoly_vsOf`：字表所有变元都带标签 `g`（§48 忠实性的第二前提）——
  由 `mem_vsOfBlock`（§54）＋ `killLabelsK` 与迹的交换（`killLabelsK_trace`）得。

**射程（诚实边界）**：本节只给**这三件输入**。**未做**：`hAdBd` 的装配（把 §46 的系数
`c_σ` 与这里的 `P_σ = tSigmaPoly (vsOf σ g)` 组合，经 §48 忠实性落进 `adjoin`）。
`invariantAlg = traceAlgS`、β1、β2 **未证**；`hZ` 未证；`S'^N ⊆ Z` 未证；H2 仍不是定理。

**工艺（教训登记）**：① `blockBeta σ (Sum.inl c)` 在 `rw` 的 implicit transparency 下不展开
⟹ 逐块陈述**直接写成具体槽类型**（`↥c.1.support`／`Unit`）并用 `exact`（default transparency）拼接，
不走 `rw`；② 需 `Fintype (blockBeta σ x)`（变元 `x` 上）⟹ 必须显式登记 `blockBetaFintype`
（instance search 不会展开 `blockBeta`）；③ `Matrix.trace_map` 在本 pin 的 mathlib 里是
**代数等价作用**的形态（不是 `RingHom` 形态）⟹ 迹与 `killLabelsK` 的交换在文件内自证
（`killLabelsK_trace`：`Matrix.trace` 展开成 `∑ i, M i i` ＋ `map_sum`）。 -/

/-- **迹桥**：矩阵的迹 ＝ 其 `End` 形态的迹。 -/
theorem trace_toLin' (F : Type) [Field F] (n : ℕ) (M : Matrix (Fin n) (Fin n) F) :
    M.trace = LinearMap.trace F (Fin n → F) (Matrix.toLin' M) := by
  rw [LinearMap.trace_eq_matrix_trace (R := F) (M := Fin n → F) (Pi.basisFun F (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

#print axioms trace_toLin'

/-- `toLin'` 保列表乘积。 -/
theorem toLin'_listProd (F : Type) [Field F] (n : ℕ) (l : List (Matrix (Fin n) (Fin n) F)) :
    Matrix.toLin' (l.prod) = (l.map Matrix.toLin').prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, Matrix.toLin'_one,
      Module.End.one_eq_id]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, Matrix.toLin'_mul,
      ← Module.End.mul_eq_comp, ih]

#print axioms toLin'_listProd

/-- **列表乘积的迹桥**。 -/
theorem trace_prod_toLin' (F : Type) [Field F] (n : ℕ)
    (l : List (Matrix (Fin n) (Fin n) F)) :
    (l.prod).trace = LinearMap.trace F (Fin n → F) ((l.map Matrix.toLin').prod) := by
  rw [trace_toLin', toLin'_listProd]

#print axioms trace_prod_toLin'

/-- 零填充在「恰为 `label`」处就是 `Y`。 -/
theorem zeroFilled_self (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) (j : Fin d) :
    zeroFilled F r n d g Y (j, g j) = Y j := by
  ext i l
  rw [zeroFilled_apply, ite_eq_left rfl]

#print axioms zeroFilled_self

/-- `vsOf` 的列表乘积就是 `BlockIdx` 上的乘积。 -/
theorem vsOf_map_prod (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (M : Type) [CommMonoid M]
    (f : List (Fin d × Fin r) → M) :
    ((vsOf F r n d g σ).map f).prod = ∏ x : BlockIdx σ, f (vsOfBlock F r n d g σ x) := by
  rw [vsOf, List.map_map, Finset.prod_map_toList]
  rfl

#print axioms vsOf_map_prod

/-- ★★★★ **轮换块对齐**：`vsOfBlock` 的矩阵迹 ＝ 沿 `cycEnum` 的 `End` 乘链之迹。 -/
theorem block_word_eq_inl (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (Y : Fin d → Matrix (Fin n) (Fin n) F)
    (c : ↥σ.cycleFactorsFinset) :
    (((vsOfBlock F r n d g σ (Sum.inl c)).map (zeroFilled F r n d g Y)).prod).trace
      = cycBlockMap F (Fin n → F) c.1
          (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
          (c.1.support.min' (Finset.card_pos.mp (by
            have h := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.two_le_card_support
            omega)))
          (Finset.min'_mem _ _)
          (fun b => Matrix.toLin' (Y (slotVal σ ⟨Sum.inl c, b⟩))) := by
  rw [vsOfBlock, cycBlockMap_apply, List.map_map]
  have hcomp : (zeroFilled F r n d g Y) ∘ (fun j => (j, g j)) = (fun j => Y j) := by
    funext j
    exact zeroFilled_self F r n d g Y j
  rw [hcomp, List.map_ofFn, trace_prod_toLin', List.map_ofFn]
  rfl

#print axioms block_word_eq_inl

/-- ★★★★ **不动点块对齐**：`vsOfBlock` 的矩阵迹 ＝ 单槽迹。 -/
theorem block_word_eq_inr (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (Y : Fin d → Matrix (Fin n) (Fin n) F)
    (i : ↥σ.supportᶜ) :
    (((vsOfBlock F r n d g σ (Sum.inr i)).map (zeroFilled F r n d g Y)).prod).trace
      = LinearMap.trace F (Fin n → F) (Matrix.toLin' (Y (slotVal σ ⟨Sum.inr i, ()⟩))) := by
  rw [vsOfBlock, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    zeroFilled_self, trace_toLin']

#print axioms block_word_eq_inr

/-- ★★★★★ **逐块对齐**：`vsOfBlock` 的矩阵迹 ＝ `blockMap` 在 `End` 层的值。 -/
theorem block_word_eq (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (Y : Fin d → Matrix (Fin n) (Fin n) F) (x : BlockIdx σ) :
    (((vsOfBlock F r n d g σ x).map (zeroFilled F r n d g Y)).prod).trace
      = blockMap F (Fin n → F) σ x
          (fun b => Matrix.toLin' (Y (slotVal σ ⟨x, b⟩))) := by
  cases x with
  | inl c => exact block_word_eq_inl F r n d g σ Y c
  | inr i => exact block_word_eq_inr F r n d g σ Y i

#print axioms block_word_eq

/-- 块的槽类型是有限的。 -/
instance blockBetaFintype {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : BlockIdx σ) :
    Fintype (blockBeta σ x) := by
  cases x with
  | inl c => exact (inferInstance : Fintype ↥c.1.support)
  | inr i => exact (inferInstance : Fintype Unit)

#print axioms blockBetaFintype

/-- 轮换块的槽乘子。 -/
theorem vsOfBlock_prod_inl (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (lam : Fin d → F) (c : ↥σ.cycleFactorsFinset) :
    ((vsOfBlock F r n d g σ (Sum.inl c)).map (fun p => lam p.1)).prod
      = ∏ b : ↥c.1.support, lam (slotVal σ ⟨Sum.inl c, b⟩) := by
  rw [vsOfBlock, List.map_map, List.map_ofFn, List.prod_ofFn]
  refine Fintype.prod_equiv
    (cycEnum c.1 (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
      (c.1.support.min' (Finset.card_pos.mp (by
        have h := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1.two_le_card_support
        omega)))
      (Finset.min'_mem _ _)) _ _ ?_
  intro i
  rfl

#print axioms vsOfBlock_prod_inl

/-- 不动点块的槽乘子。 -/
theorem vsOfBlock_prod_inr (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (lam : Fin d → F) (i : ↥σ.supportᶜ) :
    ((vsOfBlock F r n d g σ (Sum.inr i)).map (fun p => lam p.1)).prod
      = ∏ b : Unit, lam (slotVal σ ⟨Sum.inr i, b⟩) := by
  rw [vsOfBlock, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Fintype.prod_unique]

#print axioms vsOfBlock_prod_inr

/-- 每块的槽乘子。 -/
theorem vsOfBlock_prod (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (lam : Fin d → F) (x : BlockIdx σ) :
    ((vsOfBlock F r n d g σ x).map (fun p => lam p.1)).prod
      = ∏ b : blockBeta σ x, lam (slotVal σ ⟨x, b⟩) := by
  cases x with
  | inl c => exact vsOfBlock_prod_inl F r n d g σ lam c
  | inr i => exact vsOfBlock_prod_inr F r n d g σ lam i

#print axioms vsOfBlock_prod

/-- ★★★★★ **槽覆盖**：`vsOf σ g` 的每个槽恰出现一次（伸缩因子 ＝ `∏_j lam j`）。 -/
theorem vsOf_slots_prod (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) (lam : Fin d → F) :
    ((vsOf F r n d g σ).map (fun w => (w.map (fun p => lam p.1)).prod)).prod
      = ∏ j, lam j := by
  rw [vsOf_map_prod]
  refine Eq.trans (Finset.prod_congr rfl (fun x _ => vsOfBlock_prod F r n d g σ lam x)) ?_
  trans ∏ p : (Σ x : BlockIdx σ, blockBeta σ x), lam (slotVal σ p)
  · exact (Fintype.prod_sigma
      (fun p : (Σ x : BlockIdx σ, blockBeta σ x) => lam (slotVal σ p))).symm
  · exact Fintype.prod_equiv (blockEquiv σ) _ _ (fun p => rfl)

#print axioms vsOf_slots_prod

/-- ★★★★★ **`tSigmaPoly (vsOf σ g)` 块多线性**（§51 判据 ＋ 槽覆盖）。 -/
theorem isBlockMultilinear_tSigmaPoly_vsOf (F : Type) [Field F] (r n d : ℕ)
    (g : Fin d → Fin r) (σ : Equiv.Perm (Fin d)) :
    IsBlockMultilinear F d (Fin r × Fin n × Fin n)
      (tSigmaPoly F r n d (vsOf F r n d g σ)) :=
  isBlockMultilinear_tSigmaPoly F r n d _ (fun lam => vsOf_slots_prod F r n d g σ lam)

#print axioms isBlockMultilinear_tSigmaPoly_vsOf

/-- ★★★★★ **主恒等式**：`tSigmaPoly (vsOf σ g)` 的 `g`-切片 ＝ `T_σ` 的 `End` 层形态。 -/
theorem sliceForm_tSigmaPoly_vsOf (F : Type) [Field F] (r n d : ℕ) [Infinite F]
    (g : Fin d → Fin r) (σ : Equiv.Perm (Fin d)) (Y : Fin d → Matrix (Fin n) (Fin n) F) :
    sliceForm F r n d (tSigmaPoly F r n d (vsOf F r n d g σ)) g Y
      = tSigmaMap F n d σ (fun j => Matrix.toLin' (Y j)) := by
  classical
  rw [tSigmaMap_apply, tSigma_eq_sigmaRMap, sigmaRMap_apply]
  rw [sliceForm_eq_evalBlock_expansion F r n d g Y
      (isBlockMultilinear_tSigmaPoly_vsOf F r n d g σ), evalBlock_tSigmaPoly, vsOf_map_prod]
  exact Finset.prod_congr rfl (fun x _ => block_word_eq F r n d g σ Y x)

#print axioms sliceForm_tSigmaPoly_vsOf

/-- `killLabelsK` 把迹送到矩阵映射的迹。 -/
theorem killLabelsK_trace (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)) :
    killLabelsK F r n d g M.trace = (M.map (killLabelsK F r n d g)).trace := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

#print axioms killLabelsK_trace

/-- `killLabelsK` 固定「标签正确」的块矩阵。 -/
theorem killLabelsK_blkMatrix_self (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (j : Fin d) :
    (blkMatrix F r n d j (g j)).map (killLabelsK F r n d g) = blkMatrix F r n d j (g j) := by
  ext i l
  rw [Matrix.map_apply, blkMatrix, killLabelsK_X, ite_eq_left rfl]

#print axioms killLabelsK_blkMatrix_self

/-- `killLabelsK` 固定标签全对的字迹。 -/
theorem killLabelsK_blockTraceWord (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (v : List (Fin d × Fin r)) (hv : ∀ p ∈ v, p.2 = g p.1) :
    killLabelsK F r n d g (blockTraceWord F r n d v) = blockTraceWord F r n d v := by
  rw [blockTraceWord, killLabelsK_trace]
  congr 1
  induction v with
  | nil => exact Matrix.map_one (killLabelsK F r n d g) (map_zero _) (map_one _)
  | cons p v ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul,
      ih (fun q hq => hv q (List.mem_cons_of_mem p hq)),
      hv p List.mem_cons_self, killLabelsK_blkMatrix_self]

#print axioms killLabelsK_blockTraceWord

/-- `vsOf` 的每个字都标签正确（§54 的整体形态）。 -/
theorem mem_vsOf_flatten (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) {w : List (Fin d × Fin r)}
    (hw : w ∈ vsOf F r n d g σ) : ∀ p ∈ w, p.2 = g p.1 := by
  rw [vsOf] at hw
  obtain ⟨x, -, hx⟩ := List.mem_map.mp hw
  rw [← hx]
  intro p hp
  exact mem_vsOfBlock F r n d g σ x hp

#print axioms mem_vsOf_flatten

/-- ★★★★★ **label-g**：`tSigmaPoly (vsOf σ g)` 的所有变元都带标签 `g`。 -/
theorem killLabelsK_tSigmaPoly_vsOf (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (σ : Equiv.Perm (Fin d)) :
    killLabelsK F r n d g (tSigmaPoly F r n d (vsOf F r n d g σ))
      = tSigmaPoly F r n d (vsOf F r n d g σ) := by
  rw [tSigmaPoly, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left (fun w hw => killLabelsK_blockTraceWord F r n d g w
    (mem_vsOf_flatten F r n d g σ hw))

#print axioms killLabelsK_tSigmaPoly_vsOf

/-! ## 切分第 56 步：★★★★★★★★ **装配 ＝ `hAdBd` 正文 ＋ FFT `thm:12.1.3` 收口**（第 640 轮）

§55 给了三件输入（主恒等式／槽覆盖／label-g），§46 给了取系数，§48 给了忠实性，§42 给了标签分裂。
本节把它们**装配**起来，得到 AGPR `lem:12.1.2` 的正文，进而**收口 FFT 难半**：

```
多线性 ∩ 块不变量  ⊆  T_σ 环            （mem_adjoin_tSigmaPoly_of_multilinear_blockInvariant）
  ⟹ hAdBd                                （adBd_tSigmaPoly）
  ⟹ invariantAlg ≤ traceAlgS             （invariantAlg_le_traceAlgS，thm:12.1.3 的难半）
  ⟹ invariantAlg = traceAlgS             （invariantAlg_eq_traceAlgS，thm:12.1.3）
```

**装配的四步**（对每个标签 `g`：`w_g := killLabelsK g w`）：
1. **取系数**（§46）：`∃ c, ∑_σ c_σ • T_σ = sliceFormEnd w_g g`（用 `IsBlockMultilinear`＋`IsBlockInvariant`）；
2. **候选组合** `q := ∑_σ c_σ • tSigmaPoly (vsOf σ g)`：块多线性（§51＋槽覆盖）、label-g
   （§55 ＋ `killLabelsK_smul`）、切片 `= sliceForm w_g g`（线性性 ＋ **主恒等式**§55 ＋ `hc`）；
3. **忠实性**（§48）⟹ `w_g = q`；而 `q` 是 `adjoin (range tSigmaPoly)` 里的线性组合；
4. **标签分裂**（§42 `sum_killLabelsK`）⟹ `w = ∑_g w_g ∈ adjoin`。

**`CharZero` 如何进入**：§46 需要 `[NeZero (d.factorial : F)]`；本节由 `CharZero F` 用
`factorial_ne_zero_of_charZero` 提供，`Infinite F` 由 `Nat.cast_injective` 提供（不引入新假设）。

**射程（诚实边界）**：本节收口的是 **FFT 的 `thm:12.1.3`**。**未做**：(β) 搬到 `Spr` 世界
（`hZ ⟺ sprNFixedField ≤ sprCenterImageField`，β1／β2）；`S'^N ⊆ Z` 未证；`UDKTensorHypK'`
的真值 `∅-unchecked`；**H2 仍不是无条件定理**（`hZ` 未证）。

**工艺（教训登记）**：① `sliceForm_smul` 的逐项收口需要 **`smul_eq_mul` ＋ `smul_smul` 两步**
（`(c • a) • m` 与 `(c * a) • m` 在字段自作用上只差一次 `smul_eq_mul`）；
② **多线性映射的有限和逐点取值须自证**（L70：`MultilinearMap` 不是函数类型，
`Finset.sum_apply` 不可用）——新件 `multilinearMap_sum_apply` 对**一般指标族**归纳；
③ 装配里**必须**先把 `sliceForm` 与 `sliceFormEnd` 用 `sliceForm_eq_sliceFormEnd_apply` 对接
（`toMatrix' ∘ toLin' = id`），否则 §46 的系数等式无法与矩阵层切片比较。 -/

/-- `sliceForm` 对标量倍数线性。 -/
theorem sliceForm_smul (F : Type) [Field F] (r n d : ℕ) (c : F)
    (p : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    sliceForm F r n d (c • p) g = c • sliceForm F r n d p g := by
  rw [sliceForm, sliceForm, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, smul_smul]

#print axioms sliceForm_smul

/-- `sliceForm` 对有限和线性。 -/
theorem sliceForm_sum (F : Type) [Field F] (r n d : ℕ) {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r) :
    sliceForm F r n d (∑ i ∈ s, p i) g = ∑ i ∈ s, sliceForm F r n d (p i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp [sliceForm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sliceForm_add, ih]

#print axioms sliceForm_sum

/-- `killLabelsK` 对标量倍数线性。 -/
theorem killLabelsK_smul (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r) (c : F)
    (p : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :
    killLabelsK F r n d g (c • p) = c • killLabelsK F r n d g p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, killLabelsK_C]

#print axioms killLabelsK_smul

/-- `killLabelsK` 幂等。 -/
theorem killLabelsK_idem (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r) :
    (killLabelsK F r n d g).comp (killLabelsK F r n d g) = killLabelsK F r n d g := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun x => ?_)
  · simp [killLabelsK_C]
  · rw [RingHom.comp_apply, killLabelsK_X]
    by_cases h : x.2.1 = g x.1
    · rw [ite_eq_left h, killLabelsK_X, ite_eq_left h]
    · rw [ite_eq_right h, map_zero]

#print axioms killLabelsK_idem

/-- `killLabelsK` 幂等（逐元形态）。 -/
theorem killLabelsK_idem_apply (F : Type) [Field F] (r n d : ℕ) (g : Fin d → Fin r)
    (p : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) :
    killLabelsK F r n d g (killLabelsK F r n d g p) = killLabelsK F r n d g p :=
  RingHom.congr_fun (killLabelsK_idem F r n d g) p

#print axioms killLabelsK_idem_apply

/-- 多线性映射的有限和逐点取值（L70：`MultilinearMap` 不是函数类型，须归纳）。 -/
theorem multilinearMap_sum_apply (F : Type) [Field F] {ιd : Type*} {M₁ : ιd → Type*}
    [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module F (M₁ i)] {ι : Type*} (s : Finset ι)
    (f : ι → MultilinearMap F M₁ F) (Y : (i : ιd) → M₁ i) :
    (∑ i ∈ s, f i) Y = ∑ i ∈ s, f i Y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

#print axioms multilinearMap_sum_apply

/-- `sliceForm` 与 `sliceFormEnd` 的逐点桥。 -/
theorem sliceForm_eq_sliceFormEnd_apply (F : Type) [Field F] (r n d : ℕ)
    (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F) (g : Fin d → Fin r)
    (Y : Fin d → Matrix (Fin n) (Fin n) F) :
    sliceForm F r n d v g Y
      = sliceFormEnd F r n d v g (fun j => Matrix.toLin' (Y j)) := by
  rw [sliceFormEnd_apply]
  congr 1
  funext j
  exact (LinearMap.toMatrix'_toLin' (Y j)).symm

#print axioms sliceForm_eq_sliceFormEnd_apply

/-- ★★★★★★★ **装配**（AGPR `lem:12.1.2` 正文的机检形态）：多线性块不变量落在
`T_σ` 单项生成的子代数里。 -/
theorem mem_adjoin_tSigmaPoly_of_multilinear_blockInvariant (F : Type) [Field F] [CharZero F]
    (r n d : ℕ) (v : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F)
    (hv : v ∈ multilinearSubmodule F d (Fin r × Fin n × Fin n))
    (hvi : v ∈ blockInvariantSubmodule F r n d) :
    v ∈ Algebra.adjoin F (Set.range (tSigmaPoly F r n d)) := by
  classical
  haveI hInf : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  haveI hfact : NeZero (Nat.factorial d : F) := ⟨factorial_ne_zero_of_charZero F d⟩
  rw [← sum_killLabelsK F r n d hv]
  refine Subalgebra.sum_mem _ (fun g _ => ?_)
  obtain ⟨c, hc⟩ := sliceFormEnd_eq_sum_tSigmaMap F r n d g
    (killLabelsK_mem_multilinearSubmodule F r n d hv g)
    (killLabelsK_mem_blockInvariantSubmodule F r n d hvi g)
  set q : MvPolynomial (Fin d × (Fin r × Fin n × Fin n)) F :=
    ∑ σ, c σ • tSigmaPoly F r n d (vsOf F r n d g σ) with hq
  have hq_mult : IsBlockMultilinear F d (Fin r × Fin n × Fin n) q := by
    rw [hq]
    exact isBlockMultilinear_sum F d _ Finset.univ (fun σ _ =>
      isBlockMultilinear_smul F d _ (c σ) (isBlockMultilinear_tSigmaPoly_vsOf F r n d g σ))
  have hq_label : killLabelsK F r n d g q = q := by
    rw [hq, map_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [killLabelsK_smul, killLabelsK_tSigmaPoly_vsOf]
  have hq_slice : sliceForm F r n d q g
      = sliceForm F r n d (killLabelsK F r n d g v) g := by
    refine MultilinearMap.ext (fun Y => ?_)
    rw [hq, sliceForm_sum, multilinearMap_sum_apply,
      sliceForm_eq_sliceFormEnd_apply (v := killLabelsK F r n d g v) (Y := Y),
      ← hc, multilinearMap_sum_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [sliceForm_smul, smul_apply, sliceForm_tSigmaPoly_vsOf, smul_apply]
  have hvge : killLabelsK F r n d g v = q :=
    sliceForm_faithful F r n d g
      (killLabelsK_mem_multilinearSubmodule F r n d hv g) hq_mult
      (killLabelsK_idem_apply F r n d g v) hq_label hq_slice.symm
  rw [hvge, hq]
  exact Subalgebra.sum_mem _ (fun σ _ =>
    Subalgebra.smul_mem _ (tSigmaPoly_mem_adjoin F r n d (vsOf F r n d g σ)) (c σ))

#print axioms mem_adjoin_tSigmaPoly_of_multilinear_blockInvariant

end Procesi

namespace Procesi

/-- ★★★★★★★ **`hAdBd` 正文（机检）**：多线性块不变量 ⊆ 多线性块迹代数。 -/
theorem adBd_tSigmaPoly (F : Type) [Field F] [CharZero F] (r n d : ℕ) :
    multilinearSubmodule F d (Fin r × Fin n × Fin n) ⊓ blockInvariantSubmodule F r n d
      ≤ multilinearSubmodule F d (Fin r × Fin n × Fin n)
        ⊓ (blockTraceAlg F r n d).toSubmodule :=
  adBd_of_tSigma F r n d (fun v hv hvi =>
    mem_adjoin_tSigmaPoly_of_multilinear_blockInvariant F r n d v hv hvi)

#print axioms adBd_tSigmaPoly

/-- ★★★★★★★★ **FFT 难半（机检）**：`thm:12.1.3` 的「不变量 ⊆ 迹环」。 -/
theorem invariantAlg_le_traceAlgS (F : Type) [Field F] [CharZero F] (r n : ℕ) :
    invariantAlg F r n ≤ traceAlgS F r n :=
  invariantAlg_le_traceAlgS_of_tSigma F r n
    (fun d v hv hvi => mem_adjoin_tSigmaPoly_of_multilinear_blockInvariant F r n d v hv hvi)

#print axioms invariantAlg_le_traceAlgS

/-- ★★★★★★★★ **FFT `thm:12.1.3`（机检，等式）**：不变量环 ＝ 迹环。 -/
theorem invariantAlg_eq_traceAlgS (F : Type) [Field F] [CharZero F] (r n : ℕ) :
    invariantAlg F r n = traceAlgS F r n :=
  le_antisymm (invariantAlg_le_traceAlgS F r n) (traceAlgS_le_invariantAlg F r n)

#print axioms invariantAlg_eq_traceAlgS

end Procesi

