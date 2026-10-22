/-
  Procesi —— `lem:14.24` 的 **`K'`-世界端口**（路线 (乙) 的第一格）

  **背景**：`lem1424_general`（`GenericInv:11111`）的定义域是 `M_n(S')`，而本工程的
  `thetaSpr1/2` 定义在 `M_n(K')` 上（`K' = SprField = FractionRing (Spr F r n)`）。
  直接把前者的结论搬回 `K'` 会**循环**（须 `S'^N ⊆ Z`，见
  [[proj-abgv52-h2-endgame-corrected]] §7.14／§7.17），故路线 (乙) = 在 `K'`-世界**重证**。

  §7.15 的判读：`lem1424_localNoNorm`（`GenericInv:10888`）对 `α` 的**唯一**使用是
  `hα`（`sprPsiMonoR`-不变性），其余步骤对任何交换环上的矩阵都成立 ⟹ 换域复制是**机械的**。
  §7.18 的端口清单六项。本件完成**第 1 项（及其 `θ₂` 侧对应物）**：

  | # | 件 | 内容 |
  |---|---|---|
  | 1 | `isMatrixUnitSystem_theta_stdMU_sprField` | `θ` 把 `stdMU` 送到矩阵单位系（证明不提定义域环） |
  | 1 | `sprFieldExistsEta1_local` | **`Ad_{u⁻¹} ∘ θ₁ = M_n(η₁)`**（`T` 局部） |
  | 1 | `sprFieldEta2_conj` | `AT θ₂ AT⁻¹ = M_n(η₂)` |
  | 1 | `sprFieldExistsEta2_local` | **`A θ₂ A⁻¹ = M_n(η₂)`**（`T` 局部） |

  **和 `Spr` 版的关系**：四条全部是 `GenericInv` 对应件的**逐字换域**
  （`Spr F r n → SprField F r n`），证明体一字未改 —— 这验证了 §7.15 的"机械复制"判读。

  **射程（勿夸大）**：本件只完成 §7.18 清单的**第 1 项**。第 2–6 项
  （`sprConj_unit_cancel`／`lem1424_localNoNorm`／`lem1424_local`／`lem1424_of_discrUnit`／
  `lem1424_general` 的换域）**均未做**；`ThetaAgreeHypK'` **未证**；`UDKTensorHypK'`（PI）**未证**；
  `hZ` **未证**；**H2 仍不是定理**。
-/

import Procesi.GenericInv

open Matrix

namespace Procesi

/-! ## §1 第一格：局部环下的归一化（`K'`-世界）

`Spr` 版见 `GenericInv`：`isMatrixUnitSystem_theta_stdMU_spr`（`:8943`）、
`sprEta2_conj`（`:8858`）、`sprExistsEta1_local`（`:10065`）、`sprExistsEta2_local`（`:10098`）。
本节的四条是**逐字换域**。 -/

section NormalizeField

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `θ` 把 `stdMU` 送到矩阵单位系（`K'`-世界）。

证明只用到 `stdMU` 的乘法表／求和与 `θ` 的同态性，**从不提及定义域环**——
这正是换域复制能逐字通过的原因。 -/
lemma isMatrixUnitSystem_theta_stdMU_sprField
    (θ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
    IsMatrixUnitSystem (fun i j => θ (stdMU (n := Fin n) i j)) where
  mul_mem i j k l := by
    show θ (stdMU (n := Fin n) i j) * θ (stdMU (n := Fin n) k l)
      = if j = k then θ (stdMU (n := Fin n) i l) else 0
    rw [← map_mul, stdMU_mul]
    split_ifs with h
    · rfl
    · exact map_zero θ
  sum_mem := by
    show ∑ i, θ (stdMU (n := Fin n) i i) = 1
    rw [← map_sum, stdMU_sum, map_one]

#print axioms isMatrixUnitSystem_theta_stdMU_sprField

/-- ★★★ **归一化（`θ₁` 侧，`K'`-世界）**：`T` 局部时，存在单位 `u` 与 `η₁` 使
`↑u⁻¹ · θ₁ β · ↑u = β.map η₁`。

这是源文 "we may assume the `f_1(i,j)` are standard" 的机检形态（`[2.11]`）。 -/
theorem sprFieldExistsEta1_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₁ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
    ∃ u : (Matrix (Fin n) (Fin n) T)ˣ, ∃ η₁ : SprField F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
        (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₁ β
          * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
        = β.map η₁ := by
  obtain ⟨u, hu⟩ := exists_unit_conj_stdMU_of_isLocalRing (n := Fin n) (T := T)
    (isMatrixUnitSystem_theta_stdMU_sprField F r n T θ₁)
  have h₁ : ∀ i j, ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁)
      (stdMU (n := Fin n) (R := SprField F r n) i j)
      = (stdMU (n := Fin n) (R := T) i j) := by
    intro i j
    show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * θ₁ (stdMU (n := Fin n) i j) * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix _ _ T)
      = (stdMU (n := Fin n) (R := T) i j)
    have h := hu i j
    calc (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * θ₁ (stdMU (n := Fin n) i j) * ((u : (Matrix _ _ T)ˣ) : Matrix _ _ T)
        = (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix _ _ T)
            * (((u : (Matrix _ _ T)ˣ) : Matrix _ _ T) * (stdMU (n := Fin n) (R := T) i j)
              * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix _ _ T))
            * ((u : (Matrix _ _ T)ˣ) : Matrix _ _ T) := by
            rw [h]
        _ = (stdMU (n := Fin n) (R := T) i j) :=
            mul_inv_conj_mul u⁻¹ (stdMU (n := Fin n) (R := T) i j)
  obtain ⟨η₁, hη₁⟩ := exists_algHom_of_preserves_stdMU (F := F) (R := SprField F r n) (R' := T)
    (n := Fin n) ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) h₁
  exact ⟨u, η₁, fun β => hη₁ β⟩

#print axioms sprFieldExistsEta1_local

/-- ★★★ **`θ₂` 侧的归一化准备**（`K'`-世界）：若 `θ₂(stdMU i j) = ↑AT⁻¹ · stdMU i j · ↑AT`，
则 `↑AT · θ₂ β · ↑AT⁻¹ = β.map η₂`。 -/
theorem sprFieldEta2_conj [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
        * (AT : Matrix (Fin n) (Fin n) T)) :
    ∃ η₂ : SprField F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
        (AT : Matrix (Fin n) (Fin n) T) * θ₂ β
          * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) = β.map η₂ := by
  have h₂A : ∀ i j, ((conjAlgEquiv (F := F) AT).toAlgHom.comp θ₂) (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T) := by
    intro i j
    show (conjAlgEquiv (F := F) AT) (θ₂ (stdMU (n := Fin n) i j))
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
    rw [h₂ i j]
    show (AT : Matrix (Fin n) (Fin n) T)
        * ((((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
          * (AT : Matrix (Fin n) (Fin n) T))
        * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
    exact mul_inv_conj_mul AT (stdMU (n := Fin n) (R := T) i j)
  exact exists_algHom_of_preserves_stdMU (F := F) (R := SprField F r n) (R' := T) (n := Fin n)
    ((conjAlgEquiv (F := F) AT).toAlgHom.comp θ₂) h₂A

#print axioms sprFieldEta2_conj

/-- ★★★ **归一化（`θ₂` 侧，`K'`-世界）**：`T` 局部时，存在单位 `A` 与 `η₂` 使
`↑A · θ₂ β · ↑A⁻¹ = β.map η₂`。

**注意方向**（源文 "there is an `A` such that `A⁻¹f_1A = f₂`"）：本件把 `A` 取成 `u⁻¹`，
与 `GenericInv` 的 `sprExistsEta2_local` 同构。 -/
theorem sprFieldExistsEta2_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
    ∃ A : (Matrix (Fin n) (Fin n) T)ˣ, ∃ η₂ : SprField F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
        ((A : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) * θ₂ β
          * ((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
        = β.map η₂ := by
  obtain ⟨u, hu⟩ := exists_unit_conj_stdMU_of_isLocalRing (n := Fin n) (T := T)
    (isMatrixUnitSystem_theta_stdMU_sprField F r n T θ₂)
  have h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = ((((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)⁻¹) : (Matrix (Fin n) (Fin n) T)ˣ) :
          Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) (R := T) i j)
        * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by
    intro i j
    show θ₂ (stdMU (n := Fin n) i j)
      = (((u : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix _ _ T) * (stdMU (n := Fin n) (R := T) i j)
        * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix _ _ T)
    exact (hu i j).symm
  obtain ⟨η₂, hη₂⟩ := sprFieldEta2_conj F r n T θ₂ u⁻¹ h₂
  exact ⟨u⁻¹, η₂, fun β => by simpa using hη₂ β⟩

#print axioms sprFieldExistsEta2_local

end NormalizeField

/-! ## §2 第三格的辅助件（`K'`-世界）

`lem1424_local`（`GenericInv:10687`）用到五个辅助件。本节把**不涉及 `α` 与不变性**的
那几个换域（`sprStepThree_unitsUnit` 本身只涉及 `T`，**无需移植**）：

| 新件 | 对应 `Spr` 版 | 备注 |
|---|---|---|
| `sprFieldStdMU_map` | `sprStdMU_map`（`GenericInv:10574`） | `η` 的定义域换域 |
| `sprFieldScalar_map` | `sprScalar_map`（`GenericInv:10771`） | 同上 |
| `sprFieldDiscr_eq` | —（新拆的一步） | `algebraMap` 与乘积交换 |
| `sprFieldDiscr_map` | `sprDiscr_map`（`GenericInv:10251`） | 同上 |
| `sprFieldDiscrUnit` | `sprDiscrUnit`（`GenericInv:10785`） | 定义（内蕴判别式形态） |
| `sprFieldIsUnit_discr_of_discrUnit` | `sprIsUnit_discr_of_discrUnit`（`GenericInv:10793`） | 同上 |
| `sprFieldIsUnit_sub_of_discr_map` | `sprIsUnit_sub_of_discr_map`（`GenericInv:10257`） | 同上 |

**射程（勿夸大）**：本节只给**辅助件**。`lem1424_local`／`lem1424_local'`／
`lem1424_localNoNorm` 的换域（§7.18 清单第 3–4 项）**未做**；`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section DiscrField

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `stdMU` 沿 `K'`-代数同态的像。 -/
theorem sprFieldStdMU_map {S : Type} [CommRing S] [Algebra F S]
    (η : SprField F r n →ₐ[F] S) (i j : Fin n) :
    (stdMU (n := Fin n) (R := SprField F r n) i j).map η
      = stdMU (n := Fin n) (R := S) i j := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply]
  show η (stdMU (n := Fin n) (R := SprField F r n) i j a b)
    = stdMU (n := Fin n) (R := S) i j a b
  simp only [stdMU, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · rw [if_pos h, if_pos h, map_one]
  · rw [if_neg h, if_neg h, map_zero]

#print axioms sprFieldStdMU_map

/-- 纯量矩阵沿 `K'`-代数同态的像是纯量矩阵。 -/
theorem sprFieldScalar_map {S : Type} [CommRing S] [Algebra F S]
    (η : SprField F r n →ₐ[F] S) (Δ : SprField F r n) :
    (Matrix.scalar (Fin n) Δ).map η = Matrix.scalar (Fin n) (η Δ) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact map_zero η

#print axioms sprFieldScalar_map

/-- `Δ` 的 `K'`-像的显式形式（`algebraMap` 与乘积／差交换）。 -/
theorem sprFieldDiscr_eq :
    algebraMap (Spr F r n) (SprField F r n) (sprDiscr F (r := r) (n := n))
      = ∏ p ∈ sprDiscrIdx n,
          (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl p.1))
            - algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl p.2))) := by
  rw [sprDiscr, map_prod]
  exact Finset.prod_congr rfl (fun p _ => by rw [map_sub])

#print axioms sprFieldDiscr_eq

/-- `Δ` 沿 `η` 的像（`K'`-世界）。 -/
theorem sprFieldDiscr_map (η : SprField F r n →ₐ[F] T) :
    η (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F (r := r) (n := n)))
      = ∏ p ∈ sprDiscrIdx n,
          (η (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl p.1)))
            - η (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl p.2)))) := by
  rw [sprFieldDiscr_eq, map_prod]
  exact Finset.prod_congr rfl (fun p _ => by rw [map_sub])

#print axioms sprFieldDiscr_map

/-- 判别式条件（`K'`-世界的内蕴形态）：`θ(Δ·1)` 的纯量可逆。 -/
def sprFieldDiscrUnit
    (θ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (Δ : SprField F r n) : Prop :=
  ∃ x : T, θ (Matrix.scalar (Fin n) Δ) = Matrix.scalar (Fin n) x ∧ IsUnit x

#print axioms sprFieldDiscrUnit

/-- 内蕴判别式形态 ⟹ 归一形态（`K'`-世界）。 -/
theorem sprFieldIsUnit_discr_of_discrUnit [Nonempty (Fin n)]
    (θ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η : SprField F r n →ₐ[F] T)
    (hη : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n), θ β = β.map η)
    {Δ : SprField F r n} (h : sprFieldDiscrUnit F (r := r) (n := n) θ Δ) :
    IsUnit (η Δ) := by
  obtain ⟨x, hx, hxu⟩ := h
  rw [hη, sprFieldScalar_map] at hx
  have hx' : η Δ = x := Matrix.scalar_inj.mp hx
  rw [hx']
  exact hxu

#print axioms sprFieldIsUnit_discr_of_discrUnit

/-- 判别式给 `IsUnit (η x_j − η x_i)`（`K'`-世界）。 -/
theorem sprFieldIsUnit_sub_of_discr_map (η : SprField F r n →ₐ[F] T)
    (h : IsUnit (η (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F (r := r) (n := n)))))
    {i j : Fin n} (hij : i ≠ j) :
    IsUnit (η (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl j)))
      - η (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))) := by
  rw [sprFieldDiscr_map] at h
  exact sprIsUnit_sub_of_discr
    (fun i => η (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))) h hij

#print axioms sprFieldIsUnit_sub_of_discr_map

end DiscrField

/-! ## §3 第三格的两件「非逐字」辅助件（`K'`-世界）

`lem1424_local`（`GenericInv:10687`）的局部总装链里，`sprTheta_xdiag_eq`（`:10451`）与
`sprStepTwo_local`（`:10481`）都涉及 `xdiag` 在 `M_n(Spr)` 上的形态，**不可能逐字换域**。

**本节的工艺 = 传输（transport），不是重写**：

记 `φ : Spr →ₐ[F] SprField`（`IsScalarTower.toAlgHom`）。关键恒等式
`(stdMU (R := Spr) i j).map φ = stdMU (R := SprField) i j` **已在库**
（`sprStdMU_map` 对任意 `S` 成立，取 `S := SprField`）。于是对 `θ : M_n(SprField) →ₐ M_n(T)`

```
Θ := θ ∘ mapMatrix φ : M_n(Spr) →ₐ[F] M_n(T)          （F-代数同态）
η' := η ∘ φ : Spr →ₐ[F] T
```

套 `Spr`-世界的原引理得结论，再把 `Θ (stdMU …)` 用 `sprStdMU_map` 换回
`θ (stdMU (R := SprField) …)` 即得。**这条传输对 `sprStepTwo_local` 也成立**——
省掉了 `sprTheta_diag_ne_zero`／`sprStepOne_local`／`sprExistsPerm_of_diagIdem` 的逐个换域。

| 新件 | 对应 `Spr` 版 | 说明 |
|---|---|---|
| `sprFieldXdiag` | `xdiag F r n` | `xdiag` 的 `K'`-像（`def`） |
| `sprFieldXdiag_map` | `sprXdiag_map`（`:9607`） | |
| `sprFieldTheta_xdiag_eq` | `sprTheta_xdiag_eq`（`:10451`） | 直接换域 |
| `sprFieldStepOne_local` | `sprStepOne_local`（`:10465`） | **传输** |
| `sprFieldStepTwo_local` | `sprStepTwo_local`（`:10481`） | **传输** |

**工艺（一处 binder 陷阱）**：`sprStdMU_map` 的 `S` 是隐式、而 `F`／`r`／`n` 来自文件级
`variable`（`F` 显式）。写 `sprFieldStdMU_map (η := φ) i j` 会把 `i` 填到 `F` 的位置；
正解是**同时**给足 `(F := F) (S := …)` 再位置传 `i j`。另：本节的 `hstd` 必须用
**`sprStdMU_map`**（`Spr → S`）而非 `sprFieldStdMU_map`（`SprField → S`）——方向易错。

**射程（勿夸大）**：本节补齐第三格的**辅助件**。`lem1424_local`／`lem1424_local'`／
`lem1424_localNoNorm` 的换域（§7.18 清单第 3–4 项的主件）**未做**；`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section XdiagField

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `xdiag` 的 `K'`-像。 -/
noncomputable def sprFieldXdiag : Matrix (Fin n) (Fin n) (SprField F r n) :=
  (xdiag F r n).map (algebraMap (Spr F r n) (SprField F r n))

#print axioms sprFieldXdiag

/-- `xdiag` 的 `K'`-像沿同态的像仍是显式对角。 -/
theorem sprFieldXdiag_map (η : SprField F r n →ₐ[F] T) :
    (sprFieldXdiag F r n).map η
      = Matrix.diagonal (fun j => η (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl j)))) := by
  rw [sprFieldXdiag, Matrix.map_map]
  exact sprXdiag_map (F := F) (n := n) (r := r)
    (η.comp (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)))

#print axioms sprFieldXdiag_map

/-- `sprTheta_xdiag_eq` 的 `K'`-世界形态。 -/
theorem sprFieldTheta_xdiag_eq
    (η₁ : SprField F r n →ₐ[F] T)
    (θ₁ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n), θ₁ β = β.map η₁)
    (θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n)) :
    θ₂ (sprFieldXdiag F r n)
      = Matrix.diagonal (fun i => η₁ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl i)))) := by
  rw [← hX, h₁, sprFieldXdiag_map]

#print axioms sprFieldTheta_xdiag_eq

/-- `sprStepOne_local` 的 `K'`-世界形态（**传输**自 `Spr`-世界）。 -/
theorem sprFieldStepOne_local [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : SprField F r n →ₐ[F] T)
    (hC : θ₂ (sprFieldXdiag F r n)
      = Matrix.diagonal (fun i => η₁ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl i)))))
    (hc : ∀ i j : Fin n, i ≠ j →
      IsUnit (η₁ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl j)))
        - η₁ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))))
    (i : Fin n) :
    θ₂ (stdMU (n := Fin n) (R := SprField F r n) i i)
      = Matrix.diagonal (fun k => θ₂ (stdMU (n := Fin n) (R := SprField F r n) i i) k k) := by
  let φ : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  have hstd : ∀ i j, (stdMU (n := Fin n) (R := Spr F r n) i j).map φ
      = stdMU (n := Fin n) (R := SprField F r n) i j :=
    fun i j => sprStdMU_map (F := F) (S := SprField F r n) φ i j
  have hC' : (θ₂.comp (AlgHom.mapMatrix φ)) (xdiag F r n)
      = Matrix.diagonal (fun i => (η₁.comp φ) (MvPolynomial.X (Sum.inl i))) := by
    have hxd : AlgHom.mapMatrix φ (xdiag F r n) = sprFieldXdiag F r n := rfl
    show θ₂ (AlgHom.mapMatrix φ (xdiag F r n)) = _
    rw [hxd]
    exact hC
  have hc' : ∀ i j : Fin n, i ≠ j →
      IsUnit ((η₁.comp φ) (MvPolynomial.X (Sum.inl j))
        - (η₁.comp φ) (MvPolynomial.X (Sum.inl i))) := by
    intro i j hij
    exact hc i j hij
  have hres := sprStepOne_local F (θ₂.comp (AlgHom.mapMatrix φ)) (η₁.comp φ) hC' hc' i
  rw [← hstd i i]
  exact hres

#print axioms sprFieldStepOne_local

/-- `sprStepTwo_local` 的 `K'`-世界形态（**传输**）。 -/
theorem sprFieldStepTwo_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : SprField F r n →ₐ[F] T)
    (hC : θ₂ (sprFieldXdiag F r n)
      = Matrix.diagonal (fun i => η₁ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl i)))))
    (hc : ∀ i j : Fin n, i ≠ j →
      IsUnit (η₁ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl j)))
        - η₁ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i, θ₂ (stdMU (n := Fin n) (R := SprField F r n) (σ i) (σ i))
        = stdMU (n := Fin n) (R := T) i i := by
  let φ : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  have hstd : ∀ i j, (stdMU (n := Fin n) (R := Spr F r n) i j).map φ
      = stdMU (n := Fin n) (R := SprField F r n) i j :=
    fun i j => sprStdMU_map (F := F) (S := SprField F r n) φ i j
  have hC' : (θ₂.comp (AlgHom.mapMatrix φ)) (xdiag F r n)
      = Matrix.diagonal (fun i => (η₁.comp φ) (MvPolynomial.X (Sum.inl i))) := by
    have hxd : AlgHom.mapMatrix φ (xdiag F r n) = sprFieldXdiag F r n := rfl
    show θ₂ (AlgHom.mapMatrix φ (xdiag F r n)) = _
    rw [hxd]
    exact hC
  have hc' : ∀ i j : Fin n, i ≠ j →
      IsUnit ((η₁.comp φ) (MvPolynomial.X (Sum.inl j))
        - (η₁.comp φ) (MvPolynomial.X (Sum.inl i))) := by
    intro i j hij
    exact hc i j hij
  obtain ⟨σ, hσ⟩ := sprStepTwo_local F (θ₂.comp (AlgHom.mapMatrix φ)) (η₁.comp φ) hC' hc'
  refine ⟨σ, fun i => ?_⟩
  have h := hσ i
  rw [← hstd (σ i) (σ i)]
  exact h

#print axioms sprFieldStepTwo_local

end XdiagField

/-! ## §4 第三格主件的两个机械依赖（`K'`-世界）

`lem1424_local`（`GenericInv:10687`）的第 ⑤／⑥ 步用到 `sprConjForm_of_units`（`:10603`）与
`sprSameCalc_hxA`／`_hyA`（`:9993`／`:10010`）。本节给前两件：

| 新件 | 对应 `Spr` 版 | 手法 |
|---|---|---|
| `sprFieldConjForm_of_units` | `sprConjForm_of_units`（`:10603`） | **逐字换域**（证明只用 `Units`／`Matrix` 代数，不碰 `Spr`） |
| `sprFieldSameCalc_hxA` | `sprSameCalc_hxA`（`:9993`） | **传输**（`Θ_i := θ_i ∘ mapMatrix φ`、`η' := η ∘ φ`） |

**`hxA` 的传输细节**：结论里的 `(sprFieldXdiag).map η₁` 要化成 `(xdiag).map (η₁ ∘ φ)`，
用 `sprFieldXdiag = (xdiag).map φ` ＋ `Matrix.map_map`；`h₁`／`h₂` 的换域用
`AlgHom.comp_apply` ＋ `AlgHom.mapMatrix_apply` ＋ `Matrix.map_map` ＋ `rfl`
（`β.map (⇑η ∘ ⇑φ) = β.map ⇑(η.comp φ)` 是 `rfl`）。

**工艺（一处 rewrite 失效）**：`rw [AlgHom.comp_apply, h₁ (AlgHom.mapMatrix φ β)]` **不起作用**——
`(θ₁.comp g) β` 只在**定义上**等于 `θ₁ (g β)`，而 `AlgHom.comp` 后面的项在 `rw` 的模式匹配里
形状不同。正解：**改用 `simp only [AlgHom.comp_apply, h₁, AlgHom.mapMatrix_apply, Matrix.map_map]`
再 `rfl`**（`simp` 走定义等价，`rw` 走语法匹配）。与教训 26②（"卡住先怀疑记法层"）同族。

**射程（勿夸大）**：`sprFieldSameCalc_hyA`（`ymat` 侧）、`sprSameCalc`（§123，"same calculation" 本体）、
`lem1424_chain`（`:9762`）／`lem1424_closing`（`:9873`）的换域 **均未做**——后者带 `hα`
（`N`-不变性），是第三格主件里**唯一非机械**的部分。`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section ConjFormField

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `sprConjForm_of_units` 的 `K'`-世界形态（**逐字换域**）。 -/
theorem sprFieldConjForm_of_units (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (A : (Matrix (Fin n) (Fin n) T)ˣ)
    (hAU : A = sprPmatUnit T σ * sprDiagMatRUnit (T := T) c)
    (θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₂ : SprField F r n →ₐ[F] T)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
      (A : Matrix (Fin n) (Fin n) T) * θ₂ β
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = β.map η₂) :
    ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂ := by
  intro β
  have h := h₂ β
  have hAval : ((A : Matrix (Fin n) (Fin n) T))
      = sprPmat (n := n) T σ * sprDiagMatR (n := n) T c := by
    rw [hAU, Units.val_mul]
    rfl
  have hAinv : (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹ := by
    rw [hAU, _root_.mul_inv_rev, Units.val_mul]
    rfl
  rw [hAval, hAinv] at h
  have hassoc : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (((sprPmat (n := n) T σ * sprDiagMatR (n := n) T c) * θ₂ β)
        * (sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹)) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc]
  exact h

#print axioms sprFieldConjForm_of_units

/-- `sprSameCalc_hxA` 的 `K'`-世界形态（**传输**）。 -/
theorem sprFieldSameCalc_hxA (η₁ η₂ : SprField F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n))
    (c : Fin n → Tˣ)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n), θ₁ β = β.map η₁)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n)) :
    sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((sprFieldXdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (sprFieldXdiag F r n).map η₂ := by
  let φ : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  have h₁' : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      (θ₁.comp (AlgHom.mapMatrix φ)) β = β.map (η₁.comp φ) := by
    intro β
    simp only [AlgHom.comp_apply, h₁, AlgHom.mapMatrix_apply, Matrix.map_map]
    rfl
  have h₂' : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * (θ₂.comp (AlgHom.mapMatrix φ)) β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map (η₂.comp φ) := by
    intro β
    simp only [AlgHom.comp_apply, h₂, AlgHom.mapMatrix_apply, Matrix.map_map]
    rfl
  have hX' : (θ₁.comp (AlgHom.mapMatrix φ)) (xdiag F r n)
      = (θ₂.comp (AlgHom.mapMatrix φ)) (xdiag F r n) := hX
  have hmain := sprSameCalc_hxA (F := F) (r := r) (n := n) (T := T)
    (η₁.comp φ) (η₂.comp φ) σ c _ _ h₁' h₂' hX'
  rw [sprFieldXdiag, Matrix.map_map, Matrix.map_map]
  exact hmain

#print axioms sprFieldSameCalc_hxA

end ConjFormField

/-! ## §5 `hY` 侧（`ymat`）—— 第三格主件机械依赖的第二半

| 新件 | 对应 `Spr` 版 | 手法 |
|---|---|---|
| `sprFieldYmat`（`def`） | `ymat F r n k` | `ymat` 的 `K'`-像 |
| `sprFieldYmat_map` | — | 像沿同态 = `(ymat).map (η ∘ φ)` |
| `sprFieldSameCalc_hyA` | `sprSameCalc_hyA`（`GenericInv:10010`） | **传输** |

**★ 一条重要的侦察读数（R706）**：`sprSameCalc`（`GenericInv:9668`）的**签名里没有 `hα`**——
它只接收 `hx`／`hy`（生成元一致性）并产出 `η₁ = sprMonoAeval … σ c`。
⟹ §7.22 写的「`hα` 是主件里唯一非机械的部分」**应改挂到 `lem1424_chain`（`:9762`）／
`lem1424_closing`（`:9873`）**，而不是 `sprSameCalc`。
而 `hα`（`sprPsiMonoR`-不变性）在 `K'`-世界可由 `sprMatNFixed` 供：`sprPsiMonoR` 是
`sprPsiDK` 与 `sprPsiSK` 的**复合**（`sprPmat σ * sprDiagMatR c * (·).map (sprMonoAeval …) * …`），
故 `N`-不变 ⟹ 该复合不变。**这须在下一轮机检成定理**（是 `(乙)` 真正的风险点）。

**射程（勿夸大）**：第三格主件的**本体**（`sprSameCalc` 的 `K'`-形态、`lem1424_chain`／
`lem1424_closing` 的换域、`hα` ← `sprMatNFixed` 的桥）**均未做**。`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section YmatField

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `ymat` 的 `K'`-像。 -/
noncomputable def sprFieldYmat (k : {k : Fin r // k.val ≠ 0}) :
    Matrix (Fin n) (Fin n) (SprField F r n) :=
  (ymat F r n k).map (algebraMap (Spr F r n) (SprField F r n))

#print axioms sprFieldYmat

/-- `ymat` 的 `K'`-像沿同态的像 = `(ymat).map (η ∘ φ)`。 -/
theorem sprFieldYmat_map (η : SprField F r n →ₐ[F] T)
    (k : {k : Fin r // k.val ≠ 0}) :
    (sprFieldYmat F r n k).map η = (ymat F r n k).map
      (η.comp (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n))) := by
  rw [sprFieldYmat, Matrix.map_map]
  rfl

#print axioms sprFieldYmat_map

/-- `sprSameCalc_hyA` 的 `K'`-世界形态（**传输**）。 -/
theorem sprFieldSameCalc_hyA (η₁ η₂ : SprField F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n))
    (c : Fin n → Tˣ)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n), θ₁ β = β.map η₁)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (SprField F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k)) :
    ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((sprFieldYmat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (sprFieldYmat F r n k).map η₂ := by
  let φ : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  have h₁' : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      (θ₁.comp (AlgHom.mapMatrix φ)) β = β.map (η₁.comp φ) := by
    intro β
    simp only [AlgHom.comp_apply, h₁, AlgHom.mapMatrix_apply, Matrix.map_map]
    rfl
  have h₂' : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * (θ₂.comp (AlgHom.mapMatrix φ)) β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map (η₂.comp φ) := by
    intro β
    simp only [AlgHom.comp_apply, h₂, AlgHom.mapMatrix_apply, Matrix.map_map]
    rfl
  have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
      (θ₁.comp (AlgHom.mapMatrix φ)) (ymat F r n k)
        = (θ₂.comp (AlgHom.mapMatrix φ)) (ymat F r n k) := hY
  intro k
  have hmain := sprSameCalc_hyA (F := F) (r := r) (n := n) (T := T)
    (η₁.comp φ) (η₂.comp φ) σ c _ _ h₁' h₂' hY' k
  rw [sprFieldYmat_map (η := η₁), sprFieldYmat_map (η := η₂)]
  exact hmain

#print axioms sprFieldSameCalc_hyA

end YmatField

/-! ## §6 `hα` 桥的第一段（`K'`-世界）

源文 `lem:14.24` 的 `hα` 是对 **`sprPsiMonoR`**（环面 × 置换的**复合**）的不变性；
而 `sprMatNFixed`（源文 `lem:14.25` 的假设）给的是**两个分量各自**的不变性。
本节的四行给出"分量 ⟹ 复合"的第一步。

| 新件 | 内容 |
|---|---|
| ★★★★ `sprPsiDK_sprPsiSK_eq_of_sprMatNFixed` | `sprMatNFixed α ⟹ sprPsiDK b (sprPsiSK σ α) = α` |
| ★★★★ `sprPsiSK_sprPsiDK_eq_of_sprMatNFixed` | 换次序的同一结论 |

**桥的剩余（下一轮，已定位）**：把 `sprPsiDK b (sprPsiSK σ α)` 展开成
`sprPmat σ * sprDiagMatR c * α.map ξ * sprDiagMatR c⁻¹ * sprPmat σ⁻¹` 的形状
（＝ `sprPsiMonoR` 的 `R := SprField` 形态）。展开需要三步簿记：

1. **`sprDiagFieldEquiv` 固定常数** ⟹ `(sprPmatK σ).map e_b = sprPmatK σ`、
   `((sprPmatK σ)⁻¹).map e_b = (sprPmatK σ)⁻¹`（置换矩阵是 0/1 常矩阵）；
2. **`Matrix.map_map`** ⟹ `(α.map e_σ).map e_b = α.map (e_b ∘ e_σ)`；
3. **置换矩阵与对角矩阵的交换**（`P_σ⁻¹ D_b = D_{b'} P_σ⁻¹`，`b'_i = b(σ i)` 型）
   ⟹ 把 `D_{b⁻¹} P_σ (…) P_σ⁻¹ D_b` 收成 `P_σ D_{c} (…) D_c⁻¹ P_σ⁻¹`。

**为何这一步是 `(乙)` 的真正风险点**：第 3 步是**半直积簿记**，S'-世界的对应件是
`sprPerm_sprDiagHom_comp`（`GenericInv` §83：`σ ∘ φ_b = φ_{b'} ∘ σ`）。
**若 K'-世界没有对应件，须新证**；`sprPermFieldEquiv`／`sprDiagFieldEquiv` 是
`IsFractionRing.ringEquivOfRingEquiv` 出来的，故"沿 `algebraMap` 提升"应有现成路径
（`sprPermFieldEquiv_algebraMap`／`sprDiagFieldEquiv_algebraMap` 已在 `GenericInv` §138 出现）。

**射程（勿夸大）**：本节只给桥的**第一段**（4 行）。第 3 步簿记、`sprMonoAeval` 的
`sprField`-形态、`sprSameCalc` 的 `K'`-形态、`lem1424_chain`／`lem1424_closing` 的换域
**均未做**。`ThetaAgreeHypK'` **未证**；`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；
**H2 仍不是定理**。 -/

section HalphaBridge

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **桥的第一段**：`sprMatNFixed` 给出**复合作用**的不变性。 -/
theorem sprPsiDK_sprPsiSK_eq_of_sprMatNFixed
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (h : sprMatNFixed F r n α)
    (b : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    sprPsiDK F r n b (sprPsiSK F r n σ α) = α := by
  rw [h.2 σ, h.1 b]

#print axioms sprPsiDK_sprPsiSK_eq_of_sprMatNFixed

/-- 同上，换次序（`sprPsiSK σ ∘ sprPsiDK b`）。 -/
theorem sprPsiSK_sprPsiDK_eq_of_sprMatNFixed
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (h : sprMatNFixed F r n α)
    (b : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    sprPsiSK F r n σ (sprPsiDK F r n b α) = α := by
  rw [h.1 b, h.2 σ]

#print axioms sprPsiSK_sprPsiDK_eq_of_sprMatNFixed

end HalphaBridge

/-! ## §7 `hα` 桥的簿记（一）：置换矩阵是常数矩阵

`sprPmatK σ` 的条目是 `0`／`1`（`sprPmat_apply`），故任何**保常数**的环同态都逐条固定它。
这是桥的第 1 步（见 §6 节头）。

| 新件 | 内容 |
|---|---|
| `sprPmatK_map_diagFieldEquiv` | `(sprPmatK σ).map (sprDiagFieldEquiv b).toRingHom = sprPmatK σ` |
| `sprPmatK_map_permFieldEquiv` | 同上，对 `sprPermFieldEquiv τ` |

**工艺**：`sprDiagFieldEquiv`／`sprPermFieldEquiv` 的类型是 **`RingEquiv`**（非 `AlgEquiv`），
故 **没有** `.commutes` 可用（报 `RingEquiv.commutes` 不存在）。正解：**逐条目**化到
`sprPmat_apply` 的 `0`／`1`，再 `split_ifs <;> simp`（用 `map_one`／`map_zero`）——
**不需要**任何 `_algebraMap` 引理。

**射程（勿夸大）**：第 2 步（`Matrix.map_map`）与第 3 步（半直积簿记，工具 `sprPmat_mul_diag`
对任意 `R` 成立，已核）**未做**；`sprPsiMonoR` 的 `SprField` 形态**未定义**；
`lem1424_chain`／`lem1424_closing` 的换域**未做**。`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section PmatConst

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **第 1 步**：`sprDiagFieldEquiv` 逐条固定 `sprPmatK`（条目是 `0`／`1`）。 -/
theorem sprPmatK_map_diagFieldEquiv (b : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    (sprPmatK (F := F) (r := r) (n := n) σ).map
        (sprDiagFieldEquiv F r n b).toRingHom
      = sprPmatK (F := F) (r := r) (n := n) σ := by
  rw [sprPmatK_eq_map, Matrix.map_map]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, sprPmat_apply]
  split_ifs <;> simp

#print axioms sprPmatK_map_diagFieldEquiv

/-- 同上，对 `sprPermFieldEquiv`。 -/
theorem sprPmatK_map_permFieldEquiv (τ : Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin n)) :
    (sprPmatK (F := F) (r := r) (n := n) σ).map
        (sprPermFieldEquiv F r n τ).toRingHom
      = sprPmatK (F := F) (r := r) (n := n) σ := by
  rw [sprPmatK_eq_map, Matrix.map_map]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, sprPmat_apply]
  split_ifs <;> simp

#print axioms sprPmatK_map_permFieldEquiv

end PmatConst

/-! ## §8 半直积簿记（`hα` 桥的第 3 步）：状态与卡点

**目标**（`K'`-世界）：`P_σ · D_b = D_{b∘σ⁻¹} · P_σ`。工具齐备：
`sprPmat_mul_diag`（`GenericInv:8207`）**对任意 `R` 成立**，而 `sprPmatK σ = sprPmat (SprField) σ`
（`:12773`，**定义式**），故可直接用于 `SprField`。

**本轮入库的只有一件**（能编译的部分）：`sprUnitK`（`b : Fin n → Fˣ` 沿两次提升得到的 `K'`-单位族）。

**卡点的准确描述（下一轮从这里接着做）**：要证

```
sprDiagMatK b = sprDiagMatR (n := n) (SprField) (sprUnitK F r n b)
```

`Matrix.ext` ＋ `by_cases (i = j)` 之后剩两个分支：

| 分支 | 剩余目标 | 缺什么 |
|---|---|---|
| `i = j` | `algebraMap Spr K' (algebraMap F Spr ↑(b j))` 与 `sprDiagMatR` 侧的同一式 | **`MvPolynomial.C` 与 `algebraMap F Spr` 的强制转换对齐**（`sprDiagMat` 的条目写作 `C ↑(b i)`；`sprDiagMatR` 的条目是 `↑(sprUnitK …)`） |
| `i ≠ j` | `algebraMap Spr K' 0 = 0` | `map_zero`（`simp only` 未含它） |

**已查明的一条结构性事实（有价值）**：`IsScalarTower F (Spr F r n) (SprField F r n)`
**不是可由实例搜索得到的**（试图用 `IsScalarTower.algebraMap_apply` 证
`algebraMap Spr K' (C c) = algebraMap F K' c` 时报 "failed to synthesize"）。
⟹ `K'`-世界的一切 `F → Spr → K'` 换算须**显式**给出，或改用 `Spr`-层的单位族（本节 `sprUnitK` 的做法）。

**射程（勿夸大）**：第 3 步**未完成**。`hα` 桥只完成第 1 步（§7）。`sprPsiMonoR` 的 `SprField`
形态未定义；`lem1424_chain`／`lem1424_closing` 的换域未做。`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section SemiDirect

variable (F : Type) [Field F] (r n : ℕ)

/-- `b : Fin n → Fˣ` 沿 `F → Spr → SprField` 两次提升得到的 `K'`-单位族。

**为何这样写**：`IsScalarTower F Spr K'` 不可实例化（见节头），故把两层 `Units.map` 显式串起来，
避免出现 `algebraMap F K'`。 -/
noncomputable def sprUnitK (b : Fin n → Fˣ) : Fin n → (SprField F r n)ˣ :=
  fun i => Units.map (algebraMap (Spr F r n) (SprField F r n)).toMonoidHom
    (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b i))

#print axioms sprUnitK

end SemiDirect

section DiagMatKField

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`sprDiagMatK b` ＝ `sprDiagMatR` 在 `sprUnitK b` 处的值**（第 3 步的准备）。

证明：`Matrix.ext` ＋ `by_cases (i = j)`。
`i = j` 分支：两侧都化成 `algebraMap Spr K' (algebraMap F Spr ↑(b i))`，
差的只是 `RingHom` 的 `↑` 强制转换，故 `rfl` 收口。
`i ≠ j` 分支：两侧都是 `algebraMap Spr K' 0` / `0`，`map_zero` 收口。 -/
theorem sprDiagMatK_eq_sprDiagMatR (b : Fin n → Fˣ) :
    sprDiagMatK (F := F) (r := r) (n := n) b
      = sprDiagMatR (n := n) (SprField F r n) (sprUnitK F r n b) := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp only [sprDiagMatK, sprDiagMatR, sprDiagMat, sprUnitK, Matrix.diagonal_apply,
      Matrix.map_apply, Units.coe_map, if_true]
    rfl
  · simp only [sprDiagMatK, sprDiagMatR, sprDiagMat, sprUnitK, Matrix.diagonal_apply,
      Matrix.map_apply, Units.coe_map, if_neg h, map_zero]

#print axioms sprDiagMatK_eq_sprDiagMatR

/-- ★★★★★ **第 3 步：半直积簿记**（`K'`-世界）：`P_σ · D_b = D_{b∘σ⁻¹} · P_σ`。

**右端直接写成 `sprDiagMatR` 形态**（`sprUnitK` 族），绕开 `sprDiagMatK (b∘σ⁻¹)` 的**参数外延**
（`sprUnitK b (σ⁻¹ i)` 与 `sprUnitK (b ∘ σ⁻¹) i` 定义等价但语法不同 —— R709 卡在这里一整轮）。
**证明一行**：`sprPmatK = sprPmat (SprField)`（定义式）＋ §8 的 `sprDiagMatK_eq_sprDiagMatR`
＋ `sprPmat_mul_diag`（对任意 `R` 成立）。 -/
theorem sprPmatK_mul_sprDiagMatK (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ) :
    sprPmatK (F := F) (r := r) (n := n) σ * sprDiagMatK (F := F) (r := r) (n := n) b
      = sprDiagMatR (n := n) (SprField F r n) (fun i => sprUnitK F r n b (σ⁻¹ i))
        * sprPmatK (F := F) (r := r) (n := n) σ := by
  rw [sprPmatK, sprDiagMatK_eq_sprDiagMatR F r n b]
  exact sprPmat_mul_diag (SprField F r n) σ (sprUnitK F r n b)

#print axioms sprPmatK_mul_sprDiagMatK

/-- **定义式版的逆**：`(sprPmatK σ)⁻¹ = sprPmatK σ⁻¹`。

**为何要它**：`sprPmatK_inv`（`GenericInv:13008`）的右端是**映射式**
`(sprPmat (Spr) σ⁻¹).map algebraMap`，而 `sprPmatK` 的其余引理用的是**定义式**
`sprPmat (SprField) σ`。两式在 `rw` 下**不混合**（R712 的卡点）。本件把逆换回定义式：
`rw [sprPmatK_inv, ← sprPmatK_eq_map]` 一行。 -/
theorem sprPmatK_inv' (σ : Equiv.Perm (Fin n)) :
    (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹
      = sprPmatK (F := F) (r := r) (n := n) σ⁻¹ := by
  rw [sprPmatK_inv, ← sprPmatK_eq_map]

#print axioms sprPmatK_inv'

/-- ★★★★★ **桥的第 2 步**：`sprPsiSK` 沿环面作用后的显式形态。

`sprPsiSK σ α = P_σ * α.map e_σ * P_σ⁻¹`，故 `.map e_b` 之后用
`Matrix.map_mul` ×2 ＋ 步 1（`P_σ` 被 `e_b` 固定，含逆）＋ `Matrix.map_map`
得 `P_σ * α.map (e_b ∘ e_σ) * P_σ⁻¹`。 -/
theorem sprPsiSK_map_diag (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    (sprPsiSK F r n σ α).map (sprDiagFieldEquiv F r n b).toRingHom
      = sprPmatK (F := F) (r := r) (n := n) σ
        * (α.map ((sprDiagFieldEquiv F r n b).toRingHom.comp
            (sprPermFieldEquiv F r n σ).toRingHom))
        * (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹ := by
  rw [sprPsiSK, Matrix.map_mul, Matrix.map_mul,
    sprPmatK_map_diagFieldEquiv F r n b σ,
    sprPmatK_inv', sprPmatK_map_diagFieldEquiv F r n b (σ⁻¹),
    Matrix.map_map]
  rfl

#print axioms sprPsiSK_map_diag

/-! ## §9 `sprPsiMonoR` 的 `K'`-世界形态 ＋ `sprPsiDK∘sprPsiSK` 的展开（第一半）

源文 `lem:14.24` 的 `hα` 是对 `sprPsiMonoR`（`GenericInv:8487`）的不变性。本节给它在
`K'`-世界的对应物 `sprFieldPsiMono`，并把 `sprPsiDK b (sprPsiSK σ α)` 展开到
"外层对角夹住 R713 形态"（第一半）。

**第二半的指标计算（下一轮，已推完）**：`sprPmat_mul_diag` 给 `P_σ · D_c = D_{c∘σ⁻¹} · P_σ`，
由此得两条搬运律
```
D_c · P_σ      = P_σ · D_{c∘σ}
P_{σ⁻¹} · D_b  = D_{b∘σ} · P_{σ⁻¹}
```
于是取 `c := fun i => (sprUnitK F r n b (σ i))⁻¹`（即 `c = (b∘σ)⁻¹` 的提升），有
```
D_{b⁻¹} · P_σ · X · P_σ⁻¹ · D_b = P_σ · D_c · X · D_c⁻¹ · P_σ⁻¹
```
（`D_{b⁻¹}·P_σ = P_σ·D_{(b∘σ)⁻¹}` 用第一律，`b⁻¹∘σ = (b∘σ)⁻¹`；末端的
`P_σ⁻¹·D_b = D_{b∘σ}·P_σ⁻¹` 用第二律，而 `b∘σ = c⁻¹`。）右端正是 `sprFieldPsiMono ξ σ c α`
（`ξ = e_b ∘ e_σ`）。**⟹ 第二半 = 证那两条搬运律 ＋ 一次 `rw`。**

**射程（勿夸大）**：本节只给定义与第一半。两条搬运律、第二半、`hα` 的 `K'`-形态
（`sprMatNFixed α ⟹ sprFieldPsiMono … α = α`）**均未做**。`ThetaAgreeHypK'` **未证**；
`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section PsiMono

variable (F : Type) [Field F] (r n : ℕ)

/-- `sprPsiMonoR` 的 `K'`-世界形态：`P_σ * D_c * α.map ξ * D_c⁻¹ * P_σ⁻¹`。 -/
noncomputable def sprFieldPsiMono (ξ : SprField F r n →+* SprField F r n)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → (SprField F r n)ˣ)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    Matrix (Fin n) (Fin n) (SprField F r n) :=
  sprPmatK (F := F) (r := r) (n := n) σ
    * sprDiagMatR (n := n) (SprField F r n) c * α.map ξ
    * sprDiagMatR (n := n) (SprField F r n) (fun i => (c i)⁻¹)
    * sprPmatK (F := F) (r := r) (n := n) σ⁻¹

#print axioms sprFieldPsiMono

/-- ★★★★★ **展开的第一半**：`sprPsiDK b (sprPsiSK σ α)` ＝ 外层对角夹住 R713 的形态。 -/
theorem sprPsiDK_sprPsiSK_eq_expand (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiDK F r n b (sprPsiSK F r n σ α)
      = sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹)
        * (sprPmatK (F := F) (r := r) (n := n) σ
            * (α.map ((sprDiagFieldEquiv F r n b).toRingHom.comp
                (sprPermFieldEquiv F r n σ).toRingHom))
            * (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹)
        * sprDiagMatK (F := F) (r := r) (n := n) b := by
  rw [sprPsiDK, sprPsiSK_map_diag]

#print axioms sprPsiDK_sprPsiSK_eq_expand

end PsiMono

/-! ## §10 两条对角／置换搬运律（`hα` 桥第二半的工具）

`sprPmat_mul_diag`（`GenericInv:8207`，**对任意 `R`**）给 `P_σ · D_c = D_{c∘σ⁻¹} · P_σ`。
本节把它转成**反方向**的两条搬运律（展开式的第二半要用 `D` 往右搬）：

| 律 | 内容 |
|---|---|
| (1) `sprDiagMatR_mul_sprPmat` | `D_c · P_σ = P_σ · D_{c∘σ}` |
| (2) `sprPmat_symm_mul_sprDiagMatR` | `P_{σ⁻¹} · D_c = D_{c∘σ} · P_{σ⁻¹}` |

**工艺**：律 (2) 是 `sprPmat_mul_diag` 取 `τ = σ⁻¹`（`(σ⁻¹)⁻¹ = σ`，定义式）即得，**一行**。
律 (1) 需先把 `c` 换写成 `c ∘ σ ∘ σ⁻¹`：`rw [sprPmat_mul_diag … σ (fun i => c (σ i))]` 之后
用**函数层**的等式 `(fun i => c (σ (σ⁻¹ i))) = c` 改写——
`congr 1`／`simp only [Equiv.apply_symm_apply]` 在此**都不生效**（前者下钻到矩阵条目，
后者"made no progress"），正解是
`rw [show (fun i => c (σ (σ⁻¹ i))) = c from funext (fun i => congrArg c (Equiv.apply_symm_apply σ i))]`。

**射程（勿夸大）**：本节只给两条搬运律。第二半的装配、`hα` 的 `K'`-形态**未做**。
`ThetaAgreeHypK'` **未证**；`UDKTensorHypK'`（PI）**未证**；`hZ` **未证**；**H2 仍不是定理**。 -/

section TransportLaws

variable (F : Type) [Field F] (r n : ℕ)

/-- **搬运律 (1)**：`D_c · P_σ = P_σ · D_{c∘σ}`。 -/
theorem sprDiagMatR_mul_sprPmat (σ : Equiv.Perm (Fin n))
    (c : Fin n → (SprField F r n)ˣ) :
    sprDiagMatR (n := n) (SprField F r n) c * sprPmat (SprField F r n) σ
      = sprPmat (SprField F r n) σ
        * sprDiagMatR (n := n) (SprField F r n) (fun i => c (σ i)) := by
  rw [sprPmat_mul_diag (SprField F r n) σ (fun i => c (σ i))]
  rw [show (fun i => c (σ (σ⁻¹ i))) = c from
    funext (fun i => congrArg c (Equiv.apply_symm_apply σ i))]

#print axioms sprDiagMatR_mul_sprPmat

/-- **搬运律 (2)**：`P_{σ⁻¹} · D_c = D_{c∘σ} · P_{σ⁻¹}`。 -/
theorem sprPmat_symm_mul_sprDiagMatR (σ : Equiv.Perm (Fin n))
    (c : Fin n → (SprField F r n)ˣ) :
    sprPmat (SprField F r n) (σ⁻¹) * sprDiagMatR (n := n) (SprField F r n) c
      = sprDiagMatR (n := n) (SprField F r n) (fun i => c (σ i))
        * sprPmat (SprField F r n) (σ⁻¹) :=
  sprPmat_mul_diag (SprField F r n) (σ⁻¹) c

#print axioms sprPmat_symm_mul_sprDiagMatR

end TransportLaws

/-- ★★★★★ **对角-置换共轭恒等式**（`hα` 桥第二半的核）：

```
D_{C⁻¹} · (P_σ X P_σ⁻¹) · D_C = P_σ · D_{(C∘σ)⁻¹} · X · D_{C∘σ} · P_σ⁻¹
```

两条搬运律各用一次（律 1 搬左端 `D_{C⁻¹}·P_σ`、律 2 搬右端 `P_σ⁻¹·D_C`），其余是结合律。
**⟹ 这正是 `sprPsiDK b (sprPsiSK σ α)` 与 `sprFieldPsiMono` 之间的桥**：
取 `C = sprUnitK F r n b`（则 `C∘σ` 一族即 `(b∘σ)` 的提升），两端就对上。 -/
theorem sprDiag_conj_perm (σ : Equiv.Perm (Fin n))
    (C : Fin n → (SprField F r n)ˣ)
    (X : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprDiagMatR (n := n) (SprField F r n) (fun i => (C i)⁻¹)
        * (sprPmat (SprField F r n) σ * X * sprPmat (SprField F r n) σ⁻¹)
        * sprDiagMatR (n := n) (SprField F r n) C
      = sprPmat (SprField F r n) σ
        * sprDiagMatR (n := n) (SprField F r n) (fun i => (C (σ i))⁻¹)
        * X
        * sprDiagMatR (n := n) (SprField F r n) (fun i => C (σ i))
        * sprPmat (SprField F r n) σ⁻¹ := by
  calc sprDiagMatR (n := n) (SprField F r n) (fun i => (C i)⁻¹)
        * (sprPmat (SprField F r n) σ * X * sprPmat (SprField F r n) σ⁻¹)
        * sprDiagMatR (n := n) (SprField F r n) C
      = (sprDiagMatR (n := n) (SprField F r n) (fun i => (C i)⁻¹)
          * sprPmat (SprField F r n) σ) * X * sprPmat (SprField F r n) σ⁻¹
          * sprDiagMatR (n := n) (SprField F r n) C := by simp only [Matrix.mul_assoc]
    _ = (sprPmat (SprField F r n) σ
          * sprDiagMatR (n := n) (SprField F r n) (fun i => (C (σ i))⁻¹))
          * X * sprPmat (SprField F r n) σ⁻¹
          * sprDiagMatR (n := n) (SprField F r n) C := by
        rw [sprDiagMatR_mul_sprPmat]
    _ = sprPmat (SprField F r n) σ
          * sprDiagMatR (n := n) (SprField F r n) (fun i => (C (σ i))⁻¹) * X
          * (sprPmat (SprField F r n) σ⁻¹
              * sprDiagMatR (n := n) (SprField F r n) C) := by
        simp only [Matrix.mul_assoc]
    _ = sprPmat (SprField F r n) σ
          * sprDiagMatR (n := n) (SprField F r n) (fun i => (C (σ i))⁻¹) * X
          * (sprDiagMatR (n := n) (SprField F r n) (fun i => C (σ i))
              * sprPmat (SprField F r n) σ⁻¹) := by
        rw [sprPmat_symm_mul_sprDiagMatR]
    _ = sprPmat (SprField F r n) σ
        * sprDiagMatR (n := n) (SprField F r n) (fun i => (C (σ i))⁻¹)
        * X
        * sprDiagMatR (n := n) (SprField F r n) (fun i => C (σ i))
        * sprPmat (SprField F r n) σ⁻¹ := by simp only [Matrix.mul_assoc]

#print axioms sprDiag_conj_perm

/-- **`sprUnitK` 与逐点取逆交换**：`sprUnitK (b⁻¹) = (sprUnitK b)⁻¹`（逐点）。

**为何要它**：`sprPsiDK` 的左端对角是 `sprDiagMatK (fun i => (b i)⁻¹)`，而
`sprDiag_conj_perm` 要的是 `D_{(C)⁻¹}` 形态（`C = sprUnitK b`）。本件把两者接上。
**证明**：`Units.ext` ＋ `simp only [sprUnitK, map_inv]`（`MonoidHom.map_inv`，`SprField` 是域）。 -/
theorem sprUnitK_inv (b : Fin n → Fˣ) :
    sprUnitK F r n (fun i => (b i)⁻¹) = fun i => (sprUnitK F r n b i)⁻¹ := by
  funext i
  refine Units.ext ?_
  simp only [sprUnitK, map_inv]

#print axioms sprUnitK_inv

/-- ★★★★★★ **桥的第二半（装配完成）**：

`sprPsiDK b (sprPsiSK σ α)` ＝ `sprFieldPsiMono ξ σ c α` 的展开形态，其中
`ξ = e_b ∘ e_σ`、`c = fun i => (sprUnitK b (σ i))⁻¹`。

**证明四步**：`sprPsiDK_sprPsiSK_eq_expand`（§9）⟹ 把 `sprDiagMatK`／`sprPmatK` 换成
`sprDiagMatR (sprUnitK …)`／`sprPmat (SprField)` ⟹ `sprUnitK_inv`（§10）⟹ `sprDiag_conj_perm`（§10）。

**工艺（R718 的两条正解合用）**：`rw [sprDiag_conj_perm]` 不命中 ⟹ 必须**显式传参**
`(σ := σ) (C := sprUnitK F r n b)`；且 `sprPmatK` 的 def-引理要**写两次**
（`sprPmatK_inv'` 之后新出现的 `sprPmatK σ⁻¹` 需第二次才被改写）。 -/
theorem sprPsiDK_sprPsiSK_eq_psiMono (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiDK F r n b (sprPsiSK F r n σ α)
      = sprPmat (SprField F r n) σ
        * sprDiagMatR (n := n) (SprField F r n) (fun i => (sprUnitK F r n b (σ i))⁻¹)
        * (α.map ((sprDiagFieldEquiv F r n b).toRingHom.comp
            (sprPermFieldEquiv F r n σ).toRingHom))
        * sprDiagMatR (n := n) (SprField F r n) (fun i => sprUnitK F r n b (σ i))
        * sprPmat (SprField F r n) σ⁻¹ := by
  rw [sprPsiDK_sprPsiSK_eq_expand]
  rw [sprDiagMatK_eq_sprDiagMatR, sprDiagMatK_eq_sprDiagMatR, sprPmatK_inv', sprPmatK, sprPmatK]
  rw [sprUnitK_inv]
  rw [sprDiag_conj_perm (F := F) (r := r) (n := n) (σ := σ) (C := sprUnitK F r n b)]

#print axioms sprPsiDK_sprPsiSK_eq_psiMono

/-- ★★★★★★★ **`hα` 的 `K'`-形态**：`sprMatNFixed α ⟹ sprFieldPsiMono ξ σ c α = α`。

这是源文 `lem:14.24` 的 `hα`（对 `sprPsiMonoR` 的复合作用不变）在 `K'`-世界的确切内容，
由 R707 的 `sprPsiDK_sprPsiSK_eq_of_sprMatNFixed` ＋ 上一行的装配直接得到。 -/
theorem sprFieldPsiMono_eq_self_of_sprMatNFixed
    {α : Matrix (Fin n) (Fin n) (SprField F r n)} (h : sprMatNFixed F r n α)
    (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ) :
    sprPmat (SprField F r n) σ
        * sprDiagMatR (n := n) (SprField F r n) (fun i => (sprUnitK F r n b (σ i))⁻¹)
        * (α.map ((sprDiagFieldEquiv F r n b).toRingHom.comp
            (sprPermFieldEquiv F r n σ).toRingHom))
        * sprDiagMatR (n := n) (SprField F r n) (fun i => sprUnitK F r n b (σ i))
        * sprPmat (SprField F r n) σ⁻¹
      = α := by
  rw [← sprPsiDK_sprPsiSK_eq_psiMono]
  exact sprPsiDK_sprPsiSK_eq_of_sprMatNFixed F r n h b σ

#print axioms sprFieldPsiMono_eq_self_of_sprMatNFixed

end DiagMatKField

/-! ## §11 ★★★★★ **第四格：`sprSameCalc`（`GenericInv` §123）的 `K'`-形态**

源 `GenericInv:9668`。**判读（v43 §3.5 的"实质风险格"）**：结论右端 `sprMonoAeval`
的定义域是 `Spr F r n`，而 `K'`-世界的 `η₁` 定义域是 `SprField` ⟹ 等式**只能沿
`φ := algebraMap Spr K'` 比较**，写成 `η₁.comp φ = sprMonoAeval …`（**出路 1，不做新定义**）。

**实现 = 传输**（与 §4 `sprFieldSameCalc_hxA` 同一手法）：`hx`／`hy` 沿
`sprFieldXdiag = (xdiag).map φ` ＋ `Matrix.map_map` 化成 `(xdiag).map (η₁ ∘ φ)`，
再套 `Spr`-世界的 `sprSameCalc`（取 `η' := η ∘ φ`）。
**⟹ §123 的证明（`MvPolynomial.algHom_ext` 逐生成元）对定义域不敏感**——本格无新数学。 -/

section SameCalcField

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★★★ **`sprSameCalc` 的 `K'`-形态**（第四格）：`η₁` 在 `Spr`-生成元上的限制等于
"由 `η₂` 的生成元值经 `(σ, c)` 扭曲"的单项式映射。

**下游**：`hx`／`hy` 由 §4／§5 的 `sprFieldSameCalc_hxA`／`_hyA` 供给
（源：`lem:14.24` 的"`θ₁ θ₂` 在 `R(F,n,r)` 上一致"）⟹ 本件给收口链的 `hcalc`。 -/
theorem sprFieldSameCalc
    (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (η₁ η₂ : SprField F r n →ₐ[F] T)
    (hx : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((sprFieldXdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (sprFieldXdiag F r n).map η₂)
    (hy : ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((sprFieldYmat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (sprFieldYmat F r n k).map η₂) :
    η₁.comp (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n))
      = sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ ((algebraMap (Spr F r n) (SprField F r n))
            (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ ((algebraMap (Spr F r n) (SprField F r n))
            (MvPolynomial.X (Sum.inr ijk)))) σ c := by
  let phi : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  have hcoe : ∀ (eta : SprField F r n →ₐ[F] T),
      ⇑(eta.comp phi) = ⇑eta ∘ ⇑(algebraMap (Spr F r n) (SprField F r n)) := fun _ => rfl
  have hx' : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c
        * ((xdiag F r n).map (η₁.comp phi))
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (xdiag F r n).map (η₂.comp phi) := by
    have h := hx
    simp only [sprFieldXdiag, Matrix.map_map] at h
    rw [hcoe η₁, hcoe η₂]
    exact h
  have hy' : ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c
        * ((ymat F r n k).map (η₁.comp phi))
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (ymat F r n k).map (η₂.comp phi) := by
    intro k
    have h := hy k
    simp only [sprFieldYmat, Matrix.map_map] at h
    rw [hcoe η₁, hcoe η₂]
    exact h
  exact sprSameCalc (F := F) (r := r) (n := n) (T := T) σ c
    (η₁.comp phi) (η₂.comp phi) hx' hy'

#print axioms sprFieldSameCalc

end SameCalcField

/-! ## §12 ★★★ **（★）标量平衡引理的工具**（`(乙)` 第五格的核心）

第五格（K'-世界收口）归约到一个标量等式 `η₁(algebraMap s) = η₂(algebraMap s)`
（`scalar s` 为 `N`-不变）——见 [[proj-abgv52-frontier-R661]] §60.2。其数学内容 =
「`F`-单位环面作用的不动点 ⟹ 任意单位族作用的挠（twist）也不动它」。本节给所需的
两块工具：

| 件 | 内容 |
|---|---|
| ★★★★ `spr_pow_eq_of_units_imp` | **指数消去**：`∀ t ∈ Fˣ, t^A = t^B ⟹ A = B`（`F` 无限；`Polynomial` 无限根） |
| ★★★★★ `sprWtUnit_prod_eq` | **权积的因子分解**：`∏_v (wt u v)^{m v} = ∏_p (u p)^{A_p}·((u p)^{B_p})⁻¹` |

其中 `sprWtA`／`sprWtB` 是单项式 `m` 的「第一下标／第二下标出现次数」。

**工艺（教训 125）**：`Finset.prod_mul_distrib` 在 `∏ x, ∏ y, f x y * g x y` 上**用 `rw` 不命中**
（under-binder 匹配），`simp only [Finset.prod_mul_distrib]` 命中。`inv_pow` 的方向是
`a⁻¹ ^ n → (a ^ n)⁻¹`（**不是**反向）。 -/

section PowUnitsCancel

variable {F : Type} [Field F] [Infinite F]

/-- ★★★★ **指数消去**：若对**所有**单位 `t ∈ Fˣ` 都有 `t^A = t^B`，则 `A = B`（`F` 无限）。 -/
theorem spr_pow_eq_of_units_imp {A B : ℕ}
    (h : ∀ t : Fˣ, (t : F) ^ A = (t : F) ^ B) : A = B := by
  have key : ∀ k : ℕ, 0 < k → (∀ t : Fˣ, (t : F) ^ k = 1) → False := by
    intro k hk hk1
    have hroot : ∀ x : F, x ≠ 0 → (Polynomial.X ^ k - 1 : Polynomial F).IsRoot x := by
      intro x hx
      have hx' : x ^ k = 1 := by simpa using hk1 (Units.mk0 x hx)
      show (Polynomial.X ^ k - 1 : Polynomial F).eval x = 0
      simp [hx']
    have hinf : Set.Infinite {x : F | (Polynomial.X ^ k - 1 : Polynomial F).IsRoot x} :=
      Set.Infinite.mono (fun x hx => hroot x (by simpa using hx))
        (Set.infinite_univ.sdiff (Set.finite_singleton 0))
    have hzero : (Polynomial.X ^ k - 1 : Polynomial F) = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _ hinf
    have hc1 : (Polynomial.X ^ k : Polynomial F).coeff k = 1 := by
      simp [Polynomial.coeff_X_pow]
    have hc2 : (1 : Polynomial F).coeff k = 0 := by
      simp [Polynomial.coeff_one, Nat.pos_iff_ne_zero.mp hk]
    have hc : (Polynomial.X ^ k - 1 : Polynomial F).coeff k = 1 := by
      rw [Polynomial.coeff_sub, hc1, hc2, sub_zero]
    rw [hzero] at hc
    rw [Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  rcases le_total A B with hab | hab
  · have hk : ∀ t : Fˣ, (t : F) ^ (B - A) = 1 := by
      intro t
      have h1 : (t : F) ^ A = (t : F) ^ A * (t : F) ^ (B - A) := by
        rw [← pow_add, Nat.add_sub_of_le hab]
        exact h t
      exact mul_left_cancel₀ (pow_ne_zero _ (Units.ne_zero t))
        (by rw [mul_one]; exact h1.symm)
    have hz : B - A = 0 := by
      by_contra hne
      exact key (B - A) (Nat.pos_of_ne_zero hne) hk
    omega
  · have hk : ∀ t : Fˣ, (t : F) ^ (A - B) = 1 := by
      intro t
      have h1 : (t : F) ^ B = (t : F) ^ B * (t : F) ^ (A - B) := by
        rw [← pow_add, Nat.add_sub_of_le hab]
        exact (h t).symm
      exact mul_left_cancel₀ (pow_ne_zero _ (Units.ne_zero t))
        (by rw [mul_one]; exact h1.symm)
    have hz : A - B = 0 := by
      by_contra hne
      exact key (A - B) (Nat.pos_of_ne_zero hne) hk
    omega

#print axioms spr_pow_eq_of_units_imp

end PowUnitsCancel

section WtUnit

variable {r n : ℕ}

/-- 一般的环面权（值在任意交换环的单位群）：`x_ii ↦ 1`、`y_ijk ↦ u i * (u j)⁻¹`。 -/
noncomputable def sprWtUnit (R : Type) [CommRing R] (u : Fin n → Rˣ) : SprIdx r n → Rˣ
  | Sum.inl _ => 1
  | Sum.inr (i, j, _) => u i * (u j)⁻¹

/-- 「`p` 作为**第一**下标出现的次数」：`A_p`。 -/
def sprWtA (m : SprIdx r n →₀ ℕ) (p : Fin n) : ℕ :=
  ∑ j : Fin n, ∑ k : {k : Fin r // k.val ≠ 0}, m (Sum.inr (p, j, k))

/-- 「`p` 作为**第二**下标出现的次数」：`B_p`。 -/
def sprWtB (m : SprIdx r n →₀ ℕ) (p : Fin n) : ℕ :=
  ∑ i : Fin n, ∑ k : {k : Fin r // k.val ≠ 0}, m (Sum.inr (i, p, k))

/-- ★★★★★ **权积的因子分解**：`∏_v (wt u v)^{m v} = ∏_p (u p)^{A_p} · ((u p)^{B_p})⁻¹`。 -/
theorem sprWtUnit_prod_eq (R : Type) [CommRing R] (u : Fin n → Rˣ)
    (m : SprIdx r n →₀ ℕ) :
    (∏ v : SprIdx r n, sprWtUnit (r := r) R u v ^ (m v))
      = ∏ p : Fin n, ((u p) ^ (sprWtA m p) * ((u p) ^ (sprWtB m p))⁻¹) := by
  rw [Fintype.prod_sum_type]
  have h1 : (∏ i : Fin n, sprWtUnit (r := r) R u (Sum.inl i) ^ (m (Sum.inl i))) = 1 :=
    Finset.prod_eq_one (fun i _ => by simp [sprWtUnit])
  rw [h1, one_mul]
  have hy : (∏ y : YIdx r n, sprWtUnit (r := r) R u (Sum.inr y) ^ (m (Sum.inr y)))
      = ∏ i : Fin n, ∏ j : Fin n, ∏ k : {k : Fin r // k.val ≠ 0},
          (u i * (u j)⁻¹) ^ (m (Sum.inr (i, j, k))) := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    exact Finset.prod_congr rfl (fun k _ => by simp [sprWtUnit])
  rw [hy]
  have hsplit : ∀ i j : Fin n,
      (∏ k : {k : Fin r // k.val ≠ 0}, (u i * (u j)⁻¹) ^ (m (Sum.inr (i, j, k))))
        = (u i * (u j)⁻¹) ^ (∑ k : {k : Fin r // k.val ≠ 0}, m (Sum.inr (i, j, k))) :=
    fun i j => Finset.prod_pow_eq_pow_sum _ _ _
  simp only [hsplit]
  have hmul : ∀ i j : Fin n,
      (u i * (u j)⁻¹ : Rˣ) ^ (∑ k : {k : Fin r // k.val ≠ 0}, m (Sum.inr (i, j, k)))
        = (u i) ^ (∑ k : {k : Fin r // k.val ≠ 0}, m (Sum.inr (i, j, k)))
          * ((u j) ^ (∑ k : {k : Fin r // k.val ≠ 0}, m (Sum.inr (i, j, k))))⁻¹ := by
    intro i j
    rw [mul_pow, ← inv_pow]
  simp only [hmul]
  simp only [Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [sprWtA, Finset.prod_pow_eq_pow_sum]
  · rw [Finset.prod_comm]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [sprWtB]
    simp only [← inv_pow]
    rw [Finset.prod_pow_eq_pow_sum, inv_pow]

#print axioms sprWtUnit_prod_eq

end WtUnit

/-! ## §13 ★★★★★★ **（★）的标量核心：特征传递**（`(乙)` 第五格）

上游（`GenericInv` §86b）已给：`f` 被**所有** `F`-单位环面作用固定 ⟺ 其支撑上每个单项式
对每个 `b` 的权为 `1`（`sprDiagHom_all_fixed_iff`）。本节把"权为 `1`"从 **`F`-单位**
传到**任意交换 `F`-代数中的任意单位族**——这正是 (★) 需要的（c 来自 `T`，不来自 `F`）。

| 件 | 内容 |
|---|---|
| `sprWt_eq_coe_sprWtUnit` | 桥：`sprWt b v = ↑(sprWtUnit F b v)` |
| ★★★★★★ `sprWtUnit_prod_eq_one_of_all_fixed` | **特征传递**：`(∀ b, ∏_v (sprWt b v)^{m v} = 1) ⟹ (∀ R u, ∏_v (wt u v)^{m v} = 1)` |

**证明三步**：① `h` 搬到单位群 `Fˣ` ＋ §12 的权积因子分解；② 取**单点族**
`b = Function.update 1 p t` 得 `t^{A_p}·(t^{B_p})⁻¹ = 1 ∀ t ∈ Fˣ`，由 §12 的
`spr_pow_eq_of_units_imp` 得 `A_p = B_p`；③ 任意单位族代入即得（指数相等 ⟹ 因子两两相消）。

**工艺（教训 126）**：`↑z`（`Units` 强制转换）与 `Units.coeHom F z` 在 `rw` 下**不互相匹配**
（defeq 但不同形）⟹ 用 `change` 或 `rw [map_pow]` ＋ `congr 1` ＋ `exact`（defeq 收口）。
`Units` 的 coercion 引理名是 `val_mul`／`val_pow_eq_pow_val`／`val_inv_eq_inv_val`／`val_one`
（**不是** `coe_*`）；`1` 判别用 `Units.val_eq_one`。 -/

section WtCharacter

variable {F : Type} [Field F] {r n : ℕ}

/-- 权值在单位群中的桥：`sprWt b v = ↑(sprWtUnit F b v)`。 -/
theorem sprWt_eq_coe_sprWtUnit (b : Fin n → Fˣ) (v : SprIdx r n) :
    sprWt F r n b v = ((sprWtUnit (r := r) F b v : Fˣ) : F) := by
  rcases v with i | ⟨i, j, k⟩
  · simp [sprWt_inl, sprWtUnit]
  · simp [sprWt_inr, sprWtUnit]

#print axioms sprWt_eq_coe_sprWtUnit

/-- ★★★★★★ **特征传递**：若某单项式的权积对**所有** `F`-单位族为 `1`，则对**任意**
交换 `F`-代数中的**任意**单位族也为 `1`。 -/
theorem sprWtUnit_prod_eq_one_of_all_fixed [Infinite F]
    {m : SprIdx r n →₀ ℕ}
    (h : ∀ b : Fin n → Fˣ, (∏ v : SprIdx r n, (sprWt F r n b v) ^ (m v)) = 1)
    (R : Type) [CommRing R] [Algebra F R] (u : Fin n → Rˣ) :
    (∏ v : SprIdx r n, sprWtUnit (r := r) R u v ^ (m v)) = 1 := by
  have hb : ∀ b : Fin n → Fˣ,
      (∏ v : SprIdx r n, (sprWtUnit (r := r) F b v) ^ (m v)) = 1 := by
    intro b
    refine Units.val_eq_one.mp ?_
    have hcoe : (((∏ v : SprIdx r n, (sprWtUnit (r := r) F b v) ^ (m v)) : Fˣ) : F)
        = ∏ v : SprIdx r n, (sprWt F r n b v) ^ (m v) := by
      change (Units.coeHom F) (∏ v : SprIdx r n, (sprWtUnit (r := r) F b v) ^ (m v))
        = ∏ v : SprIdx r n, (sprWt F r n b v) ^ (m v)
      rw [map_prod]
      exact Finset.prod_congr rfl (fun v _ => by
        rw [map_pow]
        congr 1
        exact (sprWt_eq_coe_sprWtUnit b v).symm)
    rw [hcoe, h b]
  have h2 : ∀ b : Fin n → Fˣ,
      (∏ p : Fin n, ((b p) ^ (sprWtA m p) * ((b p) ^ (sprWtB m p))⁻¹)) = 1 := by
    intro b
    rw [← sprWtUnit_prod_eq (r := r) F b m]
    exact hb b
  have hsingle : ∀ (p : Fin n) (t : Fˣ),
      (∏ q : Fin n, (((Function.update (1 : Fin n → Fˣ) p t) q) ^ (sprWtA m q)
        * ((((Function.update (1 : Fin n → Fˣ) p t) q) ^ (sprWtB m q))⁻¹)))
        = t ^ (sprWtA m p) * (t ^ (sprWtB m p))⁻¹ := by
    intro p t
    rw [Finset.prod_eq_single p]
    · simp
    · intro q _ hq
      rw [Function.update_of_ne hq]
      simp
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  have hAB : ∀ p : Fin n, sprWtA m p = sprWtB m p := by
    intro p
    refine spr_pow_eq_of_units_imp (F := F) (fun t => ?_)
    have hpt := h2 (Function.update (1 : Fin n → Fˣ) p t)
    rw [hsingle p t] at hpt
    have hF : ((t : F) ^ (sprWtA m p)) * (((t : F) ^ (sprWtB m p)))⁻¹ = 1 := by
      have hcoe := congrArg (fun z : Fˣ => ((z : F))) hpt
      simpa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_one] using hcoe
    have hB : (t : F) ^ (sprWtB m p) ≠ 0 := pow_ne_zero _ (Units.ne_zero t)
    calc (t : F) ^ (sprWtA m p)
        = ((t : F) ^ (sprWtA m p) * ((t : F) ^ (sprWtB m p))⁻¹)
            * (t : F) ^ (sprWtB m p) := by
          rw [mul_assoc, inv_mul_cancel₀ hB, mul_one]
      _ = 1 * (t : F) ^ (sprWtB m p) := by rw [hF]
      _ = (t : F) ^ (sprWtB m p) := one_mul _
  rw [sprWtUnit_prod_eq (r := r) R u m]
  refine Finset.prod_eq_one (fun p _ => ?_)
  rw [hAB p, mul_inv_cancel]

#print axioms sprWtUnit_prod_eq_one_of_all_fixed

end WtCharacter

/-! ## §14 ★★★★★★★★ **（★）标量平衡引理（第五格的唯一实质数学）**

源：`proj-abgv52-frontier-R661` §60.2／§61.2。第五格（K'-世界收口）归约到

```
(★)  η₁ (algebraMap s) = η₂ (algebraMap s)       （s 被环面固定、被 σ 固定）
```

本节把它机检成 `sprMonoAeval_apply_of_diagFixed`：`μ = sprMonoAeval T ξ υ σ c`
（`ξ, υ = η₂` 的生成元值）在 `s` 上等于 `η₂ (algebraMap s)`，**对任意 `T` 的单位族 `c`**。

| 件 | 内容 |
|---|---|
| `sprWtUnit_inl`／`_inr`、`sprWtVal`／`_inl`／`_inr` | 权的定义方程 ＋ `T`-值形态 |
| ★★★★★ `sprMonoAeval_X_ratio` | 单变量：`μ(X v) · wt v = ν(X v)`（`ν` = `c = 1` 的同型映射） |
| ★★★★★ `sprMonoAeval_pow_ratio`／`sprMonoAeval_prod_ratio` | 幂／乘积形态：`μ(P) · W = ν(P)` |
| ★★★★★★ `sprMonoAeval_apply_of_fixed` | 组装：`hP` ＋ 逐单项式权 = 1 ⟹ `μ s = η₂ (algebraMap s)` |
| ★★★★★★★★ **`sprMonoAeval_apply_of_diagFixed`** | **（★）最终形态**：`hD`（环面不动）＋ `hP`（σ 不动）⟹ 结论 |

**证明骨架**：`sprDiagHom_all_fixed_iff`（`GenericInv` §86b，已机检）给「逐单项式 `b`-权 = 1
（∀b）」⟹ §13 `sprWtUnit_prod_eq_one_of_all_fixed` 升级到任意单位族 `c` ⟹
`μ` 与 `ν` 在每个单项式上相等（`prod_ratio` ＋ 权 = 1）⟹ `as_sum` 求和 ⟹
`ν = η₂ ∘ (algebraMap ∘ sprPermAlgEquiv σ)`（`sprMonoAeval_comp` ＋ 生成元比较）⟹ `hP` 收口。

**工艺（教训 127）**：`sprWt`／`sprWtVal`／`↑(sprWtUnit …)` 三者**defeq 但 `rw` 互不认** ⟹
一律用 `simp only [...]` 或 `change`；`Finsupp.prod`（`m.prod (fun n e => …)`）与
`m.support.prod (fun v => … ^ m v)` 亦同（先 `simp only [Finsupp.prod]`）。
`MvPolynomial.C a` 与 `algebraMap a` 之间用 `MvPolynomial.C_eq_algebraMap`。
`hP` 的 `↑(sprPermAlgEquiv σ) s` 形态用 `congrArg` 收口（`rw` 不认）。 -/

section MonoBalance

variable {F : Type} [Field F] {r n : ℕ} {T : Type} [CommRing T] [Algebra F T]

theorem sprWtUnit_inl (R : Type) [CommRing R] (u : Fin n → Rˣ) (i : Fin n) :
    sprWtUnit (r := r) R u (Sum.inl i) = 1 := rfl

theorem sprWtUnit_inr (R : Type) [CommRing R] (u : Fin n → Rˣ)
    (i j : Fin n) (k : {k : Fin r // k.val ≠ 0}) :
    sprWtUnit (r := r) R u (Sum.inr (i, j, k)) = u i * (u j)⁻¹ := rfl

/-- 权在环中的值（`T`-值形态）。 -/
noncomputable def sprWtVal (R : Type) [CommRing R] (u : Fin n → Rˣ) (v : SprIdx r n) : R :=
  ((sprWtUnit (r := r) R u v : Rˣ) : R)

theorem sprWtVal_inl (R : Type) [CommRing R] (u : Fin n → Rˣ) (i : Fin n) :
    sprWtVal (r := r) R u (Sum.inl i) = 1 := by
  simp [sprWtVal, sprWtUnit_inl]

theorem sprWtVal_inr (R : Type) [CommRing R] (u : Fin n → Rˣ)
    (i j : Fin n) (k : {k : Fin r // k.val ≠ 0}) :
    sprWtVal (r := r) R u (Sum.inr (i, j, k)) = ((u i * (u j)⁻¹ : Rˣ) : R) := by
  simp [sprWtVal, sprWtUnit_inr]

/-- 单变量恒等式（**乘法形态**，不用除法）：`μ(X v) · wt v = ν(X v)`。 -/
theorem sprMonoAeval_X_ratio (ξ : Fin n → T) (υ : YIdx r n → T)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ) (v : SprIdx r n) :
    sprMonoAeval (F := F) (r := r) T ξ υ σ c (MvPolynomial.X v)
        * (sprWtVal (r := r) T c v)
      = sprMonoAeval (F := F) (r := r) T ξ υ σ 1 (MvPolynomial.X v) := by
  rcases v with i | ⟨i, j, k⟩
  · rw [sprWtVal_inl, mul_one, sprMonoAeval_X_inl, sprMonoAeval_X_inl]
  · rw [sprMonoAeval_X_inr, sprMonoAeval_X_inr, sprWtVal_inr]
    have h1u : ((c j * (c i)⁻¹ : Tˣ)) * ((c i * (c j)⁻¹ : Tˣ)) = 1 := by group
    have h1 : ((c j * (c i)⁻¹ : Tˣ) : T) * ((c i * (c j)⁻¹ : Tˣ) : T) = 1 := by
      rw [← Units.val_mul, h1u, Units.val_one]
    have hR : ((1 : Fin n → Tˣ) j * (((1 : Fin n → Tˣ) i)⁻¹) : Tˣ) = 1 := by simp
    rw [hR, Units.val_one, one_mul]
    calc ((c j * (c i)⁻¹ : Tˣ) : T) * υ (σ i, σ j, k) * ((c i * (c j)⁻¹ : Tˣ) : T)
        = (((c j * (c i)⁻¹ : Tˣ) : T) * ((c i * (c j)⁻¹ : Tˣ) : T)) * υ (σ i, σ j, k) := by
          ring
      _ = 1 * υ (σ i, σ j, k) := by rw [h1]
      _ = υ (σ i, σ j, k) := one_mul _

#print axioms sprMonoAeval_X_ratio

/-- 幂形态：`μ(X v ^ e) · (wt v)^e = ν(X v ^ e)`。 -/
theorem sprMonoAeval_pow_ratio (ξ : Fin n → T) (υ : YIdx r n → T)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ) (v : SprIdx r n) (e : ℕ) :
    sprMonoAeval (F := F) (r := r) T ξ υ σ c ((MvPolynomial.X (R := F) v) ^ e)
        * (sprWtVal (r := r) T c v) ^ e
      = sprMonoAeval (F := F) (r := r) T ξ υ σ 1 ((MvPolynomial.X (R := F) v) ^ e) := by
  rw [map_pow, map_pow, ← mul_pow, sprMonoAeval_X_ratio]

#print axioms sprMonoAeval_pow_ratio

/-- 乘积形态（**乘法形态**）：`μ(∏ X_v^{f v}) · ∏ (wt v)^{f v} = ν(∏ X_v^{f v})`。 -/
theorem sprMonoAeval_prod_ratio (ξ : Fin n → T) (υ : YIdx r n → T)
    (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ) (u : Finset (SprIdx r n))
    (f : SprIdx r n → ℕ) :
    sprMonoAeval (F := F) (r := r) T ξ υ σ c
        (u.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v))
        * (u.prod (fun v => (sprWtVal (r := r) T c v) ^ f v))
      = sprMonoAeval (F := F) (r := r) T ξ υ σ 1
          (u.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v)) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert v u hv ih =>
    have hstep : ∀ (a b c d : T), a * b * (c * d) = (a * c) * (b * d) :=
      fun a b c d => by ring
    simp only [Finset.prod_insert hv, map_mul]
    rw [hstep, sprMonoAeval_pow_ratio, ih]

#print axioms sprMonoAeval_prod_ratio

/-- ★★★★★★★ **（★）组装**：`s` 被 `σ` 固定且各单项式权积为 `1` ⟹ `μ s = η₂ (algebraMap s)`。 -/
theorem sprMonoAeval_apply_of_fixed [Infinite F]
    (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (η₂ : SprField F r n →ₐ[F] T) {s : Spr F r n}
    (hP : sprPermAlgEquiv F r n σ s = s)
    (hbal : ∀ m ∈ s.support,
      (m.support.prod (fun v => (sprWtVal (r := r) T c v) ^ (m v))) = 1) :
    sprMonoAeval (F := F) (r := r) T
        (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
        (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inr ijk)))) σ c s
      = η₂ (algebraMap (Spr F r n) (SprField F r n) s) := by
  classical
  -- `μ₀`：`c = 1` 的 `K'`-值版本，等于 `algebraMap ∘ sprPermAlgEquiv σ`
  have hμ₀eq : sprMonoAeval (F := F) (r := r) (SprField F r n)
        (fun i => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))
        (fun ijk => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inr ijk)))
        σ (fun _ => 1)
      = (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)).comp
          (sprPermAlgEquiv F r n σ).toAlgHom := by
    refine MvPolynomial.algHom_ext (fun v => ?_)
    rcases v with i | ⟨i, j, k⟩
    · show sprMonoAeval (F := F) (r := r) (SprField F r n)
          (fun i => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))
          (fun ijk => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inr ijk)))
          σ (fun _ => 1) (MvPolynomial.X (Sum.inl i))
        = algebraMap (Spr F r n) (SprField F r n)
            (sprPermAlgEquiv F r n σ (MvPolynomial.X (Sum.inl i)))
      rw [sprPermAlgEquiv_X_inl, sprMonoAeval_X_inl]
    · show sprMonoAeval (F := F) (r := r) (SprField F r n)
          (fun i => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))
          (fun ijk => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inr ijk)))
          σ (fun _ => 1) (MvPolynomial.X (Sum.inr (i, j, k)))
        = algebraMap (Spr F r n) (SprField F r n)
            (sprPermAlgEquiv F r n σ (MvPolynomial.X (Sum.inr (i, j, k))))
      rw [sprPermAlgEquiv_X_inr, sprMonoAeval_X_inr]
      simp
  -- `ν = η₂ ∘ μ₀`
  have hν : sprMonoAeval (F := F) (r := r) T
        (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
        (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inr ijk)))) σ (fun _ => 1)
      = η₂.comp (sprMonoAeval (F := F) (r := r) (SprField F r n)
        (fun i => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))
        (fun ijk => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inr ijk)))
        σ (fun _ => 1)) := by
    rw [sprMonoAeval_comp (F := F) (r := r) (R := SprField F r n) (R' := T) η₂
      (fun i => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))
      (fun ijk => algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inr ijk)))
      σ (fun _ => 1)]
    simp
  -- 逐步：`μ s = ν s = η₂ (μ₀ s) = η₂ (algebraMap (sprPermAlgEquiv σ s)) = η₂ (algebraMap s)`
  have hmono : sprMonoAeval (F := F) (r := r) T
        (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
        (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inr ijk)))) σ c s
      = sprMonoAeval (F := F) (r := r) T
        (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
        (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inr ijk)))) σ (fun _ => 1) s := by
    conv_lhs => rw [MvPolynomial.as_sum s]
    conv_rhs => rw [MvPolynomial.as_sum s]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    set P : Spr F r n := m.support.prod (fun v => (MvPolynomial.X (R := F) v) ^ (m v)) with hP
    set W : T := m.support.prod (fun v => (sprWtVal (r := r) T c v) ^ (m v)) with hW
    have hw : W = 1 := hbal m hm
    have hr : sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
            (MvPolynomial.X (Sum.inr ijk)))) σ c P * W
        = sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
            (MvPolynomial.X (Sum.inr ijk)))) σ (fun _ => 1) P :=
      sprMonoAeval_prod_ratio (F := F) (r := r) (T := T)
        (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
        (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inr ijk)))) σ c m.support m
    have hμP : sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
            (MvPolynomial.X (Sum.inr ijk)))) σ c P
        = sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
            (MvPolynomial.X (Sum.inr ijk)))) σ (fun _ => 1) P := by
      rw [← hr, hw, mul_one]
    have hC : sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
            (MvPolynomial.X (Sum.inr ijk)))) σ c (MvPolynomial.C (s.coeff m))
        = sprMonoAeval (F := F) (r := r) T
          (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
          (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
            (MvPolynomial.X (Sum.inr ijk)))) σ (fun _ => 1) (MvPolynomial.C (s.coeff m)) := by
      rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
    conv_lhs => rw [MvPolynomial.monomial_eq (a := s.coeff m) (s := m)]
    conv_rhs => rw [MvPolynomial.monomial_eq (a := s.coeff m) (s := m)]
    simp only [Finsupp.prod]
    rw [map_mul, map_mul, hC, hμP]

  rw [hmono, hν, AlgHom.comp_apply, hμ₀eq, AlgHom.comp_apply]
  exact congrArg (fun x => η₂ (algebraMap (Spr F r n) (SprField F r n) x)) hP

#print axioms sprMonoAeval_apply_of_fixed

/-- ★★★★★★★★ **（★）最终形态**：`s` 被环面（所有 `F`-单位）固定、被 `σ` 固定 ⟹ `μ s = η₂ (algebraMap s)`。

**这是 `(乙)` 第五格唯一的实质数学**（见 `proj-abgv52-frontier-R661` §60.2／§61.2）。
证明：`sprDiagHom_all_fixed_iff`（已机检）给「逐单项式 `b`-权 = 1（∀b）」，§13 的
`sprWtUnit_prod_eq_one_of_all_fixed` 把它升级到 `T` 的任意单位族 `c`，再由
`sprMonoAeval_apply_of_fixed` 收口。 -/
theorem sprMonoAeval_apply_of_diagFixed [Infinite F]
    (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (η₂ : SprField F r n →ₐ[F] T) {s : Spr F r n}
    (hD : ∀ b : Fin n → Fˣ, sprDiagHom F r n b s = s)
    (hP : sprPermAlgEquiv F r n σ s = s) :
    sprMonoAeval (F := F) (r := r) T
        (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
        (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inr ijk)))) σ c s
      = η₂ (algebraMap (Spr F r n) (SprField F r n) s) := by
  classical
  have hw1 : ∀ (b : Fin n → Fˣ) (m : SprIdx r n →₀ ℕ), m ∈ s.support →
      (m.support.prod (fun v => (sprWt F r n b v) ^ (m v))) = 1 :=
    fun b m hm => (sprDiagHom_all_fixed_iff F r n s).mp hD b m hm
  have hbal : ∀ m ∈ s.support,
      (m.support.prod (fun v => (sprWtVal (r := r) T c v) ^ (m v))) = 1 := by
    intro m hm
    have huniv : ∀ b : Fin n → Fˣ, (∏ v : SprIdx r n, (sprWt F r n b v) ^ (m v)) = 1 := by
      intro b
      rw [← Finset.prod_subset (Finset.subset_univ m.support) (fun v _ hv => by
        rw [Finsupp.notMem_support_iff.mp hv, pow_zero])]
      exact hw1 b m hm
    have hunit := sprWtUnit_prod_eq_one_of_all_fixed (F := F) (r := r) (m := m) huniv T c
    have hcoe : (Units.coeHom T) (∏ v : SprIdx r n, sprWtUnit (r := r) T c v ^ (m v)) = 1 := by
      rw [hunit, map_one]
    rw [map_prod] at hcoe
    rw [Finset.prod_subset (Finset.subset_univ m.support) (fun v _ hv => by
      rw [Finsupp.notMem_support_iff.mp hv, pow_zero])]
    simpa [sprWtVal, Units.val_pow_eq_pow_val] using hcoe
  exact sprMonoAeval_apply_of_fixed (F := F) (r := r) (T := T) σ c η₂ hP hbal

#print axioms sprMonoAeval_apply_of_diagFixed

end MonoBalance

/-! ## §15 ★★★★★ **K'-世界 N-作用 → `Spr`-世界 N-不变性的传递（1／2）：半直积形态**

第五格（K'-世界收口）的簿记第一件：`sprMatNFixed (coeK β)` 要转回 `Spr`-世界的
`sprPsiMonoR`-不变性（`S'`-world `lem1424_local` 的 `hα` 形态）。本轮先给其中的**代数核**：

| 件 | 内容 |
|---|---|
| ★★★★ `sprMonoAeval_coeff` | 半直积的系数簿记：`(↑(b(σj))⁻¹) * (↑(b(σi))⁻¹)⁻¹ = ↑(b(σi)) * (↑(b(σj)))⁻¹` |
| ★★★★★ **`sprMonoAeval_eq_diag_comp_perm`** | **`μ(σ, b(σ·)⁻¹) = φ_b ∘ σ`**（`Spr`-值的 AlgHom 等式） |

**为何要它**：`sprFieldPsiMono`（K'）的内层映射是 `e_b ∘ e_σ`（分式域自同构），
而 `sprPsiMonoR`（`Spr`）的内层是 `sprMonoAeval`（多项式替换）。本件把两者对上——
**注意参数必须是 `b(σ·)`**：`sprMonoAeval` 的系数是 `c_j c_i⁻¹`，而 `φ_b ∘ σ` 在 `y_ijk`
上的系数是 `b(σi)/b(σj)` ⟹ 取 `c_i = (b(σ i))⁻¹` 才相等。**这一处错位是下一件（自然性）
把 `hα` 参数写成 `b(σ·)` 的根因**。

**工艺（教训 128）**：`↑(sprPermAlgEquiv σ) (X …)` 与 `sprPermAlgEquiv σ (X …)` **defeq 但
`rw` 不认** ⟹ 每个生成元分支先用 `show` 写成显式形态再 `rw`。`sprMonoAeval_X_inr` 的系数是
`((c j * (c i)⁻¹ : Rˣ) : R)`（单位群里的逆再强制转换），与 `F` 里的逆**写法不同** ⟹
先把整块系数等式提成独立引理（`sprMonoAeval_coeff`），并在最后一步用 `rfl` 收掉
`↑(algebraMap …)` 与 `algebraMap …` 的强制转换差。 -/

section MonoAevalSemidirect

variable {F : Type} [Field F] {r n : ℕ}

/-- 半直积的系数簿记。 -/
theorem sprMonoAeval_coeff (b : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ j))⁻¹))
        * ((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ i))⁻¹))⁻¹) : (Spr F r n)ˣ) :
      Spr F r n)
      = algebraMap F (Spr F r n) ((b (σ i) : F) * ((b (σ j) : F))⁻¹) := by
  have h1 : ((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ j))⁻¹))
        * ((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ i))⁻¹))⁻¹) : (Spr F r n)ˣ)
      = Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ j))⁻¹ * (b (σ i))) := by
    rw [← map_inv, ← map_mul, inv_inv]
  rw [h1, Units.coe_map]
  rw [show ((↑((b (σ j))⁻¹ * b (σ i))) : F)
      = ((↑(b (σ i)) : F) * ((↑(b (σ j)) : F))⁻¹) from by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    ring]
  rfl

#print axioms sprMonoAeval_coeff

/-- ★★★★★ **半直积形态**：`μ(σ, b(σ·)⁻¹) = φ_b ∘ σ`。 -/
theorem sprMonoAeval_eq_diag_comp_perm (b : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    sprMonoAeval (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ i))⁻¹))
      = (sprDiagHom F r n b).comp (sprPermAlgEquiv F r n σ).toAlgHom := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  rcases v with i | ⟨i, j, k⟩
  · show sprMonoAeval (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ i))⁻¹))
        (MvPolynomial.X (Sum.inl i))
      = sprDiagHom F r n b (sprPermAlgEquiv F r n σ (MvPolynomial.X (Sum.inl i)))
    rw [sprPermAlgEquiv_X_inl, sprDiagHom_X_inl, sprMonoAeval_X_inl]
  · show sprMonoAeval (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ i))⁻¹))
        (MvPolynomial.X (Sum.inr (i, j, k)))
      = sprDiagHom F r n b (sprPermAlgEquiv F r n σ (MvPolynomial.X (Sum.inr (i, j, k))))
    rw [sprPermAlgEquiv_X_inr, sprDiagHom_X_inr, sprMonoAeval_X_inr,
      sprMonoAeval_coeff, MvPolynomial.C_eq_algebraMap]

#print axioms sprMonoAeval_eq_diag_comp_perm

end MonoAevalSemidirect

/-! ## §16 ★★★★★★★ **K'-N-作用 → `Spr`-N-不变性（传递完成）**

第五格簿记的第 1 件（R723 §15 给代数核）：把 `sprMatNFixed (coeK β)`（K'-世界）转回
`Spr`-世界的 `sprPsiMonoR`-不变性——即 `S'`-world `lem1424_local` 的 `hα` 形态。

| 件 | 内容 |
|---|---|
| `sprUnitK_eq_map` | `sprUnitK` 是两次 `Units.map` 的提升 |
| ★★★★★ `sprFieldPsiMono_algebraMap` | **自然性**：`sprFieldPsiMono ξ σ cK (coeK β) = coeK (sprPsiMonoR … σ cS β)` |
| ★★★★★★ **`sprPsiMonoR_of_sprMatNFixed`** | **传递**：`sprMatNFixed (coeK β) ⟹ ∀ τ b, sprPsiMonoR (Spr) … τ (b⁻¹) β = β` |

**证明**：对给定的 `(τ, b)` 取 `b' := b ∘ τ⁻¹`（于是 `b'(τ i) = b i`）；K'-世界桥
（`sprFieldPsiMono_eq_self_of_sprMatNFixed`，R719 已机检）给 `sprFieldPsiMono … τ b'` 的不变性，
自然性把它化成 `coeK (sprPsiMonoR … τ (b'∘τ)⁻¹ β) = coeK β`，再由 `b'(τ i) = b i` 与
`coeK` 的单射性收口。**⟹ 参数错位（§15 的 `b(σ·)`）在此被 `b' := b ∘ τ⁻¹` 精确抵消。**

**工艺（教训 129）**：`Units.map` 要 `MonoidHom`（`φ.toRingHom.toMonoidHom`，写成
`φ.toRingHom` 会报「expected `α →* β`」）；`Units.map` 的**求逆**用 `← map_inv`（无
`Units.map_inv`，教训 120）；`sprDiagMatR_map` 的结论形如 `∀ c, …`，须显式传 `(n := n) (φ := phi) (c := …)`；
`Matrix.map_injective` 是 `Injective f → Injective (fun M => M.map f)`（**不是** `↔`）；
`let φ` / `let cS` 与显式形态 defeq 但 `rw` 不互认 ⟹ 关键房式先 `show`/`have` 成显式形态再 `rw`，
末尾用 `rfl` 收耦合。 -/

section NFixedTransfer

variable {F : Type} [Field F] {r n : ℕ}

theorem sprUnitK_eq_map (b : Fin n → Fˣ) (i : Fin n) :
    sprUnitK (F := F) (r := r) (n := n) b i
      = Units.map (IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)).toRingHom
          (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b i)) := rfl

#print axioms sprUnitK_eq_map

/-- ★★★★★ **自然性**：`sprFieldPsiMono` 在 `Spr`-值矩阵上的形态。 -/
theorem sprFieldPsiMono_algebraMap (b : Fin n → Fˣ) (σ : Equiv.Perm (Fin n))
    (β : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprFieldPsiMono (F := F) (r := r) (n := n)
        ((sprDiagFieldEquiv F r n b).toRingHom.comp (sprPermFieldEquiv F r n σ).toRingHom)
        σ (fun i => (sprUnitK F r n b (σ i))⁻¹)
        (β.map (algebraMap (Spr F r n) (SprField F r n)))
      = (sprPsiMonoR (F := F) (r := r) (Spr F r n)
          (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
          (fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b (σ i)))⁻¹) β).map
        (algebraMap (Spr F r n) (SprField F r n)) := by
  let phi : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  let cS : Fin n → (Spr F r n)ˣ :=
    fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b (σ i)))⁻¹
  have hP : sprPmatK (F := F) (r := r) (n := n) σ
      = (sprPmat (n := n) (Spr F r n) σ).map phi :=
    sprPmatK_eq_map (F := F) (r := r) (n := n) σ
  have hP' : sprPmatK (F := F) (r := r) (n := n) σ⁻¹
      = (sprPmat (n := n) (Spr F r n) σ⁻¹).map phi :=
    sprPmatK_eq_map (F := F) (r := r) (n := n) σ⁻¹
  have hK : ∀ i, sprUnitK (F := F) (r := r) (n := n) b (σ i)
      = Units.map phi.toRingHom.toMonoidHom ((cS i)⁻¹) := by
    intro i
    show Units.map phi.toRingHom.toMonoidHom (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b (σ i)))
      = Units.map phi.toRingHom
          ((((Units.map (algebraMap F (Spr F r n)).toMonoidHom (b (σ i)))⁻¹))⁻¹)
    rw [inv_inv]
    rfl
  have hcK : (fun i => (sprUnitK (F := F) (r := r) (n := n) b (σ i))⁻¹)
      = fun i => Units.map phi.toRingHom.toMonoidHom (cS i) := by
    funext i
    rw [hK i, ← map_inv, inv_inv]
  have hcK' : (fun i => ((sprUnitK (F := F) (r := r) (n := n) b (σ i))⁻¹)⁻¹)
      = fun i => Units.map phi.toRingHom.toMonoidHom ((cS i)⁻¹) := by
    funext i
    rw [hK i, ← map_inv, inv_inv, inv_inv]
    rfl
  have hD1 : (sprDiagMatR (n := n) (Spr F r n) cS).map phi
      = sprDiagMatR (n := n) (SprField F r n)
          (fun i => Units.map phi.toRingHom.toMonoidHom (cS i)) :=
    sprDiagMatR_map (n := n) (φ := phi) (c := cS)
  have hD2 : (sprDiagMatR (n := n) (Spr F r n) (fun i => (cS i)⁻¹)).map phi
      = sprDiagMatR (n := n) (SprField F r n) (fun i => Units.map phi.toRingHom.toMonoidHom ((cS i)⁻¹)) :=
    sprDiagMatR_map (n := n) (φ := phi) (c := fun i => (cS i)⁻¹)
  have hmiddle : (β.map (algebraMap (Spr F r n) (SprField F r n))).map
        ((sprDiagFieldEquiv F r n b).toRingHom.comp (sprPermFieldEquiv F r n σ).toRingHom)
      = (β.map (sprMonoAeval (F := F) (r := r) (Spr F r n)
          (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ cS)).map
        (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext x
    show (sprDiagFieldEquiv F r n b)
        ((sprPermFieldEquiv F r n σ) (algebraMap (Spr F r n) (SprField F r n) x))
      = algebraMap (Spr F r n) (SprField F r n)
        (sprMonoAeval (F := F) (r := r) (Spr F r n)
          (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
          (fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b (σ i)))⁻¹) x)
    have hfam : (fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b (σ i)))⁻¹)
        = fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b (σ i))⁻¹) := by
      funext i
      rw [map_inv]
    rw [hfam, sprPermFieldEquiv_algebraMap, sprDiagFieldEquiv_algebraMap,
      sprMonoAeval_eq_diag_comp_perm (F := F) (r := r) (b := b) (σ := σ), AlgHom.comp_apply]
    rfl
  rw [sprFieldPsiMono, sprPsiMonoR]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  rw [hP, hP']
  rw [hcK, hcK']
  rw [← hD1, ← hD2]
  rw [hmiddle]
  rfl

#print axioms sprFieldPsiMono_algebraMap

/-- ★★★★★★ **N-不变性传递**：`sprMatNFixed (coeK β)` ⟹ `Spr`-世界的 `sprPsiMonoR`-不变性
（`S'`-world `lem1424_local` 的 `hα` 形态）。 -/
theorem sprPsiMonoR_of_sprMatNFixed [Infinite F]
    (β : Matrix (Fin n) (Fin n) (Spr F r n))
    (h : sprMatNFixed F r n (β.map (algebraMap (Spr F r n) (SprField F r n)))) :
    ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) β = β := by
  intro τ b
  set b' : Fin n → Fˣ := fun i => b (τ⁻¹ i) with hb'def
  have hb' : ∀ i, b' (τ i) = b i := by
    intro i
    simp [hb'def]
  have hK : sprFieldPsiMono (F := F) (r := r) (n := n)
        ((sprDiagFieldEquiv F r n b').toRingHom.comp (sprPermFieldEquiv F r n τ).toRingHom)
        τ (fun i => (sprUnitK F r n b' (τ i))⁻¹)
        (β.map (algebraMap (Spr F r n) (SprField F r n))) = 
      β.map (algebraMap (Spr F r n) (SprField F r n)) :=
    sprFieldPsiMono_eq_self_of_sprMatNFixed (F := F) (r := r) (n := n) h τ b'
  rw [sprFieldPsiMono_algebraMap (F := F) (r := r) (b := b') (σ := τ) β] at hK
  have hcS : (fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b' (τ i)))⁻¹)
      = fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom (b i))⁻¹ := by
    funext i
    rw [hb' i]
  rw [hcS] at hK
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (Spr F r n) =>
      M.map (algebraMap (Spr F r n) (SprField F r n))) :=
    Matrix.map_injective (IsFractionRing.injective (Spr F r n) (SprField F r n))
  exact hinj hK

#print axioms sprPsiMonoR_of_sprMatNFixed

end NFixedTransfer

/-! ## §17 ★★★★★ **第五格组装（1／2）：β 层收口**

用 R724 的 N-不变性传递（`sprPsiMonoR_of_sprMatNFixed`）**实例化 `S'`-世界的 `lem1424_local`**：
对 `Spr`-值的 `N`-不变矩阵 `β`，两个"K'-世界同态的限制"在 `coeK β` 上相等。

**做法（纯实例化，无需新数学）**：把 `θᵢ` 沿 `AlgHom.mapMatrix φ`（`φ := algebraMap Spr K'`）拉到
`M_n(Spr)`，`η₁` 拉到 `Spr`（`η₁.comp φ`）；`hX`／`hY` 与 `hΔ` 都是 `sprFieldXdiag = (xdiag).map φ`
等定义式的搬运。 -/

section LocalBeta

variable {F : Type} [Field F] {r n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★★★ **β 层的收口**（S'-世界 `lem1424_local` 的实例化）：
`Spr`-值 N-不变矩阵在两个「K'-世界同态的限制」下相等。 -/
theorem sprLocalBeta [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
    (β : Matrix (Fin n) (Fin n) (Spr F r n))
    (hβfix : sprMatNFixed F r n (β.map (algebraMap (Spr F r n) (SprField F r n))))
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : SprField F r n →ₐ[F] T)
    (h₁ : ∀ (γ : Matrix (Fin n) (Fin n) (SprField F r n)), θ₁ γ = γ.map η₁)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k))
    (hΔ : IsUnit (η₁ (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F)))) :
    θ₁ (β.map (algebraMap (Spr F r n) (SprField F r n)))
      = θ₂ (β.map (algebraMap (Spr F r n) (SprField F r n))) := by
  let phi : Spr F r n →ₐ[F] SprField F r n :=
    IsScalarTower.toAlgHom F (Spr F r n) (SprField F r n)
  have hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) β = β :=
    sprPsiMonoR_of_sprMatNFixed (F := F) (r := r) β hβfix
  have h₁' : ∀ (γ : Matrix (Fin n) (Fin n) (Spr F r n)),
      (θ₁.comp (AlgHom.mapMatrix phi)) γ = γ.map (η₁.comp phi) := by
    intro γ
    show θ₁ (γ.map phi) = γ.map (fun x => η₁ (phi x))
    rw [h₁, Matrix.map_map]
    rfl
  have hX' : (θ₁.comp (AlgHom.mapMatrix phi)) (xdiag F r n)
      = (θ₂.comp (AlgHom.mapMatrix phi)) (xdiag F r n) := by
    show θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n)
    exact hX
  have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
      (θ₁.comp (AlgHom.mapMatrix phi)) (ymat F r n k)
        = (θ₂.comp (AlgHom.mapMatrix phi)) (ymat F r n k) := by
    intro k
    show θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k)
    exact hY k
  have hΔ' : IsUnit ((η₁.comp phi) (sprDiscr F)) := hΔ
  have hres := lem1424_local (F := F) (r := r) (n := n) (T := T) β hα
    (θ₁.comp (AlgHom.mapMatrix phi)) (θ₂.comp (AlgHom.mapMatrix phi)) (η₁.comp phi)
    h₁' hX' hY' hΔ'
  show θ₁ (β.map phi) = θ₂ (β.map phi)
  exact hres

#print axioms sprLocalBeta

end LocalBeta

/-! ## §18 ★★★★★★★★★ **第五格收口：`lem:14.24` 的 `K'`-世界局部形态**

```
sprLem1424LocalK' :
  [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
  α : M_n(K')   (hα : sprMatNFixed α)
  θ₁ θ₂ : M_n(K') →ₐ M_n(T)   η₁ : K' →ₐ T   (h₁ : θ₁ = M_n(η₁))
  hX（xdiag 上一致）  hY（ymat 上一致）  hΔ（η₁(Δ) 可逆）
  ⟹  θ₁ α = θ₂ α
```

**证明骨架（15 步）**：① 归一化 `θ₂`（`sprFieldExistsEta2_local`）；② `θ₂(X)` 对角 ＋ 判别式
（`sprFieldTheta_xdiag_eq`／`sprFieldIsUnit_sub_of_discr_map`）；③ 取置换 `σ`（`sprFieldStepTwo_local`）；
④ `A` 在 `stdMU` 上的作用（`sprFieldStdMU_map`）；⑤ `A = P_σ D_c`（`sprStepThree_unitsUnit`）＋
共轭形态 `h₂'`（`sprFieldConjForm_of_units`）；⑥ 分母 `(s, β)`（`lem1425_matrix_fixed`）；
⑦ 同一计算 `hcalc`（`sprFieldSameCalc_hxA/_hyA` ＋ §11）；⑧ **(★)**（§14）得
`η₁(alg s) = η₂(alg s)`；⑨ β 层收口（§17 `sprLocalBeta`）；⑩ β 层共轭恒等式；
⑪ `hsmul`（`sprAlgebraMap_smul_eq` ＋ `matrix_map_smul`）；⑫ 标量穿过共轭（`Matrix.smul_mul/mul_smul`）；
⑬ 标量是单位（`IsUnit`）；⑭ `α` 层共轭恒等式（用 `w⁻¹ •` 消去标量）；⑮ `sprConj_unit_cancel` 收口。

**工艺（教训 130）**：`smul_smul` 在 `a • b • X` 上**不命中**（`•` 左结合）⟹ 显式括号
`a • (b • X)`；5 重乘积的**结合结构**：`h₂'`／`hαconj` 是左结合，`↑u * X * ↑u⁻¹` 展开后右端成
`(D⁻¹ * P⁻¹)` ⟹ 用 `simp only [← Matrix.mul_assoc]` 统一到左结合再 `rw`。 -/

section Lem1424LocalKPrime

variable {F : Type} [Field F] {r n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★★★★★★ **`lem:14.24` 的 `K'`-世界局部形态**（第五格收口）：
`T` 局部、`θ₁ = M_n(η₁)`、`θ₁θ₂` 在两个生成元族上一致、`η₁(Δ)` 可逆、`α` 为 `N`-不变
⟹ `θ₁ α = θ₂ α`。 -/
theorem sprLem1424LocalK' [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (SprField F r n))
    (hα : sprMatNFixed F r n α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : SprField F r n →ₐ[F] T)
    (h₁ : ∀ (γ : Matrix (Fin n) (Fin n) (SprField F r n)), θ₁ γ = γ.map η₁)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k))
    (hΔ : IsUnit (η₁ (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F)))) :
    θ₁ α = θ₂ α := by
  classical
  -- ① 归一化 `θ₂`：`A · θ₂ · A⁻¹ = M_n(η₂)`
  obtain ⟨A, η₂, h₂⟩ := sprFieldExistsEta2_local (F := F) (r := r) (n := n) (T := T) θ₂
  -- ② `θ₂(X)` 的对角形态 ＋ 判别式给 `IsUnit (η₁ x_j − η₁ x_i)`
  have hC : θ₂ (sprFieldXdiag F r n)
      = Matrix.diagonal (fun i => η₁ (algebraMap (Spr F r n) (SprField F r n)
          (MvPolynomial.X (Sum.inl i)))) :=
    sprFieldTheta_xdiag_eq (F := F) (r := r) (n := n) (T := T) η₁ θ₁ h₁ θ₂ hX
  have hc : ∀ i j : Fin n, i ≠ j →
      IsUnit (η₁ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl j)))
        - η₁ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i)))) :=
    fun i j hij => sprFieldIsUnit_sub_of_discr_map (F := F) (r := r) (n := n) (T := T) η₁ hΔ hij
  -- ③ 存在置换 `σ`
  obtain ⟨σ, hσ⟩ := sprFieldStepTwo_local (F := F) (r := r) (n := n) (T := T) θ₂ η₁ hC hc
  -- ④ `A` 在标准矩阵单位上的作用
  have hA : ∀ i, (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
      * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = stdMU (n := Fin n) (R := T) (σ i) (σ i) := by
    intro i
    have h := h₂ (stdMU (n := Fin n) (R := SprField F r n) (σ i) (σ i))
    rw [hσ i, sprFieldStdMU_map (F := F) (S := T) η₂ (σ i) (σ i)] at h
    exact h
  obtain ⟨c, hAU⟩ := sprStepThree_unitsUnit σ A hA
  -- ⑤ `h₂` 换成 `P_σ D_c`-形态
  have h₂' : ∀ γ : Matrix (Fin n) (Fin n) (SprField F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ γ
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = γ.map η₂ :=
    sprFieldConjForm_of_units (F := F) (r := r) (n := n) (T := T) σ c A hAU θ₂ η₂ h₂
  -- ⑥ 分母：`s • α = β 的像`
  obtain ⟨s, β, hsne, hsn, hβfix, hβeq⟩ := lem1425_matrix_fixed (F := F) (r := r) (n := n) α hα
  -- ⑦ 生成元一致性 ⟹ 同一计算
  have hxA := sprFieldSameCalc_hxA (F := F) (r := r) (n := n) (T := T) η₁ η₂ σ c θ₁ θ₂ h₁ h₂' hX
  have hyA := sprFieldSameCalc_hyA (F := F) (r := r) (n := n) (T := T) η₁ η₂ σ c θ₁ θ₂ h₁ h₂' hY
  have hcalc := sprFieldSameCalc (F := F) (r := r) (n := n) (T := T) σ c η₁ η₂ hxA hyA
  -- ⑧ (★)：`η₁(algebraMap s) = η₂(algebraMap s)`
  have hscal : η₁ (algebraMap (Spr F r n) (SprField F r n) s)
      = η₂ (algebraMap (Spr F r n) (SprField F r n) s) := by
    have h1 : η₁ (algebraMap (Spr F r n) (SprField F r n) s)
        = sprMonoAeval (F := F) (r := r) T
            (fun i => η₂ (algebraMap (Spr F r n) (SprField F r n) (MvPolynomial.X (Sum.inl i))))
            (fun ijk => η₂ (algebraMap (Spr F r n) (SprField F r n)
              (MvPolynomial.X (Sum.inr ijk)))) σ c s := AlgHom.congr_fun hcalc s
    rw [h1]
    exact sprMonoAeval_apply_of_diagFixed (F := F) (r := r) (T := T) σ c η₂ hsn.1 (hsn.2 σ)
  -- ⑨ β 层收口
  have hβval : θ₁ (β.map (algebraMap (Spr F r n) (SprField F r n)))
      = θ₂ (β.map (algebraMap (Spr F r n) (SprField F r n))) :=
    sprLocalBeta (F := F) (r := r) (n := n) (T := T) β hβfix θ₁ θ₂ η₁ h₁ hX hY hΔ
  -- ⑩ β 层的共轭恒等式
  have hβconj : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c
        * ((β.map (algebraMap (Spr F r n) (SprField F r n))).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (β.map (algebraMap (Spr F r n) (SprField F r n))).map η₂ := by
    rw [← h₂' (β.map (algebraMap (Spr F r n) (SprField F r n))), ← hβval, h₁]
  -- ⑪ `s • α = 像` ⟹ 每个 `η` 下 `α` 与 `β` 的像差一个纯量
  have hsmul : ∀ (η : SprField F r n →ₐ[F] T),
      (β.map (algebraMap (Spr F r n) (SprField F r n))).map η
        = η (algebraMap (Spr F r n) (SprField F r n) s) • (α.map η) := by
    intro η
    rw [← hβeq, ← sprAlgebraMap_smul_eq (F := F) (r := r) (n := n) (s := s) α]
    exact matrix_map_smul η.toRingHom (algebraMap (Spr F r n) (SprField F r n) s) α
  -- ⑫ 标量穿过共轭
  have hconj_smul : ∀ (X : Matrix (Fin n) (Fin n) T) (u : T),
      u • (sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * X
            * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹)
        = sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * (u • X)
            * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹ := by
    intro X u
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  -- ⑬ 标量是单位
  obtain ⟨w, hw⟩ : ∃ w : Tˣ, (↑w : T) = η₁ (algebraMap (Spr F r n) (SprField F r n) s) := by
    have h0 : algebraMap (Spr F r n) (SprField F r n) s ≠ 0 := by
      intro hc
      exact hsne (IsFractionRing.injective (Spr F r n) (SprField F r n) (by simpa using hc))
    exact (isUnit_iff_ne_zero.mpr h0).map η₁.toRingHom
  have hw1 : (↑(w⁻¹) * η₁ (algebraMap (Spr F r n) (SprField F r n) s) : T) = 1 := by
    rw [← hw, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- ⑭ `α` 层的共轭恒等式
  have hkey : (↑w : T) • (sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * (α.map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹)
      = (↑w : T) • (α.map η₂) := by
    rw [show (↑w : T) = η₁ (algebraMap (Spr F r n) (SprField F r n) s) from hw]
    rw [hconj_smul, ← hsmul η₁, hβconj, hscal, hsmul η₂]
  have hcancel : ∀ (X Y : Matrix (Fin n) (Fin n) T),
      ((↑w : T) • X) = ((↑w : T) • Y) → X = Y := by
    intro X Y h
    calc X = (↑(w⁻¹) : T) • ((↑w : T) • X) := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = (↑(w⁻¹) : T) • ((↑w : T) • Y) := by rw [h]
      _ = Y := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hαconj : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * (α.map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = α.map η₂ :=
    hcancel _ _ hkey
  -- ⑮ 收口：`θ₂ α = α.map η₁`
  have hUval : ((sprPmatUnit T σ * sprDiagMatRUnit (T := T) c : (Matrix (Fin n) (Fin n) T)ˣ) :
      Matrix (Fin n) (Fin n) T)
      = sprPmat (n := n) T σ * sprDiagMatR (n := n) T c := by
    rw [Units.val_mul]
    rfl
  have hUinv : ((((sprPmatUnit T σ * sprDiagMatRUnit (T := T) c))⁻¹ :
        (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
      = sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹ := by
    rw [_root_.mul_inv_rev, Units.val_mul]
    rfl
  rw [h₁ α]
  refine (sprConj_unit_cancel (u := sprPmatUnit T σ * sprDiagMatRUnit (T := T) c) ?_).symm
  rw [hUval, hUinv]
  simp only [← Matrix.mul_assoc]
  rw [hαconj, h₂' α]

#print axioms sprLem1424LocalK'

end Lem1424LocalKPrime

/-! ## §19 ★★★★★★ **第六格（收口）：`lem:14.24` 的 `K'`-世界一般形态**

三件逐字换域（`S'`-世界 §133–§137 → `K'`-世界），把 §18 的**局部**形态推到**任意 `T`**：

| 件 | 内容 |
|---|---|
| `sprFieldDiscrUnit_conj` | 内蕴判别式条件沿单位共轭传输 |
| ★★★★★ `sprLem1424LocalNoNormK'` | **局部、未归一**（`θ₁` 不必是 `M_n(η₁)`） |
| `sprFieldDiscrUnit_mapMatrix` | 内蕴判别式条件沿 `F`-代数同态传输 |
| ★★★★★ `sprLem1424_of_discrUnitK'` | **任意 `T`，判别式内蕴可逆**（逐素局部化） |
| `sprFieldDiscrNonZeroDiv` | 判别式**非零因子**条件（源文原文口径） |
| ★★★★★★★ **`sprLem1424_generalK'`** | **`lem:14.24` 的 `K'`-世界一般形态** ＝ `(乙)` 六格收口 |

**⟹ `(乙)` 完成**：`lem:14.24` 在 `K'`-世界的**原文口径**（`T` 任意、判别式非零因子）
现在是定理。第六格全部是**逐字换域**（工具 `sprAway_injective`／`exists_isPrime_algebraMap_ne_zero`／
`sprScalar_mapGen`／`sprScalar_conj` 均世界无关），与 S'-世界 §133–§137 一一对应。 -/

section Lem1424GeneralKPrime

variable {F : Type} [Field F] {r n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- 内蕴判别式条件沿单位共轭传输（`K'`-世界）。 -/
theorem sprFieldDiscrUnit_conj (θ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (u : (Matrix (Fin n) (Fin n) T)ˣ) {Δ : SprField F r n}
    (h : sprFieldDiscrUnit F (r := r) (n := n) θ Δ) :
    sprFieldDiscrUnit F (r := r) (n := n)
      ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ) Δ := by
  obtain ⟨x, hx, hxu⟩ := h
  refine ⟨x, ?_, hxu⟩
  show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      * θ (Matrix.scalar (Fin n) Δ)
      * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) = Matrix.scalar (Fin n) x
  rw [hx]
  exact sprScalar_conj u⁻¹ x

#print axioms sprFieldDiscrUnit_conj

/-- ★★★★★★ **`lem:14.24` 的 `K'`-世界局部形态（未归一版）**：不需要 `θ₁ = M_n(η₁)`。 -/
theorem sprLem1424LocalNoNormK' [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (SprField F r n))
    (hα : sprMatNFixed F r n α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k))
    (hΔ : sprFieldDiscrUnit F (r := r) (n := n) θ₁
      (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F))) :
    θ₁ α = θ₂ α := by
  obtain ⟨u, η₁, h₁⟩ := sprFieldExistsEta1_local (F := F) (r := r) (n := n) (T := T) θ₁
  have hX' : ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) (sprFieldXdiag F r n)
      = ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂) (sprFieldXdiag F r n) := by
    show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * θ₁ (sprFieldXdiag F r n)
        * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
      = (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * θ₂ (sprFieldXdiag F r n)
        * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
    rw [hX]
  have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
      ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) (sprFieldYmat F r n k)
        = ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂) (sprFieldYmat F r n k) := by
    intro k
    show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * θ₁ (sprFieldYmat F r n k)
        * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
      = (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * θ₂ (sprFieldYmat F r n k)
        * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
    rw [hY k]
  have hΔ' : IsUnit (η₁ (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F))) :=
    sprFieldIsUnit_discr_of_discrUnit (F := F) (r := r) (n := n) (T := T)
      ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) η₁ (fun β => h₁ β)
      (sprFieldDiscrUnit_conj (F := F) (r := r) (n := n) θ₁ u hΔ)
  have hres := sprLem1424LocalK' (F := F) (r := r) (n := n) (T := T) α hα
    ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁)
    ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂) η₁ (fun β => h₁ β) hX' hY' hΔ'
  exact sprConj_unit_cancel (u := u⁻¹) hres

#print axioms sprLem1424LocalNoNormK'

/-- 内蕴判别式条件沿 `F`-代数同态传输（`K'`-世界）。 -/
theorem sprFieldDiscrUnit_mapMatrix {S : Type} [CommRing S] [Algebra F S]
    (φ : T →ₐ[F] S) (θ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    {Δ : SprField F r n}
    (h : sprFieldDiscrUnit F (r := r) (n := n) θ Δ) :
    sprFieldDiscrUnit F (r := r) (n := n) (φ.mapMatrix.comp θ) Δ := by
  obtain ⟨x, hx, hxu⟩ := h
  refine ⟨φ x, ?_, hxu.map φ⟩
  show φ.mapMatrix (θ (Matrix.scalar (Fin n) Δ)) = Matrix.scalar (Fin n) (φ x)
  rw [hx]
  exact sprScalar_mapGen (F := F) (n := n) φ x

#print axioms sprFieldDiscrUnit_mapMatrix

/-- ★★★★★ **`lem:14.24` 的 `K'`-世界（任意 `T`，判别式内蕴可逆形态）**：逐素局部化。 -/
theorem sprLem1424_of_discrUnitK' [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (SprField F r n))
    (hα : sprMatNFixed F r n α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k))
    (hΔ : sprFieldDiscrUnit F (r := r) (n := n) θ₁
      (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F))) :
    θ₁ α = θ₂ α := by
  classical
  by_cases hT : Nontrivial T
  · haveI : Nontrivial T := hT
    by_contra hne
    have hex : ∃ i j, (θ₁ α - θ₂ α) i j ≠ 0 := by
      by_contra h
      apply hne
      ext i j
      by_contra h2
      exact h ⟨i, j, sub_ne_zero.mpr h2⟩
    obtain ⟨i, j, hij⟩ := hex
    obtain ⟨m, hpm, hmap⟩ := exists_isPrime_algebraMap_ne_zero T hij
    haveI : m.IsPrime := hpm
    set φ : T →ₐ[F] Localization.AtPrime m := IsScalarTower.toAlgHom F T (Localization.AtPrime m) with hφ
    have hX' : ((φ.mapMatrix).comp θ₁) (sprFieldXdiag F r n)
        = ((φ.mapMatrix).comp θ₂) (sprFieldXdiag F r n) := by
      show φ.mapMatrix (θ₁ (sprFieldXdiag F r n)) = φ.mapMatrix (θ₂ (sprFieldXdiag F r n))
      rw [hX]
    have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
        ((φ.mapMatrix).comp θ₁) (sprFieldYmat F r n k)
          = ((φ.mapMatrix).comp θ₂) (sprFieldYmat F r n k) := by
      intro k
      show φ.mapMatrix (θ₁ (sprFieldYmat F r n k)) = φ.mapMatrix (θ₂ (sprFieldYmat F r n k))
      rw [hY k]
    have hloc := sprLem1424LocalNoNormK' (F := F) (r := r) (n := n)
      (T := Localization.AtPrime m) α hα
      ((φ.mapMatrix).comp θ₁) ((φ.mapMatrix).comp θ₂) hX' hY'
      (sprFieldDiscrUnit_mapMatrix (F := F) (r := r) (n := n) φ θ₁ hΔ)
    have hentry : φ ((θ₁ α) i j) = φ ((θ₂ α) i j) := by
      have hentry' := congrFun (congrFun hloc i) j
      simpa [AlgHom.mapMatrix_apply] using hentry'
    have hzero : φ ((θ₁ α - θ₂ α) i j) = 0 := by
      show φ ((θ₁ α) i j - (θ₂ α) i j) = 0
      rw [map_sub, hentry, sub_self]
    have hφapp : ⇑φ = algebraMap T (Localization.AtPrime m) := rfl
    rw [hφapp] at hzero
    exact hmap hzero
  · haveI : Subsingleton T := not_nontrivial_iff_subsingleton.mp hT
    exact Subsingleton.elim _ _

#print axioms sprLem1424_of_discrUnitK'

/-- `K'`-世界的判别式**非零因子**条件（源文 `lem:14.24` 的原文口径）。 -/
def sprFieldDiscrNonZeroDiv
    (θ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (Δ : SprField F r n) : Prop :=
  ∃ x : T, θ (Matrix.scalar (Fin n) Δ) = Matrix.scalar (Fin n) x ∧ ∀ y : T, x * y = 0 → y = 0

#print axioms sprFieldDiscrNonZeroDiv

/-- ★★★★★★★ **`lem:14.24` 的 `K'`-世界一般形态**（判别式为非零因子，`T` 任意）。
这是 `(乙)` 第六格的收口件。 -/
theorem sprLem1424_generalK' [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (SprField F r n))
    (hα : sprMatNFixed F r n α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (SprField F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (sprFieldXdiag F r n) = θ₂ (sprFieldXdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (sprFieldYmat F r n k) = θ₂ (sprFieldYmat F r n k))
    (hΔ : sprFieldDiscrNonZeroDiv (r := r) (n := n) θ₁
      (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F))) :
    θ₁ α = θ₂ α := by
  classical
  by_cases hT : Nontrivial T
  · haveI : Nontrivial T := hT
    obtain ⟨x, hx, hnd⟩ := hΔ
    set φ : T →ₐ[F] Localization.Away x := IsScalarTower.toAlgHom F T (Localization.Away x) with hφ
    have hΔ' : sprFieldDiscrUnit F (r := r) (n := n) ((φ.mapMatrix).comp θ₁)
        (algebraMap (Spr F r n) (SprField F r n) (sprDiscr F)) := by
      refine ⟨φ x, ?_, ?_⟩
      · show φ.mapMatrix (θ₁ (Matrix.scalar (Fin n) (algebraMap (Spr F r n) (SprField F r n)
            (sprDiscr F)))) = Matrix.scalar (Fin n) (φ x)
        rw [hx]
        exact sprScalar_mapGen (F := F) (n := n) φ x
      · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x
    have hX' : ((φ.mapMatrix).comp θ₁) (sprFieldXdiag F r n)
        = ((φ.mapMatrix).comp θ₂) (sprFieldXdiag F r n) := by
      show φ.mapMatrix (θ₁ (sprFieldXdiag F r n)) = φ.mapMatrix (θ₂ (sprFieldXdiag F r n))
      rw [hX]
    have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
        ((φ.mapMatrix).comp θ₁) (sprFieldYmat F r n k)
          = ((φ.mapMatrix).comp θ₂) (sprFieldYmat F r n k) := by
      intro k
      show φ.mapMatrix (θ₁ (sprFieldYmat F r n k)) = φ.mapMatrix (θ₂ (sprFieldYmat F r n k))
      rw [hY k]
    have hloc : ((φ.mapMatrix).comp θ₁) α = ((φ.mapMatrix).comp θ₂) α :=
      sprLem1424_of_discrUnitK' (F := F) (r := r) (n := n) α hα
        ((φ.mapMatrix).comp θ₁) ((φ.mapMatrix).comp θ₂) hX' hY' hΔ'
    have hinj : Function.Injective (algebraMap T (Localization.Away x)) :=
      sprAway_injective hnd (Localization.Away x)
    ext i j
    apply hinj
    have hφapp : ⇑φ = algebraMap T (Localization.Away x) := rfl
    have hentry' := congrFun (congrFun hloc i) j
    simpa [AlgHom.mapMatrix_apply, hφapp] using hentry'
  · haveI : Subsingleton T := not_nontrivial_iff_subsingleton.mp hT
    exact Subsingleton.elim _ _

#print axioms sprLem1424_generalK'

end Lem1424GeneralKPrime

end Procesi
