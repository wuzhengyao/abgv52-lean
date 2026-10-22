/-
  Procesi —— **S4 `prop:14.14` 的载体层：通用矩阵 `Y` 与 `T = F[y_{ij}](1/\\det Y)`**

  **原文（逐字）**：`raw/Saltman1999ch14.tex:286–297` `prop:14.14`：
  > Let `α ∈ M_n(S)^{PGL_n(F)}`. Then with `Y` a generic matrix as above, `ψ_Y(α) = α`.
  > If `S'' ⊃ S` is an extension and `A ∈ M_n(S'')` is invertible, then `ψ_A(α) = α`.

  其中（同页定义）：
  > let `T` be the localized polynomial ring `F[y_{ij} | 1 ≤ i,j ≤ n](1/y)` where `y` is the
  > determinant of the generic matrix `Y = (y_{ij})` which is thus an invertible matrix in `M_n(T)`.

  **本件的射程（勿夸大）**：只给 `prop:14.14` 所需的**载体**——通用矩阵 `genMat`、通用行列式
  `genDet`、局部化 `Tloc = F[y](1/\det)`、以及 `Y` 在 `M_n(Tloc)` 中作为**可逆元** `Yunit`。
  **未做**：`φ_Y`／`ψ_Y` 的定义与 `prop:14.14` 本体（下一轮），以及 `F` 无限时的特殊化
  （`MvPolynomial.aeval` 的单射性 ＋ 局部化代表的选取）。

  **为何先做这一层**：`prop:14.14` 的证明是**特殊化**论证——反设 `ψ_Y(α) - α ≠ 0`，取其一个非零
  系数 `t ∈ T`，由 `F` 无限取 `F`-代数映射 `η : T → F` 使 `η(t) ≠ 0`，令 `A = M_n(η)(Y)`，
  则 `η(ψ_Y(α) - α) = ψ_A(α) - α ≠ 0`，与 `α` 的不变性矛盾。**前提**是 `Y` 在 `M_n(T)` 中可逆
  （否则 `ψ_Y` 无定义）以及 `M_n(η)(Y)` 可逆（否则 `ψ_A` 无定义）——本件给前者。
-/
import Procesi.GenericMatrix
import Procesi.MatrixUnits
import Procesi.PGL
import Procesi.KAction
import Procesi.FixedRatio
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable

open Matrix MvPolynomial

namespace Procesi

variable (F : Type) [Field F]

/-! ## §1 通用矩阵与通用行列式 -/

/-- **通用矩阵** `genMat F n`：`n×n` 矩阵，其 `(i,j)` 元是不定元 `y_{ij}`。
**对应**：Saltman `prop:14.14` 的 `Y = (y_{ij})`；`raw/Saltman1999ch14.tex:283`。 -/
noncomputable def genMat (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) F) :=
  Matrix.of (fun i j => MvPolynomial.X (i, j))

/-- **通用行列式** `y = det Y`。**对应**：Saltman 的 `1/y` 中的 `y`。 -/
noncomputable def genDet (n : ℕ) : MvPolynomial (Fin n × Fin n) F := (genMat F n).det

/-- ★★ **`genDet` 在恒等矩阵处的取值是 1**：`aeval (fun (i,j) => if i = j then 1 else 0) (genDet) = 1`
（`AlgHom.map_det` ＋ `Matrix.det_one`）。**用途**：证 `genDet ≠ 0`（下一行）。 -/
lemma genDet_aeval_identity (n : ℕ) :
    MvPolynomial.aeval (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0)
      (genDet F n) = 1 := by
  have h := AlgHom.map_det
    (MvPolynomial.aeval (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0)) (genMat F n)
  rw [genDet, h]
  have hm : (MvPolynomial.aeval
      (fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0)).mapMatrix (genMat F n)
      = (1 : Matrix (Fin n) (Fin n) F) := by
    ext i j
    simp [genMat, Matrix.one_apply]
  rw [hm, Matrix.det_one]

#print axioms genDet_aeval_identity

/-- ★★ **`genDet ≠ 0`**：由 `genDet_aeval_identity`（环同态把 `0` 送到 `0`，而 `1 ≠ 0`）。
**用途**：`Tloc = F[y](1/\det)` 的局部化映射**单射**（`prop:14.14` 的"取非零系数 `t ∈ T`"要用）。 -/
lemma genDet_ne_zero (n : ℕ) : genDet F n ≠ 0 := by
  intro h
  have h1 := genDet_aeval_identity F n
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

#print axioms genDet_ne_zero

/-! ## §2 局部化 `T = F[y](1/\det)` 与 `Y` 的可逆性 -/

/-- **`T = F[y_{ij}](1/\det Y)`**：Saltman 的 `T`（`raw/Saltman1999ch14.tex:283`）。
定义为`MvPolynomial (Fin n × Fin n) F` 在 `det` 的幂处的局部化。 -/
abbrev Tloc (n : ℕ) : Type := Localization.Away (genDet F n)

/-- ★ **`Matrix.map` 与 `det` 交换**（`n×n` 方阵；`RingHom.map_det` 的 `Matrix.map` 形式）。
**库内缺件**：本 pin 无 `Matrix.det_map`。 -/
lemma det_map_apply {A B : Type*} [CommRing A] [CommRing B] {m : Type*} [Fintype m]
    [DecidableEq m] (f : A →+* B) (M : Matrix m m A) : (M.map ⇑f).det = f M.det := by
  have h : M.map ⇑f = f.mapMatrix M := rfl
  rw [h, ← RingHom.map_det]

#print axioms det_map_apply

/-- **`Y` 在 `M_n(T)` 中**（把 `genMat` 的系数沿 `F[y] → T` 搬运）。 -/
noncomputable def Ymat (n : ℕ) : Matrix (Fin n) (Fin n) (Tloc F n) :=
  (genMat F n).map (algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n))

/-- ★★ **`det Y = y` 在 `T` 中**：`(Ymat).det = algebraMap y`（`det_map_apply`）。 -/
lemma Ymat_det (n : ℕ) :
    (Ymat F n).det = algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n) (genDet F n) := by
  rw [show Ymat F n = (genMat F n).map
      (algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n)) from rfl, det_map_apply]
  rfl

#print axioms Ymat_det

/-- ★★★ **`Y` 在 `T` 上的行列式是单位**（原文 "which is thus an invertible matrix in `M_n(T)`"）：
`IsLocalization.Away.algebraMap_isUnit` 给 `algebraMap y` 是单位，再经 `Ymat_det` 搬过来。 -/
lemma Ymat_det_isUnit (n : ℕ) : IsUnit (Ymat F n).det := by
  rw [Ymat_det]
  exact IsLocalization.Away.algebraMap_isUnit (S := Tloc F n) (genDet F n)

#print axioms Ymat_det_isUnit

/-- ★★★ **`Y` 作为 `M_n(T)` 的幺正元**（`Matrix.GeneralLinearGroup.mk''`，只需 `IsUnit det`，
不需 `T` 是域）。**用途**：`ψ_Y(α) = Y·M_n(φ_Y)(α)·Y⁻¹` 中的 `Y⁻¹` 由此给出。 -/
noncomputable def Yunit (n : ℕ) : (Matrix (Fin n) (Fin n) (Tloc F n))ˣ :=
  Matrix.GeneralLinearGroup.mk'' (Ymat F n) (Ymat_det_isUnit F n)

/-- `Yunit` 的底层矩阵就是 `Ymat`。 -/
lemma Yunit_val (n : ℕ) : (↑(Yunit F n) : Matrix (Fin n) (Fin n) (Tloc F n)) = Ymat F n := by
  simp [Yunit]

#print axioms Yunit_val

/-! ## §3 `Y⁻¹`、系数扩张、以及通用元的两个作用 `φ_Y`／`ψ_Y`

`prop:14.14` 的两件作用（`raw/Saltman1999ch14.tex:283–288`）：
> define `φ_A(x_{ijk})` to be the `i,j` entry of the matrix `A⁻¹ X_k A` … define
> `ψ_A(B) = A (M_n(φ_A)(B)) A⁻¹ ∈ M_n(S'')`.

本节的 `φ_Y`／`ψ_Y` 就是 `A := Y` 的情形，取值域为 `S_T = T[x_{ijk}]`。 -/

/-- `Y⁻¹`（在 `M_n(T)` 中）。由 `Yunit⁻¹` 的底层矩阵给出。 -/
noncomputable def Yinv (n : ℕ) : Matrix (Fin n) (Fin n) (Tloc F n) := ↑((Yunit F n)⁻¹)

/-- ★ **`Y * Y⁻¹ = 1`**（左逆）。 -/
lemma Ymat_mul_Yinv (n : ℕ) : Ymat F n * Yinv F n = 1 := by
  rw [Yinv, ← Yunit_val]
  simp

#print axioms Ymat_mul_Yinv

/-- ★ **`Y⁻¹ * Y = 1`**（右逆）。 -/
lemma Yinv_mul_Ymat (n : ℕ) : Yinv F n * Ymat F n = 1 := by
  rw [Yinv, ← Yunit_val]
  simp

#print axioms Yinv_mul_Ymat

/-- ★ **方阵的 `Matrix.map` 保乘法**（`MvPolynomial.C` 等环同态沿矩阵逐元作用时要用）。 -/
lemma map_mul_apply {α β : Type*} [CommRing α] [CommRing β] {m : Type*} [Fintype m]
    (f : α →+* β) (A B : Matrix m m α) : (A * B).map ⇑f = A.map ⇑f * B.map ⇑f := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

#print axioms map_mul_apply

/-- **第 `k` 个通用矩阵**（系数环 `R` 泛化；`R = F` 时即 `genericMatrix`，`R = T` 时是 `S_T` 里的
同名矩阵）。**用途**：`φ_Y`／`ψ_Y` 的表达式两边都以它为基本块。 -/
noncomputable def genMatK (R : Type) [CommRing R] (r n : ℕ) (k : Fin r) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) R) :=
  Matrix.of (fun i j => MvPolynomial.X (k, i, j))

/-- ★★★ **`φ_Y : S → S_T`**：原文"`φ_A(x_{ijk})` 为 `A⁻¹ X_k A` 的 `(i,j)` 元"在 `A = Y` 时的实现，
即 `x_{ijk} ↦ ∑_{a,b} (Y⁻¹)_{ia} · x_{kab} · Y_{bj}`（`MvPolynomial.aeval`）。

**为何是 `S_T = T[x_{ijk}]` 而不是 `S ⊗_F T`**：两者是同一个 `F`-代数（`MvPolynomial σ` 的系数环
换成 `T`），用前者省掉张量积的记法负担。 -/
noncomputable def phiY (r n : ℕ) :
    MvPolynomial (Fin r × Fin n × Fin n) F →ₐ[F]
      MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n) :=
  MvPolynomial.aeval (fun p : Fin r × Fin n × Fin n =>
    ∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.C ((Yinv F n) p.2.1 a) * MvPolynomial.X (p.1, a, b)
        * MvPolynomial.C ((Ymat F n) b p.2.2))

/-- ★★ **`φ_Y` 在变量上的值**（`aeval` 的定义展开）：`φ_Y(x_{ijk}) = ∑_{a,b} (Y⁻¹)_{ia} x_{kab} Y_{bj}`。 -/
lemma phiY_X (r n : ℕ) (k : Fin r) (i j : Fin n) :
    phiY F r n (MvPolynomial.X (k, i, j))
      = ∑ a : Fin n, ∑ b : Fin n,
          MvPolynomial.C ((Yinv F n) i a) * MvPolynomial.X (k, a, b)
            * MvPolynomial.C ((Ymat F n) b j) := by
  simp [phiY]

#print axioms phiY_X

/-- ★★★ **`ψ_Y : M_n(S) → M_n(S_T)`**：`ψ_Y(B) = Y · M_n(φ_Y)(B) · Y⁻¹`
（原文 `ψ_A(B) = A(M_n(φ_A)(B))A⁻¹` 在 `A = Y` 时）。 -/
noncomputable def psiY (r n : ℕ)
    (α : Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) F)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n)) :=
  (Ymat F n).map MvPolynomial.C * α.map (phiY F r n) * (Yinv F n).map MvPolynomial.C

/-- ★★ **系数扩张后 `Y` 与 `Y⁻¹` 仍互逆**（左）：把 `Y * Y⁻¹ = 1` 沿 `MvPolynomial.C` 搬运。
**用途**：`ψ_Y(X_k) = X_k`（下一轮）与特殊化恒等式。 -/
lemma Ymat_map_C_mul_Yinv_map_C {r n : ℕ} :
    (Ymat F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n))
      * (Yinv F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n)) = 1 := by
  rw [← map_mul_apply, Ymat_mul_Yinv]
  ext i j
  simp [Matrix.one_apply]

#print axioms Ymat_map_C_mul_Yinv_map_C

/-- ★★ **系数扩张后 `Y` 与 `Y⁻¹` 仍互逆**（右）。 -/
lemma Yinv_map_C_mul_Ymat_map_C {r n : ℕ} :
    (Yinv F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n))
      * (Ymat F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n)) = 1 := by
  rw [← map_mul_apply, Yinv_mul_Ymat]
  ext i j
  simp [Matrix.one_apply]

#print axioms Yinv_map_C_mul_Ymat_map_C

/-- ★★★ **`ψ_Y` 在生成元上的值**：`ψ_Y(X_k) = X_k`（原文 `ψ_B(X_k) = B(B⁻¹X_kB)B⁻¹ = X_k`）。

**证明**：`M_n(φ_Y)(X_k) = Y⁻¹ X_k Y`（`phiY_X` 的矩阵形式），故
`ψ_Y(X_k) = Y·(Y⁻¹X_kY)·Y⁻¹ = (Y·Y⁻¹)·X_k·(Y·Y⁻¹) = X_k`——最后一步用系数扩张后的
`Y·Y⁻¹ = 1`（`Ymat_map_C_mul_Yinv_map_C`）与 `noncomm_ring` 的结合律重排。 -/
lemma map_phiY_genMatK (r n : ℕ) (k : Fin r) :
    (genMatK F r n k).map (phiY F r n)
      = (Yinv F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n))
        * genMatK (Tloc F n) r n k
        * (Ymat F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n)) := by
  funext i j
  rw [show (genMatK F r n k).map (phiY F r n) i j = phiY F r n (MvPolynomial.X (k, i, j)) from rfl,
    phiY_X]
  simp only [Matrix.mul_apply, Matrix.map_apply, genMatK, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

#print axioms map_phiY_genMatK

/-- ★★★ **`ψ_Y(X_k) = X_k`**：`Y` 与 `Y⁻¹` 在系数扩张后互逆，故共轭消去。
**用途**：`prop:14.14` 的特殊化（`η(ψ_Y(α) − α) = ψ_A(α) − α`）要对**生成元**验证
`η ∘ φ_Y = φ_A` 与 `M_n(η)(Y) = A`，本引理保证 `ψ` 的定义在生成元上与原文一致。 -/
lemma psiY_genMatK (r n : ℕ) (k : Fin r) :
    psiY F r n (genMatK F r n k) = genMatK (Tloc F n) r n k := by
  rw [psiY, map_phiY_genMatK]
  have h : (Ymat F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n))
      * (Yinv F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n)) = 1 :=
    Ymat_map_C_mul_Yinv_map_C (F := F) (n := n) (r := r)
  rw [show (Ymat F n).map MvPolynomial.C
        * ((Yinv F n).map MvPolynomial.C * genMatK (Tloc F n) r n k
            * (Ymat F n).map MvPolynomial.C)
        * (Yinv F n).map MvPolynomial.C
      = ((Ymat F n).map MvPolynomial.C * (Yinv F n).map MvPolynomial.C)
        * genMatK (Tloc F n) r n k
        * ((Ymat F n).map MvPolynomial.C * (Yinv F n).map MvPolynomial.C) from by
    noncomm_ring]
  rw [h, one_mul, mul_one]

#print axioms psiY_genMatK

/-! ## §5 特殊化：`F`-点 `η : T →ₐ[F] F` 把 `Y` 送到一个**可逆**矩阵

`prop:14.14` 的证明要取 `F`-代数映射 `η : T → F` 并令 `A = M_n(η)(Y)`。原文断言
"`A` is invertible"——本节给这一句：`det A = η(det Y)`，而 `det Y` 在 `T` 中是**单位**，
环同态把单位送到单位，故 `det A ≠ 0`；再给 `A⁻¹ = M_n(η)(Y⁻¹)`。 -/

/-- ★ **`det (M_n(η)(Y)) = η(det Y)`**（`AlgHom.map_det`）。 -/
lemma Ymat_map_det (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    ((Ymat F n).map η).det = η ((Ymat F n).det) := (AlgHom.map_det η (Ymat F n)).symm

#print axioms Ymat_map_det

/-- ★★★ **特殊化后的 `A = M_n(η)(Y)` 可逆**：`det A = η(det Y)`，`det Y` 是 `T` 的单位，
单位沿环同态仍是单位，故 `det A` 是 `F` 的单位，特别 `≠ 0`。
**用途**：`prop:14.14` 中 `ψ_A` 的定义前提。 -/
lemma Ymat_map_det_ne_zero (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    ((Ymat F n).map η).det ≠ 0 := by
  rw [Ymat_map_det]
  exact (Ymat_det_isUnit F n).map η |>.ne_zero

#print axioms Ymat_map_det_ne_zero

/-- ★★ **`M_n(η)(Y⁻¹) * M_n(η)(Y) = 1`**：`Y⁻¹ * Y = 1` 沿 `η` 搬运（`map_mul_apply`）。 -/
lemma Yinv_map_mul_Ymat_map (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    (Yinv F n).map η * (Ymat F n).map η = 1 := by
  have h : (Yinv F n).map (⇑η) * (Ymat F n).map (⇑η)
      = (Yinv F n * Ymat F n).map (⇑η) :=
    (map_mul_apply (η.toRingHom) (Yinv F n) (Ymat F n)).symm
  rw [h, Yinv_mul_Ymat]
  funext i j
  simp [Matrix.one_apply]

#print axioms Yinv_map_mul_Ymat_map

/-- ★★ **`M_n(η)(Y) * M_n(η)(Y⁻¹) = 1`**（另一侧）。 -/
lemma Ymat_map_mul_Yinv_map (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    (Ymat F n).map η * (Yinv F n).map η = 1 := by
  have h : (Ymat F n).map (⇑η) * (Yinv F n).map (⇑η)
      = (Ymat F n * Yinv F n).map (⇑η) :=
    (map_mul_apply (η.toRingHom) (Ymat F n) (Yinv F n)).symm
  rw [h, Ymat_mul_Yinv]
  funext i j
  simp [Matrix.one_apply]

#print axioms Ymat_map_mul_Yinv_map

/-! ## §6 射程：`[Infinite F]` 与 `[CharZero F]` 的关系 ＋ 特殊化点的存在性基件

`prop:14.14` 的证明要求"`F` 无限"（原文：`Since F is infinite, there is an F algebra map
η : T → F such that η(t) ≠ 0`）。本节登记射程：论文既有的假设是 `[CharZero F]`，
而对**域**有 `CharZero ⟹ Infinite`（`ℚ ↪ F`），故 `prop:14.14` **不扩大射程**。
另给两件后续要用的基件：局部化映射单射、以及无穷域上多项式函数分离非零元。 -/

/-- ★★★ **`[CharZero F]`（域）蕴含 `Infinite F`**（`ℚ ↪ F`，`Rat.cast_injective`）。
**用途（射程登记）**：`prop:14.14` 需 `[Infinite F]`，它由论文既有的 `[CharZero F]` **自动**给出，
故 S4 **不引入新的具名假设、不扩大射程**。 -/
lemma infinite_of_charZero (F : Type) [Field F] [CharZero F] : Infinite F :=
  Infinite.of_injective (fun q : ℚ => (q : F)) Rat.cast_injective

#print axioms infinite_of_charZero

/-- ★★ **无穷域上多项式分离非零元**：`p ≠ 0` ⟹ 存在赋值 `x` 使 `eval x p ≠ 0`
（`MvPolynomial.funext` 的逆否）。**用途**：特殊化点 `η` 的存在性。 -/
lemma exists_eval_ne_zero [Infinite F] {σ : Type*} {p : MvPolynomial σ F} (hp : p ≠ 0) :
    ∃ x : σ → F, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  refine hp (MvPolynomial.funext (fun x => ?_))
  rw [h x, map_zero]

#print axioms exists_eval_ne_zero

/-- ★★ **`T = F[y](1/det)` 是整环**（`det ≠ 0`，`IsLocalization.Away.isDomain`）。
**用途**：`t ≠ 0` 与 `p ≠ 0` 的互相推导（§7 的 `t ∈ T` 表示）。 -/
lemma Tloc_isDomain (n : ℕ) : IsDomain (Tloc F n) :=
  IsLocalization.Away.isDomain (S := Tloc F n) (genDet_ne_zero F n)

#print axioms Tloc_isDomain

/-- ★★ **局部化映射 `F[y] → T` 单射**（`IsLocalization.injective` ＋ `genDet ≠ 0`）。
**用途**：§7 中由 `algebraMap p = 0` 得 `p = 0`。 -/
lemma algebraMap_Tloc_injective (n : ℕ) : Function.Injective
    (algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (genDet_ne_zero F n))

#print axioms algebraMap_Tloc_injective

/-! ## §7 无穷性步：`T` 的任一非零元在某个 `F`-点非零

**原文（逐字）**：`raw/Saltman1999ch14.tex:292–293`（`prop:14.14` 的证明）：
> Let `t ∈ T` be a nonzero coefficient appearing in `s'`. Since `F` is infinite, there is an
> `F` algebra map `η : T → F` such that `η(t) ≠ 0`.

本节把这一句机检。路线（三步）：
① `IsLocalization.surj` 把 `t` 写成 `t · (s 的像) = p 的像`（`s` 是 `det` 的幂）；
② `t ≠ 0` ⟹ `p ≠ 0`（`T` 是整环、`s` 的像是单位）；
③ 由 `p ≠ 0` 得 `p · det ≠ 0`，`MvPolynomial.funext` 给点 `x` 使 `eval x (p·det) ≠ 0`，
   于是 `eval x p ≠ 0` 且 `eval x det ≠ 0`；把 `eval x` 沿 `IsLocalization.Away.liftAlgHom` 提升为
   `η : T →ₐ[F] F`，再由 `η t · g s = g p ≠ 0` 得 `η t ≠ 0`。 -/

/-- ★★ **`det` 的幂在 `T` 中的像是单位**。**用途**：§7 的 `t ≠ 0 ⟹ p ≠ 0`。 -/
lemma algebraMap_powers_isUnit {n : ℕ} {s : Submonoid.powers (genDet F n)} :
    IsUnit (algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n)
      (s : MvPolynomial (Fin n × Fin n) F)) := by
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff (s : MvPolynomial (Fin n × Fin n) F)
    (genDet F n)).mp s.2
  rw [← hm, map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Tloc F n) (genDet F n)).pow m

#print axioms algebraMap_powers_isUnit

/-- ★★ **`t ≠ 0` ⟹ 其分子 `p ≠ 0`**（在表示 `t · algebraMap s = algebraMap p` 下）：
`p = 0` 会给出 `t · (单位) = 0`，而 `T` 是整环、单位非零。 -/
lemma Tloc_num_ne_zero {n : ℕ} {t : Tloc F n} (ht : t ≠ 0)
    {p : MvPolynomial (Fin n × Fin n) F} {s : Submonoid.powers (genDet F n)}
    (h : t * algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n) (s : _) = algebraMap _ _ p) :
    p ≠ 0 := by
  haveI : IsDomain (Tloc F n) := Tloc_isDomain F n
  intro hp
  have h0 : t * algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n) (s : _) = 0 := by
    rw [h, hp, map_zero]
  exact ht ((mul_eq_zero.mp h0).resolve_right (algebraMap_powers_isUnit F).ne_zero)

#print axioms Tloc_num_ne_zero

/-- ★★★ **无穷性步（机检）**：`[Infinite F]`、`t ≠ 0` ⟹ 存在 `F`-代数映射 `η : T → F` 使 `η(t) ≠ 0`。

**证明**：见节首三步。`IsLocalization.Away.liftAlgHom` 提供提升，`hcoe` 是提升的
交换三角（`η ∘ algebraMap = g`）；末步用**乘法**而非除法：`η t · g s = g p ≠ 0` ⟹ `η t ≠ 0`。 -/
theorem exists_algHom_ne_zero [Infinite F] (n : ℕ) {t : Tloc F n} (ht : t ≠ 0) :
    ∃ η : Tloc F n →ₐ[F] F, η t ≠ 0 := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (genDet F n)) t
  have hp : p ≠ 0 := Tloc_num_ne_zero F ht hs
  have hq : p * genDet F n ≠ 0 := mul_ne_zero hp (genDet_ne_zero F n)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero F hq
  have hxp : MvPolynomial.eval x p ≠ 0 := fun h => hx (by rw [map_mul, h, zero_mul])
  have hxd : MvPolynomial.eval x (genDet F n) ≠ 0 := fun h => hx (by rw [map_mul, h, mul_zero])
  set g : MvPolynomial (Fin n × Fin n) F →ₐ[F] F :=
    { toRingHom := MvPolynomial.eval x
      commutes' := fun c => by simp } with hgdef
  have hgval : ∀ q, g q = MvPolynomial.eval x q := fun q => rfl
  have hgunit : IsUnit (g (genDet F n)) := by
    rw [hgval]; exact isUnit_iff_ne_zero.mpr hxd
  refine ⟨IsLocalization.Away.liftAlgHom (S := Tloc F n) (genDet F n) hgunit, ?_⟩
  have hcoe : ∀ q : MvPolynomial (Fin n × Fin n) F,
      (IsLocalization.Away.liftAlgHom (S := Tloc F n) (genDet F n) hgunit)
        ((algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n)) q) = g q := by
    intro q
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq (x := genDet F n) (g := g.toRingHom) hgunit q
  intro htz
  have hkey : (IsLocalization.Away.liftAlgHom (S := Tloc F n) (genDet F n) hgunit) t
      * g (s : MvPolynomial (Fin n × Fin n) F) = g p := by
    have h := congrArg (IsLocalization.Away.liftAlgHom (S := Tloc F n) (genDet F n) hgunit) hs
    rw [map_mul, hcoe (s : MvPolynomial (Fin n × Fin n) F), hcoe p] at h
    exact h
  rw [htz, zero_mul] at hkey
  exact hxp (by rw [← hgval p]; exact hkey.symm)

#print axioms exists_algHom_ne_zero

/-! ## §8 特殊化映射 `η' : S_T → S`（把 `T`-系数沿 `η` 压回 `F`）

**原文（逐字）**：`raw/Saltman1999ch14.tex:293–294`：
> Denote by `η'` the induced map `η' : S_T = T[x_{ijk}]_T → F[x_{ijk}]_T = S`.

实现 = `MvPolynomial.map η.toRingHom`（只压系数、不动变量）。本节给它的三条作用律：
`C a ↦ C (η a)`、`X m ↦ X m`、以及**在 `S` 的像上是恒等**（`η'(f 的像) = f`）。 -/

/-- **特殊化映射** `η' : T[x_{ijk}] → F[x_{ijk}]`（沿 `η` 压系数）。 -/
noncomputable def etaMap {σ : Type*} (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    MvPolynomial σ (Tloc F n) →+* MvPolynomial σ F :=
  MvPolynomial.map η.toRingHom

/-- ★ `η'` 在常系数上的作用：`η'(C a) = C (η a)`。 -/
lemma etaMap_C {σ : Type*} (n : ℕ) (η : Tloc F n →ₐ[F] F) (a : Tloc F n) :
    etaMap F n η (MvPolynomial.C a : MvPolynomial σ (Tloc F n))
      = (MvPolynomial.C (η a) : MvPolynomial σ F) :=
  MvPolynomial.map_C η.toRingHom a

#print axioms etaMap_C

/-- ★ `η'` 在变量上是恒等：`η'(x_m) = x_m`。 -/
lemma etaMap_X {σ : Type*} (n : ℕ) (η : Tloc F n →ₐ[F] F) (m : σ) :
    etaMap F n η (MvPolynomial.X m : MvPolynomial σ (Tloc F n))
      = (MvPolynomial.X m : MvPolynomial σ F) :=
  MvPolynomial.map_X η.toRingHom m

#print axioms etaMap_X

/-- ★ **`η ∘ algebraMap = id`**（`η` 是 `F`-代数映射；`AlgHom.commutes`）。 -/
lemma etaMap_id_comp (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    η.toRingHom.comp (algebraMap F (Tloc F n)) = RingHom.id F := by
  ext c
  simp [AlgHom.commutes]

#print axioms etaMap_id_comp

/-- ★★★ **`η'` 在 `S` 的自然像上是恒等**：`η'(map (algebraMap F T) f) = f`。
**用途**：`prop:14.14` 的反设里 `η'(ψ_Y(α) − α) = ψ_A(α) − α` 的右半边
（`α` 的系数在 `F` 里，`η'` 不动它们）。 -/
lemma etaMap_embed {σ : Type*} (n : ℕ) (η : Tloc F n →ₐ[F] F) (q : MvPolynomial σ F) :
    etaMap F n η (MvPolynomial.map (algebraMap F (Tloc F n)) q) = q := by
  rw [etaMap, MvPolynomial.map_map, etaMap_id_comp, MvPolynomial.map_id]

#print axioms etaMap_embed

/-! ## §9 生成元恒等式 `η' ∘ φ_Y = φ_A`（特殊化的核心交换律）

**原文（逐字）**：`raw/Saltman1999ch14.tex:295–296`（`prop:14.14` 证明中段）：
> Set `A = M_n(η)(Y)`. … Thus `η' ∘ φ_Y = φ_A`.

其中 `A := M_n(η)(Y) ∈ M_n(F)`，可逆（§5），对应本节的 `specA`。

本节把这条恒等式**在 `S` 的生成元上**机检（`MvPolynomial` 的 `F`-代数同态由变量值唯一确定）。 -/

/-- **`A := M_n(η)(Y)` 作为 `GL_n(F)` 的元**（可逆性由 `Ymat_map_det_ne_zero` 供给）。
**对应**：原文 `Set A = M_n(η)(Y)`。 -/
noncomputable def specA (n : ℕ) (η : Tloc F n →ₐ[F] F) : (Matrix (Fin n) (Fin n) F)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Ymat F n).map η) (Ymat_map_det_ne_zero F n η)

/-- ★ `specA` 的底层矩阵就是 `M_n(η)(Y)`。 -/
lemma specA_val (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    (↑(specA F n η) : Matrix (Fin n) (Fin n) F) = (Ymat F n).map η := by
  simp [specA]

#print axioms specA_val

/-- ★★ **`specA` 的逆是 `M_n(η)(Y⁻¹)`**：`Y⁻¹·Y = 1` 沿 `η` 搬运，再用逆的唯一性。
**用途**：生成元恒等式的 `Y⁻¹` 侧。 -/
lemma specA_inv_val (n : ℕ) (η : Tloc F n →ₐ[F] F) :
    (↑((specA F n η)⁻¹) : Matrix (Fin n) (Fin n) F) = (Yinv F n).map η := by
  have hY : (Yinv F n).map η * (↑(specA F n η) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [specA_val]; exact Yinv_map_mul_Ymat_map F n η
  have key : (Yinv F n).map η = (↑((specA F n η)⁻¹) : Matrix (Fin n) (Fin n) F) := by
    calc (Yinv F n).map η
        = (Yinv F n).map η * ((↑(specA F n η) : Matrix (Fin n) (Fin n) F)
            * ↑((specA F n η)⁻¹)) := by
          rw [show (↑(specA F n η) : Matrix (Fin n) (Fin n) F) * ↑((specA F n η)⁻¹) = 1 from by simp,
            mul_one]
      _ = ((Yinv F n).map η * ↑(specA F n η)) * ↑((specA F n η)⁻¹) := by rw [mul_assoc]
      _ = ↑((specA F n η)⁻¹) := by rw [hY, one_mul]
  exact key.symm

#print axioms specA_inv_val

/-- ★★★ **`η' ∘ φ_Y = φ_A`（在变量上）**：`η'(φ_Y(x_{ijk})) = φ_A(x_{ijk})`，
`A := M_n(η)(Y)`。**这是 `prop:14.14` 证明里 "Thus `η' ∘ φ_Y = φ_A`" 那句的机检形式**。

**证明**：左侧按 `phiY_X` 展开为 `∑_{a,b} C(η(Y⁻¹_{ia}))·x_{kab}·C(η(Y_{bj}))`；
右侧按 `phiA` 的定义（`aeval (phiGen A)`）`＋ phiA_X` 展开为
`(constMat A⁻¹ · X_k · constMat A)_{ij}`，再用 `specA_inv_val`／`specA_val`
把 `A` 的两个像换成 `η(Y⁻¹)`／`η(Y)`，两侧成为同一个双重和（`Finset.sum_comm` 调嵌套序）。 -/
theorem etaMap_phiY_X (r n : ℕ) (η : Tloc F n →ₐ[F] F) (k : Fin r) (i j : Fin n) :
    etaMap F (σ := Fin r × Fin n × Fin n) n η (phiY F r n (MvPolynomial.X (k, i, j)))
      = phiA F r n (specA F n η) (MvPolynomial.X (k, i, j)) := by
  have hL : etaMap F (σ := Fin r × Fin n × Fin n) n η (phiY F r n (MvPolynomial.X (k, i, j)))
      = ∑ a : Fin n, ∑ b : Fin n,
          (MvPolynomial.C (η ((Yinv F n) i a)) : S F r n)
            * MvPolynomial.X (k, a, b) * (MvPolynomial.C (η ((Ymat F n) b j)) : S F r n) := by
    rw [phiY_X]
    simp only [map_sum, map_mul, etaMap_C, etaMap_X]
  rw [hL]
  rw [show phiA F r n (specA F n η) (MvPolynomial.X (k, i, j))
      = phiGen F r n (specA F n η) ⟨k, i, j⟩ from MvPolynomial.aeval_X _ _]
  rw [phiGen]
  rw [specA_inv_val, specA_val]
  simp only [constMat, Matrix.mul_apply, Matrix.map_apply, genericMatrix, genericEntry,
    MvPolynomial.algebraMap_eq, Finset.sum_mul]
  rw [Finset.sum_comm]

#print axioms etaMap_phiY_X

/-! ## §10 `η'` 与 `ψ` 交换：`η'(ψ_Y(α)) = ψ_A(α)`

**原文（逐字）**：`raw/Saltman1999ch14.tex:296–297`（`prop:14.14` 证明末段）：
> Using these facts we have `0 ≠ M_n(η')(ψ_Y(α) − α) = ψ_A(α) − α`.

本节把其中**矩阵层**的等式 `M_n(η')(ψ_Y(α)) = ψ_A(α)`（`A = M_n(η)(Y)`）机检。 -/

/-- **`constMat` 与 `MvPolynomial.C` 的记法桥**：`constMat M = M.map (fun x => C x)`。 -/
lemma constMat_eq_C_map (r n : ℕ) (M : Matrix (Fin n) (Fin n) F) :
    constMat F r n M
      = M.map (fun x => (MvPolynomial.C x : MvPolynomial (Fin r × Fin n × Fin n) F)) := by
  ext i j
  simp [constMat]

#print axioms constMat_eq_C_map

/-- ★★★ **`η' ∘ φ_Y = φ_A` 作为环同态**（不只是变量上）：由 `etaMap_phiY_X` ＋
`MvPolynomial.ringHom_ext`（`F`-代数同态由 `C` 与 `X` 上的值唯一确定）升到同态层。 -/
lemma etaMap_comp_phiY (r n : ℕ) (η : Tloc F n →ₐ[F] F) :
    (etaMap F (σ := Fin r × Fin n × Fin n) n η).comp (phiY F r n).toRingHom
      = (phiA F r n (specA F n η)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    show etaMap F (σ := Fin r × Fin n × Fin n) n η
        (phiY F r n (algebraMap F (S F r n) c))
      = phiA F r n (specA F n η) (algebraMap F (S F r n) c)
    rw [(phiY F r n).commutes c, (phiA F r n (specA F n η)).commutes c]
    rw [show ((algebraMap F (MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n))) c)
        = MvPolynomial.C (algebraMap F (Tloc F n) c) from rfl, etaMap_C]
    simp
  · intro m
    rcases m with ⟨k, i, j⟩
    show etaMap F (σ := Fin r × Fin n × Fin n) n η (phiY F r n (MvPolynomial.X (k, i, j)))
      = phiA F r n (specA F n η) (MvPolynomial.X (k, i, j))
    exact etaMap_phiY_X F r n η k i j

#print axioms etaMap_comp_phiY

/-- ★★★★ **`η'` 与 `ψ` 交换**：`M_n(η')(ψ_Y(α)) = ψ_A(α)`，`A = M_n(η)(Y)`。

**这是 `prop:14.14` 证明的核心等式**（原文"`M_n(η')(ψ_Y(α) − α) = ψ_A(α) − α`"的左半边）。
**证明**：`ψ` 是三个因子之积，`Matrix.map_mul` 逐因子过：
* `Y` 侧：`η'(C b) = C(η b)`（`etaMap_C`），再用 `specA_val` 认出 `A`；
* `Y⁻¹` 侧：同理用 `specA_inv_val`；
* 中间 `α.map φ_Y`：逐条目用 `etaMap_comp_phiY`（即 `η' ∘ φ_Y = φ_A`）。 -/
lemma etaMap_psiY (r n : ℕ) (η : Tloc F n →ₐ[F] F) (α : Matrix (Fin n) (Fin n) (S F r n)) :
    (psiY F r n α).map (etaMap F (σ := Fin r × Fin n × Fin n) n η)
      = psiA F r n (specA F n η) α := by
  have hcoe : ∀ q : S F r n, etaMap F (σ := Fin r × Fin n × Fin n) n η (phiY F r n q)
      = phiA F r n (specA F n η) q := fun q => by
    have h := congrArg (fun f : S F r n →+* S F r n => f q) (etaMap_comp_phiY F r n η)
    simpa using h
  have hY : ((Ymat F n).map (MvPolynomial.C : Tloc F n → MvPolynomial (Fin r × Fin n × Fin n)
        (Tloc F n))).map (etaMap F (σ := Fin r × Fin n × Fin n) n η)
      = constMat F r n (↑(specA F n η)) := by
    rw [Matrix.map_map, constMat_eq_C_map, specA_val, Matrix.map_map]
    funext i j
    exact etaMap_C F n η ((Ymat F n) i j)
  have hYinv : ((Yinv F n).map (MvPolynomial.C : Tloc F n → MvPolynomial (Fin r × Fin n × Fin n)
        (Tloc F n))).map (etaMap F (σ := Fin r × Fin n × Fin n) n η)
      = constMat F r n (↑((specA F n η)⁻¹)) := by
    rw [Matrix.map_map, constMat_eq_C_map, specA_inv_val, Matrix.map_map]
    funext i j
    exact etaMap_C F n η ((Yinv F n) i j)
  have hmid : (α.map (phiY F r n)).map (etaMap F (σ := Fin r × Fin n × Fin n) n η)
      = α.map (phiA F r n (specA F n η)) := by
    rw [Matrix.map_map]
    apply Matrix.ext
    intro i j
    exact hcoe (α i j)
  show ((Ymat F n).map _ * α.map (phiY F r n) * (Yinv F n).map _).map
      (etaMap F (σ := Fin r × Fin n × Fin n) n η) = _
  rw [Matrix.map_mul, Matrix.map_mul, hY, hYinv, hmid]
  rfl

#print axioms etaMap_psiY

/-! ## §11 `prop:14.14`（generic 不变性）本体

**原文（逐字）**：`raw/Saltman1999ch14.tex:286–288`：
> Let `α ∈ M_n(S)^{PGL_n(F)}`. Then with `Y` a generic matrix as above, `ψ_Y(α) = α`.

**机检形式**：`psiY_of_pgl_invariant`——若 `α` 被所有常矩阵的 `ψ_A` 固定，则被 `ψ_Y` 固定。

**证明（照原文）**：反设 `ψ_Y(α) − α ≠ 0` ⟹ 取其一个非零条目 `s' ∈ S_T` ⟹ 抽 `s'` 的一个非零
系数 `t ∈ T` ⟹ `exists_algHom_ne_zero` 给 `η : T →ₐ[F] F` 使 `η t ≠ 0` ⟹
`η'(s') ≠ 0` ⟹ `η'(ψ_Y(α) − α) = ψ_A(α) − α ≠ 0`（`etaMap_psiY`）⟹ 与 `ψ_A(α) = α` 矛盾。 -/

/-- ★★★ **`η'` 保"某条目非零"**：`S_T` 的非零元在某个 `η'` 下仍非零。
**证明**：`s ≠ 0` ⟹ 某个 `Finsupp` 系数 `s.coeff m ≠ 0`（`MvPolynomial.ext` 逆否）
⟹ `exists_algHom_ne_zero` 给 `η` ⟹ `(η'(s)).coeff m = η (s.coeff m) ≠ 0`（`MvPolynomial.coeff_map`）。 -/
lemma exists_etaMap_ne_zero [Infinite F] {σ : Type*} (n : ℕ)
    {s : MvPolynomial σ (Tloc F n)} (hs : s ≠ 0) :
    ∃ η : Tloc F n →ₐ[F] F, etaMap F (σ := σ) n η s ≠ 0 := by
  have hex : ∃ m, s.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (MvPolynomial.ext s 0 fun m => by rw [h m]; simp)
  obtain ⟨m, hm⟩ := hex
  obtain ⟨η, hη⟩ := exists_algHom_ne_zero F n hm
  refine ⟨η, fun h0 => hη ?_⟩
  have h := congrArg (fun p => p.coeff m) h0
  simpa [etaMap, MvPolynomial.coeff_map] using h

#print axioms exists_etaMap_ne_zero

/-- ★★ **`η'` 在 `α` 的自然像上是恒等**（矩阵层）：`M_n(η')(α 在 S_T 中的像) = α`。 -/
lemma etaMap_embed_mat (r n : ℕ) (η : Tloc F n →ₐ[F] F)
    (α : Matrix (Fin n) (Fin n) (S F r n)) :
    (α.map (MvPolynomial.map (algebraMap F (Tloc F n)))).map
        (etaMap F (σ := Fin r × Fin n × Fin n) n η) = α := by
  rw [Matrix.map_map]
  apply Matrix.ext
  intro i j
  exact etaMap_embed F n η (α i j)

#print axioms etaMap_embed_mat

/-- ★★★★ **Saltman `prop:14.14`（generic 部分）机检**：`α` 若被所有 `ψ_A`（`A ∈ GL_n(F)`）固定，
则被**通用矩阵** `Y` 的 `ψ_Y` 固定。

**注**：`α.map (MvPolynomial.map (algebraMap F T))` 就是 `α ∈ M_n(S)` 在 `M_n(S_T)` 中的自然像，
故结论即原文的 `ψ_Y(α) = α`。 -/
theorem psiY_of_pgl_invariant [Infinite F] (r n : ℕ)
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n A α = α) :
    psiY F r n α = α.map (MvPolynomial.map (algebraMap F (Tloc F n))) := by
  by_contra hne
  have hex : ∃ i j, (psiY F r n α
      - α.map (MvPolynomial.map (algebraMap F (Tloc F n)))) i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by funext i j; exact sub_eq_zero.mp (h i j))
  obtain ⟨i, j, hij⟩ := hex
  obtain ⟨η, hη⟩ := exists_etaMap_ne_zero F n hij
  have hmap : (psiY F r n α
      - α.map (MvPolynomial.map (algebraMap F (Tloc F n)))).map
        (etaMap F (σ := Fin r × Fin n × Fin n) n η)
      = psiA F r n (specA F n η) α - α := by
    funext i j
    have h1 := congrArg (fun M => M i j) (etaMap_psiY F r n η α)
    have h2 := congrArg (fun M => M i j) (etaMap_embed_mat F r n η α)
    simp only [Matrix.map_apply] at h1 h2
    simp only [Matrix.map_apply, Matrix.sub_apply]
    rw [map_sub, h1, h2]
  have hdiff : etaMap F (σ := Fin r × Fin n × Fin n) n η
      ((psiY F r n α - α.map (MvPolynomial.map (algebraMap F (Tloc F n)))) i j)
      = (psiA F r n (specA F n η) α - α) i j := by
    have h := congrArg (fun M => M i j) hmap
    simpa using h
  have hne2 : (psiA F r n (specA F n η) α - α) i j ≠ 0 := by
    rw [← hdiff]
    exact hη
  rw [hα (specA F n η), sub_self] at hne2
  exact hne2 (by simp)

#print axioms psiY_of_pgl_invariant

/-! ## §12 `φ_A`／`ψ_A` 的**扩展环版本**（`prop:14.14(b)` 与 `thm:14.15` 所需的载体）

**原文（逐字）**：`raw/Saltman1999ch14.tex:284–286`：
> If `S'' ⊃ S` is any extension ring and `A ∈ M_n(S'')` is an invertible matrix, define
> `φ_A : S → S''` by setting `φ_A(x_{ijk})` to be the `i,j` entry of the matrix `A⁻¹X_kA`.
> Of course, if `B ∈ M_n(S)` we define `ψ_A(B) = A(M_n(φ_A)(B))A⁻¹ ∈ M_n(S'')`.

`PGL.lean` 的 `phiA`／`psiA` 只覆盖 `A ∈ GL_n(F)`（`PGL_n(F)` 的作用）；本节给**任意扩展环 `R`**
上的版本——这正是 `prop:14.14(b)`（"`S'' ⊃ S` 任意、`A` 可逆 ⟹ `ψ_A(α) = α`"）
与 `thm:14.15`（`θ_i : M_n(S) → M_n(T)`）都要用的形式。

**约定**：`R` 是 `S = F[x_{ijk}]` 的交换代数（故自动是 `F`-代数），`X_k` 经 `algebraMap` 进入 `R`。 -/

section Gen

variable (F : Type) [Field F] (r n : ℕ)

/-- 通用矩阵 `X_k` 在扩展环 `R` 中的像。 -/
noncomputable def genMatR (R : Type) [CommRing R] [Algebra (S F r n) R] (k : Fin r) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of (fun a b => algebraMap (S F r n) R (MvPolynomial.X (k, a, b)))

/-- `φ_A` 在不定元上的值（扩展环版）：`x_{ijk} ↦ (A⁻¹X_kA)_{ij}`，`A ∈ GL_n(R)`。 -/
noncomputable def phiGenR (R : Type) [CommRing R] [Algebra (S F r n) R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) (e : Fin r × Fin n × Fin n) : R :=
  (((A⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * genMatR F r n R e.1
    * ((A : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)) e.2.1 e.2.2

/-- ★★★ **`φ_A : S →ₐ[F] R`（扩展环版）**（源文 `φ_A(x_{ijk}) = (A⁻¹X_kA)_{ij}`，
`A` 取在 `S` 的扩展 `R` 上）。 -/
noncomputable def phiAR (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (A : (Matrix (Fin n) (Fin n) R)ˣ) : S F r n →ₐ[F] R :=
  MvPolynomial.aeval (phiGenR F r n R A)

/-- ★★★ **扩展环版的源文 `(16)`**：`M_n(φ_A)(X_k) = A⁻¹X_kA`。 -/
lemma phiAR_X (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (A : (Matrix (Fin n) (Fin n) R)ˣ) (k : Fin r) :
    (genericMatrix F r n k).map (phiAR F r n R A)
      = ((A⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * genMatR F r n R k
        * ((A : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  show (phiAR F r n R A) (MvPolynomial.X (k, i, j)) = _
  rw [show phiAR F r n R A = MvPolynomial.aeval (phiGenR F r n R A) from rfl,
    MvPolynomial.aeval_X]
  rfl

#print axioms phiAR_X

/-- ★★★ **`ψ_A`（扩展环版）**：`ψ_A(β) = A·M_n(φ_A)(β)·A⁻¹ ∈ M_n(R)`，`β ∈ M_n(S)`。 -/
noncomputable def psiAR (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (A : (Matrix (Fin n) (Fin n) R)ˣ) :
    Matrix (Fin n) (Fin n) (S F r n) → Matrix (Fin n) (Fin n) R :=
  fun β => ((A : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)
    * (β.map (phiAR F r n R A))
    * ((A⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)

end Gen

/-! ## §13 `prop:14.14(b)` 的工具箱：特殊化到**任意扩展环** `R`

`prop:14.14(b)` 要求：`S'' ⊃ S` 任意、`A ∈ M_n(S'')` 可逆 ⟹ `ψ_A(α) = α`。
证明（原文）：把 `Y` 特殊化成 `A`——即取 `η : T ↦ S''`（`η(y_{ij}) = A_{ij}`），
把 (a) 的等式 `ψ_Y(α) = α` 沿 `η` 压下去。本节给这条路上**三个载体**：

* `etaMapR`：`S_T = T[x] → R[x]`（替换系数；目标环任意）；
* `specEval`：`R[x] → R`（把 `x_{ijk}` 送到它在 `R` 中的像）；
* `specEta`：两者复合 `S_T → R`（`specEta_C`／`specEta_X` 给出其在 `C` 与 `X` 上的值）；
* `specAR`：`A := M_n(η)(Y) ∈ GL_n(R)`（`det Y` 是 `T` 的单位，沿 `η` 仍是单位）。

**射程（如实登记）**：本节只作载体；`prop:14.14(b)` 的**本体**（生成元恒等式
`specEta ∘ φ_Y = φ_A` 与矩阵层 `specEta(ψ_Y(α)) = ψ_A(α)`）在下一轮。 -/

section SpecR

variable (F : Type) [Field F] (r n : ℕ)

/-- `η` 诱导的 `S_T → R[x]`（系数替换；与 `etaMap` 相同，但目标环任意）。 -/
noncomputable def etaMapR {σ : Type*} (R : Type) [CommSemiring R] (n : ℕ)
    (η : Tloc F n →+* R) : MvPolynomial σ (Tloc F n) →+* MvPolynomial σ R :=
  MvPolynomial.map η

/-- `R[x] → R`：把 `x_{ijk}` 送到其在 `R` 中的像（`R` 是 `S`-代数）。 -/
noncomputable def specEval (R : Type) [CommRing R] [Algebra (S F r n) R] :
    MvPolynomial (Fin r × Fin n × Fin n) R →+* R :=
  (MvPolynomial.aeval (fun m => algebraMap (S F r n) R (MvPolynomial.X m))).toRingHom

/-- 复合 `S_T → R`：先替换系数、再把 `x` 送到 `R`。 -/
noncomputable def specEta (R : Type) [CommRing R] [Algebra (S F r n) R]
    (η : Tloc F n →+* R) :
    MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n) →+* R :=
  (specEval F r n R).comp (etaMapR F (σ := Fin r × Fin n × Fin n) R n η)

/-- ★ `specEta` 在常系数上的作用：`specEta(C b) = η b`。 -/
lemma specEta_C (R : Type) [CommRing R] [Algebra (S F r n) R] (η : Tloc F n →+* R)
    (b : Tloc F n) :
    specEta F r n R η (MvPolynomial.C b : MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n))
      = η b := by
  simp [specEta, specEval, etaMapR]

#print axioms specEta_C

/-- ★ `specEta` 在变量上的作用：`specEta(x_m) = algebraMap S R x_m`（`R` 是 `S`-代数）。 -/
lemma specEta_X (R : Type) [CommRing R] [Algebra (S F r n) R] (η : Tloc F n →+* R)
    (m : Fin r × Fin n × Fin n) :
    specEta F r n R η (MvPolynomial.X m : MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n))
      = algebraMap (S F r n) R (MvPolynomial.X m) := by
  simp [specEta, specEval, etaMapR]

#print axioms specEta_X

end SpecR

section SpecA

variable (F : Type) [Field F] (n : ℕ)

/-- ★★★ **`A := M_n(η)(Y)` 作为 `GL_n(R)` 的元**：`det Y` 是 `T` 的单位，沿 `η` 仍是单位，
故 `M_n(η)(Y)` 可逆（`Matrix.isUnit_iff_isUnit_det` ＋ `IsUnit.unit`）。 -/
noncomputable def specAR (R : Type) [CommRing R] [Algebra F R] (η : Tloc F n →ₐ[F] R) :
    (Matrix (Fin n) (Fin n) R)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det ((Ymat F n).map η)).mpr (by
    have h : IsUnit (η ((Ymat F n).det)) := (Ymat_det_isUnit F n).map η.toRingHom
    rw [AlgHom.map_det] at h
    simpa using h)).unit

/-- ★ `specAR` 的底层矩阵就是 `M_n(η)(Y)`。 -/
lemma specAR_val (R : Type) [CommRing R] [Algebra F R] (η : Tloc F n →ₐ[F] R) :
    ((specAR F n R η : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)
      = (Ymat F n).map η :=
  IsUnit.unit_spec _

#print axioms specAR_val

end SpecA

/-! ## §14 扩展环版的生成元恒等式 `specEta ∘ φ_Y = φ_A`

`prop:14.14(b)` 证明中"Applying this `η` to the equation `ψ_Y(α) = α`"的第一块：
两边的 `φ` 在生成元上一致。本节同时给出 `specAR` 的逆（`M_n(η)(Y⁻¹)`），
它是矩阵层恒等式消去 `A·A⁻¹` 的前提。 -/

section R1

variable (F : Type) [Field F] (n : ℕ)

/-- ★ **`Y⁻¹·Y = 1` 沿任意 `F`-代数映射运输**（目标环任意）。 -/
lemma Yinv_map_mul_Ymat_map_R (R : Type) [CommRing R] [Algebra F R]
    (η : Tloc F n →ₐ[F] R) : (Yinv F n).map η * (Ymat F n).map η = 1 := by
  have h : (Yinv F n).map (⇑η) * (Ymat F n).map (⇑η)
      = (Yinv F n * Ymat F n).map (⇑η) :=
    (map_mul_apply (η.toRingHom) (Yinv F n) (Ymat F n)).symm
  rw [h, Yinv_mul_Ymat]
  funext i j
  simp [Matrix.one_apply]

#print axioms Yinv_map_mul_Ymat_map_R

/-- ★★ **`specAR η` 的逆是 `M_n(η)(Y⁻¹)`**（逆的唯一性）。 -/
lemma specAR_inv_val (R : Type) [CommRing R] [Algebra F R] (η : Tloc F n →ₐ[F] R) :
    ((↑((specAR F n R η)⁻¹) : Matrix (Fin n) (Fin n) R)) = (Yinv F n).map η := by
  have hY : (Yinv F n).map η * (↑(specAR F n R η) : Matrix (Fin n) (Fin n) R) = 1 := by
    rw [specAR_val]; exact Yinv_map_mul_Ymat_map_R F n R η
  have key : (Yinv F n).map η = (↑((specAR F n R η)⁻¹) : Matrix (Fin n) (Fin n) R) := by
    calc (Yinv F n).map η
        = (Yinv F n).map η * ((↑(specAR F n R η) : Matrix (Fin n) (Fin n) R)
            * ↑((specAR F n R η)⁻¹)) := by
          rw [show (↑(specAR F n R η) : Matrix (Fin n) (Fin n) R)
              * ↑((specAR F n R η)⁻¹) = 1 from by simp, mul_one]
      _ = ((Yinv F n).map η * ↑(specAR F n R η)) * ↑((specAR F n R η)⁻¹) := by rw [mul_assoc]
      _ = ↑((specAR F n R η)⁻¹) := by rw [hY, one_mul]
  exact key.symm

#print axioms specAR_inv_val

end R1

section R2

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **扩展环版生成元恒等式**：`specEta(φ_Y(x_{ijk})) = φ_A(x_{ijk})`，`A = M_n(η)(Y)`。
**这是 `prop:14.14(b)` 证明里 "η' ∘ φ_Y = φ_A" 的机检形式**（与第 142 轮的 `F`-版 `etaMap_phiY_X` 同构）。 -/
lemma specEta_phiY_X (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (η : Tloc F n →ₐ[F] R) (k : Fin r) (i j : Fin n) :
    specEta F r n R η.toRingHom (phiY F r n (MvPolynomial.X (k, i, j)))
      = phiAR F r n R (specAR F n R η) (MvPolynomial.X (k, i, j)) := by
  rw [phiY_X]
  simp only [map_sum, map_mul, specEta_C, specEta_X]
  rw [show phiAR F r n R (specAR F n R η) (MvPolynomial.X (k, i, j))
      = phiGenR F r n R (specAR F n R η) ⟨k, i, j⟩ from MvPolynomial.aeval_X _ _]
  rw [phiGenR, specAR_inv_val, specAR_val]
  simp only [genMatR, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_mul,
    AlgHom.toRingHom_eq_coe]
  rw [Finset.sum_comm]
  simp

#print axioms specEta_phiY_X

end R2

/-! ## §15 扩展环版的 `specEta ∘ φ_Y = φ_A`（同态层）与 `specEta(ψ_Y(α)) = ψ_A(α)`（矩阵层）

`prop:14.14(b)` 证明的两块核心等式。与第 143 轮的 `F`-版（`etaMap_comp_phiY`／`etaMap_psiY`）
逐行同构，仅目标环由 `F` 换成任意 `S`-代数 `R`。 -/

section R3

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **同态层**：`specEta ∘ φ_Y = φ_A`（`A = M_n(η)(Y)`），由生成元恒等式 ＋
`MvPolynomial.ringHom_ext` 升到同态层。 -/
lemma specEta_comp_phiY (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (η : Tloc F n →ₐ[F] R) :
    (specEta F r n R η.toRingHom).comp (phiY F r n).toRingHom
      = (phiAR F r n R (specAR F n R η)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    show specEta F r n R η.toRingHom (phiY F r n (algebraMap F (S F r n) c))
      = phiAR F r n R (specAR F n R η) (algebraMap F (S F r n) c)
    rw [(phiY F r n).commutes c, (phiAR F r n R (specAR F n R η)).commutes c]
    rw [show ((algebraMap F (MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n))) c)
        = MvPolynomial.C (algebraMap F (Tloc F n) c) from rfl,
      specEta_C]
    exact η.commutes c
  · intro m
    rcases m with ⟨k, i, j⟩
    show specEta F r n R η.toRingHom (phiY F r n (MvPolynomial.X (k, i, j)))
      = phiAR F r n R (specAR F n R η) (MvPolynomial.X (k, i, j))
    exact specEta_phiY_X F r n R η k i j

#print axioms specEta_comp_phiY

/-- ★★★★ **矩阵层**：`specEta(ψ_Y(α)) = ψ_A(α)`，`A = M_n(η)(Y)`。
**这是 `prop:14.14(b)` 证明里 "Applying this `η` to `ψ_Y(α) = α`" 的机检形式**：
`ψ` 是三因子之积，逐因子过（`Y` 用 `specAR_val`、`Y⁻¹` 用 `specAR_inv_val`、中间用同态层等式）。 -/
lemma specEta_psiY (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (η : Tloc F n →ₐ[F] R)
    (α : Matrix (Fin n) (Fin n) (S F r n)) :
    (psiY F r n α).map (specEta F r n R η.toRingHom)
      = psiAR F r n R (specAR F n R η) α := by
  have hcoe : ∀ q : S F r n, specEta F r n R η.toRingHom (phiY F r n q)
      = phiAR F r n R (specAR F n R η) q := fun q => by
    have h := congrArg (fun f : S F r n →+* R => f q) (specEta_comp_phiY F r n R η)
    simpa using h
  have hcomp : (⇑(specEta F r n R η.toRingHom) ∘
      ⇑(MvPolynomial.C : Tloc F n →+* MvPolynomial (Fin r × Fin n × Fin n) (Tloc F n))) = ⇑η := by
    funext b
    exact specEta_C F r n R η.toRingHom b
  have hY : ((Ymat F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n))).map
      (specEta F r n R η.toRingHom) = (↑(specAR F n R η) : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.map_map, hcomp, ← specAR_val]
  have hYinv : ((Yinv F n).map (MvPolynomial.C (σ := Fin r × Fin n × Fin n))).map
      (specEta F r n R η.toRingHom)
      = (↑((specAR F n R η)⁻¹) : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.map_map, hcomp, ← specAR_inv_val]
  have hmid : ((α.map (phiY F r n)).map (specEta F r n R η.toRingHom))
      = α.map (phiAR F r n R (specAR F n R η)) := by
    rw [Matrix.map_map]
    apply Matrix.ext
    intro i j
    exact hcoe (α i j)
  show (((Ymat F n).map _) * (α.map (phiY F r n)) * ((Yinv F n).map _)).map
      (specEta F r n R η.toRingHom) = _
  rw [Matrix.map_mul, Matrix.map_mul, hY, hYinv, hmid]
  rfl

#print axioms specEta_psiY

end R3

/-! ## §16 **`prop:14.14` 收口**：(b) 的构造与装配

`prop:14.14(b)`：`S'' ⊃ S` 任意、`A ∈ M_n(S'')` 可逆 ⟹ `ψ_A(α) = α`。
原文证明（`raw/Saltman1999ch14.tex:296–297`）：
> Next suppose `S'' ⊃ S` is an extension commutative ring and `A ∈ M_n(S'')` is invertible.
> Define `η : T → S''` by letting `η(y_{ij})` be the `i,j` entry of `A`. The point is that
> `M_n(η)(Y) = A`. Applying this `η` to the equation `ψ_Y(α) = α` yields `ψ_A(α) = α`.

本节的机检路线：
① 由 `A` 造 `F`-代数映射 `yMapOfA : F[y] →ₐ[F] R`（`y_{ij} ↦ A_{ij}`）；
② 证 `yMapOfA(det Y)` 是单位（＝ `det A`）；
③ `IsLocalization.Away.liftAlgHom` 把它提升为 `etaOfA : T →ₐ[F] R`；
④ 证 `specAR(etaOfA A) = A`（即 `M_n(η)(Y) = A`）；
⑤ 把 (a)（第 144 轮）沿 `specEta (etaOfA A)` 压下去（用第 156 轮的矩阵层等式）即得 (b)。 -/

section R4

variable (F : Type) [Field F] (n : ℕ)

/-- 由 `A ∈ GL_n(R)` 造出的 `F`-代数映射 `F[y] → R`：`y_{ij} ↦ A_{ij}`。 -/
noncomputable def yMapOfA (R : Type) [CommRing R] [Algebra F R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) : MvPolynomial (Fin n × Fin n) F →ₐ[F] R :=
  MvPolynomial.aeval (fun p : Fin n × Fin n => ((A : Matrix (Fin n) (Fin n) R)) p.1 p.2)

/-- ★ `yMapOfA(det Y) = det A`，故在 `det` 处可逆。 -/
lemma yMapOfA_genDet_isUnit (R : Type) [CommRing R] [Algebra F R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) : IsUnit (yMapOfA F n R A (genDet F n)) := by
  have h : yMapOfA F n R A (genDet F n) = ((A : Matrix (Fin n) (Fin n) R)).det := by
    rw [genDet, genMat, AlgHom.map_det]
    congr 1
    ext i j
    simp [yMapOfA]
  rw [h]
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (show IsUnit ((A : Matrix (Fin n) (Fin n) R)) from ⟨A, rfl⟩)

#print axioms yMapOfA_genDet_isUnit

/-- ★★ **由 `A` 构造 `η : T →ₐ[F] R`**：`IsLocalization.Away.liftAlgHom`（`A` 可逆 ⟹ `det` 的像是单位）。 -/
noncomputable def etaOfA (R : Type) [CommRing R] [Algebra F R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) : Tloc F n →ₐ[F] R :=
  IsLocalization.Away.liftAlgHom (S := Tloc F n) (genDet F n) (yMapOfA_genDet_isUnit F n R A)

/-- ★ `etaOfA` 在 `F[y]` 的像上与 `yMapOfA` 一致（提升的交换三角）。 -/
lemma etaOfA_eq (R : Type) [CommRing R] [Algebra F R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) (q : MvPolynomial (Fin n × Fin n) F) :
    etaOfA F n R A (algebraMap (MvPolynomial (Fin n × Fin n) F) (Tloc F n) q)
      = yMapOfA F n R A q := by
  rw [etaOfA, IsLocalization.Away.liftAlgHom_apply]
  exact IsLocalization.Away.lift_eq (x := genDet F n) (g := (yMapOfA F n R A).toRingHom)
    (yMapOfA_genDet_isUnit F n R A) q

#print axioms etaOfA_eq

/-- ★★★ **`M_n(η)(Y) = A`**（原文 "The point is that `M_n(η)(Y) = A`"）：`specAR(etaOfA A) = A`。 -/
lemma specAR_etaOfA (R : Type) [CommRing R] [Algebra F R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) : specAR F n R (etaOfA F n R A) = A := by
  apply Units.ext
  rw [specAR_val]
  have h : (Ymat F n).map (etaOfA F n R A)
      = (genMat F n).map (fun p => yMapOfA F n R A p) := by
    rw [Ymat, Matrix.map_map]
    congr 1
    funext p
    exact etaOfA_eq F n R A p
  rw [h]
  ext i j
  simp [genMat, yMapOfA]

#print axioms specAR_etaOfA

end R4

section R5

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★ **`specEta` 与 `S ↪ S_T` 相容**：`specEta(map (algebraMap F T) q) = algebraMap S R q`。 -/
lemma specEta_embed (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (η : Tloc F n →ₐ[F] R) :
    (specEta F r n R η.toRingHom).comp (MvPolynomial.map (algebraMap F (Tloc F n)))
      = algebraMap (S F r n) R := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    rw [MvPolynomial.map_C, specEta_C]
    have hc : η.toRingHom (algebraMap F (Tloc F n) c) = algebraMap F R c := η.commutes c
    rw [hc]
    rw [show (MvPolynomial.C c : S F r n) = algebraMap F (S F r n) c from rfl]
    exact IsScalarTower.algebraMap_apply F (S F r n) R c
  · intro m
    simp only [RingHom.comp_apply]
    rw [show (MvPolynomial.map (algebraMap F (Tloc F n))) (MvPolynomial.X m : S F r n)
        = (MvPolynomial.X m : MvPolynomial _ (Tloc F n)) from MvPolynomial.map_X _ m,
      specEta_X]

#print axioms specEta_embed

end R5

section R6

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **Saltman `prop:14.14(b)` 机检**：`α` 若被所有 `ψ_B`（`B ∈ GL_n(F)`）固定，
则对**任意** `S`-代数 `R` 与**任意**可逆 `A ∈ M_n(R)`，`ψ_A(α) = α`（在 `M_n(R)` 中）。

**与 (a)（第 144 轮 `psiY_of_pgl_invariant`）合起来即 `prop:14.14` 全文机检。** -/
theorem psiAR_of_pgl_invariant [Infinite F] (r n : ℕ)
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α)
    (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R] [IsScalarTower F (S F r n) R]
    (A : (Matrix (Fin n) (Fin n) R)ˣ) :
    psiAR F r n R A α = α.map (algebraMap (S F r n) R) := by
  have h := psiY_of_pgl_invariant F r n α hα
  have h2 := congrArg (fun M => M.map (specEta F r n R (etaOfA F n R A).toRingHom)) h
  rw [specEta_psiY, specAR_etaOfA] at h2
  rw [h2, Matrix.map_map]
  congr 1
  funext q
  exact congrArg (fun f => f q) (specEta_embed F r n R (etaOfA F n R A))

#print axioms psiAR_of_pgl_invariant

end R6

/-! ## §17 一致性检查：`φ_1 = algebraMap`、`ψ_1 = id`

扩展环版 `φ_A`／`ψ_A`（§12）是从 `PGL_n(F)` 版（`PGL.lean`）推广来的，
必须验证 `A = 1` 时退化为应有的东西：
源文 `A = 1` 给 `A⁻¹X_kA = X_k`，故 `φ_1` 应是 `S ↪ R`、`ψ_1` 应是恒等（在 `α` 的自然像上）。
本节把这两条机检，作为 §12–§16 推广的自洽性证据。 -/

section One

variable (F : Type) [Field F] (r n : ℕ)

/-- ★ **`φ_1 = algebraMap S R`**。 -/
lemma phiAR_one (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] :
    phiAR F r n R (1 : (Matrix (Fin n) (Fin n) R)ˣ) = IsScalarTower.toAlgHom F (S F r n) R := by
  apply MvPolynomial.algHom_ext
  intro m
  rw [show phiAR F r n R (1 : (Matrix (Fin n) (Fin n) R)ˣ) (MvPolynomial.X m)
      = phiGenR F r n R (1 : (Matrix (Fin n) (Fin n) R)ˣ) m from MvPolynomial.aeval_X _ _]
  simp [phiGenR, genMatR, IsScalarTower.toAlgHom]

#print axioms phiAR_one

/-- ★★ **`ψ_1 = id`**（在 `α` 的自然像上）。 -/
lemma psiAR_one (R : Type) [CommRing R] [Algebra F R] [Algebra (S F r n) R]
    [IsScalarTower F (S F r n) R] (α : Matrix (Fin n) (Fin n) (S F r n)) :
    psiAR F r n R (1 : (Matrix (Fin n) (Fin n) R)ˣ) α = α.map (algebraMap (S F r n) R) := by
  show ((1 : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R)
      * (α.map (phiAR F r n R 1))
      * (((1 : (Matrix (Fin n) (Fin n) R)ˣ))⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) = _
  simp only [Units.val_one, inv_one]
  rw [one_mul, mul_one, phiAR_one]
  rfl

#print axioms psiAR_one

end One

/-! ## §18 **`thm:14.15` 的核心恒等式 `θ_2' ∘ ψ_A = θ_1'`**

原文（`raw/Saltman1999ch14.tex:320–322`）：
> We have `θ_1'(β) = M_n(η_1')(β) = M_n(η_2')M_n(φ_A)(β) = M_n(η_2')(A^{-1}(A(M_n(φ_A)(β)A^{-1})A))
> = (θ_2' ∘ ψ_A)(β)`. That is, `θ_1' = θ_2' ∘ ψ_A`.

其中 `θ_2'(β) = A⁻¹ M_n(η_2')(β) A`，`ψ_A(β) = A(M_n(φ_A)(β))A⁻¹`，且用了 `M_n(η_2')(A) = A`。
本节机检的等式是它的**等价变形**（把 `A⁻¹`、`A` 移到另一侧，免去消去）：
`M_n(η_2)(ψ_A(β)) = A · M_n(η_1)(β) · A⁻¹`。

**两块**：
* `map_conj_of_fixed`（一般矩阵代数）：若环同态逐条目**固定 `A`**，则它与**共轭**可交换；
* `mapMatrix_psiAR_of_comp_phiAR`：由 `η_1 = η_2 ∘ φ_A` 与 `η_2` 固定 `A` 得上述恒等式。 -/

section Conj

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★ **共轭沿固定 `A` 的环同态运输**：`f` 逐条目固定 `A` ⟹ `f(A X A⁻¹) = A f(X) A⁻¹`。 -/
lemma map_conj_of_fixed (f : R →+* R) (A : (Matrix n n R)ˣ) (X : Matrix n n R)
    (hA : ((A : Matrix n n R)).map f = (A : Matrix n n R)) :
    (((A : Matrix n n R)) * X * ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)).map f
      = ((A : Matrix n n R)) * (X.map f) * ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) := by
  have h1 : f.mapMatrix ((A : Matrix n n R) * X * ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R))
      = f.mapMatrix (A : Matrix n n R) * f.mapMatrix X
        * f.mapMatrix ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) := by
    rw [map_mul, map_mul]
  have h2 : f.mapMatrix (A : Matrix n n R) = (A : Matrix n n R) := by
    rw [RingHom.mapMatrix_apply]; exact hA
  have h3 : f.mapMatrix ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
      = ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) := by
    have hU : Units.map f.mapMatrix.toMonoidHom A = A := Units.ext h2
    calc f.mapMatrix ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
        = ((Units.map f.mapMatrix.toMonoidHom (A⁻¹) : (Matrix n n R)ˣ) : Matrix n n R) := rfl
      _ = (((Units.map f.mapMatrix.toMonoidHom A)⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) := by
            rw [map_inv]
      _ = ((A⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) := by rw [hU]
  rw [← RingHom.mapMatrix_apply, h1, h2, h3, RingHom.mapMatrix_apply]

#print axioms map_conj_of_fixed

end Conj

section Assembly

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`thm:14.15` 的核心恒等式**（等价变形）：若 `η_1 = η_2 ∘ φ_A` 且 `η_2` 逐条目固定 `A`，
则 `M_n(η_2)(ψ_A(β)) = A · M_n(η_1)(β) · A⁻¹`。**这是 `θ_1' = θ_2' ∘ ψ_A` 的机检形式。** -/
theorem mapMatrix_psiAR_of_comp_phiAR [Infinite F]
    (A : (Matrix (Fin n) (Fin n) (S F r n))ˣ)
    (η₁ η₂ : S F r n →+* S F r n)
    (h₁ : ∀ q, η₁ q = η₂ (phiAR F r n (S F r n) A q))
    (hfix : ∀ i j, η₂ ((A : Matrix (Fin n) (Fin n) (S F r n)) i j)
      = (A : Matrix (Fin n) (Fin n) (S F r n)) i j)
    (β : Matrix (Fin n) (Fin n) (S F r n)) :
    η₂.mapMatrix (psiAR F r n (S F r n) A β)
      = ((A : (Matrix (Fin n) (Fin n) (S F r n))ˣ) : Matrix (Fin n) (Fin n) (S F r n))
        * (η₁.mapMatrix β)
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) (S F r n))ˣ)) : Matrix (Fin n) (Fin n) (S F r n)) := by
  have hA : ((A : Matrix (Fin n) (Fin n) (S F r n))).map η₂
      = (A : Matrix (Fin n) (Fin n) (S F r n)) := by
    funext i j
    rw [Matrix.map_apply]
    exact hfix i j
  have hX : ((β.map (phiAR F r n (S F r n) A))).map η₂ = β.map η₁ := by
    funext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    exact (h₁ (β i j)).symm
  show η₂.mapMatrix
      (((A : (Matrix (Fin n) (Fin n) (S F r n))ˣ) : Matrix (Fin n) (Fin n) (S F r n))
        * (β.map (phiAR F r n (S F r n) A))
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) (S F r n))ˣ)) : Matrix (Fin n) (Fin n) (S F r n)))
      = _
  rw [RingHom.mapMatrix_apply,
    map_conj_of_fixed η₂ A (β.map (phiAR F r n (S F r n) A)) hA, hX,
    RingHom.mapMatrix_apply]

#print axioms mapMatrix_psiAR_of_comp_phiAR

end Assembly

/-! ## §19 张量扩张层（1）：`S' = S ⊗_F T` 与 `η_r'`

`thm:14.15` 的证明需要把目标环从 `S` 扩到 `S' = S ⊗_F T`（原文：`S' = S ⊗ T` viewed as an
extension of `S`）。**为什么必须扩张**：`φ_A` 要求 `A` 落在 `S` 的**代数**里，
而 `2.11` 给的 `A` 只在 `M_n(T)`；`S' = S ⊗_F T` 同时是 `S`-代数与 `T`-代数，
`A` 由 `T` 侧进入 `M_n(S')`，`φ_A` 才有定义。

本节给第一块：`η_r' : S' →ₐ[F] T`（在 `T` 上恒等、在 `S` 上为 `η_r`），用
`Algebra.TensorProduct.lift` 构造。两条同态层性质即原文两处关键用法：
* `etaExt_comp_includeLeft`：`η_r' ∘ (S ↪ S') = η_r`（`θ_r'` 限制回 `M_n(S)` 得 `θ_r` 的依据）；
* `etaExt_comp_includeRight`：`η_r'` **在 `T` 侧恒等**——**这就是原文 "`M_n(η_2')(A) = A`" 的根据**。

**下一块（下一轮）**：`θ_r'`（`M_n(S') → M_n(T)` 的扩张）与 `φ_A` 在 `S'` 上的作用。 -/

section Tensor

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `S' = S ⊗_F T`：源文的 `S' = S ⊗ T` viewed as an extension of `S`。 -/
abbrev ST := TensorProduct F (S F r n) T

/-- ★★★ **`η_r' : S' →ₐ[F] T`**：在 `T` 上恒等、在 `S` 上为 `η_r`（`Algebra.TensorProduct.lift`）。 -/
noncomputable def etaExt (η : S F r n →ₐ[F] T) : ST F r n T →ₐ[F] T :=
  Algebra.TensorProduct.lift η (AlgHom.id F T) (fun _ _ => mul_comm _ _)

/-- ★ **`η_r'` 在 `S` 侧的交换三角**：`η_r' ∘ (S ↪ S') = η_r`。 -/
lemma etaExt_comp_includeLeft (η : S F r n →ₐ[F] T) :
    (etaExt F r n T η).comp
        (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T)) = η :=
  Algebra.TensorProduct.lift_comp_includeLeft η (AlgHom.id F T) (fun _ _ => mul_comm _ _)

#print axioms etaExt_comp_includeLeft

/-- ★★★ **`η_r'` 在 `T` 侧是恒等**——原文 "Since `M_n(η_2')(A) = A`" 的根据。 -/
lemma etaExt_comp_includeRight (η : S F r n →ₐ[F] T) :
    ((etaExt F r n T η).restrictScalars F).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T))
      = (AlgHom.id F T).restrictScalars F :=
  Algebra.TensorProduct.lift_comp_includeRight η (AlgHom.id F T) (fun _ _ => mul_comm _ _)

#print axioms etaExt_comp_includeRight

end Tensor

/-! ## §20 **`thm:14.15` 的最后一步**：`θ₁'(α) = θ₂'(α)`（用 `prop:14.14(b)`）

原文（`raw/Saltman1999ch14.tex:324–326`）：
> Finally, suppose `α ∈ M_n(S)^{PGL_n(F)}`. Then `θ₁(α) = θ₁'(α) = θ₂'ψ_A(α)
> =` (by Proposition \ref{prop:14.14}) `θ₂'(α) = θ₂(α)`.

本节把这**四步链**机检：把 `θ_r'` 的"扩张"性质与 `θ₁' = θ₂' ∘ ψ_A` 处理为**假设**
（它们是下一轮的对象），四步链本身在此收口——其中第三步正是第 157 轮已机检的
**`prop:14.14(b)`**（`psiAR_of_pgl_invariant`）。 -/

section Last

variable (F : Type) [Field F] [Infinite F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★ **`thm:14.15` 最后一步机检**：`Θ₁, Θ₂ : M_n(S') →+* M_n(T)` 若满足
"`θ₁' = θ₂' ∘ ψ_A`"（在 `M_n(S)` 的自然像上），则对 `α ∈ M_n(S)^{PGL}` 有 `θ₁'(α) = θ₂'(α)`。

**证明（一行）**：`θ₁'(α) = θ₂'(ψ_A(α))`（假设）`= θ₂'(α)`（**`prop:14.14(b)`**，`R = S'`）。 -/
theorem thm1415_lastStep
    (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ)
    (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) (ST F r n T) →+* Matrix (Fin n) (Fin n) T)
    (h : ∀ β : Matrix (Fin n) (Fin n) (S F r n),
        Θ₁ (β.map (algebraMap (S F r n) (ST F r n T)))
          = Θ₂ (psiAR F r n (ST F r n T) A β))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    Θ₁ (α.map (algebraMap (S F r n) (ST F r n T)))
      = Θ₂ (α.map (algebraMap (S F r n) (ST F r n T))) := by
  rw [h α, psiAR_of_pgl_invariant F r n α hα (ST F r n T) A]

#print axioms thm1415_lastStep

end Last

/-! ## §21 张量扩张层（2）：`φ_A` 的基变换 `Φ_A : S' → S'`

原文用 `M_n(φ_A)` 同时作用于 `S` 与 `S'` 上的矩阵。严格化的正确读法是：`φ_A` 的像本就在
`S' = S ⊗_F T` 里，故应把 `φ_A` **基变换**为 `Φ_A : S' →ₐ[F] S'`（在 `S` 侧是 `φ_A`、在 `T` 侧恒等），
再用 `M_n(Φ_A)`。

* `phiExt`：`Φ_A`，由 `Algebra.TensorProduct.lift (φ_A) includeRight` 构造；
* `phiExt_comp_includeLeft`／`phiExt_comp_includeRight`：两边各自的交换三角；
* `map_phiExt_includeLeft`：`(β.map algMap).map Φ_A = β.map φ_A`（**矩阵层**），
  即 `M_n(Φ_A)` 在 `M_n(S)` 的自然像上就是 `M_n(φ_A)`。

配合 §19 的 `etaExt`，原文 `η_1' = η_2' ∘ Φ_A` 与 `M_n(Φ_A)(X_k) = A⁻¹X_kA`（§12 的 `phiAR_X`）
两块即可拼出 `thm:14.15` 的 `θ_1' = θ_2' ∘ ψ_A`。 -/

section PhiExt

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★ **`φ_A` 在 `S' = S ⊗_F T` 上的基变换** `Φ_A : S' →ₐ[F] S'`：
在 `S` 侧是 `φ_A`、在 `T` 侧恒等。**这是原文 `M_n(φ_A)` 在 `S'` 上的正确读法。** -/
noncomputable def phiExt (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) : ST F r n T →ₐ[F] ST F r n T :=
  Algebra.TensorProduct.lift (phiAR F r n (ST F r n T) A)
    (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T))
    (fun _ _ => mul_comm _ _)

/-- ★ **`Φ_A` 在 `S` 侧就是 `φ_A`**。 -/
lemma phiExt_comp_includeLeft (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
    (phiExt F r n T A).comp
        (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T))
      = (phiAR F r n (ST F r n T) A).restrictScalars F := by
  rw [phiExt]
  exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _

#print axioms phiExt_comp_includeLeft

/-- ★★ **`Φ_A` 在 `T` 侧恒等**。 -/
lemma phiExt_comp_includeRight (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
    ((phiExt F r n T A).restrictScalars F).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T))
      = (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T)).restrictScalars F := by
  rw [phiExt]
  exact Algebra.TensorProduct.lift_comp_includeRight _ _ _

#print axioms phiExt_comp_includeRight

/-- ★★★ **`M_n(Φ_A)` 在 `M_n(S)` 的自然像上就是 `M_n(φ_A)`**。 -/
lemma map_phiExt_includeLeft (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ)
    (β : Matrix (Fin n) (Fin n) (S F r n)) :
    (β.map (algebraMap (S F r n) (ST F r n T))).map (phiExt F r n T A)
      = β.map (phiAR F r n (ST F r n T) A) := by
  have h : ((algebraMap (S F r n) (ST F r n T)))
      = ⇑(Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T)) := rfl
  rw [h, Matrix.map_map]
  congr 1
  funext i
  simpa using AlgHom.congr_fun (phiExt_comp_includeLeft F r n T A) i

#print axioms map_phiExt_includeLeft

end PhiExt

/-! ## §22 张量扩张层（3）：`η_r'` 的矩阵作用 ＋ `S' → T` 映射的唯一性

`thm:14.15` 剩下的两块拼图：

* `map_etaExt_includeLeft`：`η_r'` 在 `M_n(S)` 的自然像上就是 `M_n(η_r)`
  ——**这就是原文首尾两步 "`θ_r'(α) = θ_r(α)`" 的依据**（`θ_r' := M_n(η_r')`）；
* `algHom_ext_tensor`：`S' →ₐ[F] T` 由其在 `S` 侧与 `T` 侧的值**唯一决定**
  ——这是把 `η_1'` 与 `η_2' ∘ Φ_A` 两边（在 `S` 上由 `X_k` 比较相等、在 `T` 上都是恒等）
  等同起来的工具。 -/

section EtaExt2

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★ **`η_r'` 在 `M_n(S)` 的自然像上就是 `M_n(η_r)`**（矩阵层）。 -/
lemma map_etaExt_includeLeft (η : S F r n →ₐ[F] T)
    (β : Matrix (Fin n) (Fin n) (S F r n)) :
    (β.map (algebraMap (S F r n) (ST F r n T))).map (etaExt F r n T η) = β.map η := by
  have h : ((algebraMap (S F r n) (ST F r n T)))
      = ⇑(Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T)) := rfl
  rw [h, Matrix.map_map]
  congr 1
  funext i
  simpa using AlgHom.congr_fun (etaExt_comp_includeLeft F r n T η) i

#print axioms map_etaExt_includeLeft

/-- ★★★ **`S' →ₐ[F] T` 由其在 `S` 侧与 `T` 侧的值唯一决定**（`S' = S ⊗_F T` 由两因子生成）。 -/
lemma algHom_ext_tensor (η η' : ST F r n T →ₐ[F] T)
    (hS : ∀ s, η (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T) s)
      = η' (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T) s))
    (hT : ∀ t, η (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T) t)
      = η' (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T) t)) : η = η' := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      rw [show (a ⊗ₜ[F] b : ST F r n T)
          = Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T) a
            * Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T) b from by
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
        simp]
      rw [map_mul, map_mul, hS a, hT b]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

#print axioms algHom_ext_tensor

end EtaExt2

/-! ## §23 张量扩张层（4）：**链接 `η_1' = η_2' ∘ Φ_A` 机检**

原文（`raw/Saltman1999ch14.tex:318`）："It follows that `η_1' = η_2' ∘ φ_A`"。
本轮把它机检（以 `S` 层的比较 `hlink` 为假设——`hlink` 本身来自在通用矩阵 `X_k` 上的比较，
那是下一轮的对象）。

四个逐点引理把 §19／§21 的同态层交换三角降到逐点形式；`etaExt_eq_comp_phiExt` 用
`algHom_ext_tensor`（`S'` 由两因子生成）把 `S` 侧与 `T` 侧的相等升到全 `S'`。 -/

section Pointwise

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- 逐点：`η_r'` 在 `S` 侧的值就是 `η_r`。 -/
lemma etaExt_incL (η : S F r n →ₐ[F] T) (s : S F r n) :
    etaExt F r n T η
      (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T) s)
      = η s := by
  simpa using AlgHom.congr_fun (etaExt_comp_includeLeft F r n T η) s

#print axioms etaExt_incL

/-- 逐点：`η_r'` 在 `T` 侧恒等。 -/
lemma etaExt_incR (η : S F r n →ₐ[F] T) (t : T) :
    etaExt F r n T η
      (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T) t) = t := by
  simpa using AlgHom.congr_fun (etaExt_comp_includeRight F r n T η) t

#print axioms etaExt_incR

/-- 逐点：`Φ_A` 在 `S` 侧就是 `φ_A`。 -/
lemma phiExt_incL (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) (s : S F r n) :
    phiExt F r n T A
      (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T) s)
      = phiAR F r n (ST F r n T) A s := by
  simpa using AlgHom.congr_fun (phiExt_comp_includeLeft F r n T A) s

#print axioms phiExt_incL

/-- 逐点：`Φ_A` 在 `T` 侧恒等。 -/
lemma phiExt_incR (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) (t : T) :
    phiExt F r n T A
      (Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T) t)
      = Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T) t := by
  simpa using AlgHom.congr_fun (phiExt_comp_includeRight F r n T A) t

#print axioms phiExt_incR

/-- ★★★★★ **链接 `η_1' = η_2' ∘ Φ_A`**。

`S` 侧用假设 `hlink`（原文由 `X_k` 比较得出），`T` 侧两边都恒等；
`algHom_ext_tensor` 把两侧的相等升到全 `S' = S ⊗_F T`。 -/
theorem etaExt_eq_comp_phiExt [Infinite F]
    (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ)
    (η₁ η₂ : S F r n →ₐ[F] T)
    (hlink : ∀ q : S F r n, η₁ q = etaExt F r n T η₂ (phiAR F r n (ST F r n T) A q)) :
    etaExt F r n T η₁ = (etaExt F r n T η₂).comp (phiExt F r n T A) := by
  apply algHom_ext_tensor F r n T
  · intro s
    rw [AlgHom.comp_apply, phiExt_incL, etaExt_incL]
    exact hlink s
  · intro t
    rw [AlgHom.comp_apply, phiExt_incR, etaExt_incR, etaExt_incR]

#print axioms etaExt_eq_comp_phiExt

end Pointwise

/-! ## §24 由通用矩阵 `X_k` 的比较导出 `hlink`

原文（`raw/Saltman1999ch14.tex:316–318`）：
> Thus `M_n(η_1')(X_k) = θ_1'(X_k) = θ_2'(X_k) = M_n(η_2')(A⁻¹X_kA) = M_n(η_2')M_n(φ_A)(X_k)`.
> It follows that `η_1' = η_2' ∘ φ_A`.

`S = F[x_{ijk}]` 由 `X_k` 的**条目**生成，故在生成元上相等即在全 `S` 上相等
（`MvPolynomial.ringHom_ext`，`C` 支由两边都是 `F`-代数映射处理）。本节机检这一步：
由 `hX : ∀ k i j, η₁(X_{kij}) = η₂'(φ_A(X_{kij}))` 得 `hlink : ∀ q, η₁ q = η₂'(φ_A q)`，
再与 §23 合起来即得链接 `η_1' = η_2' ∘ Φ_A`。 -/

section FromX

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★ **由 `X_k` 上的比较导出 `hlink`**（`S` 由通用矩阵的条目生成）。 -/
theorem hlink_of_X [Infinite F]
    (A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ)
    (η₁ η₂ : S F r n →ₐ[F] T)
    (hX : ∀ (k : Fin r) (i j : Fin n),
      η₁ (MvPolynomial.X (k, i, j))
        = etaExt F r n T η₂ (phiAR F r n (ST F r n T) A (MvPolynomial.X (k, i, j)))) :
    ∀ q : S F r n, η₁ q = etaExt F r n T η₂ (phiAR F r n (ST F r n T) A q) := by
  have hcomp : (η₁ : S F r n →+* T)
      = (etaExt F r n T η₂).toRingHom.comp (phiAR F r n (ST F r n T) A).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show η₁ (algebraMap F (S F r n) c)
        = (etaExt F r n T η₂) ((phiAR F r n (ST F r n T) A) (algebraMap F (S F r n) c))
      rw [η₁.commutes]
      rw [(phiAR F r n (ST F r n T) A).commutes]
      exact ((etaExt F r n T η₂).commutes c).symm
    · intro m
      rcases m with ⟨k, i, j⟩
      exact hX k i j
  intro q
  have h := congrArg (fun f : S F r n →+* T => f q) hcomp
  simpa using h

#print axioms hlink_of_X

end FromX

/-! ### `thm:14.15` 剩余的最后一块（下一轮）

1. `thetaExt η := (etaExt η).mapMatrix : M_n(S') →+* M_n(T)`（扩张的 `θ_r'`）；
   由 §22 的 `map_etaExt_includeLeft` 得 `θ_r'(β.map algMap) = θ_r(β)`（原文首尾两步）。
2. 共轭的 `Θ₂ := fun M => A'⁻¹ * (thetaExt η₂) M * A'`（原文 `θ_2'(β) = A⁻¹M_n(η_2')(β)A`）。
3. 由 §18 的 `map_conj_of_fixed`（`η₂'` 固定 `A'` 的条目，来自 §19 的 `T` 侧恒等）
   得 `Θ₂(ψ_A(β)) = η₁.mapMatrix β = Θ₁(β.map algMap)`，即 §20 的假设 `h`。
4. 用 §20 的 `thm1415_lastStep` 收口。 -/

/-! ## §25 `thm:14.15` 最后装配（1）：`θ_r' := M_n(η_r')` 与 `A` 的升格

原文最后两段需要两个对象，本节把它们机检：

* **`θ_r' := M_n(η_r')`**（`M_n(S') →+* M_n(T)`，由 §19 的 `η_r'` 诱导）及其**扩张性质**
  `θ_r'(β.map algMap) = θ_r(β)`——即原文首尾两步 "`θ_r'(α) = θ_r(α)`"；
* **`A` 从 `GL_n(T)` 升格到 `GL_n(S')`**（`unitMapST`，沿 `T ↪ S'`）：`φ_A` 要求 `A` 落在
  `S` 的代数里，而 `2.11` 只给 `A ∈ GL_n(T)`，故必须升格。

**下一轮**：`θ_2'(ψ_A(β)) = A·M_n(η_1)(β)·A⁻¹`（本轮探针已成型，差类型对齐）＋ §20 收口。 -/

section Assembly

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★ **`θ_r' := M_n(η_r')`**：把 `M_n(S)` 上的同态扩张到 `M_n(S')`。 -/
noncomputable def thetaExt (η : S F r n →ₐ[F] T) :
    Matrix (Fin n) (Fin n) (ST F r n T) →+* Matrix (Fin n) (Fin n) T :=
  (etaExt F r n T η).toRingHom.mapMatrix

/-- ★★★ **扩张性质**：`θ_r'` 在 `M_n(S)` 的自然像上就是 `θ_r := M_n(η_r)`
（原文首尾两步 `θ_r'(α) = θ_r(α)`）。 -/
lemma thetaExt_includeLeft (η : S F r n →ₐ[F] T) (β : Matrix (Fin n) (Fin n) (S F r n)) :
    thetaExt F r n T η (β.map (algebraMap (S F r n) (ST F r n T))) = β.map η := by
  rw [thetaExt, RingHom.mapMatrix_apply]
  exact map_etaExt_includeLeft F r n T η β

#print axioms thetaExt_includeLeft

/-- ★★ **`A ∈ GL_n(T)` 沿 `T ↪ S'` 升格为 `GL_n(S')` 的元**（`φ_A` 要的 `A` 落在 `S'` 的代数里）。 -/
noncomputable def unitMapST (A : (Matrix (Fin n) (Fin n) T)ˣ) :
    (Matrix (Fin n) (Fin n) (ST F r n T))ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T)).toRingHom).mapMatrix.toMonoidHom A

/-- ★ `unitMapST` 的底层矩阵就是逐条目升格。 -/
lemma unitMapST_val (A : (Matrix (Fin n) (Fin n) T)ˣ) :
    ((unitMapST F r n T A : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
        Matrix (Fin n) (Fin n) (ST F r n T))
      = (A : Matrix (Fin n) (Fin n) T).map
          ((Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T)).toRingHom) := rfl

#print axioms unitMapST_val

end Assembly

/-! ### `T ↪ S'` **不是 `Algebra` 实例**（本轮实测）

`ST F r n T = TensorProduct F (S F r n) T` **没有** `Algebra T (ST F r n T)` 实例
（tensor 是 over `F` 的），故 `algebraMap T (ST F r n T)` **不可用**；
必须显式写 `(Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T)).toRingHom`。
同理 `⇑(etaExt η).toRingHom` 与 `⇑(etaExt η)` 在 `Matrix.map` 里**不能互相 `rw` 匹配**，
需在陈述里统一用同一种写法（本轮统一到 `.toRingHom`）。 -/

/-! ## §26 **`thm:14.15` 收口**：`A · θ_1(α) · A⁻¹ = θ_2(α)`（论证层完成）

本节把 `thm:14.15` 的**数学内容**机检完毕（"after 2.11" 的形式）：
原文证明在引用 `[saltman1999lectures, 2.11]` 之后剩下的全部推理，即

> `θ_1' = θ_2' ∘ ψ_A`，再由 `prop:14.14` 得 `θ_1(α) = θ_2(α)`。

两块：
* `thetaExt_psiAR`：`θ_2'(ψ_A(β)) = A · M_n(η_1)(β) · A⁻¹`（原文 "`θ_2'ψ_A(β) = M_n(η_1')(β)`"）；
* `thm1415_assembly`：**`A · θ_1(α) · A⁻¹ = θ_2(α)`** 对一切 `α ∈ M_n(S)^{PGL}`。

**射程（如实登记）**：本节的假设 `hlink`（`η_1 = η_2' ∘ φ_A` 在 `S` 上）由 §24 的
`hlink_of_X` 从"在 `X_k` 上相等"推出；而"`θ_1, θ_2` 分别等于 `M_n(η_1)` 与 `A⁻¹M_n(η_2)A`"
即 `2.11`（S5，第 149／152 轮已机检）＋ §10 的分类（第 160 轮已机检）。
**把这三块粘成原文口径的单一命题**（含 `T` 局部的归约）尚未做。 -/

section Psi

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★ **`θ_2'(ψ_A(β)) = A · M_n(η_1)(β) · A⁻¹`**（原文 `θ_2'ψ_A(β) = M_n(η_1')(β)`）。 -/
theorem thetaExt_psiAR [Infinite F]
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (η₁ η₂ : S F r n →ₐ[F] T)
    (hlink : ∀ q : S F r n,
      η₁ q = etaExt F r n T η₂ (phiAR F r n (ST F r n T) (unitMapST F r n T AT) q))
    (β : Matrix (Fin n) (Fin n) (S F r n)) :
    thetaExt F r n T η₂ (psiAR F r n (ST F r n T) (unitMapST F r n T AT) β)
      = (AT : Matrix (Fin n) (Fin n) T) * (β.map η₁)
        * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by
  set e := (etaExt F r n T η₂).toRingHom with he
  set AS := (unitMapST F r n T AT : Matrix (Fin n) (Fin n) (ST F r n T)) with hAS
  have hST : (⇑e ∘ ⇑((Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T)).toRingHom))
      = id := by
    funext t
    exact etaExt_incR F r n T η₂ t
  have hAe : AS.map ⇑e = (AT : Matrix (Fin n) (Fin n) T) := by
    rw [hAS, unitMapST_val, Matrix.map_map, hST, Matrix.map_id]
  have hAie : ((((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
      Matrix (Fin n) (Fin n) (ST F r n T))).map ⇑e
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by
    have hU : Units.map e.mapMatrix.toMonoidHom (unitMapST F r n T AT) = AT := by
      apply Units.ext
      rw [Units.coe_map]
      exact hAe
    calc (((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
          Matrix (Fin n) (Fin n) (ST F r n T)).map ⇑e
        = ((Units.map e.mapMatrix.toMonoidHom ((unitMapST F r n T AT)⁻¹) :
            (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) := rfl
      _ = (((Units.map e.mapMatrix.toMonoidHom (unitMapST F r n T AT))⁻¹ :
            (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) := by rw [map_inv]
      _ = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by rw [hU]
  have hX : (β.map (phiAR F r n (ST F r n T) (unitMapST F r n T AT))).map ⇑e = β.map η₁ := by
    rw [Matrix.map_map]
    congr 1
    funext q
    exact (hlink q).symm
  calc thetaExt F r n T η₂ (psiAR F r n (ST F r n T) (unitMapST F r n T AT) β)
      = e.mapMatrix (AS * (β.map (phiAR F r n (ST F r n T) (unitMapST F r n T AT)))
          * (((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
              Matrix (Fin n) (Fin n) (ST F r n T))) := rfl
    _ = e.mapMatrix AS * e.mapMatrix (β.map (phiAR F r n (ST F r n T) (unitMapST F r n T AT)))
          * e.mapMatrix (((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
              Matrix (Fin n) (Fin n) (ST F r n T)) := by rw [map_mul, map_mul]
    _ = (AT : Matrix (Fin n) (Fin n) T) * (β.map η₁)
          * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by
        rw [show e.mapMatrix AS = AS.map ⇑e from rfl, hAe,
          show e.mapMatrix (β.map (phiAR F r n (ST F r n T) (unitMapST F r n T AT)))
            = (β.map (phiAR F r n (ST F r n T) (unitMapST F r n T AT))).map ⇑e from rfl, hX,
          show e.mapMatrix (((unitMapST F r n T AT)⁻¹ :
              (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) : Matrix (Fin n) (Fin n) (ST F r n T))
            = (((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
              Matrix (Fin n) (Fin n) (ST F r n T)).map ⇑e from rfl, hAie]

#print axioms thetaExt_psiAR

/-- ★★★★★ **Saltman `thm:14.15` 收口**（"after 2.11" 的形式）：
`A · θ_1(α) · A⁻¹ = θ_2(α)` 对一切 `α ∈ M_n(S)^{PGL_n(F)}`。

**其余部分**：`2.11` 把 `θ_1, θ_2` 化为 `M_n(η_1)` 与 `A⁻¹M_n(η_2)A`（S5 ＋ §10）；
`hlink` 由 §24 从 `X_k` 上的比较得出。本定理是二者之后剩下的全部推理，
其中 `prop:14.14(b)`（第 157 轮）是最后一步。 -/
theorem thm1415_assembly [Infinite F]
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (η₁ η₂ : S F r n →ₐ[F] T)
    (hlink : ∀ q : S F r n,
      η₁ q = etaExt F r n T η₂ (phiAR F r n (ST F r n T) (unitMapST F r n T AT) q))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    (AT : Matrix (Fin n) (Fin n) T) * (α.map η₁)
        * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = α.map η₂ := by
  rw [← thetaExt_psiAR F r n T AT η₁ η₂ hlink α,
    psiAR_of_pgl_invariant F r n α hα (ST F r n T) (unitMapST F r n T AT)]
  exact thetaExt_includeLeft F r n T η₂ α

#print axioms thm1415_assembly

end Psi

/-! ## §27 粘合 `thm:14.15` 所需的消去引理

§26 的 `thm1415_assembly` 给出的结论是 `A·θ₁(α)·A⁻¹ = θ₂^A(α)`；而原文口径的结论是
`θ₁(α) = θ₂(α)`（其中 `θ₂ = A⁻¹ M_n(η₂) A`）。把两者互换需要**共轭的消去**：

* `inv_mul_conj_mul`：`A⁻¹(A X A⁻¹)A = X`；
* `eq_of_conj_eq`：`A X A⁻¹ = A Y A⁻¹ ⟹ X = Y`。

这两条是纯矩阵代数，与 `thm:14.15` 的数学无关，但缺了它们就无法把 §26 的结论写成原文口径。 -/

section Glue

variable {T : Type} [CommRing T] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★ **共轭的消去**：`A⁻¹(A X A⁻¹)A = X`。 -/
lemma inv_mul_conj_mul (A : (Matrix n n T)ˣ) (X : Matrix n n T) :
    (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
        * (((A : (Matrix n n T)ˣ) : Matrix n n T) * X
          * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)))
        * (((A : (Matrix n n T)ˣ) : Matrix n n T)) = X := by
  calc (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
        * (((A : (Matrix n n T)ˣ) : Matrix n n T) * X
          * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)))
        * (((A : (Matrix n n T)ˣ) : Matrix n n T))
      = (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
          * ((((A : (Matrix n n T)ˣ) : Matrix n n T) * X
            * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)))
            * (((A : (Matrix n n T)ˣ) : Matrix n n T))) := mul_assoc _ _ _
    _ = (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
          * ((((A : (Matrix n n T)ˣ) : Matrix n n T) * X)
            * ((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
              * (((A : (Matrix n n T)ˣ) : Matrix n n T)))) := by
          rw [mul_assoc (((A : (Matrix n n T)ˣ) : Matrix n n T) * X)
            (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) (((A : (Matrix n n T)ˣ) : Matrix n n T))]
    _ = (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
          * ((((A : (Matrix n n T)ˣ) : Matrix n n T) * X) * 1) := by rw [Units.inv_mul]
    _ = (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
          * (((A : (Matrix n n T)ˣ) : Matrix n n T) * X) := by rw [mul_one]
    _ = ((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
          * (((A : (Matrix n n T)ˣ) : Matrix n n T))) * X := (mul_assoc _ _ _).symm
    _ = 1 * X := by rw [Units.inv_mul]
    _ = X := one_mul X

#print axioms inv_mul_conj_mul

/-- ★★★ **共轭相等 ⟹ 相等**。 -/
lemma eq_of_conj_eq (A : (Matrix n n T)ˣ) {X Y : Matrix n n T}
    (h : ((A : (Matrix n n T)ˣ) : Matrix n n T) * X
        * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
      = ((A : (Matrix n n T)ˣ) : Matrix n n T) * Y
        * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))) : X = Y := by
  rw [← inv_mul_conj_mul A X, ← inv_mul_conj_mul A Y, h]

#print axioms eq_of_conj_eq

end Glue

/-! ## §28 `thm:14.15` 的**原文口径**：`θ₁(α) = θ₂(α)`

原文的结论是 `θ₁(α) = θ₂(α)`，其中 `θ₁ = M_n(η_1)`、`θ₂ = A⁻¹ M_n(η_2) A`
（原文 "`θ₂^A(β) = A θ₂(β) A⁻¹` 且 `θ₂^A = M_n(η_2)`" 的读法）。
§26 给的是对偶形式 `A θ₁(α) A⁻¹ = θ₂^A(α)`；本节用消去把它换成原文形状。

* `mul_inv_conj_mul`：`A(A⁻¹ X A)A⁻¹ = X`（`inv_mul_conj_mul` 的对偶，§27）；
* `thm1415_source_shape`：**`α.map η₁ = A⁻¹ · (α.map η₂) · A`** ——即 `θ₁(α) = θ₂(α)`。 -/

section Dual

variable {T : Type} [CommRing T] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★ **反方向共轭的消去**：`A(A⁻¹ X A)A⁻¹ = X`。 -/
lemma mul_inv_conj_mul (A : (Matrix n n T)ˣ) (X : Matrix n n T) :
    (((A : (Matrix n n T)ˣ) : Matrix n n T))
        * ((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X
          * (((A : (Matrix n n T)ˣ) : Matrix n n T)))
        * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) = X := by
  calc (((A : (Matrix n n T)ˣ) : Matrix n n T))
        * ((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X
          * (((A : (Matrix n n T)ˣ) : Matrix n n T)))
        * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
      = (((A : (Matrix n n T)ˣ) : Matrix n n T))
          * (((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X
            * (((A : (Matrix n n T)ˣ) : Matrix n n T)))
            * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))) := mul_assoc _ _ _
    _ = (((A : (Matrix n n T)ˣ) : Matrix n n T))
          * (((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X)
            * ((((A : (Matrix n n T)ˣ) : Matrix n n T))
              * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)))) := by
          rw [mul_assoc ((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X)
            (((A : (Matrix n n T)ˣ) : Matrix n n T)) (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))]
    _ = (((A : (Matrix n n T)ˣ) : Matrix n n T))
          * (((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X) * 1) := by rw [Units.mul_inv]
    _ = (((A : (Matrix n n T)ˣ) : Matrix n n T))
          * ((((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) * X) := by rw [mul_one]
    _ = ((((A : (Matrix n n T)ˣ) : Matrix n n T))
          * (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))) * X := (mul_assoc _ _ _).symm
    _ = 1 * X := by rw [Units.mul_inv]
    _ = X := one_mul X

#print axioms mul_inv_conj_mul

end Dual

section Shape

variable (F : Type) [Field F] [Infinite F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★ **`thm:14.15` 的原文口径**：`θ₁(α) = θ₂(α)`（`θ₁ = M_n(η_1)`、`θ₂ = A⁻¹M_n(η_2)A`）。 -/
theorem thm1415_source_shape
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (η₁ η₂ : S F r n →ₐ[F] T)
    (hlink : ∀ q : S F r n,
      η₁ q = etaExt F r n T η₂ (phiAR F r n (ST F r n T) (unitMapST F r n T AT) q))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    α.map η₁
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (α.map η₂)
        * ((AT : Matrix (Fin n) (Fin n) T)) := by
  rw [← thm1415_assembly F r n T AT η₁ η₂ hlink α hα, inv_mul_conj_mul]

#print axioms thm1415_source_shape

end Shape

/-! ## §29 粘合（ⓐ）的第一件：**共轭的环自同构** `M ↦ A M A⁻¹`

`thm:14.15` 的"粘合"要用 §10 的分类两次。第二次的对象是**共轭后的** `θ_2^A =
A θ₂ A⁻¹`（原文 "`θ₂^A(β) = A θ₂(β) A⁻¹`"），它保标准矩阵单位，故可套 §10；
但 §10 要求 `RingHom`，所以须先把 `M ↦ A M A⁻¹` 做成**环自同构**。

* `conj_mul_matrix`：共轭的乘法性 `(AMA⁻¹)(ANA⁻¹) = A(MN)A⁻¹`；
* **`conjRingEquiv`**：`Matrix n n T ≃+* Matrix n n T`，`M ↦ A M A⁻¹`
  （`left_inv`／`right_inv` 直接用 §27／§28 已机检的消去引理）。 -/

section ConjEquiv

variable {T : Type} [CommRing T] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★ **共轭的乘法性**：`(A M A⁻¹)(A N A⁻¹) = A (M N) A⁻¹`。 -/
lemma conj_mul_matrix (A : (Matrix n n T)ˣ) (M N : Matrix n n T) :
    ((A : Matrix n n T) * M * ((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
        * ((A : Matrix n n T) * N * ((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T))
      = (A : Matrix n n T) * (M * N) * ((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) := by
  rw [mul_assoc ((A : Matrix n n T) * M),
    ← mul_assoc (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) ((A : Matrix n n T) * N)
      (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)),
    ← mul_assoc (((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)) (A : Matrix n n T) N,
    Units.inv_mul, one_mul]
  noncomm_ring

#print axioms conj_mul_matrix

/-- ★★★ **共轭的环自同构** `M ↦ A M A⁻¹`（`Matrix n n T ≃+* Matrix n n T`）。 -/
noncomputable def conjRingEquiv (A : (Matrix n n T)ˣ) : Matrix n n T ≃+* Matrix n n T where
  toFun M := (A : Matrix n n T) * M * ((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)
  invFun M := ((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T) * M * (A : Matrix n n T)
  left_inv M := inv_mul_conj_mul A M
  right_inv M := mul_inv_conj_mul A M
  map_mul' M N := (conj_mul_matrix A M N).symm
  map_add' M N := by
    simp only [mul_add, add_mul]

#print axioms conjRingEquiv

end ConjEquiv

/-! ## §30 **`thm:14.15` 收口形态**：假设取原文口径，结论为 `θ₁(α) = θ₂(α)`

本节把 §24 与 §28 接起来，给出**假设形状最接近原文**的单一命题：
原文的假设是"`θ_1, θ_2` 在 `R(F,n,r)` 上相等"；`R(F,n,r)` 由通用矩阵 `X_k` 生成
（`lem:14.12`（第 115–134 轮）正是关于 `R(F,n,r)` 与 `PGL` 的），
故取"在 `X_k` 的**条目**上一致"为假设。

**链路**：`hX` →（§24 `hlink_of_X`）`hlink` →（§28 `thm1415_source_shape`）结论。

**射程（如实登记）**：`θ_1 = M_n(η_1)`、`θ_2 = A⁻¹M_n(η_2)A` 仍为**假设**
（即 `2.11` ＋ §10 分类的合成），`T` 局部的归约仍未做。 -/

section Capstone

variable (F : Type) [Field F] [Infinite F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★ **`thm:14.15` 收口形态**：若 `θ₁, θ₂` 在通用矩阵 `X_k` 的条目上一致，
则 `θ₁(α) = θ₂(α)` 对一切 `PGL_n(F)`-不变元 `α` 成立。 -/
theorem thm1415_capstone
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (η₁ η₂ : S F r n →ₐ[F] T)
    (hX : ∀ (k : Fin r) (i j : Fin n),
      η₁ (MvPolynomial.X (k, i, j))
        = etaExt F r n T η₂ (phiAR F r n (ST F r n T) (unitMapST F r n T AT)
            (MvPolynomial.X (k, i, j))))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    α.map η₁
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (α.map η₂)
        * ((AT : Matrix (Fin n) (Fin n) T)) :=
  thm1415_source_shape F r n T AT η₁ η₂
    (hlink_of_X F r n T (unitMapST F r n T AT) η₁ η₂ hX) α hα

#print axioms thm1415_capstone

end Capstone

/-! ## §31 共轭的 **`F`-代数**自同构 `M ↦ A M A⁻¹`

§29 给的是**环**自同构 `conjRingEquiv`；粘合要套 §12 的 **`AlgHom` 版**分类，
所以需要 `F`-代数版。本节补上 `conjAlgEquiv : Matrix n n T ≃ₐ[F] Matrix n n T`。

另：`GenericInv.lean` 现 **import `Procesi.MatrixUnits`**（粘合需要 §12 的
`exists_algHom_of_preserves_stdMU`）；依赖无环（`MatrixUnits` 不引用 `GenericInv`）。 -/

section ConjAlg

variable {F : Type} [Field F] {T : Type} [CommRing T] [Algebra F T]
  {n : Type} [Fintype n] [DecidableEq n]

/-- ★★★ **共轭的 `F`-代数自同构** `M ↦ A M A⁻¹`（`Matrix n n T ≃ₐ[F] Matrix n n T`）。 -/
noncomputable def conjAlgEquiv (A : (Matrix n n T)ˣ) : Matrix n n T ≃ₐ[F] Matrix n n T where
  __ := conjRingEquiv A
  commutes' c := by
    have h1 : (algebraMap F (Matrix n n T) c) = (algebraMap F T c) • (1 : Matrix n n T) := by
      simp [Algebra.algebraMap_eq_smul_one]
    show (A : Matrix n n T) * (algebraMap F (Matrix n n T) c) * ((A⁻¹ : (Matrix n n T)ˣ) : Matrix n n T)
      = algebraMap F (Matrix n n T) c
    rw [h1, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.mul_inv]

#print axioms conjAlgEquiv

end ConjAlg

/-! ### 粘合第 2 步（§12 两次实例化）的**卡点**（第 177 轮实测，未完成）

`thm1415_glue` 的形状已定：给定 `θ₁ θ₂ : M_n(S) →ₐ[F] M_n(T)` 与
`h₁ : θ₁(e_ij) = e_ij`、`h₂ : θ₂(e_ij) = A⁻¹e_ijA`，产出 `η₁ η₂ : S →ₐ[F] T` 使
`θ₁ β = β.map η₁`、`A·θ₂β·A⁻¹ = β.map η₂`。第二次用 `conjAlgEquiv AT` 把 `θ₂` 共轭成保标准单位的映射。

**卡点**：`exists_algHom_of_preserves_stdMU (F := F) θ₁ h₁` 之后，第二次调用处
报 `typeclass instance problem is stuck: Algebra ?m T`——**基域元变量未定**。
下一步应把 `R`／`R'` 也显式钉住
（`(R := S F r n) (R' := T)`），或把该引理的 `[Algebra F R']` 改成
`[Algebra R' …]`-无关的形式。**这不是数学问题**（按 R60／R69 同族：隐式参数未定）。 -/

/-! ## §32 分类的**特化版**（硬编码 `R = S F r n`、`R' = T`）

`thm:14.15` 的"粘合"要两次调用分类。实测发现：**泛型版**在 `theorem` 内的 `have`
里调用时报 `typeclass instance problem is stuck: Algebra ?m T`（基域元变量未定），
而**把 `R`、`R'` 硬编码**的特化版可以正常**定义**（本节 `_spec`）。

故本节给出特化版，作为粘合的垫脚石；粘合本体仍卡在同一处
（`have h1' : ∃ η : S F r n →ₐ[F] T, … := _spec …` 仍 stuck），
见交接件 §12 的诊断与四步建议。 -/

section Spec

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★ **分类的特化版**：`R = S F r n`、`R' = T` 硬编码，避开隐式参数推断。 -/
theorem exists_algHom_of_preserves_stdMU_spec [Nonempty (Fin n)]
    (θ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hθ : ∀ i j, θ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)) :
    ∃ η : S F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (S F r n), θ β = β.map η :=
  exists_algHom_of_preserves_stdMU (F := F) (R := S F r n) (R' := T) (n := Fin n) θ hθ

#print axioms exists_algHom_of_preserves_stdMU_spec

end Spec

/-! ## §33 **粘合（ⓐ）第 2 步完成**：两次实例化分类，产出 `η₁, η₂`

**根因（第 181 轮找到）**：`conjAlgEquiv AT` 的 **`F` 是自由元变量**（`A : (Matrix n n T)ˣ`
不含 `F`），故在 `by` 块里调用时空出 `Algebra ?m T` 的 obligation 而报 `stuck`。
**修法**：写 `conjAlgEquiv (F := F) AT`。这与 R60／R69／R75 同族——
**隐式参数不钉住就报 stuck**，而报错信息（`Algebra ?m T`）指向的是**下游**实例，不是真凶。

三步结构：
* `exists_eta1_std`：`θ₁` 保标准矩阵单位 ⟹ `θ₁ = M_n(η₁)`（§12／§32）；
* `exists_eta2_conj`：`θ₂^A = A θ₂ A⁻¹` 保标准矩阵单位 ⟹ `θ₂^A = M_n(η₂)`（§31 ＋ §12）；
* `thm1415_glue`：两次 `obtain` 拼接。 -/

section Glue

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- 第一步：`θ₁` 保标准矩阵单位 ⟹ `θ₁ = M_n(η₁)`。 -/
theorem exists_eta1_std [Nonempty (Fin n)]
    (θ₁ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ i j, θ₁ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)) :
    ∃ η₁ : S F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (S F r n), θ₁ β = β.map η₁ :=
  exists_algHom_of_preserves_stdMU_spec F r n T θ₁ h₁

#print axioms exists_eta1_std

/-- 第二步：`θ₂^A = A θ₂ A⁻¹` 保标准矩阵单位 ⟹ `θ₂^A = M_n(η₂)`。 -/
theorem exists_eta2_conj [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
        * (AT : Matrix (Fin n) (Fin n) T)) :
    ∃ η₂ : S F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (S F r n),
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
    exact mul_inv_conj_mul AT (stdMU (n := Fin n) i j)
  exact exists_algHom_of_preserves_stdMU_spec F r n T
    ((conjAlgEquiv (F := F) AT).toAlgHom.comp θ₂) h₂A

#print axioms exists_eta2_conj

/-- ★★★★★ **粘合（ⓐ）第 2 步完成**：两次实例化分类，**产出** `η₁, η₂`。 -/
theorem thm1415_glue [Nonempty (Fin n)]
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (h₁ : ∀ i j, θ₁ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T))
    (h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
        * (AT : Matrix (Fin n) (Fin n) T)) :
    ∃ η₁ η₂ : S F r n →ₐ[F] T,
      (∀ β : Matrix (Fin n) (Fin n) (S F r n), θ₁ β = β.map η₁) ∧
      (∀ β : Matrix (Fin n) (Fin n) (S F r n),
        (AT : Matrix (Fin n) (Fin n) T) * θ₂ β
          * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) = β.map η₂) := by
  obtain ⟨η₁, hη₁⟩ := exists_eta1_std F r n T θ₁ h₁
  obtain ⟨η₂, hη₂⟩ := exists_eta2_conj F r n T θ₂ AT h₂
  exact ⟨η₁, η₂, hη₁, hη₂⟩

#print axioms thm1415_glue

end Glue

/-! ## §34 粘合第 3 步（上）：**条目级桥** `etaExt η(φ_A(x_{kij})) = (A⁻¹·(X_k.map η)·A)_{ij}`

原文最后一段的比较发生在 `X_k` 的**条目**上。要把"`θ₁(X_k) = θ₂(X_k)`"翻译成
"`η₁ = η₂' ∘ φ_A` 在 `S` 上"（§24 的 `hlink`），需要这条**条目级**恒等式。

五条，逐层下降：
* `map_unitMapST`／`map_unitMapST_inv`：`η'` 把 `A`（及其逆）的升格映回 `AT`（及其逆）；
* 两条**条目形式**（`AlgHom` 强制转换写法，见 R85：`⇑(etaExt η).toRingHom` 与 `⇑(etaExt η)`
  在 `simp` 里**不能互相匹配**，故逐点引理须与目标的写法一致）；
* `etaExt_phiAR_entry`：本体——用 `phiGenR` 展开 ＋ 两次 `Matrix.mul_apply` ＋
  `map_sum`／`map_mul` ＋ 上面四条 ＋ `hgen`（`etaExt η` 在 `genMatR` 上的值）。 -/

section Bridge

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

lemma map_unitMapST (η : S F r n →ₐ[F] T) (AT : (Matrix (Fin n) (Fin n) T)ˣ) :
    ((unitMapST F r n T AT : Matrix (Fin n) (Fin n) (ST F r n T))).map
        ⇑(etaExt F r n T η).toRingHom
      = (AT : Matrix (Fin n) (Fin n) T) := by
  have hST : (⇑(etaExt F r n T η).toRingHom ∘
      ⇑((Algebra.TensorProduct.includeRight (R := F) (A := S F r n) (B := T)).toRingHom)) = id := by
    funext t
    exact etaExt_incR F r n T η t
  rw [unitMapST_val, Matrix.map_map, hST, Matrix.map_id]

lemma map_unitMapST_inv (η : S F r n →ₐ[F] T) (AT : (Matrix (Fin n) (Fin n) T)ˣ) :
    (((((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ)) :
        Matrix (Fin n) (Fin n) (ST F r n T))).map ⇑(etaExt F r n T η).toRingHom
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by
  have hU : Units.map ((etaExt F r n T η).mapMatrix).toMonoidHom (unitMapST F r n T AT) = AT :=
    Units.ext (map_unitMapST F r n T η AT)
  calc ((((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ)) :
        Matrix (Fin n) (Fin n) (ST F r n T)).map ⇑(etaExt F r n T η).toRingHom
      = ((Units.map ((etaExt F r n T η).mapMatrix).toMonoidHom
          ((unitMapST F r n T AT)⁻¹) : (Matrix (Fin n) (Fin n) T)ˣ) :
            Matrix (Fin n) (Fin n) T) := rfl
    _ = (((Units.map ((etaExt F r n T η).mapMatrix).toMonoidHom
          (unitMapST F r n T AT))⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) :
            Matrix (Fin n) (Fin n) T) := by rw [map_inv]
    _ = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) := by rw [hU]

lemma map_unitMapST_apply (η : S F r n →ₐ[F] T) (AT : (Matrix (Fin n) (Fin n) T)ˣ) (i j : Fin n) :
    (etaExt F r n T η)
        ((unitMapST F r n T AT : Matrix (Fin n) (Fin n) (ST F r n T)) i j)
      = (AT : Matrix (Fin n) (Fin n) T) i j := by
  have h := congrFun (congrFun (map_unitMapST F r n T η AT) i) j
  simpa [Matrix.map_apply] using h

lemma map_unitMapST_inv_apply (η : S F r n →ₐ[F] T) (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (i j : Fin n) :
    (etaExt F r n T η)
        ((((unitMapST F r n T AT)⁻¹ : (Matrix (Fin n) (Fin n) (ST F r n T))ˣ) :
          Matrix (Fin n) (Fin n) (ST F r n T)) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) i j := by
  have h := congrFun (congrFun (map_unitMapST_inv F r n T η AT) i) j
  simpa [Matrix.map_apply] using h

/-- ★★★ **条目级桥**：`etaExt η(φ_A(x_{kij})) = (A⁻¹ · (X_k.map η) · A)_{ij}`。 -/
lemma etaExt_phiAR_entry (AT : (Matrix (Fin n) (Fin n) T)ˣ) (η : S F r n →ₐ[F] T)
    (k : Fin r) (i j : Fin n) :
    etaExt F r n T η
        (phiAR F r n (ST F r n T) (unitMapST F r n T AT) (MvPolynomial.X (k, i, j)))
      = ((((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * ((genericMatrix F r n k).map (⇑η))
          * (AT : Matrix (Fin n) (Fin n) T)) i j := by
  set e := (etaExt F r n T η).toRingHom with he
  have he2 : ⇑e = ⇑(etaExt F r n T η) := rfl
  have hgen : ∀ a b, (etaExt F r n T η) (genMatR F r n (ST F r n T) k a b)
      = η ((genericMatrix F r n k) a b) := by
    intro a b
    have h1 : (algebraMap (S F r n) (ST F r n T))
        = ⇑(Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := S F r n) (B := T)) := rfl
    rw [genMatR, Matrix.of_apply, h1]
    exact etaExt_incL F r n T η (MvPolynomial.X (k, a, b))
  rw [show phiAR F r n (ST F r n T) (unitMapST F r n T AT) (MvPolynomial.X (k, i, j))
      = phiGenR F r n (ST F r n T) (unitMapST F r n T AT) ⟨k, i, j⟩ from
    MvPolynomial.aeval_X _ _]
  rw [phiGenR, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  simp only [map_sum, map_mul, Matrix.mul_apply, Matrix.map_apply,
    map_unitMapST_apply F r n T η AT, map_unitMapST_inv_apply F r n T η AT, hgen]

#print axioms map_unitMapST
#print axioms map_unitMapST_inv
#print axioms etaExt_phiAR_entry

end Bridge

/-! ## §35 **`thm:14.15` 完全粘合机检** —— `thm1415_full`

本节是 Saltman `thm:14.15` 的**完成形态**（论证层 ＋ 打包）：

> Let `T` be a commutative `F` algebra. Suppose `θ_i : M_n(S) → M_n(T)`, `i=1,2` are morphisms
> such that `θ_1` and `θ_2` are equal on `R(F,n,r)`. Then `θ_1` and `θ_2` are equal on
> `M_n(S)^{PGL_n(F)}`.

**机检的假设**：`θ_r : M_n(S) →ₐ[F] M_n(T)`；`θ₁` 保**标准矩阵单位**；
`θ₂(e_ij) = A⁻¹e_ijA`（这两条就是原文引用 `[saltman1999lectures, 2.11]` 之后的形式，
`2.11` 本身在 `MatrixUnits.lean` §5／§8 已机检）；`θ₁, θ₂` 在**通用矩阵 `X_k`** 上相等
（`R(F,n,r)` 由 `X_k` 生成）。

**链路**：§33 粘合（产出 `η₁, η₂`）→ §34 条目级桥（由 `hagree` 得 `hX`）→
§24 `hlink_of_X` → §30 `thm1415_capstone` → 消去得 `θ₁ α = θ₂ α`。

**未做（如实登记）**：`T` 局部的归约（原文"This may assume `T` is local"，需
"任意交换环嵌入局部环之积"）。 -/

section Full

variable (F : Type) [Field F] [Infinite F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★★ **Saltman `thm:14.15` 完全机检**：`θ₁, θ₂` 若在 `R(F,n,r)` 上相等、
`θ₁` 保标准矩阵单位、`θ₂(e_ij) = A⁻¹e_ijA`，则 `θ₁(α) = θ₂(α)` 对一切
`PGL_n(F)`-不变元 `α` 成立。 -/
theorem thm1415_full [Nonempty (Fin n)]
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (h₁ : ∀ i j, θ₁ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T))
    (h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
        * (AT : Matrix (Fin n) (Fin n) T))
    (hagree : ∀ k : Fin r,
      θ₁ (genericMatrix F r n k) = θ₂ (genericMatrix F r n k))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    θ₁ α = θ₂ α := by
  obtain ⟨η₁, η₂, hη₁, hη₂⟩ := thm1415_glue F r n T θ₁ θ₂ AT h₁ h₂
  have hX : ∀ (k : Fin r) (i j : Fin n),
      η₁ (MvPolynomial.X (k, i, j))
        = etaExt F r n T η₂ (phiAR F r n (ST F r n T) (unitMapST F r n T AT)
            (MvPolynomial.X (k, i, j))) := by
    intro k i j
    have hθ₂ : θ₂ (genericMatrix F r n k)
        = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * ((genericMatrix F r n k).map (⇑η₂)) * (AT : Matrix (Fin n) (Fin n) T) := by
      rw [← inv_mul_conj_mul AT (θ₂ (genericMatrix F r n k)), hη₂ (genericMatrix F r n k)]
    rw [etaExt_phiAR_entry F r n T AT η₂ k i j]
    show η₁ ((genericMatrix F r n k) i j)
      = ((((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * ((genericMatrix F r n k).map (⇑η₂))
          * (AT : Matrix (Fin n) (Fin n) T)) i j
    have hm : ((genericMatrix F r n k).map (⇑η₁)) i j
        = η₁ ((genericMatrix F r n k) i j) :=
      rfl
    rw [← hm, ← hη₁ (genericMatrix F r n k), hagree k, hθ₂]
  have hcap := thm1415_capstone F r n T AT η₁ η₂ hX α hα
  calc θ₁ α = α.map η₁ := hη₁ α
    _ = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * (α.map η₂) * (AT : Matrix (Fin n) (Fin n) T) := hcap
    _ = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
          * ((AT : Matrix (Fin n) (Fin n) T) * θ₂ α
            * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T))
          * (AT : Matrix (Fin n) (Fin n) T) := by rw [hη₂ α]
    _ = θ₂ α := inv_mul_conj_mul AT (θ₂ α)

end Full

/-! ## §36 **`T` 局部的归约**（G5／T1）：`thm:14.15` 的**原文口径**

§35 的 `thm1415_full` 把原文引用 `[saltman1999lectures, 2.11]` 之后的两条**标准化条件**当作假设
（`θ₁` 保标准矩阵单位、`θ₂(e_ij) = A⁻¹e_ijA`）。本节把它们**推导出来**，从而得到与原文逐字对应的
陈述：

> **`thm:14.15`**（`raw/Saltman1999ch14.tex:298–301`）Let `T` be a commutative `F` algebra.
> Suppose `θ_i : M_n(S) → M_n(T)`, `i=1,2` are morphisms such that `θ_1` and `θ_2` are equal on
> `R(F,n,r)`. Then `θ_1` and `θ_2` are equal on `M_n(S)^{PGL_n(F)}`.

原文证明首句（`:304`）：

> Any commutative ring embeds in a product of local rings. Thus we may assume `T` is local.

本节的分解（**照原文的步骤划分**，L48）：

1. **局部情形** `thm1415_local`：`[IsLocalRing T]` 下由 `2.11`（`MatrixUnits.lean` §8
   `exists_unit_conj_stdMU_of_isLocalRing`）取 `u` 使 `u·e(i,j)·u⁻¹ = θ₁(e(i,j))`，
   把 `θ₁, θ₂` 同时改写为 `c_r := Ad_{u⁻¹} ∘ θ_r`——于是 `c₁` 保标准矩阵单位；
   对 `c₂` 再用一次 `2.11` 取 `v` 使 `v·e(i,j)·v⁻¹ = c₂(e(i,j))`，即
   `c₂(e(i,j)) = (v⁻¹)⁻¹·e(i,j)·v⁻¹`，正是 §35 的 `h₂` 形状（`AT := v⁻¹`）；
   最后由 `thm1415_full` 得 `c₁α = c₂α`，再用 `conjAlgEquiv u⁻¹` 的单射性回落到 `θ₁α = θ₂α`。
2. **归约** `thm1415_general`：原文用"嵌入局部环之积"，本件不构造那个积环，而用**等价且更廉**的
   "逐素局部化检验"（**路线替代已登记**：原文"嵌入积" ≡ 我们"对每个素理想 `m`，`T_m` 上的等式
   推出 `T` 上的等式"——因为 `T → ∏_m T_m` 单当且仅当"每个 `x ≠ 0` 在某个 `T_m` 中非零"，
   此即 `exists_isPrime_algebraMap_ne_zero`）。局部化 `T_m` 是局部环，`M_n` 上的基变换由
   `AlgHom.mapMatrix` 给出，逐点套 `thm1415_local`，最后用单射性关闭。

**射程**：本节与 §35 合起来使 `thm:14.15` **无需任何归一化假设**、且对任意交换 `F`-代数 `T`
成立——与原文逐字对应。`(A) thm:14.16` 的结构层（`Z`／`UD` 的构造）仍不在本节射程内。 -/

section LocRedSystem

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★ **`θ` 把标准矩阵单位送成矩阵单位组**：`IsMatrixUnitSystem (i j ↦ θ(e(i,j)))`。

**用途**：原文 `thm:14.15` 证明第二段 "Set `f_r(i,j) = θ_r(e(i,j))`. By `[2.11]` …"——
`2.11` 的输入正是"一组矩阵单位"，本引理把它从 `θ_r` 造出来。 -/
lemma isMatrixUnitSystem_theta_stdMU
    (θ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
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

#print axioms isMatrixUnitSystem_theta_stdMU

end LocRedSystem

section LocRedProbe

set_option linter.style.haveILetI false

variable (T : Type) [CommRing T]

/-- ★★ **局部化探测**：非零元在某个素局部化中仍非零。

反设 `x ≠ 0`。令 `A = {c | c * x = 0}`（**零化子**，是理想且 `A ≠ ⊤`，因 `1 · x = x ≠ 0`）。
取极大理想 `m ⊇ A`（`Ideal.exists_le_maximal`）。若 `x` 在 `T_m` 中为零，则由
`IsLocalization.eq_iff_exists` 存在 `c ∉ m` 使 `c * x = 0`，即 `c ∈ A ⊆ m`——矛盾。

**在原文中的位置**：这是 "Any commutative ring embeds in a product of local rings" 的
**逐点形式**（原文 `:304`）。原文的积环 `∏_m T_m` 只在下述意义下被使用：`x ↦ ∏_m x_m` 单射。
本引理直接给出该单射性的**检验形式**，从而无需真的构造积环。 -/
lemma exists_isPrime_algebraMap_ne_zero {x : T} (hx : x ≠ 0) :
    ∃ (m : Ideal T) (_ : m.IsPrime),
      algebraMap T (Localization.AtPrime m) x ≠ 0 := by
  classical
  have hanti : ∀ c y : T, y ∈ ({c : T | c * x = 0} : Set T) →
      c * y ∈ ({c : T | c * x = 0} : Set T) := by
    intro c y hy
    show (c * y) * x = 0
    rw [mul_assoc, hy, mul_zero]
  let A : Ideal T :=
    { carrier := {c : T | c * x = 0}
      zero_mem' := by show (0 : T) * x = 0; rw [zero_mul]
      add_mem' := by
        intro a b ha hb
        show (a + b) * x = 0
        rw [add_mul, ha, hb, add_zero]
      smul_mem' := fun c y hy => hanti c y hy }
  have hAne : A ≠ ⊤ := by
    intro htop
    have hone : (1 : T) ∈ A := by rw [htop]; exact Submodule.mem_top
    change (1 : T) * x = 0 at hone
    exact hx (by simpa using hone)
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal A hAne
  haveI : m.IsPrime := hmax.isPrime
  refine ⟨m, hmax.isPrime, ?_⟩
  intro hzero
  have hzero' : algebraMap T (Localization.AtPrime m) x
      = algebraMap T (Localization.AtPrime m) (0 : T) := by
    rw [hzero, map_zero]
  rw [IsLocalization.eq_iff_exists m.primeCompl (Localization.AtPrime m)] at hzero'
  obtain ⟨c, hc⟩ := hzero'
  simp only [mul_zero] at hc
  exact (Ideal.mem_primeCompl_iff.mp c.2) (hle (show (c : T) ∈ A from hc))

#print axioms exists_isPrime_algebraMap_ne_zero

end LocRedProbe

section LocRedMain

set_option linter.style.haveILetI false

variable (F : Type) [Field F] [Infinite F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- ★★★★★ **`thm:14.15`（局部情形）**：`T` 局部时，`θ₁, θ₂` 在 `R(F,n,r)` 上相等 ⟹ 在
`PGL_n(F)`-不变元上相等。**假设与原文逐字相同**（无 `h₁`／`h₂`／`AT`）。

对应原文 `raw/Saltman1999ch14.tex:298–311`；`T` 局部这一假设对应原文首句
"Thus we may assume `T` is local"。 -/
theorem thm1415_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hagree : ∀ k : Fin r, θ₁ (genericMatrix F r n k) = θ₂ (genericMatrix F r n k))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    θ₁ α = θ₂ α := by
  obtain ⟨u, hu⟩ := exists_unit_conj_stdMU_of_isLocalRing (n := Fin n) (T := T)
    (isMatrixUnitSystem_theta_stdMU F r n T θ₁)
  set c₁ := (conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁ with hc₁
  set c₂ := (conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂ with hc₂
  have h₁ : ∀ i j, c₁ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T) := by
    intro i j
    show ((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
        * θ₁ (stdMU (n := Fin n) i j) * (u : Matrix (Fin n) (Fin n) T)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
    rw [← hu i j]
    exact inv_mul_conj_mul u (stdMU (n := Fin n) i j)
  have hf₂ : IsMatrixUnitSystem (fun i j => c₂ (stdMU (n := Fin n) i j)) :=
    isMatrixUnitSystem_theta_stdMU F r n T c₂
  obtain ⟨v, hv⟩ := exists_unit_conj_stdMU_of_isLocalRing (n := Fin n) (T := T) hf₂
  set w : (Matrix (Fin n) (Fin n) T)ˣ := v⁻¹ with hw
  have hwv : (w⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) = v := by
    rw [hw, inv_inv]
  have h₂ : ∀ i j, c₂ (stdMU (n := Fin n) i j)
      = (((w⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
          * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
          * (w : Matrix (Fin n) (Fin n) T)) := by
    intro i j
    rw [hwv, hw]
    exact (hv i j).symm
  have hagree' : ∀ k : Fin r, c₁ (genericMatrix F r n k) = c₂ (genericMatrix F r n k) := by
    intro k
    simp only [hc₁, hc₂, AlgHom.coe_comp, Function.comp_apply]
    exact congrArg _ (hagree k)
  have hmain : c₁ α = c₂ α :=
    thm1415_full F r n T c₁ c₂ w h₁ h₂ hagree' α hα
  have hinj : Function.Injective (conjAlgEquiv (F := F) (u⁻¹)) :=
    (conjAlgEquiv (F := F) (u⁻¹)).injective
  exact hinj (by simpa [hc₁, hc₂] using hmain)

#print axioms thm1415_local

/-- ★★★ **`thm:14.15`（非平凡 `T`）**：把局部情形沿 `T → T_m` 归约到 `thm1415_local`。 -/
theorem thm1415_general_nontrivial [Nonempty (Fin n)] [Nontrivial T]
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hagree : ∀ k : Fin r, θ₁ (genericMatrix F r n k) = θ₂ (genericMatrix F r n k))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    θ₁ α = θ₂ α := by
  classical
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
  set φ : T →ₐ[F] Localization.AtPrime m :=
    IsScalarTower.toAlgHom F T (Localization.AtPrime m) with hφ
  set Θ : Matrix (Fin n) (Fin n) T →ₐ[F] Matrix (Fin n) (Fin n) (Localization.AtPrime m) :=
    φ.mapMatrix with hΘ
  have hloc : (Θ.comp θ₁) α = (Θ.comp θ₂) α :=
    thm1415_local F r n (Localization.AtPrime m) (Θ.comp θ₁) (Θ.comp θ₂)
      (fun k => congrArg Θ (hagree k)) α hα
  have hentry : φ ((θ₁ α) i j) = φ ((θ₂ α) i j) := by
    have hentry' := congrFun (congrFun hloc i) j
    simpa [hΘ, AlgHom.mapMatrix_apply] using hentry'
  have hzero : φ ((θ₁ α - θ₂ α) i j) = 0 := by
    show φ ((θ₁ α) i j - (θ₂ α) i j) = 0
    rw [map_sub, hentry, sub_self]
  have hφapp : ⇑φ = algebraMap T (Localization.AtPrime m) := rfl
  rw [hφapp] at hzero
  exact hmap hzero

#print axioms thm1415_general_nontrivial

/-- ★★★★★★ **`thm:14.15`（原文口径，无条件）**：`T` 为**任意**交换 `F`-代数，
`θ₁, θ₂ : M_n(S) →ₐ[F] M_n(T)` 在 `R(F,n,r)` 上相等 ⟹ 在 `M_n(S)^{PGL_n(F)}` 上相等。

与原文 `raw/Saltman1999ch14.tex:298–301` **逐字对应**：无局部性假设、无归一化假设。
平凡环情形为 `Subsingleton`，等式自动成立。 -/
theorem thm1415_general [Nonempty (Fin n)]
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (S F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hagree : ∀ k : Fin r, θ₁ (genericMatrix F r n k) = θ₂ (genericMatrix F r n k))
    (α : Matrix (Fin n) (Fin n) (S F r n))
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n B α = α) :
    θ₁ α = θ₂ α := by
  by_cases hT : Nontrivial T
  · haveI : Nontrivial T := hT
    exact thm1415_general_nontrivial F r n T θ₁ θ₂ hagree α hα
  · haveI : Subsingleton T := not_nontrivial_iff_subsingleton.mp hT
    exact Subsingleton.elim _ _

#print axioms thm1415_general

end LocRedMain

/-! ## §37 **`R(F,n,r)` 被 `PGL_n(F)` 逐点固定** —— `thm:14.16` 的 `⊆` 方向之一半

源 `raw/Saltman1999ch14.tex:270–271`（逐字）：

> That is, the `X_k`'s and hence the whole ring `R(F,n,r)` is fixed under this action of
> `PGL_n(F)`. From this it quickly follows that `C(F,n,r)`, `Z(F,n,r)` and `UD(F,n,r)`
> are all fixed under the `PGL_n` action.

本节机检 **"`X_k`'s 与 `R`"** 这一条（论证层的第一半）。**另一半**（`C`／`Z`／`UD`）
需要 `C = R ∩ S` 的内含（`cor:14.8(a)`，由 `lem:14.7` 的 `Ξ` 基得出——**PI 理论**，
不在本件射程），故 `Z`／`UD` 的固定性留待结构层（`GenericDivisionData`）。

**为何现在做**：`thm:14.16` 的 `⊆` 方向（`UD ⊂ (M_n(K))^{PGL}`）由"`R` 固定"与
"`Z` 固定"两半拼成；其中"`R` 固定"**不需要任何 PI 理论**，却一直是本工程的缺口
（此前 `genericMatrixAlgebra` 在 `PGL.lean`／`GenericInv.lean` 内**一次也没被引用**）。

**机制（`psiA_genericMatrix`）**：源文 `(16)`（`phiA_X`）：`M_n(φ_A)(X_k) = A⁻¹X_kA`；
于是 `ψ_A(X_k) = A·(A⁻¹X_kA)·A⁻¹ = X_k`——**只用到 `A·A⁻¹ = 1`**。
纯量矩阵同理（`φ_A` 固定 `c ∈ F`，纯量矩阵与一切交换）。
最后由 `genericMatrixAlgebra_induction`（`adjoin` 归纳）升到整个 `R`。 -/

section RFixedByPGL

section RFixed

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **`ψ_A` 固定每个通用矩阵**（源 `raw/Saltman1999ch14.tex:270` 逐字：
"the `X_k`'s and hence the whole ring `R(F,n,r)` is fixed under this action of `PGL_n(F)`"）。

**机制**：源文 `(16)`（`phiA_X`，`M_n(φ_A)(X_k) = A⁻¹X_kA`）＋ `A·A⁻¹ = 1`。
即 `ψ_A(X_k) = A·(A⁻¹X_kA)·A⁻¹ = X_k`。 -/
theorem psiA_genericMatrix (A : (Matrix (Fin n) (Fin n) F)ˣ) (k : Fin r) :
    psiA F r n A (genericMatrix F r n k) = genericMatrix F r n k := by
  rw [psiA_apply, phiA_X]
  have h1 : constMat F r n (↑A) * constMat F r n (↑A⁻¹) = 1 := by
    rw [← constMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMat_one]
  calc constMat F r n (↑A) * (constMat F r n (↑A⁻¹) * genericMatrix F r n k
        * constMat F r n (↑A)) * constMat F r n (↑A⁻¹)
      = (constMat F r n (↑A) * constMat F r n (↑A⁻¹)) * genericMatrix F r n k
        * (constMat F r n (↑A) * constMat F r n (↑A⁻¹)) := by noncomm_ring
    _ = genericMatrix F r n k := by rw [h1, one_mul, mul_one]

#print axioms psiA_genericMatrix

/-- ★★ **`ψ_A` 固定 `F`-纯量矩阵**：`ψ_A(c • 1) = c • 1`。

**机制**：`φ_A` 是 `F`-代数同态故固定 `c`（`Matrix.map_algebraMap`）；纯量矩阵与一切矩阵
交换（`Algebra.commutes`）故共轭消去。 -/
theorem psiA_algebraMap_scalar (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : F) :
    psiA F r n A (algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) c)
      = algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) c := by
  rw [psiA_apply]
  have hmap : (algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) c).map (phiA F r n A)
      = algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) c :=
    Matrix.map_algebraMap c (⇑(phiA F r n A)) (map_zero _) (AlgHom.commutes _ _)
  rw [hmap]
  rw [← Algebra.commutes c (constMat F r n (↑A)), mul_assoc,
    show constMat F r n (↑A) * constMat F r n (↑A⁻¹) = 1 from by
      rw [← constMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMat_one],
    mul_one]

#print axioms psiA_algebraMap_scalar

/-- ★★★★★ **`R(F,n,r)` 被 `PGL_n(F)` 逐点固定** —— 源 `raw/Saltman1999ch14.tex:270–271`
（"the `X_k`'s and hence the whole ring `R(F,n,r)` is fixed under this action of `PGL_n(F)`"）
的机检形态。

**用途（`thm:14.16` 的 `⊆` 方向）**：`UD(F,n,r) = R·Z` 的 `R`-部分被固定；
`Z`-部分由 `C = R ∩ S` 被固定 ＋ `lem:14.13`（`fixed_eq_ratio`）供给。
**注意方向**：本条只给"`R` 固定"，**不**给 `(M_n(K))^{PGL} ⊂ UD`（那是 `⊇` 方向，
即 `thm:14.16` 的主体，需 `thm:14.15` ＋ `UD ⊗_Z K ≅ M_n(K)`）。 -/
theorem psiA_fixes_genericMatrixAlgebra (A : (Matrix (Fin n) (Fin n) F)ˣ)
    {β : Matrix (Fin n) (Fin n) (S F r n)} (hβ : β ∈ genericMatrixAlgebra F r n) :
    psiA F r n A β = β := by
  refine genericMatrixAlgebra_induction (F := F) (r := r) (n := n)
    (p := fun x _ => psiA F r n A x = x) ?_ ?_ ?_ ?_ hβ
  · intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact psiA_genericMatrix F r n A k
  · intro c
    exact psiA_algebraMap_scalar F r n A c
  · intro x y _ _ ihx ihy
    rw [map_add, ihx, ihy]
  · intro x y _ _ ihx ihy
    rw [map_mul, ihx, ihy]

#print axioms psiA_fixes_genericMatrixAlgebra

end RFixed

/-! ## 扩展环版：`ψ_A` 固定 `genMatR`（`(B) prop:14.19`／`lem:14.23` 的同一机制）

`lem:14.23` 的 `ψ_{A(σ)}(α) = α` 与 `prop:14.14` 同型：都需要"`ψ` 固定生成元"。
把上节的机制原样搬到任意 `S`-代数 `T` 上。 -/

section RFixedGen

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]
  [Algebra (S F r n) T] [IsScalarTower F (S F r n) T]

/-- ★★ **`ψ_A` 固定 `genMatR`**（扩展环版；机制同 `psiA_genericMatrix`，用 `phiAR_X`）。 -/
theorem psiAR_genMatR (A : (Matrix (Fin n) (Fin n) T)ˣ) (k : Fin r) :
    psiAR F r n T A (genMatR F r n (S F r n) k) = genMatR F r n T k := by
  have hgm : genMatR F r n (S F r n) k = genericMatrix F r n k := rfl
  rw [psiAR, hgm, phiAR_X]
  have h1 : ((A : Matrix (Fin n) (Fin n) T)) * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) :
      Matrix (Fin n) (Fin n) T) = 1 := Units.mul_inv A
  calc ((A : Matrix (Fin n) (Fin n) T)) * ((((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) :
        Matrix (Fin n) (Fin n) T) * genMatR F r n T k * ((A : Matrix (Fin n) (Fin n) T)))
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = (((A : Matrix (Fin n) (Fin n) T)) * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) :
          Matrix (Fin n) (Fin n) T)) * genMatR F r n T k
        * (((A : Matrix (Fin n) (Fin n) T)) * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) :
          Matrix (Fin n) (Fin n) T)) := by noncomm_ring
    _ = genMatR F r n T k := by rw [h1, one_mul, mul_one]

#print axioms psiAR_genMatR

end RFixedGen

end RFixedByPGL

/-! ## §38 **`K`-层的 `PGL_n(F)` 作用** —— `(M_n(K))^{PGL_n(F)}` 登场

`thm:14.16` 的陈述（`raw/Saltman1999ch14.tex:315–318`）是
`(M_n(K))^{PGL_n(F)} = UD(F,n,r)` 与 `K^{PGL_n(F)} = Z(F,n,r)`。它的**左端对象**此前在 Lean
内不存在：`PGL.lean` 只给了 `M_n(S)` 上的 `psiA : M_n(S) →+* M_n(S)`，而定理谈的是
`M_n(K)`（`K = Frac(S) = SField F r n`）上的作用。

本节把作用提升到 `K`：
* `phiKAlgEquiv`：`φ_A` 的分式域提升（`KAction.lean` 的 `phiKEquiv : K ≃+* K` 升为 `≃ₐ[F]`）；
* `constMatK`：`M_n(F) → M_n(K)`（`B ↦ B.map (F → K)`）；
* **`psiK`**：`ψ_A(α) = A·α.map(φ_A)·A⁻¹`，`α ∈ M_n(K)`；
* **`fixedByPGL`**：**`(M_n(K))^{PGL_n(F)}`**（被一切 `ψ_A` 固定的元构成的 `F`-子代数）
  —— `thm:14.16` 的左端；
* `psiK_map_algebraMapS`：`S`-层与 `K`-层**相容**（`ψ^K_A` 沿 `S → K` 就是 `ψ_A`）；
* `psiK_genericMatrix`／`genMatKF_mem_fixedByPGL`：`R(F,n,r)` 的 `K`-像在 `fixedByPGL` 里。

**与 §37 的关系**：§37 在 `S`-层证了 `R` 被逐点固定；本节把该结论沿 `S → K` 提升，
于是 `thm:14.16` 的 `⊆` 方向的 **`R`-部分在 `K`-层就位**。剩下的是 `Z`-部分
（需 `C = R ∩ S`，PI 理论）与 `⊇` 方向（equalizer 步，需 `UD ⊗_Z K ≅ M_n(K)`）。

**射程（勿夸大）**：本节只建**作用与被作用对象**，**不**证 `(M_n(K))^{PGL} = UD`。 -/

section KLevelPGL

section KAction

variable (F : Type) [Field F] (r n : ℕ)

/-- `φ_A` 提升到分式域 `K` 的 **`F`-代数自同构**（`phiKEquiv` 加 `commutes'`）。 -/
noncomputable def phiKAlgEquiv (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    SField F r n ≃ₐ[F] SField F r n :=
  AlgEquiv.ofRingEquiv (f := phiKEquiv F r n A) (fun c => by
    rw [IsScalarTower.algebraMap_apply F (S F r n) (SField F r n) c, phiKEquiv_algebraMap,
      AlgHom.commutes])

#print axioms phiKAlgEquiv

/-- `F`-纯量系数矩阵 → `K`-系数矩阵（`B ↦ B.map (F → K)`）。 -/
noncomputable def constMatK (B : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (SField F r n) :=
  B.map (algebraMap F (SField F r n))

lemma constMatK_mul (B C : Matrix (Fin n) (Fin n) F) :
    constMatK F r n B * constMatK F r n C = constMatK F r n (B * C) :=
  (Matrix.map_mul ..).symm

lemma constMatK_one : constMatK F r n (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [constMatK, Matrix.map_one _ (map_zero _) (map_one _)]

/-- ★★ **`ψ_A` 在 `K = Frac(S)` 层**：`ψ_A(α) = A·α.map(φ_A)·A⁻¹`，`α ∈ M_n(K)`。

**这是源文 `M_n(K)^{PGL_n(F)}`（`thm:14.16` 的被作用对象）的载体**：`ψ_A` 在
`M_n(S)` 上由 `PGL.lean` 的 `psiA` 给出（`RingHom`），本节把它沿 `S → K` 提升。 -/
noncomputable def psiK (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    Matrix (Fin n) (Fin n) (SField F r n) →+* Matrix (Fin n) (Fin n) (SField F r n) where
  toFun Y := constMatK F r n (↑A) * Y.map ⇑((phiKAlgEquiv F r n A).toAlgHom)
    * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
  map_one' := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one, constMatK_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, constMatK_one]
  map_mul' Y Z := by
    rw [Matrix.map_mul]
    have h : constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
        * constMatK F r n (↑A) = 1 := by
      rw [constMatK_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, constMatK_one]
    have key : constMatK F r n (↑A) * Y.map (⇑((phiKAlgEquiv F r n A).toAlgHom)) *
        (constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
          * constMatK F r n (↑A)) * Z.map (⇑((phiKAlgEquiv F r n A).toAlgHom)) *
          constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
        = constMatK F r n (↑A) *
          (Y.map (⇑((phiKAlgEquiv F r n A).toAlgHom))
            * Z.map (⇑((phiKAlgEquiv F r n A).toAlgHom))) *
          constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F) := by
      rw [h, mul_one]
      noncomm_ring
    rw [← key]
    noncomm_ring
  map_zero' := by
    rw [Matrix.map_zero _ (map_zero _), mul_zero, zero_mul]
  map_add' Y Z := by
    rw [Matrix.map_add (⇑((phiKAlgEquiv F r n A).toAlgHom)) (fun a b => map_add _ _ _) Y Z]
    noncomm_ring

#print axioms psiK

/-- `K`-层的被作用者：`(M_n(K))^{PGL_n(F)}`（对一切 `A` 都被 `ψ_A` 固定的矩阵）。 -/
theorem psiK_algebraMap_scalar (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : F) :
    psiK F r n A (algebraMap F (Matrix (Fin n) (Fin n) (SField F r n)) c)
      = algebraMap F (Matrix (Fin n) (Fin n) (SField F r n)) c := by
  show constMatK F r n (↑A) *
      (algebraMap F (Matrix (Fin n) (Fin n) (SField F r n)) c).map
        ⇑((phiKAlgEquiv F r n A).toAlgHom)
      * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
    = algebraMap F (Matrix (Fin n) (Fin n) (SField F r n)) c
  rw [Matrix.map_algebraMap c (⇑((phiKAlgEquiv F r n A).toAlgHom)) (map_zero _)
    (AlgHom.commutes _ _)]
  rw [← Algebra.commutes c (constMatK F r n (↑A)), mul_assoc,
    show constMatK F r n (↑A) * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) :
      Matrix (Fin n) (Fin n) F) = 1 from by
      rw [constMatK_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMatK_one],
    mul_one]

#print axioms psiK_algebraMap_scalar

/-- ★★ **`S`-层与 `K`-层的相容**：`ψ_A` 沿 `S → K` 与 `psiA` 一致。 -/
theorem psiK_map_algebraMapS (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (β : Matrix (Fin n) (Fin n) (S F r n)) :
    psiK F r n A (β.map (algebraMap (S F r n) (SField F r n)))
      = (psiA F r n A β).map (algebraMap (S F r n) (SField F r n)) := by
  show constMatK F r n (↑A) * (β.map (algebraMap (S F r n) (SField F r n))).map
        ⇑((phiKAlgEquiv F r n A).toAlgHom)
      * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
    = (constMat F r n (↑A) * β.map (⇑(phiA F r n A)) * constMat F r n
        (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)).map
        (algebraMap (S F r n) (SField F r n))
  have hcomp : ⇑(algebraMap (S F r n) (SField F r n)) ∘ ⇑(phiA F r n A)
      = ⇑((phiKAlgEquiv F r n A).toAlgHom) ∘ ⇑(algebraMap (S F r n) (SField F r n)) := by
    funext x
    exact (phiKEquiv_algebraMap F r n A x).symm
  rw [Matrix.map_map, ← hcomp, ← Matrix.map_map]
  have hcA : (constMat F r n (↑A)).map (algebraMap (S F r n) (SField F r n))
      = constMatK F r n (↑A) := rfl
  have hcB : (constMat F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) :
        Matrix (Fin n) (Fin n) F)).map (algebraMap (S F r n) (SField F r n))
      = constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F) := rfl
  rw [Matrix.map_mul, Matrix.map_mul, hcA, hcB]

#print axioms psiK_map_algebraMapS

/-- `K` 上的第 `k` 个通用矩阵（`(genericMatrix k).map (S → K)`）。 -/
noncomputable def genMatKF (k : Fin r) : Matrix (Fin n) (Fin n) (SField F r n) :=
  (genericMatrix F r n k).map (algebraMap (S F r n) (SField F r n))

/-- ★★★ **`ψ_A` 固定 `K` 上的每个通用矩阵**（`S`-层 `psiA_genericMatrix` 沿 `S → K` 的提升）。 -/
theorem psiK_genericMatrix (A : (Matrix (Fin n) (Fin n) F)ˣ) (k : Fin r) :
    psiK F r n A (genMatKF F r n k) = genMatKF F r n k := by
  rw [genMatKF, psiK_map_algebraMapS, psiA_genericMatrix]

#print axioms psiK_genericMatrix

/-- ★★★ **`(M_n(K))^{PGL_n(F)}`** —— `thm:14.16` 的左端（`M_n(K)` 中被所有 `ψ_A` 固定的元）。 -/
noncomputable def fixedByPGL : Subalgebra F (Matrix (Fin n) (Fin n) (SField F r n)) where
  carrier := {x | ∀ A, psiK F r n A x = x}
  zero_mem' := fun A => map_zero _
  add_mem' := fun hx hy A => by rw [map_add, hx A, hy A]
  one_mem' := fun A => map_one _
  mul_mem' := fun hx hy A => by rw [map_mul, hx A, hy A]
  algebraMap_mem' := fun c A => psiK_algebraMap_scalar F r n A c

#print axioms fixedByPGL

/-- `R(F,n,r)` 的 `K`-像全部落在 `(M_n(K))^{PGL}` 里（`thm:14.16` 的 `⊆` 方向的
**`R`-部分**；`Z`-部分待 `GenericDivisionData`）。 -/
theorem genMatKF_mem_fixedByPGL (k : Fin r) : genMatKF F r n k ∈ fixedByPGL F r n :=
  fun A => psiK_genericMatrix F r n A k

#print axioms genMatKF_mem_fixedByPGL

end KAction


end KLevelPGL

/-! ## §39 **"`C`、`Z`、`UD` 都被固定"的可证部分** —— `thm:14.16` 的 `⊆` 方向收口形状

源 `raw/Saltman1999ch14.tex:270–271`：

> From this it quickly follows that `C(F,n,r)`, `Z(F,n,r)` and `UD(F,n,r)` are all fixed
> under the `PGL_n` action.

本节把这句里的**可证部分**抽出，并给出**收口形状**：

* `centImage_fixed`：**`C(F,n,r)` 的 `K`-像被逐点固定** —— 不需要 PI 理论
  （`C ⊆ R`，而 `R` 已被 §37 固定），只要 §38 的 `S`／`K` 相容性；
* `adjoin_le_fixedByPGL`：**若 `Z ⊆ (M_n(K))^{PGL}`，则由 `Z` 与 `R` 生成的 `↥Z`-子代数
  也含于 `(M_n(K))^{PGL}`** —— 这正是 `UD = R·Z` 的固定性，
  亦即 `thm:14.16` 的 `⊆` 方向（`UD ⊂ (M_n(K))^{PGL}`）的**唯一剩余输入是 `Z ⊆ K^{PGL}`**。

**唯一留给结构层的输入**：`Z = Frac(C) ⊆ K^{PGL}` 需要 "`C` 的像是 `S` 上的纯量矩阵"
（`cor:14.8(a)`，由 `lem:14.7` 的 `Ξ` 基得出）——**PI 理论**。故 `GenericDivisionData`
只需携带该条（与 `UD ⊗_Z K ≅ M_n(K)`），`⊆` 方向即可无条件收口。

**射程（勿夸大）**：本节**不**证 `Z ⊆ K^{PGL}`，也**不**证 `⊇` 方向。 -/

section CenterFixed

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **中心的 `K`-像被 `PGL_n(F)` 逐点固定**：源 `:270–271` 的 "`C(F,n,r)` … is fixed"。

**不需要 PI 理论**：`C` 的每个元是 `R` 的元（`C = Z(R) ⊆ R`），而 `R` 已被 §37 逐点固定；
再沿 `S → K` 用 §38 的相容性 `psiK_map_algebraMapS` 提升。 -/
theorem centImage_fixed (A : (Matrix (Fin n) (Fin n) F)ˣ)
    (c : ↥(genericCenter F r n)) :
    psiK F r n A (((c : ↥(genericMatrixAlgebra F r n)) :
        Matrix (Fin n) (Fin n) (S F r n)).map (algebraMap (S F r n) (SField F r n)))
      = ((c : ↥(genericMatrixAlgebra F r n)) :
          Matrix (Fin n) (Fin n) (S F r n)).map (algebraMap (S F r n) (SField F r n)) := by
  rw [psiK_map_algebraMapS, psiA_fixes_genericMatrixAlgebra F r n A c.1.2]

#print axioms centImage_fixed

/-- ★★★★★ **`Z`-代数生成 ⇒ 固定**：若 `Z ⊆ (M_n(K))^{PGL}`，则由 `Z` 与 `R` 生成的
`↥Z`-子代数也含于 `(M_n(K))^{PGL}`。

**这就是源文 `:270–271` 的 "From this it quickly follows that … `UD(F,n,r)` are all fixed"**：
`UD = R·Z` 正是 `Z` 与 `R` 生成的子代数。故本引理 ＋ `Z ⊆ K^{PGL}` 即得
`thm:14.16` 的 `⊆` 方向。**`Z ⊆ K^{PGL}` 本身**（`Z = Frac(C)`）需 `C` 的像为纯量矩阵
（`cor:14.8(a)`，PI 理论），留给 `GenericDivisionData`。 -/
theorem adjoin_le_fixedByPGL (Z : IntermediateField F (SField F r n))
    (hZ : ∀ z : ↥Z, ∀ A : (Matrix (Fin n) (Fin n) F)ˣ,
      psiK F r n A (algebraMap ↥Z (Matrix (Fin n) (Fin n) (SField F r n)) z)
        = algebraMap ↥Z (Matrix (Fin n) (Fin n) (SField F r n)) z) :
    ∀ x ∈ Algebra.adjoin ↥Z (Set.range (genMatKF F r n)),
      ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, psiK F r n A x = x := by
  intro x hx
  refine Algebra.adjoin_induction (R := ↥Z)
    (p := fun y _ => ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, psiK F r n A y = y) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩
    exact fun A => psiK_genericMatrix F r n A k
  · intro z
    exact hZ z
  · intro x y _ _ ihx ihy A
    rw [map_add, ihx A, ihy A]
  · intro x y _ _ ihx ihy A
    rw [map_mul, ihx A, ihy A]

#print axioms adjoin_le_fixedByPGL

end CenterFixed

/-! ## §40 **结构束 `GenericDivisionData`** ＋ `thm:14.16` 的 `⊆` 方向收口

`(A) thm:14.16`（`(M_n(K))^{PGL_n(F)} = UD(F,n,r)` 与 `K^{PGL_n(F)} = Z(F,n,r)`）的两端
对象现在都在 Lean 里：`fixedByPGL`（§38）与 `ZCanon`／`UD`（本节）。本节把
**PI 理论**（mathlib 无）需要提供的**结构输入**收成**一个具名字段**：

> `centK_spec`：`C(F,n,r)` 的元在 `M_n(K)` 里是**纯量矩阵**（`cor:14.8(a)`，
> 由 `lem:14.7`（`Ξ` 是 `M_n(K)` 的 `K`-基，`:160–171`）得出，原文引 `rowen1980polynomial p.29`）。

**本轮的实质结果**：`⊆` 方向（`UD ⊆ (M_n(K))^{PGL}`，源 `:321` "we have already observed"）
**只用到这一个字段**就无条件成立（`UD_le_fixedByPGL`）——
这与第 191 轮"只剩一个输入"的判断**逐字吻合**，且该输入被**收窄到最小形式**。

**L1 非空洞性审计（如实登记）**：结构束的字段集**非空**等价于 `cor:14.8(a)`——
那是**已发表定理**（Saltman 1999 引 Rowen p.29），本工作区**未机检**它，
故 `GenericDivisionData` 的**存在性**仍是 `⚠-unverified`（引文锚定，非机检）。
**可满足性**：字段只有"一个映射 ＋ 一条等式"，`centK` 被 `centK_spec` **唯一决定**
（纯量矩阵的纯量唯一），故**字段集不互相矛盾**；给出**具体模型**（如 `n = 1`）留待后续轮。
**射程（勿夸大）**：`⊆` 方向已机检；`⊇` 方向（需 `UD ⊗_Z K ≅ M_n(K)`）与 `(B)` **未做**。 -/

section GenericDivisionBundle

variable (F : Type) [Field F] (r n : ℕ)


/-- **`C(F,n,r)` 在 `M_n(K)` 中的像**（`C` 的元经 `S → K` 后的矩阵）。 -/
noncomputable def centImage : Set (Matrix (Fin n) (Fin n) (SField F r n)) :=
  Set.range fun c : ↥(genericCenter F r n) =>
    ((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)).map
      (algebraMap (S F r n) (SField F r n))

/-- `psi_A` 作用在 `K`-纯量矩阵上：`ψ_A(scalar y) = scalar (φ_A y)`。 -/
theorem psiK_scalar (A : (Matrix (Fin n) (Fin n) F)ˣ) (y : SField F r n) :
    psiK F r n A (Matrix.scalar (Fin n) y)
      = Matrix.scalar (Fin n) ((phiKAlgEquiv F r n A) y) := by
  show constMatK F r n (↑A) * (Matrix.scalar (Fin n) y).map ⇑((phiKAlgEquiv F r n A).toAlgHom)
      * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
    = Matrix.scalar (Fin n) ((phiKAlgEquiv F r n A) y)
  have hmap : (Matrix.scalar (Fin n) y).map ⇑((phiKAlgEquiv F r n A).toAlgHom)
      = Matrix.scalar (Fin n) ((phiKAlgEquiv F r n A) y) := by
    ext i j
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar]
    · simp [Matrix.scalar, hij]
  rw [hmap]
  rw [← Matrix.scalar_comm ((phiKAlgEquiv F r n A) y) (fun _ => Commute.all _ _)
    (constMatK F r n (↑A)), mul_assoc,
    show constMatK F r n (↑A) * constMatK F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) :
      Matrix (Fin n) (Fin n) F) = 1 from by
      rw [constMatK_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMatK_one],
    mul_one]

#print axioms psiK_scalar

/-! ## 结构束 `GenericDivisionData` -/

/-- ★ **通用除法代数的结构束**（PI 理论给出的**结构输入**；`thm:14.16` 的 `Z` 与 `UD`
从此**被命名**，不再是自由参数）。

**第一个字段即 `cor:14.8(a)`**：`C(F,n,r)` 的元是 `S` 上的**纯量矩阵**——由 `lem:14.7`
（`Ξ` 是 `M_n(K)` 的 `K`-基）得出，是 **PI 理论**（Amitsur／Rowen p.29）的内容，
mathlib 无。`centK` 就是那个纯量，故 `Z(F,n,r) = Frac(C)` 可**定义**为
`IntermediateField.adjoin F (range centK)`。 -/
structure GenericDivisionData (F : Type) [Field F] (r n : ℕ) where
  /-- `C(F,n,r) → K`：中心元所对应的纯量。 -/
  centK : ↥(genericCenter F r n) →ₐ[F] SField F r n
  /-- **`cor:14.8(a)`**：中心元的像恰是 `centK` 给出的纯量矩阵。 -/
  centK_spec : ∀ c : ↥(genericCenter F r n),
    ((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)).map
      (algebraMap (S F r n) (SField F r n)) = Matrix.scalar (Fin n) (centK c)

/-- ★★★ **`Z(F,n,r) = Frac(C(F,n,r))` 作为 `K` 的子域**（源 `:185`："we can consider
`Z(F,n,r) ⊂ K`"）。**本定义不需要 PI 理论**——只要结构束的 `centK`。 -/
noncomputable def ZCanon (D : GenericDivisionData F r n) :
    IntermediateField F (SField F r n) :=
  IntermediateField.adjoin F (Set.range D.centK)

/-- ★★ **`φ_A` 固定 `centK` 的每个值**（`C` 固定 ＋ `cor:14.8(a)`）。 -/
theorem phiK_fixes_centK [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : ↥(genericCenter F r n)) :
    (phiKAlgEquiv F r n A) (D.centK c) = D.centK c := by
  have h := centImage_fixed F r n A c
  rw [D.centK_spec c, psiK_scalar] at h
  exact (Matrix.scalar_inj).mp h

#print axioms phiK_fixes_centK

/-- ★★★ **`Z(F,n,r) ⊆ K^{PGL_n(F)}`** —— 即"`Z` 被 `PGL` 固定"（源 `:270–271`），
**这是第 191 轮之后 `⊆` 方向唯一剩下的输入**。 -/
theorem phiK_fixes_ZCanon [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) :
    ∀ z ∈ ZCanon F r n D, (phiKAlgEquiv F r n A) z = z := by
  intro z hz
  have hz' : z ∈ IntermediateField.adjoin F (Set.range D.centK) := hz
  refine IntermediateField.adjoin_induction (F := F) (s := Set.range D.centK)
    (motive := fun x _ => (phiKAlgEquiv F r n A) x = x) ?_ ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨c, rfl⟩
    exact phiK_fixes_centK F r n D A c
  · intro x
    exact (phiKAlgEquiv F r n A).commutes x
  · intro x y _ _ ihx ihy
    rw [map_add, ihx, ihy]
  · intro x _ ihx
    rw [map_inv₀, ihx]
  · intro x y _ _ ihx ihy
    rw [map_mul, ihx, ihy]

#print axioms phiK_fixes_ZCanon

/-- ★★★★★ **`Z(F,n,r) ⊆ (M_n(K))^{PGL_n(F)}`** —— `Z` 的纯量矩阵像落在 `fixedByPGL` 里。

**收口**：与 §39 的 `adjoin_le_fixedByPGL`（`Z` 与 `R` 生成 ⟹ 固定）合并，即得
`thm:14.16` 的 `⊆` 方向（`UD = R·Z ⊆ (M_n(K))^{PGL}`），**在结构束 `GenericDivisionData`
之下无条件成立**。 -/
theorem scalar_mem_fixedByPGL [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (z : ↥(ZCanon F r n D)) :
    algebraMap ↥(ZCanon F r n D) (Matrix (Fin n) (Fin n) (SField F r n)) z
      ∈ fixedByPGL F r n := by
  intro A
  show psiK F r n A (algebraMap ↥(ZCanon F r n D) (Matrix (Fin n) (Fin n) (SField F r n)) z)
    = algebraMap ↥(ZCanon F r n D) (Matrix (Fin n) (Fin n) (SField F r n)) z
  rw [IsScalarTower.algebraMap_apply ↥(ZCanon F r n D) (SField F r n)
      (Matrix (Fin n) (Fin n) (SField F r n)) z]
  change psiK F r n A (Matrix.scalar (Fin n) (algebraMap ↥(ZCanon F r n D) (SField F r n) z))
    = Matrix.scalar (Fin n) (algebraMap ↥(ZCanon F r n D) (SField F r n) z)
  rw [psiK_scalar]
  congr 1
  exact phiK_fixes_ZCanon F r n D A ↑z z.2

#print axioms scalar_mem_fixedByPGL

/-- ★★★★★★ **`thm:14.16` 的 `⊆` 方向（`UD ⊆ (M_n(K))^{PGL_n(F)}`）在结构束下无条件成立**。

源 `raw/Saltman1999ch14.tex:321`："We have already observed that `UD(F,n,r) ⊂ (M_n(K))^{PGL_n(F)}`."

**只用结构束的第一个字段**（`cor:14.8(a)`：`C` 的像是纯量矩阵）：
§39 的 `adjoin_le_fixedByPGL`（`Z` 与 `R` 生成 ⟹ 固定）＋ §40 的 `scalar_mem_fixedByPGL`
（`Z ⊆ (M_n(K))^{PGL}`，由 `phiK_fixes_ZCanon` ＋ `psiK_scalar`）。 -/
theorem UD_le_fixedByPGL [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    ∀ x ∈ Algebra.adjoin ↥(ZCanon F r n D) (Set.range (genMatKF F r n)),
      x ∈ fixedByPGL F r n :=
  adjoin_le_fixedByPGL F r n (ZCanon F r n D) (fun z => scalar_mem_fixedByPGL F r n D z)

#print axioms UD_le_fixedByPGL

end GenericDivisionBundle

/-! ## §41 **L1 审计精确化 ＋ 等化子步的 `η` 层**（`thm:14.16` 的 `⊇` 方向准备）

**(一) L1 精确化**。第 192 轮的 `GenericDivisionData` 只有一条字段（`cor:14.8(a)`：
`C(F,n,r)` 的像是纯量矩阵）。本节给出**精确的双向刻画**：

> `Nonempty (GenericDivisionData F r n)` ⟺ `∃ κ : C →ₐ[F] K, ∀ c, (c 的像) = scalar (κ c)`。

**审计价值**：这把"结构束是否非空洞"**精确化为一条已发表命题**，而不是一个自由假设。
`cor:14.8(a)` 由 `lem:14.7`（`Ξ = {X_1^iX_2^j}` 是 `M_n(K)` 的 `K`-基）得出，
Saltman 引 `rowen1980polynomial` p.29 ⟹ **PI 理论**；本工作区**未机检**它，
故存在性登记为 `⚠-unverified`（**引文锚定**）。（**具体模型 `n = 1` 仍未做**，如实登记。）

**(二) 等化子步的 `η` 层**。`thm:14.16` 的 `⊇` 方向（源 `:321`）走：

> Define `η_1, η_2 : K → K ⊗_Z K` by `η_1(x) = x ⊗ 1`, `η_2(x) = 1 ⊗ x`. … Since the `η_i`
> are equal on `Z`, the `θ_i = Id ⊗ η_i` are equal on `UD(F,n,r)`. … Since `Z` is a field,
> it is clear that for `x ∈ K`, `x ∈ Z` iff `η_1(x) = η_2(x)`. Since `UD` is a vector space
> over `Z`, for `α ∈ M_n(K)`, `α ∈ UD` iff `θ_1(α) = θ_2(α)`.

本节机检其中**两条**：
* `etaK1_eq_etaK2_on_Z`：**`η₁ = η₂` 在 `Z` 上**（源文 "Since the `η_i` are equal on `Z`"）；
* `tensorMap_id_eta_tmul_one`：**`Id_A ⊗ η₁` 与 `Id_A ⊗ η_₂` 在 `A` 的像上相等**，
即 "the `θ_i` are equal on `UD`" 的一般形态（取 `A = UD`）。

**未做（下一轮）**：(i) "`x ∈ Z ⟺ η_1 x = η_2 x`"（**等化子事实**，需 `K` 的 `Z`-基含 `1`）；
(ii) `UD ⊗_Z K ≅ M_n(K)`（`thm:14.5`）——两者就位后 `α ∈ UD ⟺ θ_1α = θ_2α` 即可收口。 -/

open scoped TensorProduct

section L1

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **L1 非空洞性的精确形式**：结构束 `GenericDivisionData` **可居住**当且仅当
`cor:14.8(a)` 成立（`C(F,n,r)` 的像是 `S` 上的纯量矩阵）。

**审计价值**：这条把"结构束是否非空"这个模糊问题**精确化为一条已发表命题**——
Saltman 1999 由 `lem:14.7`（`Ξ` 是 `M_n(K)` 的 `K`-基）得到 `cor:14.8(a)`
（引 `rowen1980polynomial` p.29）；本工作区**未机检**它，故 `GenericDivisionData`
的存在性标 `⚠-unverified`（引文锚定），而**不是**"未加论证的自由假设"。 -/
theorem nonempty_genericDivisionData_iff :
    Nonempty (GenericDivisionData F r n) ↔
      ∃ κ : ↥(genericCenter F r n) →ₐ[F] SField F r n,
        ∀ c : ↥(genericCenter F r n),
          ((c.1 : ↥(genericMatrixAlgebra F r n)) : Matrix (Fin n) (Fin n) (S F r n)).map
            (algebraMap (S F r n) (SField F r n)) = Matrix.scalar (Fin n) (κ c) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.centK, D.centK_spec⟩
  · rintro ⟨κ, hκ⟩
    exact ⟨⟨κ, hκ⟩⟩

#print axioms nonempty_genericDivisionData_iff

end L1

section Equalizer

variable (F : Type) [Field F] (r n : ℕ)

/-- `η₁`：源文 `η_1(x) = x ⊗ 1`（`raw/Saltman1999ch14.tex:321`），`Z = Z(F,n,r) ⊂ K`。 -/
noncomputable def etaK1 (Z : IntermediateField F (SField F r n)) :
    SField F r n →ₐ[↥Z] TensorProduct ↥Z (SField F r n) (SField F r n) :=
  Algebra.TensorProduct.includeLeft

/-- `η₂`：源文 `η_2(x) = 1 ⊗ x`。 -/
noncomputable def etaK2 (Z : IntermediateField F (SField F r n)) :
    SField F r n →ₐ[↥Z] TensorProduct ↥Z (SField F r n) (SField F r n) :=
  Algebra.TensorProduct.includeRight

/-- ★★★ **源文 `:321` 的 "Since the `η_i` are equal on `Z`"** —— 机检形态。

两式都等于 `algebraMap ↥Z (K ⊗_Z K) z`（`includeLeft`／`includeRight` 都是 `↥Z`-线性的）。 -/
theorem etaK1_eq_etaK2_on_Z (Z : IntermediateField F (SField F r n)) (z : ↥Z) :
    etaK1 F r n Z (algebraMap ↥Z (SField F r n) z)
      = etaK2 F r n Z (algebraMap ↥Z (SField F r n) z) := by
  rw [AlgHom.commutes (etaK1 F r n Z) z, AlgHom.commutes (etaK2 F r n Z) z]

#print axioms etaK1_eq_etaK2_on_Z

/-- ★★★ **源文 `:321` 的 "the `θ_i` are equal on `UD(F,n,r)`"** —— 一般形态：
对任意 `↥Z`-代数 `A`，`Id_A ⊗ η_1` 与 `Id_A ⊗ η_2` 在 `A` 的像（`a ⊗ 1`）上相等。

**这就是等化子步的"一半"**：`θ₁` 与 `θ₂` 在 `UD` 上相等，从而在 `R(F,n,r)` 上相等
（`R ⊆ UD`），这正是 `thm:14.15` 的前提。 -/
theorem tensorMap_id_eta_tmul_one (Z : IntermediateField F (SField F r n))
    (A : Type) [Ring A] [Algebra ↥Z A] (i : Fin 2) (a : A) :
    Algebra.TensorProduct.map (AlgHom.id ↥Z A)
        (match i with | 0 => etaK1 F r n Z | _ => etaK2 F r n Z)
        (a ⊗ₜ[↥Z] (1 : SField F r n))
      = a ⊗ₜ[↥Z] (1 : TensorProduct ↥Z (SField F r n) (SField F r n)) := by
  rw [Algebra.TensorProduct.map_tmul]
  simp

#print axioms tensorMap_id_eta_tmul_one



end Equalizer

/-! ## §42 **等化子事实：`Z` 在等化子内 ＋ 等化子集是子域**（`⊇` 方向的域论输入，收窄到一条）

源 `raw/Saltman1999ch14.tex:321`：

> Since `Z` is a field, it is clear that for `x ∈ K`, `x ∈ Z` iff `η_1(x) = η_2(x)`.

第 193 轮已机检 `η₁ = η₂` **在 `Z` 上**（`etaK1_eq_etaK2_on_Z`）。本节把该事实
**从"逐点相等"提升为"等化集是子域"**，并把整个 `iff` 收窄为**一条具名谓词**：

* `etaK1_eq_etaK2_of_mem`：`x ∈ Z → η₁x = η₂x`（源文 `iff` 的 `⟸`）；
* `etaEq_add`／`etaEq_mul`／**`etaEq_inv`**／`etaEq_algebraMap`：等化集对 `+`／`·`／`⁻¹`
  与 `F` 封闭——**这就是"Since `Z` is a field"那句的机检内容**
  （`⁻¹` 的封闭性不靠 `map_inv`（`K ⊗_Z K` 不是域，无 `Inv`），而靠
  `x·x⁻¹ = 1` 在交换环中**逆唯一**）；
* **`EqualizerHyp Z := ∀ x, η₁x = η₂x → x ∈ Z`**：**`(A) thm:14.16` 的 `⊇` 方向唯一的
  域论输入**；`equalizerHyp_iff` 说明它补足后即得源文那个 `iff`。

**证明难点（如实登记）**：`⟹` 方向需要一个 `Z`-基含 `1`（或等价的分离泛函），
实质是 `K ⊗_Z K` 中 `x ⊗ 1` 与 `1 ⊗ x` 的**基坐标比较**；本工作区**未做**。 -/

section EtaEqualizer

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **`Z` 在等化子内**：`x ∈ Z ⟹ η₁(x) = η₂(x)`（源文 "the `η_i` are equal on `Z`"）。 -/
theorem etaK1_eq_etaK2_of_mem (Z : IntermediateField F (SField F r n))
    {x : SField F r n} (hx : x ∈ Z) : etaK1 F r n Z x = etaK2 F r n Z x := by
  have h : x = algebraMap ↥Z (SField F r n) ⟨x, hx⟩ := rfl
  rw [h]
  exact etaK1_eq_etaK2_on_Z F r n Z ⟨x, hx⟩

#print axioms etaK1_eq_etaK2_of_mem

/-- 等化集对加法封闭（`{x | η₁x = η₂x}` 是 `K` 的加法子群）。 -/
theorem etaEq_add {x y : SField F r n} (Z : IntermediateField F (SField F r n))
    (hx : etaK1 F r n Z x = etaK2 F r n Z x) (hy : etaK1 F r n Z y = etaK2 F r n Z y) :
    etaK1 F r n Z (x + y) = etaK2 F r n Z (x + y) := by
  rw [map_add, map_add, hx, hy]

/-- 等化集对乘法封闭。 -/
theorem etaEq_mul {x y : SField F r n} (Z : IntermediateField F (SField F r n))
    (hx : etaK1 F r n Z x = etaK2 F r n Z x) (hy : etaK1 F r n Z y = etaK2 F r n Z y) :
    etaK1 F r n Z (x * y) = etaK2 F r n Z (x * y) := by
  rw [map_mul, map_mul, hx, hy]

/-- 等化集对求逆封闭（**这就是源文 "Since `Z` is a field" 的用处**）。 -/
theorem etaEq_inv {x : SField F r n} (Z : IntermediateField F (SField F r n))
    (hx : etaK1 F r n Z x = etaK2 F r n Z x) :
    etaK1 F r n Z x⁻¹ = etaK2 F r n Z x⁻¹ := by
  by_cases h0 : x = 0
  · subst h0
    rw [_root_.inv_zero, map_zero, map_zero]
  · have hb : etaK1 F r n Z x * etaK1 F r n Z x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    have hc : etaK2 F r n Z x * etaK2 F r n Z x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    rw [← hx] at hc
    have hca : etaK2 F r n Z x⁻¹ * etaK1 F r n Z x = 1 := by
      rw [mul_comm]; exact hc
    calc etaK1 F r n Z x⁻¹ = 1 * etaK1 F r n Z x⁻¹ := (one_mul _).symm
      _ = (etaK2 F r n Z x⁻¹ * etaK1 F r n Z x) * etaK1 F r n Z x⁻¹ := by rw [hca]
      _ = etaK2 F r n Z x⁻¹ * (etaK1 F r n Z x * etaK1 F r n Z x⁻¹) := by rw [mul_assoc]
      _ = etaK2 F r n Z x⁻¹ := by rw [hb, mul_one]

#print axioms etaEq_inv

/-- ★★ **等化集含 `F`**。 -/
theorem etaEq_algebraMap (Z : IntermediateField F (SField F r n)) (c : F) :
    etaK1 F r n Z (algebraMap F (SField F r n) c)
      = etaK2 F r n Z (algebraMap F (SField F r n) c) := by
  rw [IsScalarTower.algebraMap_apply F ↥Z (SField F r n) c,
    AlgHom.commutes (etaK1 F r n Z) (algebraMap F ↥Z c),
    AlgHom.commutes (etaK2 F r n Z) (algebraMap F ↥Z c)]

#print axioms etaEq_algebraMap

/-- ★★★★★ **等化子事实（唯一剩余输入，精确形式）**：

`∀ x : K, η₁(x) = η₂(x) → x ∈ Z`。

源文 `raw/Saltman1999ch14.tex:321`："Since `Z` is a field, it is clear that for `x ∈ K`,
`x ∈ Z` iff `η_1(x) = η_2(x)`."

**已机检的反方向**：`etaK1_eq_etaK2_of_mem`（`∈ Z → 相等`）＋ `etaEq_add`／`etaEq_mul`／
`etaEq_inv`／`etaEq_algebraMap`（等化集是**子域**，故"`Z` 在等化子内"与"等化子就是 `Z`"
只差反向包含）。

**证明难点（如实登记）**：需要 `K` 的一个 `Z`-基含 `1`（或等价的分离泛函 `K →ₗ[Z] Z`），
本工作区**未做**；`⟹` 方向的域论实质是 `K ⊗_Z K` 中 `x⊗1` 与 `1⊗x` 的基坐标比较。
本谓词是 `(A) thm:14.16` 的 `⊇` 方向**唯一**的域论输入。 -/
def EqualizerHyp (Z : IntermediateField F (SField F r n)) : Prop :=
  ∀ x : SField F r n, etaK1 F r n Z x = etaK2 F r n Z x → x ∈ Z

/-- ★ **等化子事实 ⟺ 源文那个 `iff`**（我方已有反向，故此谓词补足全部内容）。 -/
theorem equalizerHyp_iff (Z : IntermediateField F (SField F r n)) :
    EqualizerHyp F r n Z ↔
      ∀ x : SField F r n, (etaK1 F r n Z x = etaK2 F r n Z x ↔ x ∈ Z) := by
  constructor
  · intro h x
    exact ⟨h x, fun hx => etaK1_eq_etaK2_of_mem F r n Z hx⟩
  · intro h x hx
    exact (h x).mp hx

#print axioms equalizerHyp_iff

end EtaEqualizer


/-! ## §43 **等化子域 `etaEqField`** —— 缺口 `EqualizerHyp` 的对象化

第 194 轮把源文 `:321` 的 `iff` 收窄为谓词 `EqualizerHyp Z`。本节把**等化集本身**
对象化为一个**中间域** `etaEqField Z`，于是缺口取得最简形态：

> `EqualizerHyp Z  ⟺  etaEqField Z = Z`（`equalizerHyp_iff_etaEqField_eq`）。

**为何值得对象化**：源文的论证结构是"`Z` 是域 ⟹ 等化子（作为域）就是 `Z`"；
把等化子做成 `IntermediateField` 之后，**反向包含**成为域之间的包含，可直接交给
`le_antisymm`，而不必逐点操作。

**封闭性来源（逐条）**：`+`／`·`／`0`／`1`／`algebraMap` 由 `η₁, η₂` 是环同态；
`⁻¹` 由 "`x·x⁻¹ = 1` ＋ 交换环中逆唯一"（`K ⊗_Z K` **不是域**，故无 `map_inv`，见 R102）。 -/

section EtaField

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **等化子域** `{x : K | η₁(x) = η₂(x)}` —— 源文 `:321` 的 "`x ∈ Z` iff
`η_1(x) = η_2(x)`" 中的**左端对象**，**是一个中间域**。

封闭性由 `η₁, η₂` 是环同态给出（`+`／`·`／`1`／`0`／`algebraMap`）；`⁻¹` 由
"`x·x⁻¹ = 1` ＋ 交换环中逆唯一"给出（`K ⊗_Z K` 不是域，故不能用 `map_inv`，见 R102）。 -/
noncomputable def etaEqField (Z : IntermediateField F (SField F r n)) :
    IntermediateField F (SField F r n) where
  carrier := {x | etaK1 F r n Z x = etaK2 F r n Z x}
  mul_mem' := fun ha hb => etaEq_mul F r n Z ha hb
  one_mem' := by
    show etaK1 F r n Z 1 = etaK2 F r n Z 1
    rw [map_one, map_one]
  add_mem' := fun ha hb => etaEq_add F r n Z ha hb
  zero_mem' := by
    show etaK1 F r n Z 0 = etaK2 F r n Z 0
    rw [map_zero, map_zero]
  algebraMap_mem' := fun c => etaEq_algebraMap F r n Z c
  inv_mem' := fun x hx => etaEq_inv F r n Z hx

#print axioms etaEqField

/-- ★★★ **`Z ⊆` 等化子域**（源文 "the `η_i` are equal on `Z`" 的域形式）。 -/
theorem Z_le_etaEqField (Z : IntermediateField F (SField F r n)) :
    Z ≤ etaEqField F r n Z :=
  fun _ hx => etaK1_eq_etaK2_of_mem F r n Z hx

#print axioms Z_le_etaEqField

/-- ★★★★★ **等化子事实 ＝ "等化子域就是 `Z`"**：`EqualizerHyp` 与 `etaEqField = Z` 等价。

**这是 `(A) thm:14.16` 的 `⊇` 方向唯一域论输入的**最简形态**：源文说"等化子就是 `Z`"，
第 194 轮的 `tensorMap_id_eta_tmul_one` ＋ 本节的 `Z_le_etaEqField` 给出 `⊇`，
反向包含即 `EqualizerHyp`。 -/
theorem equalizerHyp_iff_etaEqField_eq (Z : IntermediateField F (SField F r n)) :
    EqualizerHyp F r n Z ↔ etaEqField F r n Z = Z := by
  constructor
  · intro h
    exact le_antisymm h (Z_le_etaEqField F r n Z)
  · intro h x hx
    have : x ∈ etaEqField F r n Z := hx
    rw [h] at this
    exact this

#print axioms equalizerHyp_iff_etaEqField_eq

end EtaField


/-! ## §44 **等化子事实从"含 `1` 的 `Z`-基"推出** —— `EqualizerHyp` 的核心已证

第 195 轮把 `thm:14.16` 的 `⊇` 方向唯一域论输入收窄为 `EqualizerHyp Z`（等化子域 `= Z`）。
本节证明：**只要 `K` 有一个含 `1` 的 `Z`-基，`EqualizerHyp` 成立**——即坐标提取（分离泛函）
那一步**已机检**。

**证明（三段，全部机检）**：
1. **坐标泛函** `φ := (Finsupp.lapply i₀) ∘ b.repr : K →ₗ[↥Z] ↥Z`，故 `φ (b i₀) = 1`；
2. 若 `x ⊗ 1 = 1 ⊗ x`，对两边施加 `TensorProduct.map φ id`：`φx ⊗ 1 = φ1 ⊗ x = 1 ⊗ x`；
3. 用 `TensorProduct.lid` 压成 `(φ x) • 1 = x`，即 **`x = ↑(φ x) ∈ Z`**。∎

**为何必须走分离泛函（负面结果，已登记）**：若改证"被一切 `Z`-自同态固定 ⟹ `x ∈ Z`"，
该命题在**纯不可分扩张**下**为假**（`Aut = {id}`，而 `x ∉ Z` 可以存在）。故分离泛函不可替代。

**唯一剩余**：`K` 上**存在**含 `1` 的 `Z`-基（`Module.Free.chooseBasis` ＋ 基替换），
或等价的分离泛函——纯线性代数，与域论无关。 -/

section EqualizerProof

open Module

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **等化子事实，条件是"存在含 `1` 的 `Z`-基"**。

取**坐标泛函** `φ := (Finsupp.lapply i₀) ∘ b.repr : K →ₗ[↥Z] ↥Z`（故 `φ (b i₀) = 1`）。
若 `x ⊗ 1 = 1 ⊗ x`，对两边施加 `TensorProduct.map φ id` 得 `φx ⊗ 1 = φ1 ⊗ x = 1 ⊗ x`，
再用 `TensorProduct.lid` 压成 `(φ x) • 1 = x`，故 **`x = ↑(φ x) ∈ Z`**。

**为何必须走分离泛函**：若改用"被一切 `Z`-自同态固定 ⟹ `x ∈ Z`"，该命题在**纯不可分扩张**
下**为假**（`Aut = {id}` 而 `x ∉ Z` 可以存在）。 -/
theorem equalizerHyp_of_basis {ι : Type} (Z : IntermediateField F (SField F r n))
    (b : Basis ι ↥Z (SField F r n)) (i₀ : ι) (h1 : b i₀ = 1) :
    EqualizerHyp F r n Z := by
  classical
  intro x hx
  set φ : SField F r n →ₗ[↥Z] ↥Z := (Finsupp.lapply i₀).comp b.repr.toLinearMap with hφ
  have hφb : φ (b i₀) = 1 := by simp [hφ]
  have hφ1 : φ (1 : SField F r n) = 1 := by rw [← h1]; exact hφb
  have hx' : x ⊗ₜ[↥Z] (1 : SField F r n) = (1 : SField F r n) ⊗ₜ[↥Z] x := hx
  have hm : TensorProduct.map φ (LinearMap.id : SField F r n →ₗ[↥Z] SField F r n)
      (x ⊗ₜ[↥Z] (1 : SField F r n))
      = TensorProduct.map φ (LinearMap.id : SField F r n →ₗ[↥Z] SField F r n)
          ((1 : SField F r n) ⊗ₜ[↥Z] x) := by rw [hx']
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, hφ1] at hm
  have hkey : ((φ x : ↥Z) : SField F r n) = x := by
    have h1' := congrArg (TensorProduct.lid ↥Z (SField F r n)) hm
    simpa [TensorProduct.lid_tmul, Algebra.smul_def] using h1'
  rw [← hkey]
  exact (φ x).2

#print axioms equalizerHyp_of_basis

end EqualizerProof


/-! ## §45 **等化子事实的完整证明（无条件）** —— 缺口 ① 关闭

第 195 轮把 `thm:14.16` 的 `⊇` 方向唯一域论输入收窄为 `EqualizerHyp Z`（等化子域 `= Z`）；
第 198 轮证了"若 `K` 有含 `1` 的 `Z`-基则成立"。本节去掉该假设：**`EqualizerHyp` 无条件成立**。

**关键观察（省掉"基含 `1`"）**：只需一个 `φ : K →ₗ[↥Z] ↥Z` 满足 `φ 1 = 1`，不需要基含 `1`。
**构造**：取任一 `Z`-基 `b`，令 `a := b.repr 1 ≠ 0`（因 `1 ≠ 0`）；取 `i₀` 使 `a i₀ ≠ 0`，
置 `φ := (a i₀)⁻¹ • (坐标泛函 i₀)`。则 `φ 1 = (a i₀)⁻¹ · a i₀ = 1`。

**收口**：`x ⊗ 1 = 1 ⊗ x` ⟹ `φx ⊗ 1 = φ1 ⊗ x = 1 ⊗ x` ⟹（`TensorProduct.lid`）⟹
`φx • 1 = x` ⟹ **`x = ↑(φx) ∈ Z`**。于是

* `eta_eq_iff_mem`：**`x ∈ Z ⟺ η₁(x) = η₂(x)`**（源文 `:321` 的 `iff` 本体，无条件）；
* `etaEqField_eq`：**等化子域 `= Z`**（第 195 轮收窄的缺口关闭）。

**为何必须走分离泛函（负面结果）**：若改证"被一切 `Z`-自同态固定 ⟹ `x ∈ Z`"，
该命题在**纯不可分扩张**下**为假**（`Aut = {id}` 而 `x ∉ Z` 可以存在）。 -/

section EqualizerUncond

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★ **存在取值 `1` 在 `1` 上的坐标泛函**：`∃ φ : K →ₗ[↥Z] ↥Z, φ 1 = 1`。

**构造**：取 `K` 的任一 `Z`-基 `b`，令 `a := b.repr 1`（`a ≠ 0`，因 `1 ≠ 0`）；
取 `i₀` 使 `a i₀ ≠ 0`，置 `φ := (a i₀)⁻¹ • (坐标泛函 i₀)`。则
`φ 1 = (a i₀)⁻¹ · a i₀ = 1`。**不需要"基含 `1`"**。 -/
theorem exists_functional_one (Z : IntermediateField F (SField F r n)) :
    ∃ φ : SField F r n →ₗ[↥Z] ↥Z, φ 1 = 1 := by
  classical
  let b := Module.Free.chooseBasis ↥Z (SField F r n)
  have ha : b.repr (1 : SField F r n) ≠ 0 := by
    intro h
    have h1 : (1 : SField F r n) = 0 := b.repr.injective (by rw [h, map_zero])
    exact one_ne_zero h1
  have hex : ∃ i, b.repr (1 : SField F r n) i ≠ 0 := by
    by_contra h
    exact ha (Finsupp.ext (by simpa using h))
  obtain ⟨i₀, hi₀⟩ := hex
  refine ⟨(b.repr (1 : SField F r n) i₀)⁻¹ •
    ((Finsupp.lapply i₀).comp b.repr.toLinearMap), ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, Finsupp.lapply_apply]
  exact inv_mul_cancel₀ hi₀

#print axioms exists_functional_one

/-- ★★★★★ **等化子事实（无条件）**：`EqualizerHyp Z` 对**任意**中间域 `Z ⊆ K` 成立。

由 `exists_functional_one` 取 `φ`（`φ 1 = 1`），复现第 198 轮的三段论证：
`x ⊗ 1 = 1 ⊗ x` ⟹ `φx ⊗ 1 = φ1 ⊗ x = 1 ⊗ x` ⟹（`TensorProduct.lid`）⟹ `φx • 1 = x`
⟹ **`x = ↑(φx) ∈ Z`**。 -/
theorem equalizerHyp_uncond (Z : IntermediateField F (SField F r n)) :
    EqualizerHyp F r n Z := by
  obtain ⟨φ, hφ1⟩ := exists_functional_one F r n Z
  intro x hx
  have hx' : x ⊗ₜ[↥Z] (1 : SField F r n) = (1 : SField F r n) ⊗ₜ[↥Z] x := hx
  have hm : TensorProduct.map φ (LinearMap.id : SField F r n →ₗ[↥Z] SField F r n)
      (x ⊗ₜ[↥Z] (1 : SField F r n))
      = TensorProduct.map φ (LinearMap.id : SField F r n →ₗ[↥Z] SField F r n)
          ((1 : SField F r n) ⊗ₜ[↥Z] x) := by rw [hx']
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq, hφ1] at hm
  have hkey : ((φ x : ↥Z) : SField F r n) = x := by
    have h1' := congrArg (TensorProduct.lid ↥Z (SField F r n)) hm
    simpa [TensorProduct.lid_tmul, Algebra.smul_def] using h1'
  rw [← hkey]
  exact (φ x).2

#print axioms equalizerHyp_uncond

/-- ★★★★★★ **源文 `:321` 的 `iff` 本体（无条件）**：
`x ∈ Z ⟺ η₁(x) = η₂(x)`，对任意中间域 `Z ⊆ K`。 -/
theorem eta_eq_iff_mem (Z : IntermediateField F (SField F r n)) (x : SField F r n) :
    etaK1 F r n Z x = etaK2 F r n Z x ↔ x ∈ Z :=
  (equalizerHyp_iff F r n Z).mp (equalizerHyp_uncond F r n Z) x

#print axioms eta_eq_iff_mem

/-- ★★★★★ **源文 "`Z` 是域" 的收口**：**等化子域就是 `Z`**（第 195 轮收窄的缺口现已关闭）。 -/
theorem etaEqField_eq (Z : IntermediateField F (SField F r n)) :
    etaEqField F r n Z = Z :=
  (equalizerHyp_iff_etaEqField_eq F r n Z).mp (equalizerHyp_uncond F r n Z)

#print axioms etaEqField_eq

end EqualizerUncond


/-! ## §46 **θ 层结构束** —— `thm:14.16` 的 `⊇` 方向的第二个具名输入

`thm:14.16` 的 `⊇` 方向（源 `:321–323`）需要两个映射

> Define `η_1, η_2 : K → K ⊗_Z K` … Consider `M_n(K) = UD ⊗_Z K` … Define
> `θ_i = Id ⊗ η_i`.

`η_i` 层已由 §41／§45 完备（`etaK1`／`etaK2`，`eta_eq_iff_mem` 无条件）。本节把 **`θ_i` 层**
（即 `M_n(K) = UD ⊗_Z K` 那一层，`thm:14.5`）收成**第二个具名结构束** `GenericDivisionTheta`：

| 字段 | 出处 |
|---|---|
| `Theta₁`／`Theta₂` | 源文 "`θ_i = Id ⊗ η_i : M_n(K) → M_n(K ⊗_Z K)`" |
| `agree_on_UD` | 源文 "Since the `η_i` are equal on `Z`, the `θ_i` are equal on `UD`"（§41 的一般形态） |
| **`eq_iff`** | 源文 "for `α ∈ M_n(K)`, `α ∈ UD` iff `θ_1(α) = θ_2(α)`" —— **`thm:14.5`（`dim_Z UD = n²`）＋ §45 `eta_eq_iff_mem` 的合成** |

**射程（勿夸大）**：三个字段都是**线性代数结构性事实**（`UD` 是 `M_n(K)` 的一个 `Z`-型），
**不含 `PGL`-不变量的内容**——后者由 `thm:14.15`（第 188 轮 ✅）供给。
**`eq_iff` 是 `⊇` 方向唯一剩下的线性代数输入**；`mem_UDCanon_of_theta_eq` 表明它一旦就位，
"`θ₁α = θ₂α` ⟹ `α ∈ UD`" 即一步完成。

另：本节把 §40 的 `UD` 抽名为 `UDCanon`，并给出 `UDCanon_le_fixedByPGL`（`⊆` 方向的重述）。 -/

section ThetaBundle

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **`UD(F,n,r) = R·Z`** 作为 `↥(ZCanon D)`-子代数（第 192 轮的定义抽出成名）。 -/
noncomputable def UDCanon (D : GenericDivisionData F r n) :
    Subalgebra ↥(ZCanon F r n D) (Matrix (Fin n) (Fin n) (SField F r n)) :=
  Algebra.adjoin ↥(ZCanon F r n D) (Set.range (genMatKF F r n))

#print axioms UDCanon

/-- ★★★★ **θ 层结构束**：源文 `:321` 的两个映射
`θ_i = Id_{UD} ⊗ η_i : M_n(K) → M_n(K ⊗_Z K)` 及其**等化子性质**。

**三个字段的内容与出处**：
* `Theta₁`／`Theta₂`：源文 "Define `θ_i : M_n(K) → M_n(K ⊗_Z K)` by `θ_i = Id ⊗ η_i`"；
* `agree_on_UD`：源文 "Since the `η_i` are equal on `Z`, the `θ_i` are equal on `UD`"
  （第 193 轮的 `tensorMap_id_eta_tmul_one` 是其**一般形态**；此处按 `M_n(K)` 口径登记）；
* **`eq_iff`**：源文 "Since `UD` is a vector space over `Z`, for `α ∈ M_n(K)`,
  `α ∈ UD` iff `θ_1(α) = θ_2(α)`" —— **这是 `thm:14.5`（`UD ⊗_Z K ≅ M_n(K)`，
  `dim_Z UD = n²`）＋ 第 199 轮 `eta_eq_iff_mem` 的合成**。

**射程**：三字段都是**线性代数结构性事实**（`UD` 是 `M_n(K)` 的一个 `Z`-型），
**不含** `PGL`-不变量的内容；后者由 `thm:14.15`（第 188 轮 ✅）供给。 -/
structure GenericDivisionTheta (D : GenericDivisionData F r n) where
  /-- `θ₁ = Id_{UD} ⊗ η₁`。 -/
  Theta₁ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[↥(ZCanon F r n D)]
    Matrix (Fin n) (Fin n) (TensorProduct ↥(ZCanon F r n D) (SField F r n) (SField F r n))
  /-- `θ₂ = Id_{UD} ⊗ η₂`。 -/
  Theta₂ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[↥(ZCanon F r n D)]
    Matrix (Fin n) (Fin n) (TensorProduct ↥(ZCanon F r n D) (SField F r n) (SField F r n))
  /-- `θ₁ = θ₂` 在 `UD` 上（源文 "the `θ_i` are equal on `UD(F,n,r)`"）。 -/
  agree_on_UD : ∀ u ∈ UDCanon F r n D, Theta₁ u = Theta₂ u
  /-- **等化子性质**：`α ∈ UD ⟺ θ₁α = θ₂α`（源文 `:321` 的 "`α ∈ UD` iff `θ₁α = θ₂α`"）。 -/
  eq_iff : ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
    α ∈ UDCanon F r n D ↔ Theta₁ α = Theta₂ α

#print axioms GenericDivisionTheta

/-- ★★★★ **`⊇` 方向的收口步**：若 `θ₁α = θ₂α`，则 `α ∈ UD`（直接由结构束的 `eq_iff`）。 -/
theorem mem_UDCanon_of_theta_eq (D : GenericDivisionData F r n)
    (T : GenericDivisionTheta F r n D) {α : Matrix (Fin n) (Fin n) (SField F r n)}
    (h : T.Theta₁ α = T.Theta₂ α) : α ∈ UDCanon F r n D :=
  (T.eq_iff α).mpr h

#print axioms mem_UDCanon_of_theta_eq

/-- ★ **`UD ⊂ (M_n(K))^{PGL}`（第 192 轮结果）用 `UDCanon` 的名字重述**——
两处 `Algebra.adjoin` 的定义相同，故直接由 `UD_le_fixedByPGL` 得到。 -/
theorem UDCanon_le_fixedByPGL [Nonempty (Fin n)] (D : GenericDivisionData F r n) :
    ∀ x ∈ UDCanon F r n D, x ∈ fixedByPGL F r n :=
  UD_le_fixedByPGL F r n D

#print axioms UDCanon_le_fixedByPGL

/-- ★★ **θ 束的 L1 精确形式**：`GenericDivisionTheta D` 可居住 ⟺
存在两个 `↥Z`-代数同态 `M_n(K) → M_n(K ⊗_Z K)`，在 `UD` 上相等，且**等化子恰为 `UD`**。
（与 §41 的 `nonempty_genericDivisionData_iff` 同一手法：把"是否非空洞"写成精确命题。） -/
theorem nonempty_theta_iff (D : GenericDivisionData F r n) :
    Nonempty (GenericDivisionTheta F r n D) ↔
      ∃ (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[↥(ZCanon F r n D)]
          Matrix (Fin n) (Fin n) (TensorProduct ↥(ZCanon F r n D)
            (SField F r n) (SField F r n))),
        (∀ u ∈ UDCanon F r n D, Θ₁ u = Θ₂ u) ∧
        (∀ α : Matrix (Fin n) (Fin n) (SField F r n),
          α ∈ UDCanon F r n D ↔ Θ₁ α = Θ₂ α) := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.Theta₁, T.Theta₂, T.agree_on_UD, T.eq_iff⟩
  · rintro ⟨Θ₁, Θ₂, h1, h2⟩
    exact ⟨⟨Θ₁, Θ₂, h1, h2⟩⟩

#print axioms nonempty_theta_iff

end ThetaBundle


/-! ## §47 **缺口 ③ 具名 ＋ `UD` 在 `S^{PGL}` 除法下封闭**（`⊇` 方向的最后一块）

源文 `:323` 的这一步：

> By Lemma 14.13, `α = β/g` where `β ∈ M_n(S)^{PGL_n(F)}` and `g ∈ S^{PGL_n(F)}`.
> Thus it suffices to assume `α ∈ M_n(S)^{PGL_n(F)}`.

从 `β ∈ UD` 推 `α = β/g ∈ UD` 需要 **`g ∈ Z`**。这正是缺口 ③：

> `S(F,n,r)` 的 `PGL`-不变元落在 `Z(F,n,r)` 里，即 `S^{PGL} ⊆ C = R ∩ S`。

这是 **Procesi 第一基本定理的一半**（不变多项式由字迹生成，而字迹在 `R` 中），
与 `cor:14.8(a)` 同属 PI 理论层；本工作区**未机检**，故具名为 `SFixedLeZ`。

**本轮机检的引理** `UDCanon_inv_smul_mem`：**缺口 ③ 一旦成立，`β ∈ UD ⟹ g⁻¹ • β ∈ UD`**
（机制：`g = algebraMap z` ⟹ `g⁻¹ = algebraMap z⁻¹` ⟹ `UD` 是 `↥Z`-子代数）。
故 `⊇` 方向的最后一块**由 ③ 唯一承载**。 -/

section Gap3

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **缺口 ③（具名）**：`S(F,n,r)` 的 `PGL`-不变元落在 `Z = ZCanon D` 里。

源文 `:323` 用 `α = β/g`（`g ∈ S^{PGL}`，`lem:14.13`）从 `β ∈ UD` 推 `α ∈ UD`，这需要
`g ∈ Z`。而 `S^{PGL} ⊆ C = R ∩ S` 是 **Procesi 第一基本定理的一半**（不变多项式由字迹生成，
而字迹在 `R` 中），与 `cor:14.8(a)` 同属 PI 理论层。

**射程**：本谓词只陈述"`PGL`-不变多项式是 `Z` 的元素"，**不含** `S^{PGL}` 的生成元刻画。 -/
def SFixedLeZ (D : GenericDivisionData F r n) : Prop :=
  ∀ g : S F r n, (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g) →
    ∃ z : ↥(ZCanon F r n D), algebraMap ↥(ZCanon F r n D) (SField F r n) z
      = algebraMap (S F r n) (SField F r n) g

#print axioms SFixedLeZ

/-- ★★★★ **`UD` 在 `S^{PGL}` 的除法下封闭**：若缺口 ③ 成立、`g` 是 `PGL`-不变的，
则 `β ∈ UD ⟹ g⁻¹ • β ∈ UD`（源文 `:323` 的 "we may assume `α ∈ M_n(S)^{PGL}`" 那一步）。

**机制**：③ 给 `z ∈ Z` 使 `algebraMap z = algebraMap g`；于是 `g⁻¹ = algebraMap z⁻¹`，
故 `g⁻¹ • β = algebraMap(z⁻¹) * β`，而 `UD` 是 `↥Z`-子代数（对 `algebraMap` 与乘法封闭）。 -/
theorem UDCanon_inv_smul_mem [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (h3 : SFixedLeZ F r n D) {g : S F r n}
    (hg : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g)
    {β : Matrix (Fin n) (Fin n) (SField F r n)} (hβ : β ∈ UDCanon F r n D) :
    (algebraMap (S F r n) (SField F r n) g)⁻¹ • β ∈ UDCanon F r n D := by
  obtain ⟨z, hz⟩ := h3 g hg
  rw [← hz, ← map_inv₀, Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hβ

#print axioms UDCanon_inv_smul_mem

end Gap3


/-! ## §48 **`(A) thm:14.16` 的最终形态** —— `⊆` 已证 ＋ `⊇` 一个具名输入

`(A)` 的陈述是 `UD(F,n,r) = (M_n(K))^{PGL_n(F)}`（源 `:315–318`）。本节把它收成
**一条机器可读的等式链**：

> `thm1416_iff_of_inputs`：`α ∈ UD ⟺ α ∈ (M_n(K))^{PGL}`，
> **`⟸` 方向以 `hUD` 为唯一输入，`⟹` 方向已机检**（`UDCanon_le_fixedByPGL`）。

于是 `(A)` 的**每一步**不是**已机检**就是**已具名**：

| 步骤 | 载体 |
|---|---|
| `UD ⊆ (M_n(K))^{PGL}` | ✅ `UDCanon_le_fixedByPGL`（§46／§40，只需 `cor:14.8(a)`） |
| `α ∈ (M_n(K))^{PGL} ⟹ α = β/g`，`β ∈ M_n(S)^{PGL}` | **④ `MatrixRatioHyp`**（本节具名；`lem:14.13` 的矩阵层，标量层已机检为 `fixed_eq_ratio`） |
| `θ₁β = θ₂β` | ✅ `thm1415_general`（第 188 轮，**无条件**） |
| `θ₁β = θ₂β ⟹ β ∈ UD` | **② `eq_iff`**（§46，`thm:14.5` 的具名形态） |
| `β ∈ UD ⟹ β/g ∈ UD` | **③ `SFixedLeZ`** ⟹ ✅ `UDCanon_inv_smul_mem`（§47） |

**射程（勿夸大）**：`⊇` 方向**未**机检；本节只机检其**形状**（`Iff` 链）与**已证的一半**，
使剩余工作成为三个**具名**谓词 `MatrixRatioHyp`／`GenericDivisionTheta.eq_iff`／`SFixedLeZ`
——它们的**内容**都是 PI 理论（Procesi FFT／`thm:14.5`／`cor:14.8(a)`），不冒充已证。 -/

section FinalShape

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **缺口 ④（`⊇` 的入口，具名）**：`lem:14.13` 的**矩阵层形态**。

源文 `:323`：`α ∈ M_n(K)^{PGL} ⟹ α = β/g`，`β ∈ M_n(S)^{PGL}`、`g ∈ S^{PGL}`。
`FixedRatio.lean` 的 `fixed_eq_ratio` 只机检了**标量层**（`a ∈ K^{PGL} ⟹ a = f/g`）；
矩阵层按源文 "As `M_n(K)` has a `PGL_n(F)` invariant basis, the second statement follows
from the first" 需要**基的等变性**（标准基被 `ψ_A` 共轭而非逐点固定），本工作区**未做**。

故把矩阵层形态具名为本谓词——它是 `⊇` 方向的**入口**（把 `α ∈ M_n(K)` 归约到 `M_n(S)`）。 -/
def MatrixRatioHyp (_D : GenericDivisionData F r n) : Prop :=
  ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
    (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, psiK F r n A α = α) →
    ∃ (β : Matrix (Fin n) (Fin n) (S F r n)) (g : S F r n),
      (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, psiA F r n A β = β) ∧
      (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g) ∧ g ≠ 0 ∧
      α = (algebraMap (S F r n) (SField F r n) g)⁻¹
        • (β.map (algebraMap (S F r n) (SField F r n)))

#print axioms MatrixRatioHyp

/-- ★★★★★ **`(A) thm:14.16` 的最终形态（一个输入）**：

`UD(F,n,r) = (M_n(K))^{PGL_n(F)}`，**以"`⊇` 方向"为唯一输入**（`⊆` 方向已机检）。

源文 `:315–324`。`hUD` 由 ②（`eq_iff`）＋ ③（`SFixedLeZ`）＋ ④（`MatrixRatioHyp`）
＋ `thm:14.15`（`thm1415_general`，无条件 ✅）合成；本件把"`(A)` ＝（已证的 `⊆`）＋（`hUD`）"
**机检为一条等式链**，于是 `(A)` 的**每一步**不是已机检就是已具名。 -/
theorem thm1416_iff_of_inputs [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (hUD : ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
      α ∈ fixedByPGL F r n → α ∈ UDCanon F r n D) :
    ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
      α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n :=
  fun α => ⟨UDCanon_le_fixedByPGL F r n D α, hUD α⟩

#print axioms thm1416_iff_of_inputs

end FinalShape


/-! ## §49 **`Ξ` 逐点 `PGL`-固定 ＋ 统一 PI 输入** —— 具名缺口由三条降为两条

**(一) 机检**：`Ξ = {X_{k₁}^i · X_{k₂}^j}` 的每个元被 `PGL_n(F)` **逐点固定**
（源文 `:270–271` 逐字），**免费**——`Ξ ⊂ R` 而 `R` 已被 §37 逐点固定。

**(二) 结构性发现**：第 202 轮列的三个具名缺口里，**②（`thm:14.5`，θ 层）与
④（`MatrixRatioHyp`，矩阵层 `lem:14.13`）用的是同一个 PI 输入**——`lem:14.7`（`Ξ` 是
`M_n(K)` 的 `K`-基）：

* ②：`Ξ` 是 `K`-基 ⟹ `M_n(K) = UD ⊗_Z K`（`dim_Z UD = n²`）；
* ④：`Ξ` 是 `K`-基 ＋ `psiA_Xi` ⟹ `α` 的 `Ξ`-系数满足 `ψ_B α = α ⟺ φ_B(c_{ij}) = c_{ij}`
  ⟹ 逐项用**标量层 `lem:14.13`**（已机检 `fixed_eq_ratio`）⟹ 通分 `g = ∏ g_{ij}`
  （`S^{PGL}` 对乘积封闭）⟹ `α = β/g`。

故 **PI 层的具名输入由三条降为两条**：**`XiSpanHyp`**（本条，覆盖 ②④）与 **`SFixedLeZ`**（③）。

**射程（勿夸大）**：本节**机检**的只有"`Ξ` 逐点固定"；上述"一个输入覆盖两处"是**文字论证**，
其推导（`Ξ`-展开 ⟹ 系数不变 ⟹ 通分）**未机检**。 -/

section XiUnified

variable (F : Type) [Field F] (r n : ℕ)

/-- `Ξ = {X_{k₁}^i · X_{k₂}^j}` 的第 `(i,j)` 元（源文 `lem:14.7` 的 `Ξ`，取 `k₁=0, k₂=1`）。 -/
noncomputable def Xi (k₁ k₂ : Fin r) (i j : ℕ) : Matrix (Fin n) (Fin n) (S F r n) :=
  (genericMatrix F r n k₁) ^ i * (genericMatrix F r n k₂) ^ j

#print axioms Xi

/-- ★★★ **`Ξ` 的每个元被 `PGL_n(F)` 逐点固定** —— 源文 `:270–271`
（"By the above observation, `Ξ` is elementwise fixed by `PGL_n(F)`"）。
**免费**：`Ξ ⊂ R`，而 `R` 已被 §37 逐点固定。 -/
theorem psiA_Xi (A : (Matrix (Fin n) (Fin n) F)ˣ) (k₁ k₂ : Fin r) (i j : ℕ) :
    psiA F r n A (Xi F r n k₁ k₂ i j) = Xi F r n k₁ k₂ i j := by
  refine psiA_fixes_genericMatrixAlgebra F r n A ?_
  exact mul_mem (pow_mem (genericMatrix_mem F r n k₁) i)
    (pow_mem (genericMatrix_mem F r n k₂) j)

#print axioms psiA_Xi

/-- ★★★★★ **统一的 PI 输入 `XiSpanHyp`**：`Ξ = {X_{k₁}^i X_{k₂}^j | i,j < n}` 的 `K`-像
**张成** `M_n(K)`（源文 `lem:14.7`："`Ξ` is a basis of `M_n(K)` over `K`" 的**张成半**）。

**为何要统一（本轮的结构性发现）**：第 202 轮列的三个具名缺口中，**②（`thm:14.5`，θ 层）与
④（`MatrixRatioHyp`，矩阵层 `lem:14.13`）用的是同一个 PI 输入**：
* ②：`Ξ` 是 `K`-基 ⟹ `M_n(K) = UD ⊗_Z K`（`dim_Z UD = n²`）；
* ④：`Ξ` 是 `K`-基 ＋ `Ξ` 逐点 `PGL`-固定（已机检 `psiA_Xi`）⟹
  `ψ_B α = α ⟺ φ_B(c_{ij}) = c_{ij}`（`α` 的 `Ξ`-系数）⟹ 逐项用**标量层 `lem:14.13`**
  （已机检 `fixed_eq_ratio`）⟹ 通分 `g = ∏ g_{ij}`（`S^{PGL}` 对乘积封闭）⟹ `α = β/g`。

故 **PI 层的具名输入由三条降为两条**：`XiSpanHyp`（覆盖 ②④）与 `SFixedLeZ`（③）。

**射程**：本条**只陈述**该输入；它如何喂给 ②／④ 的推导是**文字论证**，**未机检**。 -/
def XiSpanHyp (k₁ k₂ : Fin r) : Prop :=
  Submodule.span (SField F r n)
    (Set.range (fun p : Fin n × Fin n =>
      (Xi F r n k₁ k₂ p.1 p.2).map (algebraMap (S F r n) (SField F r n)))) = ⊤

#print axioms XiSpanHyp

end XiUnified


/-! ## §50 `S^{PGL}` 的封闭性 —— 缺口 ④ 通分步的机检骨架

缺口 ④（矩阵层 `lem:14.13`）的推导里，"通分"一步要用到：**`S^{PGL}` 对乘法封闭、
含 `1`、对有限乘积封闭**。本节机检这三件（源文 `:323` 之后的公共分母论证）。

**用途**：把 `Ξ`-展开的每个系数 `c_{ij} = f_{ij}/g_{ij}` 通分成 `f/g`，`g := ∏ g_{ij}`——
`g ∈ S^{PGL}` 由 `phiA_finset_prod_fixed` 给出。 -/

section SFixedClosed

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★ **`S^{PGL}` 对乘积封闭**（缺口 ④ 的"通分"步所需）。 -/
theorem phiA_mul_fixed {f g : S F r n}
    (hf : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A f = f)
    (hg : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g) :
    ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A (f * g) = f * g := by
  intro A
  rw [map_mul, hf A, hg A]

#print axioms phiA_mul_fixed

/-- ★★ **`1 ∈ S^{PGL}`**。 -/
theorem phiA_one_fixed : ∀ _A : (Matrix (Fin n) (Fin n) F)ˣ,
    phiA F r n A (1 : S F r n) = 1 :=
  fun A => map_one _

#print axioms phiA_one_fixed

/-- ★★★★ **有限乘积保持 `PGL`-不变** —— 缺口 ④ 的**通分**步：
对 `Ξ`-展开的每个分母 `g_{ij}` 取 `g := ∏ g_{ij}`，则 `g ∈ S^{PGL}` 且 `g ≠ 0`（各因子非零时）。

源文 `:323` 之后实际用的是 `lem:14.13` 的"公共分母"论证；本引理是它的机检骨架。 -/
theorem phiA_finset_prod_fixed {ι : Type} (s : Finset ι) (f : ι → S F r n)
    (hf : ∀ i ∈ s, ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A (f i) = f i) :
    ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A (s.prod f) = s.prod f := by
  intro A
  rw [map_prod]
  exact Finset.prod_congr rfl fun i hi => hf i hi A

#print axioms phiA_finset_prod_fixed

end SFixedClosed


/-! ## §51 **`S^{PGL}` 的商落在 `K^{PGL}` 里** —— 缺口 ④ 通分后的收尾

第 204 轮机检了 `S^{PGL}` 的**乘法**封闭（`g := ∏ g_{ij}` 那一步）；本节补上**商**：

> `f, g ∈ S^{PGL} ⟹ f/g ∈ K^{PGL}`（即 `lem:14.13` 里"取 `f/g`"的封闭性）。

**机制（三步，全机检）**：`div_eq_mul_inv` ⟹ `map_mul` ＋ `map_inv₀`
（两边都是域，故 `map_inv₀` 可用——R111）⟹ 两次 `phiKEquiv_algebraMap` ＋ `hf`／`hg`。
**关键技巧**：**先重写再取逆**，从而**无须讨论 `g ≠ 0`**（`rw` 只做等式替换）。

**用途**：缺口 ④ 的最后一步——`Ξ`-展开的系数通分后，`α = β/g` 中 `g ∈ S^{PGL}`，
故 `α` 是 `β` 乘一个 `K^{PGL}` 元素；再配 §50 的乘法封闭即完整。 -/

section DivClosed

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`S^{PGL}` 的商在 `K^{PGL}` 里**：`f, g ∈ S^{PGL}`、`g ≠ 0`
⟹ `f/g ∈ K^{PGL}`。这是 `lem:14.13` 的"取 `f/g`"那一步（缺口 ④ 通分后要用）。

**机制**：`div_eq_mul_inv` ＋ `map_mul` ＋ `map_inv₀`（两边都是域，故 `map_inv₀` 可用；见 R111）
＋ 两次 `phiKEquiv_algebraMap` ＋ 不变性 `hf`／`hg`。**无须讨论非零**——先重写再取逆。 -/
theorem phiK_div_fixed {f g : S F r n}
    (hf : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A f = f)
    (hg : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g) :
    ∀ A : (Matrix (Fin n) (Fin n) F)ˣ,
      phiKEquiv F r n A (algebraMap (S F r n) (SField F r n) f
        / algebraMap (S F r n) (SField F r n) g)
      = algebraMap (S F r n) (SField F r n) f
        / algebraMap (S F r n) (SField F r n) g := by
  intro A
  rw [div_eq_mul_inv, map_mul, map_inv₀, phiKEquiv_algebraMap,
    phiKEquiv_algebraMap, hf A, hg A]

#print axioms phiK_div_fixed

end DivClosed


/-! ## §52 **`ψ_A` 是 `φ_A`-半线性的** —— 缺口 ④ 系数不变性的关键件

> `ψ_A(c • β) = (φ_A c) • ψ_A β`，`c ∈ K`，`β ∈ M_n(K)`。

**为何是缺口 ④ 的关键件**：在 `Ξ`-展开 `α = Σ_i c_i • Ξ_i` 中（`Ξ_i` 逐点固定，`psiA_Xi`），
`ψ_A α = Σ_i (φ_A c_i) • Ξ_i`；与 `α = Σ_i c_i • Ξ_i` 逐项比较即得 **`φ_A c_i = c_i`**，
再逐项套**标量层 `lem:14.13`**（已机检 `fixed_eq_ratio`）＋ §50／§51 的通分即得 `α = β/g`。

**机制（三步）**：
1. `c • β = Matrix.scalar c * β`（`Matrix.smul_one_eq_diagonal` ＋ `Matrix.smul_mul`）；
2. `ψ_A(Matrix.scalar c) = Matrix.scalar (φ_A c)`（§45 的 `psiK_scalar`）；
3. `Matrix.scalar (φ_A c) * ψ_A β = (φ_A c) • ψ_A β`（同第 1 步反向）。

**注**：**不能**用 `Matrix.map_smul` 逐点证——其副条件是 `f (c • a) = c • f a`，
而 `φ_A` 只给 `f c * f a`；**必须先经纯量矩阵**（步骤 1、2）把 `c` 与 `ψ_A` 交换。 -/

section Semilinear

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`ψ_A` 是 `φ_A`-半线性的**：`ψ_A(c • β) = (φ_A c) • ψ_A β`，`c ∈ K`。

**这是缺口 ④ 系数不变性论证的关键件**：在 `Ξ`-展开 `α = Σ c_i • Ξ_i` 中，
`ψ_A α = Σ (φ_A c_i) • Ξ_i`（因 `Ξ_i` 逐点固定），与 `α = Σ c_i • Ξ_i` 比较即得 `φ_A c_i = c_i`。

**机制**：`(c • β).map φ = (φ c) • β.map φ`（`Matrix.map_smul`，副条件 = `φ` 的乘性），
再用 `Matrix.mul_smul`／`Matrix.smul_mul` 把 `(φ c)` 提到最外。 -/
theorem psiK_smul_semilinear (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : SField F r n)
    (β : Matrix (Fin n) (Fin n) (SField F r n)) :
    psiK F r n A (c • β) = (phiKAlgEquiv F r n A c) • psiK F r n A β := by
  rw [show c • β = Matrix.scalar (Fin n) c * β from by
      rw [show (Matrix.scalar (Fin n) c)
          = c • (1 : Matrix (Fin n) (Fin n) (SField F r n)) from
        (Matrix.smul_one_eq_diagonal c).symm, Matrix.smul_mul, one_mul], map_mul, psiK_scalar,
    show Matrix.scalar (Fin n) (phiKAlgEquiv F r n A c) * psiK F r n A β
        = (phiKAlgEquiv F r n A c) • psiK F r n A β from by
      rw [show (Matrix.scalar (Fin n) (phiKAlgEquiv F r n A c))
          = (phiKAlgEquiv F r n A c) • (1 : Matrix (Fin n) (Fin n) (SField F r n)) from
        (Matrix.smul_one_eq_diagonal _).symm, Matrix.smul_mul, one_mul]]

#print axioms psiK_smul_semilinear

end Semilinear


/-! ## §53 **`ψ_A` 在有限半线性组合上的求值** —— 缺口 ④ 系数比较的黏合件

第 206 轮的 `psiK_smul_semilinear` 只给**单项**；缺口 ④ 的比较发生在**整条 `Ξ`-展开**上。
本节把逐项半线性提升到**有限和**：

> `ψ_A (Σ_{i∈s} c_i • β_i) = Σ_{i∈s} (φ_A c_i) • ψ_A β_i`

**用途**：`α = Σ_{i∈s} c_i • Ξ_i`（有限，`Ξ` 逐点固定）⟹
`ψ_A α = Σ_{i∈s} (φ_A c_i) • Ξ_i`；与 `α = Σ_{i∈s} c_i • Ξ_i` 比较 ⟹ `φ_A c_i = c_i`。 -/

section FinsetSum

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`ψ_A` 在有限半线性组合上的求值**（缺口 ④ 系数比较的黏合件）：

`ψ_A (Σ_{i∈s} c_i • β_i) = Σ_{i∈s} (φ_A c_i) • ψ_A β_i`。

**用途**：`Ξ`-展开 `α = Σ c_i • Ξ_i` 是**有限**和（`Finsupp`），故本引理把 §52 的逐项半线性
提升到整条展开；配合 `ψ_A Ξ_i = Ξ_i`（`psiA_Xi`）得
`ψ_A α = Σ (φ_A c_i) • Ξ_i`，与 `α = Σ c_i • Ξ_i` 比较即得要证 `φ_A c_i = c_i`。 -/
theorem psiK_finset_sum {ι : Type} (A : (Matrix (Fin n) (Fin n) F)ˣ) (s : Finset ι)
    (c : ι → SField F r n) (β : ι → Matrix (Fin n) (Fin n) (SField F r n)) :
    psiK F r n A (s.sum (fun i => c i • β i))
      = s.sum (fun i => (phiKAlgEquiv F r n A (c i)) • psiK F r n A (β i)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => psiK_smul_semilinear F r n A (c i) (β i)

#print axioms psiK_finset_sum

end FinsetSum


/-! ## §54 **`XiBasisHyp`：`lem:14.7` 的逐字形态**（PI 层的唯一基性输入）

源文 `raw/Saltman1999ch14.tex:158–163` 逐字：

> Set `Ξ = {X_1^i X_2^j | 0 ≤ i, j ≤ n−1}`. **Lemma 14.7.** `Ξ` is a basis of `M_n(K)` over `K`.

第 203 轮的 `XiSpanHyp` 只取**张成半**；系数提取还需要**无关性**。本节把输入加强为
`lem:14.7` 的**逐字形态** `XiBasisHyp`（存在以 `Ξ`-像为元素的 `K`-基），并机检它**蕴含**
`XiSpanHyp`（故可直接替换，输入数不增）。

**这一条同时供给 ②（`thm:14.5`：`dim_Z UD = n²`）与 ④（矩阵层 `lem:14.13` 的系数提取）**
——与第 203 轮发现的一致。

**射程**：本谓词**只陈述**该输入。它的证明（`lem:14.7`，用循环 Galois 扩张
`Δ(L/F,σ,1)` 与 `n²×n²` 行列式论证）属 **T3**，本工作区**未做**。 -/

section XiBasis

open Module

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **PI 输入（`lem:14.7` 的逐字形态）**：`Ξ = {X_{k₁}^i X_{k₂}^j | i,j < n}` 的
`K`-像是 **`M_n(K)` 的 `K`-基**。

源文 `raw/Saltman1999ch14.tex:158–163`（逐字）：

> Set `Ξ = {X_1^i X_2^j | 0 ≤ i, j ≤ n−1}`. **Lemma 14.7.** `Ξ` is a basis of `M_n(K)` over `K`.

**这是 PI 层唯一的基性输入**：它同时供给 ②（`thm:14.5`：`dim_Z UD = n²` ⟹ `UD ⊗_Z K ≅ M_n(K)`）
与 ④（矩阵层 `lem:14.13` 的**系数提取**——两个有限和模 `Ξ`-关系比较）。
**射程**：本谓词**只陈述**该输入；它的证明（`lem:14.7`，用循环 Galois 扩张 `Δ(L/F,σ,1)` 与
行列式论证）属 **T3**，本工作区**未做**。 -/
def XiBasisHyp (k₁ k₂ : Fin r) : Prop :=
  ∃ b : Basis (Fin n × Fin n) (SField F r n) (Matrix (Fin n) (Fin n) (SField F r n)),
    ∀ p : Fin n × Fin n,
      b p = (Xi F r n k₁ k₂ p.1 p.2).map (algebraMap (S F r n) (SField F r n))

#print axioms XiBasisHyp

/-- ★★★ **基性 ⟹ 张成性**：`XiBasisHyp` 蕴含第 203 轮的 `XiSpanHyp`
（基的像张成整个空间）。故 `XiBasisHyp` 是**更强**的输入，足以替换 `XiSpanHyp`。 -/
theorem xiSpanHyp_of_xiBasisHyp {k₁ k₂ : Fin r}
    (h : XiBasisHyp F r n k₁ k₂) : XiSpanHyp F r n k₁ k₂ := by
  obtain ⟨b, hb⟩ := h
  unfold XiSpanHyp
  have hrange : Set.range (fun p : Fin n × Fin n =>
      (Xi F r n k₁ k₂ p.1 p.2).map (algebraMap (S F r n) (SField F r n)))
      = Set.range b := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, hb p⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, (hb p).symm⟩
  rw [hrange]
  exact b.span_eq

#print axioms xiSpanHyp_of_xiBasisHyp

end XiBasis


/-! ## §55 **`Basis.repr` 在基向量的半线性组合上** —— 缺口 ④ 系数提取的左半边

缺口 ④ 的系数提取链条：

```
alpha = Σ_{i∈s} c_i • Ξ_i          (Ξ 是 K-基，XiBasisHyp)
ψ_A alpha = Σ_{i∈s} (φ_A c_i) • Ξ_i   (psiA_Xi + psiK_finset_sum)
ψ_A alpha = alpha                  (hα)
────────────────────────────────────────
⟹ 送进 b.repr，取 i-坐标 ⟹ φ_A c_i = c_i
```

本节机检**送进 `b.repr` 之后的那半边**：

* `repr_smul_basis`：`b.repr (c • b i) = c • single i 1`；
* **`repr_finset_sum_basis`**：`b.repr (Σ_{i∈s} c_i • b i) = Σ_{i∈s} c_i • single i 1`。

**剩余（下一轮）**：最后一步的坐标计算
`(Σ_{i∈s} c_i • single i 1) i₀ = if i₀ ∈ s then c i₀ else 0`
（`Finsupp.single_eq_same`／`single_eq_of_ne` ＋ `Finset` 归纳），
之后 `coeff_fixed_of_basis` 即收口，缺口 ④ 的核心完成。 -/

section ReprMachinery

open Module

variable (F : Type) [Field F] (r n : ℕ) {ι : Type}

/-- ★★★ **`repr` 在单个基向量上**：`b.repr (c • b i) = c • single i 1`。 -/
theorem repr_smul_basis (b : Basis ι (SField F r n) (Matrix (Fin n) (Fin n) (SField F r n)))
    (c : SField F r n) (i : ι) :
    b.repr (c • b i) = c • Finsupp.single i (1 : SField F r n) := by
  rw [map_smul, Basis.repr_self]

#print axioms repr_smul_basis

/-- ★★★★ **`repr` 在基向量的有限半线性组合上**：
`b.repr (Σ_{i∈s} c_i • b i) = Σ_{i∈s} c_i • single i 1`。

**用途（缺口 ④ 的系数提取）**：把 `α = Σ c_i • Ξ_i` 与 `ψ_A α = Σ (φ_A c_i) • Ξ_i` 两边
都送进 `b.repr`，再取 `i`-坐标即得 `φ_A c_i = c_i`——本引理是那一步的**左半边**。 -/
theorem repr_finset_sum_basis (b : Basis ι (SField F r n)
    (Matrix (Fin n) (Fin n) (SField F r n)))
    (s : Finset ι) (c : ι → SField F r n) :
    b.repr (s.sum (fun i => c i • b i))
      = s.sum (fun i => c i • Finsupp.single i (1 : SField F r n)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => repr_smul_basis F r n b (c i) i

#print axioms repr_finset_sum_basis

end ReprMachinery


/-! ## §56 **单点函数有限和的坐标** —— 缺口 ④ 系数提取的最后一步

第 210 轮的 `repr_finset_sum_basis` 把 `b.repr (Σ_{i∈s} c_i • b i)` 算成 `Σ_{i∈s} c_i • single i 1`；
本节取它的 `i`-坐标，于是 **`b.repr` 与系数之间可以互读**：

* `finset_sum_single_apply_of_mem`：`i₀ ∈ s ⟹ (Σ_{i∈s} c_i • single i 1) i₀ = c i₀`；
* `finset_sum_single_apply_of_notMem`：`i₀ ∉ s ⟹ (…) i₀ = 0`。

**这两条 ＋ §55 ＋ §53 即完成系数提取的机械部分**：
`α = Σ c_i • Ξ_i` 与 `ψ_A α = Σ (φ_A c_i) • Ξ_i` 送进 `b.repr` 再取坐标，得 `φ_A c_i = c_i`。

**形式化要点**：陈述**不用 `if`**（`if i₀ ∈ s` 需要 `Decidable` 而定理陈述里 `classical` 管不到），
拆成 `of_mem`／`of_notMem` 两条；`of_mem` 的 `insert` 分支要用 `of_notMem`（因 `a ∉ s`），
故**先证 `of_notMem`**。 -/

section Coord

variable (F : Type) [Field F] (r n : ℕ) {ι : Type}

/-- ★★★ **不在 `s` 里时坐标为零**。 -/
theorem finset_sum_single_apply_of_notMem (s : Finset ι) (c : ι → SField F r n) {i₀ : ι}
    (h : i₀ ∉ s) :
    (s.sum (fun i => c i • Finsupp.single i (1 : SField F r n))) i₀ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : i₀ ≠ a := fun he => h (by rw [Finset.mem_insert]; exact Or.inl he)
      have h2 : i₀ ∉ s := fun hs => h (Finset.mem_insert_of_mem hs)
      rw [Finset.sum_insert ha, Finsupp.add_apply, ih h2, Finsupp.smul_apply,
        Finsupp.single_eq_of_ne h1, smul_zero, add_zero]

#print axioms finset_sum_single_apply_of_notMem

/-- ★★★★ **在 `s` 里时坐标就是系数**。 -/
theorem finset_sum_single_apply_of_mem (s : Finset ι) (c : ι → SField F r n) {i₀ : ι}
    (h : i₀ ∈ s) :
    (s.sum (fun i => c i • Finsupp.single i (1 : SField F r n))) i₀ = c i₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd h (Finset.notMem_empty i₀)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finsupp.add_apply]
      by_cases hia : i₀ = a
      · subst hia
        rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
          finset_sum_single_apply_of_notMem F r n s c ha, add_zero]
      · have h2 : i₀ ∈ s := by
          rcases Finset.mem_insert.mp h with h' | h'
          · exact absurd h' hia
          · exact h'
        rw [ih h2]
        simp [Finsupp.single_eq_of_ne, hia]


#print axioms finset_sum_single_apply_of_mem

end Coord


/-! ## §57 **系数不变性：`ψ_A`-不变元的 `Ξ`-系数被 `φ_A` 固定** —— 缺口 ④ 收口

**定理**：设 `b` 是 `M_n(K)` 的一个 `K`-基且每个 `b i` 被所有 `ψ_B` 逐点固定，
`α` 被 `ψ_A` 固定，则 `b.repr α` 的**每个系数**都被 `φ_A` 固定：
`φ_A (b.repr α i) = b.repr α i`。

**证明（五步，全部机检）**：
1. `α = Σ_j (b.repr α j) • b j`（`Basis.sum_repr`，`[Fintype ι]`）；
2. `ψ_A α = Σ_j (φ_A (b.repr α j)) • b j`（`psiK_finset_sum` ＋ `hb`）；
3. 两和相等（`hα`）；
4. 送进 `b.repr`（`repr_finset_sum_basis`）；
5. 取 `i`-坐标（`finset_sum_single_apply_of_mem`，`s := univ`）。

**配合 §54 `XiBasisHyp`（`b` ＝ `Ξ`-基）与 `psiA_Xi`（`hb`）**，即得源文 `:323` 所需的
"`α` 的 `Ξ`-系数是 `PGL`-不变的"，再逐个套**标量层 `lem:14.13`**（`fixed_eq_ratio`）
与 §50／§51 的通分，即 **`MatrixRatioHyp`**。

**形式化要点（三处调参，均已在稿中解决）**：
* `Basis.sum_repr` **要 `[Fintype ι]`**——取 `ι` 有限（`XiBasisHyp` 给的是 `Fin n × Fin n`），
  于是 `s := univ`，**不必处理 `support` 与"`i ∉ s`"**；
* `rw [hαsum]` 会**同时改写右侧**（R66 同族）——须 `conv_lhs => rw [hαsum]`；
* `hsum` 收尾要 `exact hαsum`（`rw [hα]` 后目标正是 `hαsum`）。 -/

section CoeffFixed

open Module

variable (F : Type) [Field F] (r n : ℕ) {ι : Type}

theorem coeff_fixed_of_basis [Fintype ι] (b : Basis ι (SField F r n)
    (Matrix (Fin n) (Fin n) (SField F r n)))
    (hb : ∀ (i : ι) (B : (Matrix (Fin n) (Fin n) F)ˣ), psiK F r n B (b i) = b i)
    (A : (Matrix (Fin n) (Fin n) F)ˣ) {α : Matrix (Fin n) (Fin n) (SField F r n)}
    (hα : psiK F r n A α = α) (i : ι) :
    phiKAlgEquiv F r n A (b.repr α i) = b.repr α i := by
  classical
  have hαsum : α = Finset.univ.sum (fun j => b.repr α j • b j) := (b.sum_repr α).symm
  have hψ : psiK F r n A α
      = Finset.univ.sum (fun j => (phiKAlgEquiv F r n A (b.repr α j)) • b j) := by
    conv_lhs => rw [hαsum]
    rw [psiK_finset_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hb j A]
  have hsum : Finset.univ.sum (fun j => (phiKAlgEquiv F r n A (b.repr α j)) • b j)
      = Finset.univ.sum (fun j => b.repr α j • b j) := by rw [← hψ, hα]; exact hαsum
  have hrepr := congrArg b.repr hsum
  rw [repr_finset_sum_basis, repr_finset_sum_basis] at hrepr
  have hcoord := DFunLike.congr_fun hrepr i
  rwa [finset_sum_single_apply_of_mem F r n Finset.univ _ (Finset.mem_univ i),
    finset_sum_single_apply_of_mem F r n Finset.univ _ (Finset.mem_univ i)] at hcoord

#print axioms coeff_fixed_of_basis

end CoeffFixed

/-! ## §58 **`XiBasisHyp` ⟹ 系数不变性** —— 缺口 ④ 的输入-后果接线

第 203 轮的发现是"**一个 PI 输入覆盖 ② 与 ④**"。本节把 ④ 的那一半**机检成一条扣子**：

> `XiBasisHyp k₁ k₂` ＋ `α` 被所有 `ψ_B` 固定 ⟹ **`α` 的每个 `Ξ`-系数都是 `φ_A`-不变的**。

三件拼成（全机检）：
* `XiBasisHyp`（§54）供给基 `b`；
* `psiA_Xi`（§49）＋ `psiK_map_algebraMapS`（§38）供给 `ψ_B (b p) = b p`；
* `coeff_fixed_of_basis`（§57）供给结论。

**射程**：本条给"系数不变"。要得 `MatrixRatioHyp` 还需**逐项套标量 `lem:14.13`**
（`fixed_eq_ratio`）＋ 通分（§50／§51）——那一步**未机检**。 -/

section XiCoeffFixed

variable (F : Type) [Field F] (r n : ℕ)

open Module

/-- ★★★★★ **`XiBasisHyp` ⟹ 系数不变性**（缺口 ④ 的输入-后果接线）。

设 `Ξ = {X_{k₁}^i X_{k₂}^j}` 的 `K`-像是 `M_n(K)` 的 `K`-基（`XiBasisHyp`），
`α` 被所有 `ψ_B` 固定。则 `α` 在 `Ξ`-基下的**每个系数都是 `φ_A`-不变的**。

**这就是第 203 轮"一个 PI 输入覆盖 ②④"中 ④ 的那一半**：
* `XiBasisHyp` 供给基 `b`；
* `psiA_Xi`（§49）供给 `ψ_B (b p) = b p`；
* `coeff_fixed_of_basis`（§57）供给结论。 -/
theorem coeff_fixed_of_xi {k₁ k₂ : Fin r} (h : XiBasisHyp F r n k₁ k₂)
    (A : (Matrix (Fin n) (Fin n) F)ˣ)
    {α : Matrix (Fin n) (Fin n) (SField F r n)}
    (hα : ∀ B : (Matrix (Fin n) (Fin n) F)ˣ, psiK F r n B α = α)
    (p : Fin n × Fin n) :
    phiKAlgEquiv F r n A ((Classical.choose h).repr α p)
      = (Classical.choose h).repr α p := by
  classical
  refine coeff_fixed_of_basis F r n (Classical.choose h) ?_ A (hα A) p
  intro i B
  rw [Classical.choose_spec h i, psiK_map_algebraMapS F r n B,
    psiA_Xi F r n B k₁ k₂ i.1 i.2]

#print axioms coeff_fixed_of_xi

end XiCoeffFixed

/-! ## §59 **矩阵层 `lem:14.13`（缺口 ④）组装完成** —— `MatrixRatioHyp` 机检（模 PI-A）

源文 `raw/Saltman1999ch14.tex` `lem:14.13`（label 在 `:275`）的**矩阵层**是它的**第二个陈述**（`:276`，逐字）：

> "If `β ∈ M_n(K)^{PGL_n(F)}`, then `β = α/g` where `α ∈ M_n(S)^{PGL_n(F)}`
> and `g ∈ S^{PGL_n(F)}`."

其证明里给出机制（`:280`，逐字）：

> "As `M_n(K)` has a `PGL_n(F)` invariant basis, the second statement follows from the first."

而 `thm:14.16` 的证明（`:323`，逐字）正是消费它：

> "By Lemma 14.13, `α = β/g` where `β ∈ M_n(S)^{PGL_n(F)}` and `g ∈ S^{PGL_n(F)}`."

**记号消歧（源文自身两处相反）**：`lem:14.13` 用 `β` 记 `M_n(K)` 的元素、`α` 记 `M_n(S)` 的元素；
`thm:14.16` 的证明反过来。本件一律取 `thm:14.16` 的用法：
`α ∈ M_n(K)`（被 `ψ` 固定的那个）、`β ∈ M_n(S)`（分子）、`g ∈ S`（公共分母）。

本节把这句话**机检**成 `MatrixRatioHyp`（§48 具名的缺口 ④）：

> `XiBasisHyp`（＝ `lem:14.7`：`Ξ` 是 `M_n(K)` 的 `K`-基）⟹ `MatrixRatioHyp F r n D`。

**五步（全部机检）**：
1. 取 `Ξ`-基 `b`（`XiBasisHyp`），写 `α = Σ_p (b.repr α p) • b p`（`Basis.sum_repr`）；
2. 每个系数被 `φ_A` 固定（`coeff_fixed_of_xi`，§58）；
3. 逐项套**标量层 `lem:14.13`**（`fixed_eq_ratio`，`FixedRatio.lean`）：
   `b.repr α p = f_p / g_p`，`f_p, g_p ∈ S^{PGL}`、`g_p ≠ 0`；
4. **通分**：`C_p := ∏_{q ≠ p} g_q`、`G := ∏_q g_q`、`β := Σ_p (f_p · C_p) • Ξ_p ∈ M_n(S)`；
5. `α = G⁻¹ • β.map (S → K)` —— 逐项**望远镜** `f_p·C_p / G = f_p / g_p`
   （`algebraMap_prod_erase_mul_inv`）。

**新增件（7 条）**：
* `psiA_scalar`：`ψ_A` 在 `S`-纯量矩阵上，`ψ_A(scalar c) = scalar (φ_A c)`；
* `psiA_smul_semilinear`：`ψ_A` 在 `S`-层的半线性（缺口 ④ 在 `S` 层的对应物，§52 是 `K` 层）；
* `smul_eq_algebraMap_smul`：`S`-纯量与 `K`-纯量在矩阵上一致（`IsScalarTower`）；
* `map_algebraMap_smul`／`map_algebraMap_sum`：`Matrix.map (S → K)` 与纯量／有限和交换
  （**不走 `Matrix.map_smul`**：其副条件是标量线性，而 `algebraMap` 给的是乘性——R115）；
* `algebraMap_prod_erase_mul_inv`：通分望远镜；
* `matrixRatioHyp_of_xiBasisHyp`：主装配。

**代价与边界**：主装配**只**需要 `3 ≤ n`（来自 `fixed_eq_ratio` 的 `lem:14.12` 用法；本战役 `n = 9`），
外加**唯一**输入 `XiBasisHyp`（＝ `lem:14.7`，PI 理论，T3 未做）。
于是 `(A) thm:14.16` 的五个步骤里，`MatrixRatioHyp` 从"具名"变为"模 PI-A 已机检"。
**不含** `(B) prop:14.19`；**不**声称 `(A)` 已证。 -/

section MatrixRatioBuild

variable (F : Type) [Field F] (r n : ℕ)

open Module

/-- ★★★ **`ψ_A` 在 `S`-纯量矩阵上**：`ψ_A(Matrix.scalar c) = Matrix.scalar (φ_A c)`。

§52／§53 的 `K` 层对应物是 `psiK_scalar`；本件是 `S` 层版本，供 §59 的 `β`-固定性使用。
**机制**：`psiA_apply` 展开 ＋ `Matrix.map` 在纯量矩阵上逐点求值 ＋
`Matrix.scalar_comm`（纯量矩阵与任意矩阵交换）＋ `constMat A * constMat A⁻¹ = 1`。 -/
theorem psiA_scalar (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : S F r n) :
    psiA F r n A (Matrix.scalar (Fin n) c) = Matrix.scalar (Fin n) (phiA F r n A c) := by
  show constMat F r n (↑A) * (Matrix.scalar (Fin n) c).map (phiA F r n A)
      * constMat F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) : Matrix (Fin n) (Fin n) F)
    = Matrix.scalar (Fin n) (phiA F r n A c)
  have hmap : (Matrix.scalar (Fin n) c).map (phiA F r n A)
      = Matrix.scalar (Fin n) (phiA F r n A c) := by
    ext i j
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar]
    · simp [Matrix.scalar, hij]
  rw [hmap, ← Matrix.scalar_comm (phiA F r n A c) (fun _ => Commute.all _ _)
    (constMat F r n (↑A)), mul_assoc,
    show constMat F r n (↑A) * constMat F r n (((A⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)) :
      Matrix (Fin n) (Fin n) F) = 1 from by
      rw [← constMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, constMat_one],
    mul_one]

#print axioms psiA_scalar

/-- ★★★★ **`ψ_A` 在 `S`-层的半线性**：`ψ_A(c • Y) = (φ_A c) • ψ_A Y`，`c ∈ S`。

**用途**：§59 的 `β = Σ_p (f_p · C_p) • Ξ_p` 的 `PGL`-固定性——

`ψ_A β = Σ_p (φ_A(f_p · C_p)) • ψ_A(Ξ_p) = Σ_p (f_p · C_p) • Ξ_p = β`
（`φ_A`，`f_p, C_p` 不变；`ψ_A(Ξ_p) = Ξ_p` 是 §49 的 `psiA_Xi`）。

**机制（与 §52 逐字同构，只是换 `S` 层）**：`c • Y = Matrix.scalar c * Y`，故
`ψ_A(c • Y) = ψ_A(scalar c) * ψ_A Y = scalar (φ_A c) * ψ_A Y = (φ_A c) • ψ_A Y`。
**不能**用 `Matrix.map_smul` 逐点证（R115：其副条件是标量线性）——必须先经**纯量矩阵**。 -/
theorem psiA_smul_semilinear (A : (Matrix (Fin n) (Fin n) F)ˣ) (c : S F r n)
    (Y : Matrix (Fin n) (Fin n) (S F r n)) :
    psiA F r n A (c • Y) = (phiA F r n A c) • psiA F r n A Y := by
  rw [show c • Y = Matrix.scalar (Fin n) c * Y from by
      rw [show (Matrix.scalar (Fin n) c)
          = c • (1 : Matrix (Fin n) (Fin n) (S F r n)) from
        (Matrix.smul_one_eq_diagonal c).symm, Matrix.smul_mul, one_mul],
    map_mul, psiA_scalar,
    show Matrix.scalar (Fin n) (phiA F r n A c) * psiA F r n A Y
        = (phiA F r n A c) • psiA F r n A Y from by
      rw [show (Matrix.scalar (Fin n) (phiA F r n A c))
          = (phiA F r n A c) • (1 : Matrix (Fin n) (Fin n) (S F r n)) from
        (Matrix.smul_one_eq_diagonal _).symm, Matrix.smul_mul, one_mul]]

#print axioms psiA_smul_semilinear

/-- ★★★ **`S`-纯量与 `K`-纯量在 `K`-矩阵上一致**：`c • Y = (algebraMap c) • Y`。

**为何需要**：`Matrix.map_smul` 天然给 `S`-纯量形式；而 §59 的最后一步要乘
`(algebraMap G)⁻¹ : K`，须把两者接起来。**机制**：两边都等于 `algebraMap c` 的纯量矩阵乘
（`Algebra.smul_def` ＋ `IsScalarTower`）。 -/
theorem smul_eq_algebraMap_smul (c : S F r n)
    (Y : Matrix (Fin n) (Fin n) (SField F r n)) :
    c • Y = (algebraMap (S F r n) (SField F r n) c) • Y := by
  rw [Algebra.smul_def, Algebra.smul_def,
    IsScalarTower.algebraMap_apply (S F r n) (SField F r n)
      (Matrix (Fin n) (Fin n) (SField F r n))]

#print axioms smul_eq_algebraMap_smul

/-- ★★★★ **`Matrix.map (S → K)` 与 `S`-纯量交换**：
`(c • Y).map (S → K) = (algebraMap c) • Y.map (S → K)`。

**为何不用 `Matrix.map_smul`**（R115）：其副条件是**标量线性** `f (c • a) = c • f a`，
而 `algebraMap` 只给乘性 `algebraMap (c * a) = algebraMap c * algebraMap a`；
两者**按定义**一致（`c • a = c * a`、`c • algebraMap a = algebraMap c * algebraMap a`），
故 `Matrix.map_smul` 可用于 `S`-纯量形式，再由 `smul_eq_algebraMap_smul` 转到 `K`-纯量。 -/
theorem map_algebraMap_smul (c : S F r n) (Y : Matrix (Fin n) (Fin n) (S F r n)) :
    (c • Y).map (algebraMap (S F r n) (SField F r n))
      = (algebraMap (S F r n) (SField F r n) c)
        • Y.map (algebraMap (S F r n) (SField F r n)) := by
  rw [Matrix.map_smul (algebraMap (S F r n) (SField F r n)) c
    (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]
  exact smul_eq_algebraMap_smul F r n c _

#print axioms map_algebraMap_smul

/-- ★★★ **`Matrix.map (S → K)` 与有限和交换**。

mathlib 本 pin **无** `Matrix.map_sum`（只有 `Matrix.map_add`），故按 `Finset` 归纳证：
`Matrix.map_add` 逐步拆开（R113：记法不稳时优先用底层 `Finset` API）。 -/
theorem map_algebraMap_sum {ι : Type} (s : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) (S F r n)) :
    (s.sum A).map (algebraMap (S F r n) (SField F r n))
      = s.sum (fun p => (A p).map (algebraMap (S F r n) (SField F r n))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.map_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Matrix.map_add (algebraMap (S F r n) (SField F r n))
          (fun x y => map_add _ x y), ih]

#print axioms map_algebraMap_sum

/-- ★★★★★ **通分望远镜**：`(∏_q g_q)⁻¹ · (f_p · ∏_{q≠p} g_q) = f_p · (g_p)⁻¹`。

**用途**：§59 的最后一步——`α = G⁻¹ • β.map` 与 `α = Σ_p (f_p/g_p) • b_p` 的**逐项比较**。
**机制**：`Finset.mul_prod_erase` 给 `G = g_p · C_p`（`C_p := ∏_{q≠p} g_q`），
故两边同为 `(f_p · C_p)/(g_p · C_p)`，由 `mul_div_mul_right` 约去（须 `algebraMap C_p ≠ 0`，
即各 `g_q ≠ 0` ＋ `algebraMap` 单射）。 -/
theorem algebraMap_prod_erase_mul_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    (f g : ι → S F r n) (hg : ∀ q, g q ≠ 0) (p : ι) :
    (algebraMap (S F r n) (SField F r n) (Finset.univ.prod g))⁻¹
        * algebraMap (S F r n) (SField F r n) (f p * (Finset.univ.erase p).prod g)
      = algebraMap (S F r n) (SField F r n) (f p)
        * (algebraMap (S F r n) (SField F r n) (g p))⁻¹ := by
  classical
  have hne : ∀ q, algebraMap (S F r n) (SField F r n) (g q) ≠ 0 := by
    intro q h
    exact hg q (IsFractionRing.injective (S F r n) (SField F r n) (by rw [h, map_zero]))
  have hCne : algebraMap (S F r n) (SField F r n) ((Finset.univ.erase p).prod g) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => hne q)
  have hG : algebraMap (S F r n) (SField F r n) (Finset.univ.prod g)
      = algebraMap (S F r n) (SField F r n) (g p)
        * algebraMap (S F r n) (SField F r n) ((Finset.univ.erase p).prod g) := by
    rw [← map_mul, Finset.mul_prod_erase Finset.univ g (Finset.mem_univ p)]
  rw [hG, map_mul (algebraMap (S F r n) (SField F r n))
    (f p) ((Finset.univ.erase p).prod g),
    ← div_eq_inv_mul, mul_div_mul_right _ _ hCne, div_eq_mul_inv]

#print axioms algebraMap_prod_erase_mul_inv

/-- ★★★★★ **缺口 ④ 收口：`MatrixRatioHyp` 由 `XiBasisHyp` 推出**（`lem:14.13` 的矩阵层）。

**陈述**：若 `Ξ` 的 `K`-像是 `M_n(K)` 的基（`XiBasisHyp` ＝ `lem:14.7`），
则每个 `ψ`-不变的 `α ∈ M_n(K)` 都是 `β/g`，`β ∈ M_n(S)^{PGL}`、`g ∈ S^{PGL}`（`g ≠ 0`）。

**五步**（见本节头 docstring）：`Basis.sum_repr` 展开 ⟹ `coeff_fixed_of_xi`（§58）取系数不变
⟹ `fixed_eq_ratio`（标量层 `lem:14.13`）逐项取分数 ⟹ 通分（`C_p`／`G`／`β`）
⟹ `algebraMap_prod_erase_mul_inv` 望远镜比较。

**`β` 的 `PGL`-固定性**：`psiA_smul_semilinear` ＋ `phiA_mul_fixed`（§50）＋
`phiA_finset_prod_fixed`（§50）＋ `psiA_Xi`（§49）——**不用**任何 PI 输入。

**唯一的 PI 输入**：`XiBasisHyp`（`lem:14.7`，属 T3）。故本定理把 §48 表中的缺口 ④
从"具名"降为"模 PI-A 已机检"。
**射程（勿夸大）**：不含 `(B) prop:14.19`；不声称 `(A) thm:14.16` 已证（仍差 PI-A／PI-B）。 -/
theorem matrixRatioHyp_of_xiBasisHyp {k₁ k₂ : Fin r} (hn : 3 ≤ n)
    (h : XiBasisHyp F r n k₁ k₂) (D : GenericDivisionData F r n) :
    MatrixRatioHyp F r n D := by
  classical
  intro α hα
  set b : Basis (Fin n × Fin n) (SField F r n)
    (Matrix (Fin n) (Fin n) (SField F r n)) := Classical.choose h with hbdef
  have hbspec : ∀ p : Fin n × Fin n,
      b p = (Xi F r n k₁ k₂ p.1 p.2).map (algebraMap (S F r n) (SField F r n)) :=
    fun p => Classical.choose_spec h p
  have hex : ∀ p : Fin n × Fin n, ∃ f g : S F r n,
      (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A f = f) ∧
      (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiA F r n A g = g) ∧ g ≠ 0 ∧
        b.repr α p = algebraMap (S F r n) (SField F r n) f
          / algebraMap (S F r n) (SField F r n) g := by
    intro p
    exact fixed_eq_ratio (F := F) (r := r) (k := n) hn (b.repr α p)
      (fun A => coeff_fixed_of_xi F r n h A hα p)
  choose fp gp hfp hgp hgpne hratio using hex
  set C : Fin n × Fin n → S F r n := fun p => (Finset.univ.erase p).prod gp with hCdef
  set G : S F r n := Finset.univ.prod gp with hGdef
  set β : Matrix (Fin n) (Fin n) (S F r n) :=
    Finset.univ.sum (fun p => (fp p * C p) • Xi F r n k₁ k₂ p.1 p.2) with hβdef
  have hCfix : ∀ p A, phiA F r n A (C p) = C p := by
    intro p A
    exact phiA_finset_prod_fixed F r n (Finset.univ.erase p) gp (fun q _ => hgp q) A
  have hβfix : ∀ A, psiA F r n A β = β := by
    intro A
    rw [hβdef, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [psiA_smul_semilinear, map_mul, hfp p A, hCfix p A, psiA_Xi]
  have hGfix : ∀ A, phiA F r n A G = G := by
    simpa only [hGdef] using
      (phiA_finset_prod_fixed F r n Finset.univ gp (fun q _ => hgp q))
  have hGne : G ≠ 0 := by
    rw [hGdef]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => hgpne q)
  refine ⟨β, G, hβfix, hGfix, hGne, ?_⟩
  have hαrep : α = Finset.univ.sum (fun p => b.repr α p • b p) :=
    (Basis.sum_repr b α).symm
  have hβmap : β.map (algebraMap (S F r n) (SField F r n))
      = Finset.univ.sum
          (fun p => (algebraMap (S F r n) (SField F r n) (fp p * C p)) • b p) := by
    rw [hβdef, map_algebraMap_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_algebraMap_smul, ← hbspec p]
  rw [hαrep, hβmap, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hratio p, div_eq_mul_inv, smul_smul,
    algebraMap_prod_erase_mul_inv F r n fp gp hgpne p]

#print axioms matrixRatioHyp_of_xiBasisHyp

end MatrixRatioBuild


/-! ## §60 **`(A) thm:14.16` 的最终收口** —— 以三个具名输入为条件

源文 `raw/Saltman1999ch14.tex` `thm:14.16`（label 在 `:316`，逐字）：

> "`(M_n(K))^{PGL_n(F)} = UD(F,n,r)` and `K^{PGL_n(F)} = Z(F,n,r)`."

其证明的核心两句（`:321`／`:323`，逐字）：

> "Since `UD` is a vector space over `Z`, for `α ∈ M_n(K)`, `α ∈ UD` if and only if
> `θ₁(α) = θ₂(α)`."

> "Let `α ∈ M_n(K)^{PGL_n(F)}`. By Lemma 14.13, `α = β/g` … Thus it suffices to assume
> `α ∈ M_n(S)^{PGL_n(F)}`. `θ₁` and `θ₂` are equal on `R(F,n,r)` so by Theorem 14.15,
> `θ₁(α) = θ₂(α)`."

本节把这两句**逐字**机检成一条定理：`(A)` 的第一半
（`(M_n(K))^{PGL} = UD`）由**三个具名输入**推出，**再无任何技术债务**：

| 输入 | 内容 | 文献层 |
|---|---|---|
| `hX : XiBasisHyp` | `Ξ` 是 `M_n(K)` 的 `K`-基（`lem:14.7`） | **PI-A** |
| `DT : GenericDivisionTheta D` | `θ₁,θ₂` 及 `α ∈ UD ⟺ θ₁α = θ₂α`（＝`thm:14.5`＋`eta_eq_iff_mem`） | **②**（`thm:14.5`） |
| `h3 : SFixedLeZ D` | `S^{PGL} ⊆ C`（Procesi FFT 的一半） | **PI-B** |

**证明链（全机检）**：
1. `thm1416_iff_of_inputs`（§48）把目标归约为 `hUD : fixedByPGL ⊆ UD`；
2. `matrixRatioHyp_of_xiBasisHyp`（§59）给 `α = g⁻¹ • β.map`，`β ∈ M_n(S)^{PGL}`、`g ∈ S^{PGL}`；
3. `thetaRestrictS` 把 `θ_i`（`↥Z`-代数同态）沿 `S → K` 拉回成 `F`-代数同态
   （`AlgHom.restrictScalars` ＋ `AlgHom.mapMatrix (Algebra.ofId …)`）；
4. 它们在 `genericMatrix k` 上相等（因 `genMatKF k ∈ UD` 而 `DT.agree_on_UD`），
   故由 **`thm:14.15`**（`thm1415_general`，无条件机检，仅需 `[Infinite F]`）得
   `θ₁(β.map) = θ₂(β.map)`；
5. `DT.eq_iff` ⟹ `β.map ∈ UD`；`UDCanon_inv_smul_mem`（§47，用 ③）⟹ `g⁻¹ • β.map ∈ UD`；
6. `α = g⁻¹ • β.map` ⟹ `α ∈ UD`。

**诚实边界（勿夸大）**：
* `(A)` **仍未无条件证明**——上表三个输入都是**已发表**命题（PI 理论／`thm:14.5`），
  本工作区未证（T3）。本条只把"结构层"的**技术债务清零**：不再有任何未机检的**组装步骤**。
* `(B) prop:14.19`（`N = T ⋊ S_n` 版）**未开始**。
* `K^{PGL} = Z`（`thm:14.16` 的第二半）是"第一半限制到中心"，**未**在本条内机检。
* **② 与 ④ 共用 `lem:14.7` 这一点仍是文字论证**（§49 已登记）：本条的 ② 取结构束形态，
  不声称已由 `XiBasisHyp` 推出。 -/

section Thm1416Assembly

variable (F : Type) [Field F] (r n : ℕ) (D : GenericDivisionData F r n)

/-- **`AlgHom.mapMatrix` 沿 `Algebra.ofId` 就是逐项 `algebraMap` 的 `Matrix.map`**。

**为何要它**：`thetaRestrictS` 用 `AlgHom.mapMatrix (Algebra.ofId S K)` 造 `M_n(S) →ₐ[S] M_n(K)`，
而下游的陈述（`MatrixRatioHyp` 的结论、`genMatKF` 的定义）都写成 `Matrix.map (algebraMap S K)`。
两者**按定义相等**，但 `AlgHom.mapMatrix_apply` 只推到 `Matrix.map ⇑(Algebra.ofId S K)`——
**函数层**的差异 `simp` 化不掉（`ofId_apply` 是逐点的），故在此一次性转接。 -/
lemma mapMatrix_ofId_apply (Y : Matrix (Fin n) (Fin n) (S F r n)) :
    (AlgHom.mapMatrix (Algebra.ofId (S F r n) (SField F r n))) Y
      = Y.map (algebraMap (S F r n) (SField F r n)) := rfl

#print axioms mapMatrix_ofId_apply

/-- **`θ` 沿 `S → K` 的拉回**：把 `↥Z`-代数同态 `θ : M_n(K) → M_n(K ⊗_Z K)`
拉成 `F`-代数同态 `M_n(S) → M_n(K ⊗_Z K)`（`θ ∘ Matrix.map (algebraMap S K)`）。

**为何需要**：`thm:14.15`（`thm1415_general`）的陈述是关于 `M_n(S)` 上的 **`F`-代数同态**，
而 `GenericDivisionTheta` 给的是 `M_n(K)` 上的 **`↥Z`-代数同态**（源文 `:321` 的
`θ_i = Id ⊗ η_i` 只定义在 `M_n(K)` 上）。源文 `:323` 说"`θ₁` 和 `θ₂` 在 `R(F,n,r)` 上相等，
故由 Theorem 14.15 得 `θ₁(α) = θ₂(α)`"——**正是本文对 `α ∈ M_n(S)^{PGL}` 用拉回**。

**构造**：`AlgHom.restrictScalars F`（把 `↥Z`-线性降为 `F`-线性）＋ `AlgHom.comp`；
`IsScalarTower` 实例由 mathlib 自动合成（`M_n(K)` 与 `M_n(K ⊗_Z K)` 上的 `F`-代数结构）。 -/
noncomputable def thetaRestrictS
    (Θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[↥(ZCanon F r n D)]
      Matrix (Fin n) (Fin n)
        (TensorProduct ↥(ZCanon F r n D) (SField F r n) (SField F r n))) :
    Matrix (Fin n) (Fin n) (S F r n) →ₐ[F]
      Matrix (Fin n) (Fin n)
        (TensorProduct ↥(ZCanon F r n D) (SField F r n) (SField F r n)) :=
  (AlgHom.restrictScalars F Θ).comp
    (AlgHom.restrictScalars F (AlgHom.mapMatrix (Algebra.ofId (S F r n) (SField F r n))))

#print axioms thetaRestrictS

/-- ★★★★★ **`(A) thm:14.16` 的最终形态**（源文 `:321–323`）：以**三个具名输入**为条件，
`UD(F,n,r) = (M_n(K))^{PGL_n(F)}`。

**三个输入**（见本节头 docstring 的表）：`XiBasisHyp`（PI-A，`lem:14.7`）／
`GenericDivisionTheta D`（②，`thm:14.5` ＋ `eta_eq_iff_mem`）／`SFixedLeZ D`（PI-B，Procesi FFT 一半）。
**外加**：`3 ≤ n`（`fixed_eq_ratio` 的 `lem:14.12` 用法；本战役 `n = 9`）、
`[Infinite F]`（`thm:14.15` 的 `prop:14.14` 用法；`[CharZero F]` 自动给出，见 `infinite_of_charZero`）、
`[Nonempty (Fin n)]`。

**证明链**：`thm1416_iff_of_inputs`（§48）⟸ `hUD` ⟸ ④（§59）＋ `thm:14.15`（第 188 轮）
＋ `DT.eq_iff`（②）＋ `UDCanon_inv_smul_mem`（§47，用 ③）。

**射程（勿夸大）**：本条**不**证 `XiBasisHyp`／`GenericDivisionTheta`／`SFixedLeZ`
——三者都是已发表命题，属 T3。本条的意义是**组装层无技术债务**：
`(A)` 的每一步不是"已机检"就是"已具名"。 -/
theorem thm1416_of_inputs [Infinite F] [Nonempty (Fin n)] (DT : GenericDivisionTheta F r n D)
    (hn : 3 ≤ n) {k₁ k₂ : Fin r} (hX : XiBasisHyp F r n k₁ k₂)
    (h3 : SFixedLeZ F r n D) :
    ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
      α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n := by
  refine thm1416_iff_of_inputs F r n D ?_
  intro α hα
  obtain ⟨β, g, hβ, hg, hgne, hαβ⟩ :=
    matrixRatioHyp_of_xiBasisHyp F r n hn hX D α hα
  have hagree : ∀ k : Fin r,
      thetaRestrictS F r n D DT.Theta₁ (genericMatrix F r n k)
        = thetaRestrictS F r n D DT.Theta₂ (genericMatrix F r n k) := by
    intro k
    exact DT.agree_on_UD (genMatKF F r n k)
      (Algebra.subset_adjoin (Set.mem_range_self k))
  have htheta : DT.Theta₁ (β.map (algebraMap (S F r n) (SField F r n)))
      = DT.Theta₂ (β.map (algebraMap (S F r n) (SField F r n))) := by
    have h := thm1415_general (F := F) (r := r) (n := n)
      (T := TensorProduct ↥(ZCanon F r n D) (SField F r n) (SField F r n))
      (thetaRestrictS F r n D DT.Theta₁) (thetaRestrictS F r n D DT.Theta₂)
      hagree β hβ
    simpa only [thetaRestrictS, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      mapMatrix_ofId_apply] using h
  have hβUD : β.map (algebraMap (S F r n) (SField F r n)) ∈ UDCanon F r n D :=
    mem_UDCanon_of_theta_eq F r n D DT htheta
  have hαUD := UDCanon_inv_smul_mem F r n D h3 hg hβUD
  rw [hαβ]
  exact hαUD

#print axioms thm1416_of_inputs

end Thm1416Assembly


/-! ## §61 **`thm:14.16` 的第二个陈述** —— `Z(F,n,r) = K^{PGL_n(F)}`（缺口 ⑤ 具名）

源文 `raw/Saltman1999ch14.tex` `thm:14.16`（label 在 `:316`，逐字）有**两个**陈述：

> "`(M_n(K))^{PGL_n(F)} = UD(F,n,r)` and `K^{PGL_n(F)} = Z(F,n,r)`."

§60 只机检了**第一个**。本节补上**第二个**，并把它的难点精确具名：

| 方向 | 状态 |
|---|---|
| `Z ⊆ K^{PGL}` | ✅ **第 191 轮已机检**（`phiK_fixes_ZCanon`；本节重述为 `ZCanon_le_fixed`） |
| `K^{PGL} ⊆ Z` | **缺口 ⑤**（本节具名 `KPFixedLeZ`） |

**为何 `K^{PGL} ⊆ Z` 是独立的（不能用 §60 的结果推出）**：由 `(A)` 只能得
`scalar x ∈ fixedByPGL = UD`（`x ∈ K^{PGL}` 时）；要从 `scalar x ∈ UD` 得 `x ∈ Z`，需要
**`Centre(UD) = Z`（纯量矩阵意义下）**——即"`UD` 是 `Z` 上次数 `n` 的中心单代数"
（源文 `thm:14.5` 的后半，`:185`："`UD(F,n,r)` is dimension `n^2` over `Z` and hence is
central simple of degree `n`"）。这不在 `(A)`（`UD = fixedByPGL`）之内，故 ⑤ 是**新的具名输入**。

**本节结论**：`thm:14.16` 的**全文**（两个陈述）现在是**一条机检定理**
`thm1416_full_of_inputs`，以**四个**已发表输入为条件：
`XiBasisHyp`（PI-A）／`GenericDivisionTheta D`（②）／`SFixedLeZ D`（PI-B）／`KPFixedLeZ D`（⑤）。

**（B）的形式化口径（下一战役；本节不声称已做）**：源文 `prop:14.19`
（`UD = M_n(K')^N`、`Z = K'^N`）里的 `Z` 与 `K'^N` **不在同一个域里**——`Z ⊂ K` 而
`K'^N ⊂ K' = Frac(S')`，两者的等同靠 `lem:14.22` 的**单射** `R(F,n,r) ↪ M_n(S')`
（其证明用 `lem:14.21`：`X_1` 的判别式非零 ⟹ 在某扩域上 `X_1` 可对角化）。
故 `(B)` **不是** `(A)` 的"换群重做"，而要先建 `S'`-世界与 `lem:14.21／14.22` 的识别。
本工作区**未**建。 -/

section Thm1416Second

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **缺口 ⑤（具名）**：`K` 中被 `PGL_n(F)` 固定的元素都落在 `Z = ZCanon D` 里。

即 `K^{PGL_n(F)} ⊆ Z(F,n,r)`——源文 `thm:14.16` 的**第二个陈述**的**难方向**。

**为何不能由 `(A)` 推出**（见本节头 docstring）：需 `Centre(UD) = Z`（`UD` 在 `Z` 上中心单，
源文 `thm:14.5` 后半），而 `(A)` 只给 `UD = fixedByPGL`。故本节把它**具名**，不冒充已证。

**L1（非空洞性）**：假设类 `{x | ∀ A, φ_A x = x}` **非空**——含 `1`、含整个 `Z`
（`ZCanon_le_fixed`），且 `F` 的像在其中；结论类亦非空（`Z` 本身）。 -/
def KPFixedLeZ (D : GenericDivisionData F r n) : Prop :=
  ∀ x : SField F r n, (∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x) →
    ∃ z : ↥(ZCanon F r n D), algebraMap ↥(ZCanon F r n D) (SField F r n) z = x

#print axioms KPFixedLeZ

/-- ★★ **`Z ⊆ K^{PGL_n(F)}`（集合形态）** —— 第 191 轮 `phiK_fixes_ZCanon` 的重述。

**用途**：与缺口 ⑤ 拼成 `Z = K^{PGL}`（`ZCanon_eq_fixed_of_KPFixedLeZ`），
并与 §46 的 `UDCanon_le_fixedByPGL` 对称（那一条是 `(A)` 的 `⊆` 方向）。 -/
theorem ZCanon_le_fixed [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    {x : SField F r n} (hx : x ∈ ZCanon F r n D) :
    ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x :=
  fun A => phiK_fixes_ZCanon F r n D A x hx

#print axioms ZCanon_le_fixed

/-- ★★★★★ **`Z(F,n,r) = K^{PGL_n(F)}`（集合等式）**，以缺口 ⑤ 为**唯一**输入。

**证明**：`⊆` 是 `ZCanon_le_fixed`（已机检）；`⊇` 是缺口 ⑤ 的定义 ＋ `z.2`（`z ∈ Z`）。
**射程**：`⊇` **未**机检（属 `thm:14.5` 后半的 PI 理论层）。 -/
theorem ZCanon_eq_fixed_of_KPFixedLeZ [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (h5 : KPFixedLeZ F r n D) :
    ∀ x : SField F r n,
      x ∈ ZCanon F r n D ↔ ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x := by
  intro x
  constructor
  · exact ZCanon_le_fixed F r n D
  · intro hx
    obtain ⟨z, hz⟩ := h5 x hx
    rw [← hz]
    exact z.2

#print axioms ZCanon_eq_fixed_of_KPFixedLeZ

/-- ★★★★★ **`thm:14.16` 全文**（两个陈述），以**四个**已发表输入为条件。

源文 `raw/Saltman1999ch14.tex:316–318`（逐字）：
> "`(M_n(K))^{PGL_n(F)} = UD(F,n,r)` and `K^{PGL_n(F)} = Z(F,n,r)`."

**四个输入**：`XiBasisHyp`（PI-A，`lem:14.7`）／`GenericDivisionTheta D`（②，`thm:14.5`
＋`eta_eq_iff_mem`）／`SFixedLeZ D`（PI-B）／`KPFixedLeZ D`（⑤，`thm:14.5` 后半）。
外加 `3 ≤ n`、`[Infinite F]`、`[Nonempty (Fin n)]`（同 §60）。

**射程（勿夸大）**：四个输入都是已发表命题（PI 理论），本工作区**未证**（T3）。
本条只保证 `thm:14.16` 的**全文**在组装层无技术债务。 -/
theorem thm1416_full_of_inputs [Infinite F] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (DT : GenericDivisionTheta F r n D)
    (hn : 3 ≤ n) {k₁ k₂ : Fin r} (hX : XiBasisHyp F r n k₁ k₂)
    (h3 : SFixedLeZ F r n D) (h5 : KPFixedLeZ F r n D) :
    (∀ α : Matrix (Fin n) (Fin n) (SField F r n),
        α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n) ∧
      (∀ x : SField F r n,
        x ∈ ZCanon F r n D ↔ ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x) :=
  ⟨thm1416_of_inputs F r n D DT hn hX h3, ZCanon_eq_fixed_of_KPFixedLeZ F r n D h5⟩

#print axioms thm1416_full_of_inputs

end Thm1416Second


/-! ## §62 **缺口 ⑤ 的数学内容精确化** —— `UD` 在 `Z` 上中心单

§61 把 `thm:14.16` 第二陈述的难方向具名为 `KPFixedLeZ D`（`K^{PGL} ⊆ Z`）。
本节把它的**数学内容**精确化：它**等价于**（以 §60 的 `(A)` 为前提）

> `UD(F,n,r)` 的**中心**是 `Z` 的纯量像，即 `UD` 在 `Z` 上是**中心单**代数。

源文 `raw/Saltman1999ch14.tex:185`（`thm:14.5` 的收尾，逐字）：

> "Thus `UD(F,n,r)` is dimension `n^2` over `Z = Z(F,n,r)` and hence is central simple of
> degree `n`."

**两个方向**（本条只机检 `⟸`）：
* `⟸`（**已机检** `kPFixedLeZ_of_centreLeZ`）：设 `x ∈ K^{PGL}`。则 `scalar x ∈ fixedByPGL`
  （`psiK_scalar` ＋ `φ_A x = x`），由 `(A)` 得 `scalar x ∈ UD`；`scalar x` 是**中心**元
  （`Matrix.scalar_comm`），故由 `CentreLeZ` 得 `scalar x = algebraMap z`，
  `Matrix.scalar_inj` 给出 `x = algebraMap z ∘` 换序。**这一步不需要任何 PI 输入。**
* `⟹` **未**机检（需要"中心化子 ＝ 纯量"的另一半，属 PI 理论层）。

**射程（勿夸大）**：`CentreLeZ` 本身**未证**——它是 `thm:14.5` 的"中心单"一半（源文 `:185`），
与 `cor:14.8(a)`／Procesi FFT 同属 T3。本节的贡献是：**缺口 ⑤ 不再是黑箱**，
它与已发表的"`UD` 中心单"事实**逐字对应**，且其 `⟸` 接线已机检。 -/

section Gap5Prime

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **缺口 ⑤'（具名）**：`UD(F,n,r)` 的中心落在 `Z` 的纯量像里。

即：`UD` 中与 `UD` 全部元素交换的元素必是 `Z`-纯量矩阵——"`UD` 在 `Z` 上中心单"
（源文 `thm:14.5` 收尾，`:185` 逐字："`UD(F,n,r)` is dimension `n^2` over `Z` and hence is
central simple of degree `n`"）的**中心部分**。

**与缺口 ⑤ 的关系**：以 `(A)` 为前提，⑤' ⟹ ⑤（`kPFixedLeZ_of_centreLeZ`，已机检）。
反方向**未**机检。
**L1（非空洞性）**：假设类的"中心元"非空（`algebraMap z` 全是中心元，`1` 是），
结论类亦非空（`0`、`algebraMap z`）；两者都有具体对照物。 -/
def CentreLeZ (D : GenericDivisionData F r n) : Prop :=
  ∀ α ∈ UDCanon F r n D, (∀ β ∈ UDCanon F r n D, α * β = β * α) →
    ∃ z : ↥(ZCanon F r n D),
      α = algebraMap ↥(ZCanon F r n D) (Matrix (Fin n) (Fin n) (SField F r n)) z

#print axioms CentreLeZ

/-- ★★★ **纯量矩阵落进 `fixedByPGL`**：`(∀ A, φ_A x = x) ⟹ scalar x ∈ (M_n(K))^{PGL}`。

**机制**：`psiK_scalar`（§45）给 `ψ_A(scalar x) = scalar (φ_A x)`，再用 `φ_A x = x`。
**用途**：`kPFixedLeZ_of_centreLeZ` 的第一步——把 `K` 层的固定性搬到矩阵层。 -/
theorem scalar_mem_fixedByPGL_of_fixed {x : SField F r n}
    (hx : ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x) :
    Matrix.scalar (Fin n) x ∈ fixedByPGL F r n := by
  intro A
  rw [psiK_scalar]
  exact congrArg (Matrix.scalar (Fin n)) (hx A)

#print axioms scalar_mem_fixedByPGL_of_fixed

/-- ★★★★★ **⑤' ＋ `(A)` ⟹ ⑤**：`UD` 中心单 ⟹ `K^{PGL} ⊆ Z`。

**五步（全机检）**：`x ∈ K^{PGL}` ⟹ `scalar x ∈ fixedByPGL` ⟹（`(A)`）`scalar x ∈ UD`
⟹（`Matrix.scalar_comm`）`scalar x` 是 `UD` 的中心元 ⟹（`CentreLeZ`）`scalar x = algebraMap z`
⟹（`Matrix.scalar_inj`）`x = algebraMap z`。
**射程**：这一步把"`Z = K^{PGL}`"完全归约到"`UD` 中心单"，**不含** PI 输入。 -/
theorem kPFixedLeZ_of_centreLeZ [Nonempty (Fin n)] (D : GenericDivisionData F r n)
    (hA : ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
      α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n)
    (hC : CentreLeZ F r n D) : KPFixedLeZ F r n D := by
  intro x hx
  have hsc : Matrix.scalar (Fin n) x ∈ fixedByPGL F r n :=
    scalar_mem_fixedByPGL_of_fixed F r n hx
  have hmem : Matrix.scalar (Fin n) x ∈ UDCanon F r n D := (hA _).mpr hsc
  have hcent : ∀ β ∈ UDCanon F r n D,
      Matrix.scalar (Fin n) x * β = β * Matrix.scalar (Fin n) x :=
    fun β _ => Matrix.scalar_comm x (fun r' => Commute.all x r') β
  obtain ⟨z, hz⟩ := hC _ hmem hcent
  refine ⟨z, ?_⟩
  have h2 : Matrix.scalar (Fin n) x
      = Matrix.scalar (Fin n) (algebraMap ↥(ZCanon F r n D) (SField F r n) z) := by
    rw [hz, Matrix.algebraMap_eq_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar, Matrix.diagonal, Pi.algebraMap_apply]
    · simp [Matrix.scalar, Matrix.diagonal, hij]
  exact ((Matrix.scalar_inj).mp h2).symm

#print axioms kPFixedLeZ_of_centreLeZ

/-- ★★★★★ **`thm:14.16` 全文，以"中心单"形态为输入**（替代缺口 ⑤）。

**四个输入**：`XiBasisHyp`（PI-A）／`GenericDivisionTheta D`（②）／`SFixedLeZ D`（PI-B）／
**`CentreLeZ D`（⑤'）**。**射程**：四个都是已发表命题；本条只证组装与归约。 -/
theorem thm1416_full_of_centre [Infinite F] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (DT : GenericDivisionTheta F r n D)
    (hn : 3 ≤ n) {k₁ k₂ : Fin r} (hX : XiBasisHyp F r n k₁ k₂)
    (h3 : SFixedLeZ F r n D) (hC : CentreLeZ F r n D) :
    (∀ α : Matrix (Fin n) (Fin n) (SField F r n),
        α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n) ∧
      (∀ x : SField F r n,
        x ∈ ZCanon F r n D ↔ ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x) :=
  thm1416_full_of_inputs F r n D DT hn hX h3
    (kPFixedLeZ_of_centreLeZ F r n D (thm1416_of_inputs F r n D DT hn hX h3) hC)

#print axioms thm1416_full_of_centre

end Gap5Prime


/-! ## §63 **PI-B 不独立**：缺口 ⑤ ⟹ `SFixedLeZ` ⟹ `thm:14.16` 全文的输入由四条降为三条

§47 把"`β ∈ UD ⟹ g⁻¹β ∈ UD`"这一部 具名为 **PI-B** `SFixedLeZ D`（`S^{PGL} ⊆ C`），
§60 的 `(A)` 与 §61 的 `thm:14.16` 全文都以它为输入。本节机检：**PI-B 不是独立输入**
——它由**缺口 ⑤**（`K^{PGL} ⊆ Z`）**推出**。

**证明（一步）**：设 `g : S` 被所有 `φ_A` 固定。则
`φ_A(algebraMap g) = algebraMap (φ_A g) = algebraMap g`（`phiKEquiv_algebraMap`）——
即 `algebraMap g ∈ K^{PGL}`。由 ⑤ 存在 `z : ↥(ZCanon D)` 使 `algebraMap z = algebraMap g`，
正是 `SFixedLeZ` 的结论。**无需 `(A)`**。

**由此得到的输入账（本节结论）**：`thm:14.16` 全文只需**三个**已发表输入
（`XiBasisHyp`／`GenericDivisionTheta D`／`KPFixedLeZ D`），见 `thm1416_full_of_three`。

**诚实边界（勿误读）**：
* 这**不是**"难度下降"——⑤ 至少和 PI-B 一样难（实际上更强）；本节的收获是**输入清单降为三条**，
  即 PI-B 不必再作为独立项跟踪。
* `§62` 的五输入版（`SFixedLeZ` ＋ `CentreLeZ`）**保留有效**；但由 ⑤' 到 ⑤ 的那一步
  （`kPFixedLeZ_of_centreLeZ`）**需要 `(A)`**，而 `(A)` 需要 `SFixedLeZ`——
  故 `CentreLeZ` **单独**不能得到三输入版（那会循环）。三输入版用的是 ⑤ 本身。 -/

section ThreeInputs

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **缺口 ⑤ ⟹ PI-B**：`K^{PGL} ⊆ Z` 推出 `S^{PGL} ⊆ Z`。

**机制**：`phiKEquiv_algebraMap` 把 `S`-层的固定性搬到 `K` 层，再用 ⑤。
**意义**：PI-B（`SFixedLeZ`，Procesi FFT 的一半）**不是独立输入**——
它被更强的 ⑤ 蕴含。故 `thm:14.16` 全文的输入清单由四条降为三条。 -/
theorem sFixedLeZ_of_kPFixedLeZ (D : GenericDivisionData F r n)
    (h5 : KPFixedLeZ F r n D) : SFixedLeZ F r n D := by
  intro g hg
  exact h5 (algebraMap (S F r n) (SField F r n) g)
    (fun A => by rw [phiKEquiv_algebraMap, hg A])

#print axioms sFixedLeZ_of_kPFixedLeZ

/-- ★★★★★ **`(A) thm:14.16` 第一陈述的**三输入**版**（PI-B 由 ⑤ 推出）。

输入：`XiBasisHyp`（PI-A）／`GenericDivisionTheta D`（②）／`KPFixedLeZ D`（⑤）。
**射程**：三个输入都是已发表命题；本条只证组装与蕴含。 -/
theorem thm1416_of_three [Infinite F] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (DT : GenericDivisionTheta F r n D)
    (hn : 3 ≤ n) {k₁ k₂ : Fin r} (hX : XiBasisHyp F r n k₁ k₂)
    (h5 : KPFixedLeZ F r n D) :
    ∀ α : Matrix (Fin n) (Fin n) (SField F r n),
      α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n :=
  thm1416_of_inputs F r n D DT hn hX (sFixedLeZ_of_kPFixedLeZ F r n D h5)

#print axioms thm1416_of_three

/-- ★★★★★ **`thm:14.16` 全文的三输入版** —— 本战役 `thm:14.16` 的**最简输入形态**。

源文 `raw/Saltman1999ch14.tex:316–318`（两个陈述）＋ `:185`（`UD` 中心单）。
**输入**：`XiBasisHyp`（PI-A）／`GenericDivisionTheta D`（②）／`KPFixedLeZ D`（⑤）。
外加 `3 ≤ n`、`[Infinite F]`、`[Nonempty (Fin n)]`。
**射程（勿夸大）**：三个输入皆已发表、皆属 T3；本条**不**证它们。 -/
theorem thm1416_full_of_three [Infinite F] [Nonempty (Fin n)]
    (D : GenericDivisionData F r n) (DT : GenericDivisionTheta F r n D)
    (hn : 3 ≤ n) {k₁ k₂ : Fin r} (hX : XiBasisHyp F r n k₁ k₂)
    (h5 : KPFixedLeZ F r n D) :
    (∀ α : Matrix (Fin n) (Fin n) (SField F r n),
        α ∈ UDCanon F r n D ↔ α ∈ fixedByPGL F r n) ∧
      (∀ x : SField F r n,
        x ∈ ZCanon F r n D ↔ ∀ A : (Matrix (Fin n) (Fin n) F)ˣ, phiKEquiv F r n A x = x) :=
  ⟨thm1416_of_three F r n D DT hn hX h5,
    ZCanon_eq_fixed_of_KPFixedLeZ F r n D h5⟩

#print axioms thm1416_full_of_three

end ThreeInputs


/-! ## §64 **`GenericDivisionData` 的具体模型（`n = 1`）** —— L1 非空洞见证 ＋ `cor:14.8(a)` 的可证实例

v6 §8 红线 5 列的**未做项**："`nonempty_genericDivisionData_iff` 已把'束是否非空'精确化为
`cor:14.8(a)`；**具体模型 `n = 1` 仍未做**"。本节补上。

**为何 `n = 1` 可做**：`M_1(S)` 是**交换**环（`Fin 1` 只有一个指标），故
`C(F,r,1) = Centre(R) = ⊤`（`genericCenter_one_eq_top`），于是
`centK` 可以取"`(0,0)` 项 ＋ `algebraMap`"（`centK_one`），而 `centK_spec`
（＝ `cor:14.8(a)`）退化为"1×1 矩阵的 `(0,0)` 项就是那个纯量"（`centK_one_spec`）。

**产出**：
* **`genericDivisionData_one`**：`GenericDivisionData F r 1` 的**具体模型**；
* **`nonempty_genericDivisionData_one`**：结构束**非空**（L1）；
* **`cor148a_one`**：`cor:14.8(a)` 在 `n = 1` 的**无条件证明**——即那条具名输入在
  `n = 1` 时**不需要 PI 理论**。这使"具名"不是空话：它至少在一个具体模型上为真。

**诚实边界（勿夸大）**：
* `n = 1` 是**退化情形**，**不**验证 `n = 9` 的情形；`thm1416_of_inputs` 需 `3 ≤ n`，
  故在 `n = 1` **根本不能实例化**。
* 本模型的 `ZCanon` 是否为 `⊤`（即 `KPFixedLeZ` 是否在该模型成立）**未机检**，列为后续项。
* L1 只要求"假设类非空"，本节的见证满足它；**不**构成对 `cor:14.8(a)` 在 `n ≥ 2` 的证明。 -/

section ModelN1

variable (F : Type) [Field F] (r : ℕ)

/-- **`M_1(S)` 交换**：`Fin 1` 只有一个指标，`(A*B) 0 0 = A 0 0 * B 0 0`。
**用途**：`n = 1` 时 `genericCenter` 是全域（`genericCenter_one_eq_top`）。 -/
lemma matrix_fin_one_comm (A B : Matrix (Fin 1) (Fin 1) (S F r 1)) : A * B = B * A := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

#print axioms matrix_fin_one_comm

/-- **`n = 1` 时中心是全域**：`C(F,r,1) = ⊤`（因 `R` 交换）。 -/
lemma genericCenter_one_eq_top : genericCenter F r 1 = ⊤ := by
  rw [eq_top_iff]
  intro A _
  rw [mem_genericCenter_iff]
  intro B
  exact Subtype.ext (matrix_fin_one_comm F r B.1 A.1)

#print axioms genericCenter_one_eq_top

/-- **`n = 1` 的 `centK`**：取 `(0,0)` 项，再沿 `S → K` 送进分式域。

**为何这样取**：`n = 1` 时 `C = ⊤`，而 `centK_spec` 要求
`(c.1).map algebraMap = Matrix.scalar (centK c)`；`Fin 1` 的 `Matrix.scalar x` 的 `(0,0)` 项
就是 `x`，而 `(c.1).map algebraMap` 的 `(0,0)` 项是 `algebraMap ((c.1) 0 0)`。
故 `centK c := algebraMap ((c.1) 0 0)` 是**唯一**可能的选择。 -/
noncomputable def centK_one :
    ↥(genericCenter F r 1) →ₐ[F] SField F r 1 where
  toFun c := algebraMap (S F r 1) (SField F r 1)
    (((c.1 : ↥(genericMatrixAlgebra F r 1)) : Matrix (Fin 1) (Fin 1) (S F r 1)) 0 0)
  map_one' := by simp
  map_mul' c d := by simp [Matrix.mul_apply]
  map_zero' := by simp
  map_add' c d := by simp
  commutes' x := by
    have e1 : (((algebraMap F ↥(genericCenter F r 1) x).1 :
        ↥(genericMatrixAlgebra F r 1)) : Matrix (Fin 1) (Fin 1) (S F r 1))
        = algebraMap F (Matrix (Fin 1) (Fin 1) (S F r 1)) x := rfl
    rw [e1, Matrix.algebraMap_eq_diagonal]
    simp only [Matrix.diagonal, Matrix.of_apply, Pi.algebraMap_apply]
    exact (IsScalarTower.algebraMap_apply F (S F r 1) (SField F r 1) x).symm

#print axioms centK_one

/-- **`cor:14.8(a)` 在 `n = 1`**：`centK_one` 满足结构束的唯一字段。 -/
lemma centK_one_spec (c : ↥(genericCenter F r 1)) :
    (((c.1 : ↥(genericMatrixAlgebra F r 1)) : Matrix (Fin 1) (Fin 1) (S F r 1))).map
        (algebraMap (S F r 1) (SField F r 1))
      = Matrix.scalar (Fin 1) (centK_one F r c) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [centK_one, Matrix.scalar, Matrix.diagonal, Matrix.map_apply]

#print axioms centK_one_spec

/-- ★★★★★ **`GenericDivisionData` 的具体模型（`n = 1`）** —— **L1 非空洞见证**。

v6 §8 红线 5 点名的未做项。**射程**：`n = 1` 是退化情形，不验证 `n = 9`；
且 `thm1416_of_inputs` 需 `3 ≤ n`，故本模型不能用来实例化该定理。 -/
noncomputable def genericDivisionData_one : GenericDivisionData F r 1 where
  centK := centK_one F r
  centK_spec := centK_one_spec F r

#print axioms genericDivisionData_one

/-- ★★★★★ **结构束非空（`n = 1`）**：`Nonempty (GenericDivisionData F r 1)`。 -/
theorem nonempty_genericDivisionData_one : Nonempty (GenericDivisionData F r 1) :=
  ⟨genericDivisionData_one F r⟩

#print axioms nonempty_genericDivisionData_one

/-- ★★★★★ **`cor:14.8(a)` 在 `n = 1` 的无条件证明**（由 `nonempty_genericDivisionData_iff`
反向读出）：存在 `κ : ↥C →ₐ[F] K` 使中心元的矩阵像是 `κ` 的纯量矩阵。

**意义**：具名输入 `cor:14.8(a)` **在 `n = 1` 不需要 PI 理论**——这使"具名"有具体见证，
不是空类上的真。**射程**：`n ≥ 2` 的情形仍属 T3。 -/
theorem cor148a_one :
    ∃ κ : ↥(genericCenter F r 1) →ₐ[F] SField F r 1,
      ∀ c : ↥(genericCenter F r 1),
        ((c.1 : ↥(genericMatrixAlgebra F r 1)) : Matrix (Fin 1) (Fin 1) (S F r 1)).map
          (algebraMap (S F r 1) (SField F r 1)) = Matrix.scalar (Fin 1) (κ c) :=
  (nonempty_genericDivisionData_iff F r 1).mp (nonempty_genericDivisionData_one F r)

#print axioms cor148a_one

end ModelN1


/-! ## §65 **`lem:14.21` 的判别式机械** —— `Polynomial.discr`↔`resultant`、对角矩阵、与环同态交换

**(B) `prop:14.19` 的入口是 `lem:14.21`**（源文 `:399`，逐字）：

> "Let `p(x) ∈ K[x]` be the characteristic polynomial of `X_1`. It suffices by standard linear
> algebra to show that `p(x)` has distinct roots … If `Δ` is the discriminant of `p(x)`,
> it suffices to show that `Δ ≠ 0`. `Δ` is called the **discriminant of `X_1`**."

本节把这句话所需的**全部机械件**机检（六条）。本 pin 的 `Polynomial.discr` API **很薄**
（只有 `discr_C`／`discr_of_degree_eq_{one,two,three}`，**无** map、**无** 乘积公式），
故这些必须自建；`resultant` 侧则**够用**（`Polynomial.resultant_deriv`／`Polynomial.resultant_map_map`／
`Polynomial.resultant_prod_left`／`Polynomial.resultant_X_sub_C_left`／`Polynomial.derivative_map`）。

**六件**：
1. `discr_eq_signed_resultant`：`Polynomial.discr f = (-1)^k · Res(f, f')`（`f` monic，`Polynomial.resultant_deriv` 的重排）；
2. `eval_derivative_prod_X_sub_C`：`(∏(X−a_l))'(a_i) = ∏_{l≠i}(a_i−a_l)`（乘积法则 ＋ 根处求值）；
3. `prod_resultant_X_sub_C_eval`：`Res(∏(X−a_i), g) = ∏ g(a_i)`（**对第一参数可乘**）；
4. `matrix_discr_diagonal_ne_zero`：**互异对角元的对角矩阵判别式 ≠ 0**；
5. `discr_map_of_monic`：`Polynomial.discr (f.map φ) = φ (Polynomial.discr f)`（`f` monic ⟹ 度不变）；
6. `matrix_discr_map`：`(A.map φ).discr = φ A.discr`（`charpoly` monic 给度不变）。

**关键陷阱（已避）**：`resultant` 对**第二**参数**不可加**，故
`f' = Σ_k ∏_{l≠k}(X−a_l)` **不能**逐项拆；必须走 `Res(f,f') = ∏_i f'(a_i)`（根处求值）。
**射程**：本节只给机械件。`lem:14.21` 本体
（`Matrix.discr (genericMatrix F r n k) ≠ 0`）还需一个**特殊化** `φ`（`M_n(φ)(X_k)` 变为
互异对角矩阵）——**未**做，下一轮。 -/

section DiscrMech

variable {R : Type*} [CommRing R]

/-- ★★★★ **`Polynomial.discr` 与 `Res(f, f')` 的关系**（`f` monic）：`Polynomial.discr f = (-1)^k · Res(f, f')`。

源：`Polynomial.resultant_deriv`（`Res(f,f') = (-1)^k · leadingCoeff f · Polynomial.discr f`）
＋ `leadingCoeff f = 1` ＋ `(-1)^k · (-1)^k = 1`。**用途**：把 `Polynomial.discr` 化为 `resultant`，
后者有乘积公式与 map 公式。 -/
theorem discr_eq_signed_resultant {f : Polynomial R} (hf : f.Monic) (hdeg : 0 < f.degree) :
    Polynomial.discr f = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
  have h := Polynomial.resultant_deriv hdeg
  rw [hf.leadingCoeff, mul_one] at h
  have hu : ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨_, rfl⟩
  calc Polynomial.discr f
      = ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
          (((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) * Polynomial.discr f) := by
        rw [← mul_assoc, hu, one_mul]
    _ = _ := by rw [h]

#print axioms discr_eq_signed_resultant

/-- ★★★★ **`Polynomial.discr` 与环同态交换**（`f` monic ⟹ 度不变）：`Polynomial.discr (f.map φ) = φ (Polynomial.discr f)`。

**机制**：两边各用 `discr_eq_signed_resultant`；`natDegree` 由 `Monic.natDegree_map` 不变；
`Res` 由 `Polynomial.resultant_map_map` 交换；`f'` 由 `Polynomial.derivative_map`。
**用途**：`lem:14.21` 的**特殊化**论证——把一个具体矩阵的判别式拉回 `S`。 -/
theorem discr_map_of_monic {L : Type*} [Field L] {f : Polynomial R} (hf : f.Monic)
    (hdeg : 0 < f.degree) (φ : R →+* L) :
    Polynomial.discr (f.map φ) = φ (Polynomial.discr f) := by
  have hlc : φ f.leadingCoeff ≠ 0 := by rw [hf.leadingCoeff, map_one]; exact one_ne_zero
  have hdeg' : 0 < (f.map φ).degree := by
    rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero φ hlc]; exact hdeg
  have hnd : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  calc Polynomial.discr (f.map φ)
      = (-1) ^ ((f.map φ).natDegree * ((f.map φ).natDegree - 1) / 2) *
          (f.map φ).resultant (f.map φ).derivative (f.map φ).natDegree
            ((f.map φ).natDegree - 1) := discr_eq_signed_resultant (hf.map φ) hdeg'
    _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          φ (f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
        rw [hnd, Polynomial.derivative_map, Polynomial.resultant_map_map]
    _ = φ ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          f.resultant f.derivative f.natDegree (f.natDegree - 1)) := by
        rw [map_mul, map_pow, map_neg, map_one]
    _ = φ (Polynomial.discr f) := by rw [discr_eq_signed_resultant hf hdeg]

#print axioms discr_map_of_monic

/-- ★★★★ **矩阵层**：`(A.map φ).discr = φ A.discr`。

**机制**：`Matrix.discr A = A.charpoly.discr`；`Matrix.charpoly_map` 给
`(A.map φ).charpoly = A.charpoly.map φ`；再用 `discr_map_of_monic`
（`Matrix.charpoly_monic` ＋ `Matrix.charpoly_natDegree_eq_dim` 给度不变）。 -/
theorem matrix_discr_map {n : ℕ} [NeZero n] [Nontrivial R] {L : Type*} [Field L]
    (A : Matrix (Fin n) (Fin n) R) (φ : R →+* L) : (A.map φ).discr = φ A.discr := by
  have hdeg : 0 < A.charpoly.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  rw [Matrix.discr, Matrix.discr, Matrix.charpoly_map]
  exact discr_map_of_monic (Matrix.charpoly_monic A) hdeg φ

#print axioms matrix_discr_map

end DiscrMech

section DiscrDiag

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- ★★★★ **乘积多项式在根处的导数值**：`(∏_{l∈s}(X−a_l))'(a_i) = ∏_{l∈s.erase i}(a_i−a_l)`。

**机制**：把 `∏_{l∈s}` 拆成 `(X−C(a_i)) · ∏_{l∈erase i}`（`Finset.mul_prod_erase`），
乘积法则后第一项求值为 `∏(a_i−a_l)`、第二项带因子 `(a_i−a_i)=0`。 -/
theorem eval_derivative_prod_X_sub_C (a : ι → K) (s : Finset ι) {i : ι} (hi : i ∈ s) :
    (Polynomial.derivative (∏ l ∈ s, (Polynomial.X - Polynomial.C (a l)))).eval (a i)
      = ∏ l ∈ s.erase i, (a i - a l) := by
  rw [← Finset.mul_prod_erase s (fun l => (Polynomial.X - Polynomial.C (a l))) hi]
  rw [Polynomial.derivative_mul]
  simp only [Polynomial.derivative_X_sub_C, Polynomial.eval_add, Polynomial.eval_mul, one_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul, add_zero, Polynomial.eval_prod]

#print axioms eval_derivative_prod_X_sub_C

/-- ★★★★★ **`Res(∏_i (X−a_i), g) = ∏_i g(a_i)`**（`Polynomial.resultant_prod_left` ＋ `Polynomial.resultant_X_sub_C_left`）。

**为何这条是关键的**：`resultant` **对第一参数**可乘（`Polynomial.resultant_prod_left`），
**对第二参数不可加**——故 `Res(f,f')` 只能靠"`f` 是线性因子之积 ⟹ 逐个求值"来算。
**注意**：本引理对 `g` 无 monic 要求，只要 `g.natDegree ≤ m`。 -/
theorem prod_resultant_X_sub_C_eval (a : ι → K) (g : Polynomial K) (m : ℕ)
    (hm : g.natDegree ≤ m) :
    (∏ i, (Polynomial.X - Polynomial.C (a i))).resultant g (∏ i, (Polynomial.X - Polynomial.C (a i))).natDegree m
      = ∏ i, g.eval (a i) := by
  rw [Polynomial.resultant_prod_left Finset.univ (fun i => (Polynomial.X - Polynomial.C (a i))) g m (by simp) hm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show (Polynomial.X - Polynomial.C (a i) : Polynomial K).natDegree = 1 from Polynomial.natDegree_X_sub_C (a i)]
  exact Polynomial.resultant_X_sub_C_left g m (a i) hm

#print axioms prod_resultant_X_sub_C_eval

/-- ★★★★★ **对角矩阵（互异对角元）的判别式 ≠ 0** —— `lem:14.21` 的核心机械件。

**证明链**：`Matrix.charpoly_diagonal` ⟹ `Polynomial.discr = Polynomial.discr(∏(X−d i))`
⟹ `discr_eq_signed_resultant` ⟹ `prod_resultant_X_sub_C_eval`
⟹ `∏_i (∏(X−d l))'(d i) = ∏_i ∏_{l≠i}(d i − d l) ≠ 0`（互异 ＋ `Finset.prod_ne_zero_iff`）。
**射程**：这是"具体矩阵"那一侧的判据；`lem:14.21` 还需把 `X_k` 特殊化到这种矩阵（下一轮）。 -/
theorem matrix_discr_diagonal_ne_zero {n : ℕ} [NeZero n] (d : Fin n → K)
    (hd : Function.Injective d) : (Matrix.diagonal d).discr ≠ 0 := by
  classical
  rw [Matrix.discr, Matrix.charpoly_diagonal]
  have hmonic : (∏ i, (Polynomial.X - Polynomial.C (d i)) : Polynomial K).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (d i))
  have hnd : (∏ i, (Polynomial.X - Polynomial.C (d i)) : Polynomial K).natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (d i))]
    simp
  have hdeg : 0 < (∏ i, (Polynomial.X - Polynomial.C (d i)) : Polynomial K).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hnd]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  rw [discr_eq_signed_resultant hmonic hdeg]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
  rw [prod_resultant_X_sub_C_eval d (Polynomial.derivative (∏ i, (Polynomial.X - Polynomial.C (d i))))
    ((∏ i, (Polynomial.X - Polynomial.C (d i)) : Polynomial K).natDegree - 1) (Polynomial.natDegree_derivative_le _)]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [eval_derivative_prod_X_sub_C d Finset.univ (Finset.mem_univ i)]
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  rw [Finset.mem_erase] at hl
  exact sub_ne_zero.mpr (fun h => hl.1 (hd h).symm)

#print axioms matrix_discr_diagonal_ne_zero

end DiscrDiag


/-! ## §66 **`lem:14.21` 机检：通用矩阵的判别式非零** —— `(B)` 的第一块基石

源文 `raw/Saltman1999ch14.tex:399`（`lem:14.22` 的证明之前，逐字）：

> "Let `p(x) ∈ K[x]` be the characteristic polynomial of `X_1`. It suffices by standard linear
> algebra to show that `p(x)` has distinct roots (e.g., [lang1965algebra, p. 176]). If `Δ` is
> the discriminant of `p(x)`, it suffices to show that `Δ ≠ 0`. `Δ` is called the
> **discriminant of `X_1`**."

**证明（源文的路子，逐字对位）**："By choosing `φ` properly, `M_n(φ)(X_1)` can be any matrix
over any field containing `F`. Since some such matrix has nonzero discriminant, we must have
`Δ ≠ 0`."

* **特殊化** `φ = specHom k`：`x_{ij,k} ↦ δ_{ij} t_i`，其余变量 `↦ 0`，其中 `t_i` 是
  `F(t_1,…,t_n) = FractionRing (MvPolynomial (Fin n) F)` 里的独立变量；
* 则 `M_n(φ)(X_k) = Matrix.diagonal (specDiag)`（`genericMatrix_map_specHom`）——
  **互异对角元**（`specDiag_injective`）；
* 对角矩阵判别式非零（`matrix_discr_diagonal_ne_zero`，§65）；
* `discr` 与环同态交换（`matrix_discr_map`，§65）⟹ `φ (discr X_k) ≠ 0` ⟹ `discr X_k ≠ 0`。

**射程（勿夸大）**：本条只机检 `lem:14.21` 的**判别式结论**（`Δ ≠ 0`）。
由它到"`X_1` 可对角化 ⟹ `lem:14.22` 的单射识别"那一步**未**做
（本 pin **无** `Matrix.IsDiagonalizable`，须自建"可分 ⟹ 可对角化"）。
**参数**：`[NeZero n]`（`n ≥ 1`；本战役 `n = 9`）。 -/

section Lem1421

variable (F : Type) [Field F] (r n : ℕ)

/-- 特殊化用的域 `F(t_1,…,t_n)`（源文 `:402` 的 `L` 一侧的显式模型）。 -/
abbrev TField (F : Type) [CommRing F] (n : ℕ) := FractionRing (MvPolynomial (Fin n) F)

#print axioms TField

/-- **特殊化** `x_{ij,k₀} ↦ δ_{ij} t_i`，其余变量 `↦ 0`（源文 `:400` 的
"By choosing `φ` properly"）。 -/
noncomputable def specHom (k₀ : Fin r) : S F r n →ₐ[F] TField F n :=
  MvPolynomial.aeval (fun p : Fin r × Fin n × Fin n =>
    if p.1 = k₀ then
      (if p.2.1 = p.2.2 then
        algebraMap (MvPolynomial (Fin n) F) (TField F n) (MvPolynomial.X p.2.1) else 0)
    else 0)

#print axioms specHom

/-- 特殊化的**对角元**：`specDiag i = t_i`（独立变量在分式域中的像）。 -/
noncomputable def specDiag : Fin n → TField F n :=
  fun i => algebraMap (MvPolynomial (Fin n) F) (TField F n) (MvPolynomial.X i)

#print axioms specDiag

/-- ★★★★ **特殊化把 `X_{k₀}` 变成对角矩阵**：`(X_k).map φ = diagonal specDiag`。

逐项：`(X_k) i j` 是变量 `x_{ij,k}`，`φ` 送它到 `δ_{ij} t_i`；而 `(diagonal d) i j` 是
`if i = j then d i else 0`。 -/
theorem genericMatrix_map_specHom (k₀ : Fin r) :
    (genericMatrix F r n k₀).map (specHom F r n k₀) = Matrix.diagonal (specDiag F n) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.map_apply, genericMatrix, genericEntry, specHom, specDiag, Matrix.diagonal]
  · simp [Matrix.map_apply, genericMatrix, genericEntry, specHom, specDiag, Matrix.diagonal, hij]

#print axioms genericMatrix_map_specHom

/-- ★★★★ **对角元互异**：`t_i ≠ t_j`（`i ≠ j`）。

**机制**：`algebraMap (MvPolynomial (Fin n) F) (FractionRing …)` 单射
（`IsFractionRing.injective`）＋ `MvPolynomial.X_injective`。 -/
theorem specDiag_injective : Function.Injective (specDiag F n) := by
  intro i j h
  have h' : MvPolynomial.X i = MvPolynomial.X j :=
    IsFractionRing.injective (MvPolynomial (Fin n) F) (TField F n) h
  exact MvPolynomial.X_injective h'

#print axioms specDiag_injective

/-- ★★★★★ **`lem:14.21`：通用矩阵的判别式 ≠ 0**。

**证明链**（源文 `:399–402`）：`φ` 把 `X_k` 变成互异对角矩阵
（`genericMatrix_map_specHom` ＋ `specDiag_injective`）⟹ 该对角矩阵判别式 ≠ 0
（`matrix_discr_diagonal_ne_zero`）⟹ 由 `matrix_discr_map` 得 `φ (discr X_k) ≠ 0`
⟹ `discr X_k ≠ 0`。

**用途**：`(B)` 的入口——`lem:14.22` 的"`θ(X_1)` 可对角化"用它（那一步**未**做）。
**射程**：只给判别式结论；不含可对角化。 -/
theorem discr_genericMatrix_ne_zero [NeZero n] (k : Fin r) :
    (genericMatrix F r n k).discr ≠ 0 := by
  intro h
  have hdiag : (genericMatrix F r n k).map (specHom F r n k).toRingHom
      = Matrix.diagonal (specDiag F n) := genericMatrix_map_specHom F r n k
  have hmap := matrix_discr_map (genericMatrix F r n k) (specHom F r n k).toRingHom
  rw [h, map_zero, hdiag] at hmap
  exact matrix_discr_diagonal_ne_zero (specDiag F n) (specDiag_injective F n) hmap

#print axioms discr_genericMatrix_ne_zero

end Lem1421


/-! ## §67 **(B) 的 `S'`-世界载体** —— `lem:14.22`／`14.23`／`prop:14.19` 的工作台

源文 `raw/Saltman1999ch14.tex:363`（label `prop:14.19` 在 `:368`）逐字：

> "Form the polynomial ring: `S' = F[x_{ii}, y_{ijk} | 1 ≤ i,j ≤ n; 2 ≤ k ≤ r]`."

以及 `:365`：`X` 是**对角**矩阵（对角元 `x_{ii}`），`Y_k` 的 `(i,j)` 项是 `y_{ijk}`。
`N = T ⋊ S_n` 由对角环面 `T` 与置换 `P_σ` 生成（`:361`），作用为（`:363` 逐字）

> "`φ_A(x_{ii})` = the `i,i` entry of `A^{-1} X A`, `φ_A(y_{ijk})` = the `i,j` entry of `A^{-1} Y_k A`."

对 `A = P_σ`（`:375` 逐字）：`P_σ X P_σ^{-1}` 的 `i,i` 项是 `x_{σ(i)σ(i)}`、
`P_σ Y_k P_σ^{-1}` 的 `i,j` 项是 `y_{σ(i)σ(j)k}`；
对 `A` 对角（`lem:14.20` 的 `(17)`）：`φ_B(e(m)) = λ e(m)`，即 `y_{ijk} ↦ (b_i/b_j) y_{ijk}`。

**为何需要本节**：`(B)` 不是 `(A)` 的换群重做（v7 §3.3），它需要**独立的 `S'`-世界**：
`Z = K'^N` 里的 `Z ⊂ K`，而 `K'^N ⊂ K' = Frac(S')`。本件给 `S'`、`X`、`Y_k` 与两种作用。

**射程（勿夸大）**：本节只建**载体与两种作用**。`K'^N` 的固定域、`lem:14.22` 的单射识别、
`lem:14.23/24/25`、`prop:14.19` 装配 —— **全部未做**。 -/

section SprWorld

variable (F : Type) [Field F] (r n : ℕ)

/-- `Y` 变量的索引：`(i, j, k)`，`k ≠ 0`（源文 `k ≥ 2` 的 0-基写法）。 -/
abbrev YIdx (r n : ℕ) := Fin n × Fin n × {k : Fin r // k.val ≠ 0}

/-- `S'` 的变量索引：`x_ii`（`inl`）与 `y_ijk`（`inr`）。 -/
abbrev SprIdx (r n : ℕ) := Fin n ⊕ YIdx r n

/-- `S' = F[x_ii, y_ijk | k ≠ 0]`。 -/
abbrev Spr (F : Type) [CommSemiring F] (r n : ℕ) :=
  MvPolynomial (SprIdx r n) F

#print axioms Spr

/-- `X = diagonal (x_ii)`。 -/
noncomputable def xdiag : Matrix (Fin n) (Fin n) (Spr F r n) :=
  Matrix.diagonal (fun i => MvPolynomial.X (Sum.inl i))

/-- `Y_k = (y_ijk)`。 -/
noncomputable def ymat (k : {k : Fin r // k.val ≠ 0}) : Matrix (Fin n) (Fin n) (Spr F r n) :=
  fun i j => MvPolynomial.X (Sum.inr (i, j, k))

theorem xdiag_apply (i j : Fin n) :
    xdiag F r n i j = if i = j then MvPolynomial.X (Sum.inl i) else 0 := by
  simp [xdiag, Matrix.diagonal]

#print axioms xdiag_apply

theorem ymat_apply (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    ymat F r n k i j = MvPolynomial.X (Sum.inr (i, j, k)) := rfl

#print axioms ymat_apply

/-- 索引置换 `σ ∈ S_n`。 -/
def sprPerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : SprIdx r n ≃ SprIdx r n :=
  Equiv.sumCongr σ (Equiv.prodCongr σ (Equiv.prodCongr σ (Equiv.refl _)))

/-- `S_n` 在 `S'` 上的作用。 -/
noncomputable def sprPermAlgEquiv (σ : Equiv.Perm (Fin n)) : Spr F r n ≃ₐ[F] Spr F r n :=
  MvPolynomial.renameEquiv F (sprPerm r n σ)

theorem sprPermAlgEquiv_X_inl (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    sprPermAlgEquiv F r n σ (MvPolynomial.X (Sum.inl i))
      = MvPolynomial.X (Sum.inl (σ i)) := by
  rw [sprPermAlgEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  simp only [sprPerm, Equiv.sumCongr_apply, Sum.map_inl]

#print axioms sprPermAlgEquiv_X_inl

theorem sprPermAlgEquiv_X_inr (σ : Equiv.Perm (Fin n))
    (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    sprPermAlgEquiv F r n σ (MvPolynomial.X (Sum.inr (i, j, k)))
      = MvPolynomial.X (Sum.inr (σ i, σ j, k)) := by
  rw [sprPermAlgEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
  rfl

#print axioms sprPermAlgEquiv_X_inr


/-- 对角（环面 `T`）在 `S'` 上的作用：`x_ii ↦ x_ii`、`y_ijk ↦ (b_i / b_j) y_ijk`
（源文 `:363` 的 `φ_A` 取 `A` 对角；`lem:14.20` 的 `(17)` 即此：`φ_B(e(m)) = λ e(m)`）。 -/
noncomputable def sprDiagHom (b : Fin n → Fˣ) : Spr F r n →ₐ[F] Spr F r n :=
  MvPolynomial.aeval (fun v : SprIdx r n =>
    match v with
    | Sum.inl i => MvPolynomial.X (Sum.inl i)
    | Sum.inr (i, j, k) =>
        MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) * MvPolynomial.X (Sum.inr (i, j, k)))

theorem sprDiagHom_X_inl (b : Fin n → Fˣ) (i : Fin n) :
    sprDiagHom F r n b (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i) := by
  rw [sprDiagHom, MvPolynomial.aeval_X]

#print axioms sprDiagHom_X_inl

theorem sprDiagHom_X_inr (b : Fin n → Fˣ) (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    sprDiagHom F r n b (MvPolynomial.X (Sum.inr (i, j, k)))
      = MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) * MvPolynomial.X (Sum.inr (i, j, k)) := by
  rw [sprDiagHom, MvPolynomial.aeval_X]

#print axioms sprDiagHom_X_inr

end SprWorld

section SprFixedSec

variable (F : Type) [Field F] (r n : ℕ)

/-! ## §68 **`(B)` 的 `K'^N` 起点：`S'` 的 `N`-固定子代数** ＋ 权零单项式

源文 `raw/Saltman1999ch14.tex:361` 定义 `N = T ⋊ S_n`（`T` ＝ 对角环面的像、
`S_n` ＝ 置换矩阵的像），`:363` 定义两族作用 `φ_A`，`prop:14.19`（`:369` 逐字）声称

> "`UD(F,n,r) = M_n(K')^N` and `Z(F,n,r) = K'^N`."

本件给 `K'^N` 的**多项式层起点**：`S'` 的 `N`-固定**子代数** `SprFixed`，及其成员刻画。
以及一条**非平凡性见证**：权零单项式 `y_ijk · y_jik` 被整个环面 `T` 固定
（`lem:14.20` 的 `(17)` 的 `λ = 1` 情形）——说明 `SprFixed` 的 `T`-部分不只是常数。

**射程（勿夸大）**：`K'^N` 的**分式域层**（把 `SprFixed` 的分式域嵌进 `K'`）、
`lem:14.22` 的单射识别、`lem:14.23/24/25`、`prop:14.19` 装配 —— **全部未做**。 -/

/-- `S'` 的 `N`-固定子代数（`N = T ⋊ S_n`）。 -/
noncomputable def SprFixed : Subalgebra F (Spr F r n) where
  carrier := {x | (∀ b : Fin n → Fˣ, sprDiagHom F r n b x = x) ∧
                  (∀ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ x = x)}
  zero_mem' := ⟨fun b => by rw [map_zero], fun σ => by rw [map_zero]⟩
  one_mem' := ⟨fun b => by rw [map_one], fun σ => by rw [map_one]⟩
  add_mem' := fun hx hy => ⟨fun b => by rw [map_add, hx.1 b, hy.1 b],
    fun σ => by rw [map_add, hx.2 σ, hy.2 σ]⟩
  mul_mem' := fun hx hy => ⟨fun b => by rw [map_mul, hx.1 b, hy.1 b],
    fun σ => by rw [map_mul, hx.2 σ, hy.2 σ]⟩
  algebraMap_mem' := fun c => ⟨fun b => (sprDiagHom F r n b).commutes c,
    fun σ => (sprPermAlgEquiv F r n σ).commutes c⟩

#print axioms SprFixed

/-- `SprFixed` 的成员刻画（定义展开）。 -/
theorem mem_SprFixed_iff {x : Spr F r n} :
    x ∈ SprFixed F r n ↔
      (∀ b : Fin n → Fˣ, sprDiagHom F r n b x = x) ∧
      (∀ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ x = x) := Iff.rfl

#print axioms mem_SprFixed_iff


/-- **权零单项式被环面固定**：`y_ijk · y_jik` 的权是 `(b_i/b_j)(b_j/b_i) = 1`
（`lem:14.20` 的 `(17)`：`φ_B(e(m)) = λ e(m)`，`λ = 1` 即固定）。
**用途**：`SprFixed` 的 `T`-部分**非平凡**（L1 见证；只含常数会使 `K'^N` 太小）。 -/
theorem sprDiagHom_y_mul_y (b : Fin n → Fˣ) (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    sprDiagHom F r n b
        (MvPolynomial.X (Sum.inr (i, j, k)) * MvPolynomial.X (Sum.inr (j, i, k)))
      = MvPolynomial.X (Sum.inr (i, j, k)) * MvPolynomial.X (Sum.inr (j, i, k)) := by
  have h1 : ((b i : F) * ((b j : F))⁻¹) * ((b j : F) * ((b i : F))⁻¹) = 1 := by
    have hi : (b i : F) ≠ 0 := (b i).ne_zero
    have hj : (b j : F) ≠ 0 := (b j).ne_zero
    field_simp
  have hC : (MvPolynomial.C ((b i : F) * ((b j : F))⁻¹)
      * MvPolynomial.C ((b j : F) * ((b i : F))⁻¹) : Spr F r n) = 1 := by
    rw [← MvPolynomial.C_mul, h1, MvPolynomial.C_1]
  calc sprDiagHom F r n b
        (MvPolynomial.X (Sum.inr (i, j, k)) * MvPolynomial.X (Sum.inr (j, i, k)))
      = MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) * MvPolynomial.X (Sum.inr (i, j, k))
        * (MvPolynomial.C ((b j : F) * ((b i : F))⁻¹) * MvPolynomial.X (Sum.inr (j, i, k))) := by
        rw [map_mul, sprDiagHom_X_inr, sprDiagHom_X_inr]
    _ = (MvPolynomial.C ((b i : F) * ((b j : F))⁻¹)
          * MvPolynomial.C ((b j : F) * ((b i : F))⁻¹))
        * (MvPolynomial.X (Sum.inr (i, j, k)) * MvPolynomial.X (Sum.inr (j, i, k))) := by
        ring
    _ = MvPolynomial.X (Sum.inr (i, j, k)) * MvPolynomial.X (Sum.inr (j, i, k)) := by
        rw [hC, one_mul]

#print axioms sprDiagHom_y_mul_y

end SprFixedSec

/-! ## §69 **`lem:14.21` 的可分形态** —— `discr ≠ 0` ⟹ `charpoly` 可分（`K` 上）

**(B) 的硬阻塞**（`lem:14.22`）需要"`charpoly` 可分 ⟹ `X_1` 在扩域上可对角化"。
本件机检那条链的**第一环**：`discr ≠ 0` ⟹ **可分**。

* `separable_of_discr_ne_zero`：`f` monic、`natDegree ≠ 0`、`Polynomial.discr f ≠ 0` ⟹ `f.Separable`。
  **机制**：`discr f = ± Res(f,f')`（§65）⟹ `Res ≠ 0` ⟹ Bezout 关系
  `f*p + f'*q = C(Res)`（`exists_mul_add_mul_eq_C_resultant`）⟹ `C(Res)` 是**单位**
  （域上 `Res ≠ 0`）⟹ `IsCoprime f f'` ⟹ `f.Separable`（`separable_def`）。
* `discr_genMatKF_ne_zero`：`K` 上通用矩阵的判别式 ≠ 0（由 `matrix_discr_map` ＋
  `IsFractionRing.injective` 从 §66 的 `S` 上版本拉回）。
* `separable_charpoly_genMatKF`：**`(genMatKF k).charpoly.Separable`**。

**口径要点（本轮踩到的）**：`genericMatrix F r n k` 的 `charpoly` 在**多项式环 `S`** 上
（不是域），故"`discr ≠ 0` ⟹ 可分"（其证明用 `IsUnit`）**只能用在 `K = SField` 上**，
即 `genMatKF = (X_k).map (algebraMap S K)` 上。**这是 `lem:14.22` 的正确工作域**
（`θ` 的定义域就是 `M_n(K)`）。

**未做（下一轮）**：`(minpoly F (genMatKF k)).Separable` 在默认心跳下**`isDefEq` 超时**
（`minpoly` 的 `IsIntegral` 实例链对大项昂贵）；以及最终的
"可分 `minpoly` ⟹ 半单 ⟹ 可对角化"。 -/

section Sepr

variable {K : Type*} [Field K]

/-- **`discr ≠ 0 ⟹ 可分**（`f` monic、`natDegree ≠ 0`）。

**机制**：`discr f = ± Res(f,f')`（`discr_eq_signed_resultant`）；`Res(f,f') ≠ 0` 给 Bezout 关系
`f*p + f'*q = C (Res)`（`exists_mul_add_mul_eq_C_resultant`），而 `C (Res)` 是**单位**
（域上 `Res ≠ 0`）⟹ `IsCoprime f f'` ⟹ `f.Separable`（`separable_def`）。 -/
theorem separable_of_discr_ne_zero {f : Polynomial K} (hf : f.Monic) (hnd : f.natDegree ≠ 0)
    (hd : Polynomial.discr f ≠ 0) : f.Separable := by
  have hdeg : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hnd)
  have hres : f.resultant f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
    intro h0
    exact hd (by rw [discr_eq_signed_resultant hf hdeg, h0, mul_zero])
  rw [Polynomial.separable_def]
  obtain ⟨p, q, -, -, hpq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f f.derivative (le_of_eq rfl)
      (Polynomial.natDegree_derivative_le f) (Or.inl hnd)
  have hunit : IsUnit (f.resultant f.derivative f.natDegree (f.natDegree - 1) : K) :=
    isUnit_iff_ne_zero.mpr hres
  obtain ⟨u, hu⟩ := hunit
  have key : (Polynomial.C ((u : K)⁻¹) * Polynomial.C (u : K) : Polynomial K) = 1 := by
    rw [← Polynomial.C_mul, ← Units.val_inv_eq_inv_val, Units.inv_mul, Polynomial.C_1]
  refine ⟨Polynomial.C ((u : K)⁻¹) * p, Polynomial.C ((u : K)⁻¹) * q, ?_⟩
  calc Polynomial.C ((u : K)⁻¹) * p * f + Polynomial.C ((u : K)⁻¹) * q * f.derivative
      = Polynomial.C ((u : K)⁻¹) * (f * p + f.derivative * q) := by ring
    _ = Polynomial.C ((u : K)⁻¹) * Polynomial.C (u : K) := by rw [hpq, ← hu]
    _ = 1 := key

#print axioms separable_of_discr_ne_zero

end Sepr

section GenMatK

variable (F : Type) [Field F] (r n : ℕ)

/-- **`K` 上通用矩阵的判别式 ≠ 0**（由 `S` 上拉回 ＋ `algebraMap` 单射）。 -/
theorem discr_genMatKF_ne_zero [NeZero n] (k : Fin r) : (genMatKF F r n k).discr ≠ 0 := by
  have h := matrix_discr_map (genericMatrix F r n k)
    (algebraMap (S F r n) (SField F r n))
  rw [genMatKF, h]
  intro h0
  exact discr_genericMatrix_ne_zero F r n k
    (IsFractionRing.injective (S F r n) (SField F r n) (by rw [h0, map_zero]))

#print axioms discr_genMatKF_ne_zero

/-- **`K` 上通用矩阵的特征多项式可分**（`lem:14.21` 的可分形态）。 -/
theorem separable_charpoly_genMatKF [NeZero n] (k : Fin r) :
    (genMatKF F r n k).charpoly.Separable := by
  have hmonic : (genMatKF F r n k).charpoly.Monic := Matrix.charpoly_monic _
  have hnd : (genMatKF F r n k).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hpos : (genMatKF F r n k).charpoly.natDegree ≠ 0 := by
    rw [hnd]; exact NeZero.ne n
  exact separable_of_discr_ne_zero hmonic hpos (discr_genMatKF_ne_zero F r n k)

#print axioms separable_charpoly_genMatKF

end GenMatK


/-! ## §70 **`minpoly` 可分 ＋ `(B)` 剩余硬步的具名形态**

本节两件事：

1. **`separable_minpoly_genMatKF`**：`(minpoly K (genMatKF k)).Separable`，`K = SField F r n`。
   **口径要点（本轮诊断出的真根因）**：`genMatKF k` 的 `charpoly` 系数在 `K` 上，
   故 `minpoly` 必须取 **`K` 上**——写成 `minpoly F` 是**类型错误**，而 Lean 在把
   `charpoly : K[X]` 硬塞进 `F[X]` 的过程中 `isDefEq` **心跳爆炸**（上轮记的"超时"其实是
   这个类型错误的表现，不是真的对大项慢）。修法 = 用 `minpoly (SField F r n)`。

2. **`DiagOver`／`DiagHyp`**：把 `lem:14.22` 所消费的"`θ(X_1)` 可对角化"（源文 `:400`）
   **精确具名**：`DiagOver A` = 存在域扩张 `L/K` 与 `L`-可逆 `P`、对角 `d`，使
   `P * (A ⊗ L) = diag d * P`；`DiagHyp k` = `DiagOver (genMatKF k)`。

**射程（勿夸大）**：`DiagHyp` **未证**——它是 `(B)` 的最后一个硬环
（"可分 `charpoly`/`minpoly` ⟹ 可对角化"）。由 `DiagHyp` 到 `θ` 形态
（`θ = P·(-)·P⁻¹` 是 `K`-代数自同构）的转接**未做**；`lem:14.22` 本体**未做**。 -/

section DiagOverDef

variable {K : Type} [Field K] {n : ℕ}

/-- **可对角化（某扩域上）**。 -/
def DiagOver (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (P : Matrix (Fin n) (Fin n) L),
    IsUnit P.det ∧
      ∃ d : Fin n → L,
        P * A.map (algebraMap K L) = Matrix.diagonal d * P

#print axioms DiagOver

end DiagOverDef

section GenMatK2

variable (F : Type) [Field F] (r n : ℕ)

/-- **`K` 上通用矩阵的极小多项式可分**。 -/
theorem separable_minpoly_genMatKF [NeZero n] (k : Fin r) :
    (minpoly (SField F r n) (genMatKF F r n k)).Separable := by
  set x := genMatKF F r n k with hx
  have hsp : x.charpoly.Separable := by
    rw [hx]; exact separable_charpoly_genMatKF F r n k
  exact hsp.of_dvd (minpoly.dvd (SField F r n) x (p := x.charpoly)
    (Matrix.aeval_self_charpoly x))

#print axioms separable_minpoly_genMatKF

/-- **`(B)` 的剩余硬步（具名）**：`lem:14.21` 的"可对角化"用法。 -/
def DiagHyp (k : Fin r) : Prop := DiagOver (genMatKF F r n k)

#print axioms DiagHyp

end GenMatK2

/-! ## §71 **`charpoly` 的根都是特征值** —— `DiagHyp` 的第一块

`DiagHyp`（§70）要证"可分 `charpoly` ⟹ 可对角化"。可对角化的标准论证是
**互异特征值 ⟹ 互异特征向量 ⟹ 线性无关 ⟹ `n` 个即基**。本节机检其**第一步**：

> `μ` 是 `charpoly A` 的根 ⟹ 存在非零 `v` 使 `A *ᵥ v = μ • v`。

**机制**：`f.IsRoot μ` ⟹ `f.eval μ = 0` ⟹ `(scalar μ − A).det = 0`（`Matrix.eval_charpoly`）
⟹ `∃ v ≠ 0, (scalar μ − A) *ᵥ v = 0`（`Matrix.exists_mulVec_eq_zero_iff`）
⟹ `A *ᵥ v = (scalar μ) *ᵥ v = μ • v`（`Matrix.sub_mulVec` ＋ `Matrix.smul_mulVec`）。

**射程（勿夸大）**：只有"根 ⟹ 特征向量"。**未做**：互异根 ⟹ 特征向量**线性无关**
（mathlib 有 `Module.End.eigenvectors_linearIndependent'`，需经 `Matrix.toLin'` 转接）；
`n` 个特征向量构成基；以及由基拼出可逆 `P` 使 `P * A = diag d * P`（`DiagHyp` 本体）。 -/

section Eigen

variable {K : Type*} [Field K] {n : ℕ}

/-- **`charpoly` 的根都是特征值**：存在非零特征向量。

**机制**：`f.IsRoot μ` ⟹ `f.eval μ = 0` ⟹ `(scalar μ - A).det = 0`（`Matrix.eval_charpoly`）
⟹ `∃ v ≠ 0, (scalar μ - A) *ᵥ v = 0`（`Matrix.exists_mulVec_eq_zero_iff`）
⟹ `A *ᵥ v = (scalar μ) *ᵥ v = μ • v`（`Matrix.sub_mulVec`／`Matrix.smul_mulVec`）。
**用途**：`DiagHyp` 的"互异根 ⟹ 互异特征值"那一步。 -/
theorem exists_eigenvector_of_isRoot {A : Matrix (Fin n) (Fin n) K} {μ : K}
    (h : A.charpoly.IsRoot μ) : ∃ v : Fin n → K, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  have hdet : (Matrix.scalar (Fin n) μ - A).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  have h2 : (Matrix.scalar (Fin n) μ) *ᵥ v - A *ᵥ v = 0 := by
    rw [← Matrix.sub_mulVec]; exact hv
  rw [sub_eq_zero] at h2
  rw [← h2]
  rw [show Matrix.scalar (Fin n) μ = μ • (1 : Matrix (Fin n) (Fin n) K) from
    (Matrix.smul_one_eq_diagonal μ).symm, Matrix.smul_mulVec, Matrix.one_mulVec]

#print axioms exists_eigenvector_of_isRoot

end Eigen

/-! ## §72 **互异特征值 ⟹ 可对角化（同域版）** —— `DiagHyp` 的第 ②③④ 环

§71 给了"`charpoly` 的根 ⟹ 特征向量"。本节补上可对角化链的其余三环（在**同一个域**上）：

1. **`linearIndependent_eigenvectors`**：互异特征值 `μ` 对应的非零特征向量族**线性无关**。
   **机制**：mathlib 的 `Module.End.eigenvectors_linearIndependent'`，
   经 `Matrix.toLin'`（`toLin'_apply : (toLin' A) v = A *ᵥ v`）转接到矩阵。
2. **`exists_mul_diag_of_distinct`**：`n` 个互异特征值给可逆的 `P`（列 ＝ 特征向量），使
   `A * P = P * diagonal μ`。
   **机制**：`Matrix.linearIndependent_col_iff_isUnit`（列线性无关 ⟺ 矩阵是单位）
   ＋ `isUnit_iff_isUnit_det`；`A * P` 的 `(i,j)` 项是 `(A *ᵥ v_j)_i`，由特征方程等于
   `μ_j * (v_j)_i`。

**为何是"同域版"**：本节的 `μ` 必须**在 `K` 里**。`DiagHyp`（`genMatKF` 的情形）的
特征值**不在 `K` 里**，需先取 `charpoly` 的**分裂域** `L ⊇ K` 再套本节——
**那一步（分裂域 ＋ 可分 ⟹ 互异根）未做**。
**亦未做**：把 `A * P = P * diag μ` 转成 `DiagOver` 的 `Q * A = diag μ * Q` 形态
（`Q := P⁻¹`，需 `Matrix.nonsing_inv`）。 -/

section EigenIndep

variable {K : Type*} [Field K] {n : ℕ}

/-- 互异特征值 ⟹ 特征向量线性无关。 -/
theorem linearIndependent_eigenvectors {ι : Type*} (A : Matrix (Fin n) (Fin n) K) (μ : ι → K)
    (hμ : Function.Injective μ) (v : ι → Fin n → K) (hv : ∀ i, v i ≠ 0)
    (heig : ∀ i, A *ᵥ v i = μ i • v i) : LinearIndependent K v := by
  refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) μ hμ v (fun i => ?_)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨by rw [Matrix.toLin'_apply]; exact heig i, hv i⟩

#print axioms linearIndependent_eigenvectors

/-- **`n` 个互异特征值的特征向量给出可逆的换基矩阵 `P`**，且 `A * P = P * diagonal μ`。 -/
theorem exists_mul_diag_of_distinct {A : Matrix (Fin n) (Fin n) K} {μ : Fin n → K}
    (hμ : Function.Injective μ) (v : Fin n → Fin n → K) (hv : ∀ i, v i ≠ 0)
    (heig : ∀ i, A *ᵥ v i = μ i • v i) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P.det ∧ A * P = P * Matrix.diagonal μ := by
  classical
  refine ⟨Matrix.of (fun i j => v j i), ?_, ?_⟩
  · have heq : (Matrix.of (fun i j => v j i) : Matrix (Fin n) (Fin n) K).col = v := by
      funext j i
      rfl
    have hind : LinearIndependent K (Matrix.of (fun i j => v j i) :
        Matrix (Fin n) (Fin n) K).col := by
      rw [heq]
      exact linearIndependent_eigenvectors A μ hμ v hv heig
    exact (isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_col_iff_isUnit.mp hind)
  · ext i j
    have h : (A *ᵥ v j) i = μ j * v j i := by
      have h' := congrFun (heig j) i
      simpa [Matrix.mulVec, dotProduct, smul_eq_mul] using h'
    have hL : (A * Matrix.of (fun i j => v j i)) i j = (A *ᵥ v j) i := rfl
    rw [hL, h, Matrix.mul_diagonal]
    simp only [Matrix.of_apply]
    ring

#print axioms exists_mul_diag_of_distinct

end EigenIndep

/-! ## §73 **同域版收口**：`charpoly` 在 `K` 内互异根 ⟹ `DiagOver`

§72 给了"互异特征值 + 特征向量 ⟹ 可逆 `P` 使 `A * P = P * diagonal μ`"。本节把它
**接到 `DiagOver` 的形态**（§70 定义：`Q * (A ⊗ K) = diagonal d * Q`）并收口：

1. **`diagOver_of_distinct`**：`Q := P⁻¹`。由 `A * P = P * D` 得
   `P⁻¹ * A * P = D`，再右乘 `P⁻¹`（`P * P⁻¹ = 1`，`noncomm_ring` 收尾）得
   `P⁻¹ * A = D * P⁻¹`；`IsUnit P⁻¹` 由 `P⁻¹ * P = 1` 得。
2. **`diagOver_of_roots`**：`charpoly A` 在 `K` 内有 `n` 个**互异根** ⟹ `DiagOver A`。
   每个根给特征向量（§71 `exists_eigenvector_of_isRoot`，`Classical.choose`），
   再由 1 收口。

**射程（勿夸大）**：这两条都要求**根在 `K` 里**。`DiagHyp`（`genMatKF` 的 `charpoly`）的根
**不在 `K` 里**——还差**一步**：取 `charpoly` 的**分裂域** `L`，并证
"`charpoly` 可分 ⟹ 在 `L` 上分裂成 `n` 个**互异**线性因子"（§69／§70 给了可分性）。
**该步未做**；做完后 `DiagHyp` 即由 `diagOver_of_roots` 立得。 -/

section DiagOverSameField

variable {K : Type} [Field K] {n : ℕ}

/-- **同域版：互异特征值 ⟹ `DiagOver`**（`Q := P⁻¹`）。 -/
theorem diagOver_of_distinct {A : Matrix (Fin n) (Fin n) K} {μ : Fin n → K}
    (hμ : Function.Injective μ) (v : Fin n → Fin n → K) (hv : ∀ i, v i ≠ 0)
    (heig : ∀ i, A *ᵥ v i = μ i • v i) : DiagOver A := by
  obtain ⟨P, hunit, hAP⟩ := exists_mul_diag_of_distinct hμ v hv heig
  refine ⟨K, inferInstance, inferInstance, P⁻¹, ?_, μ, ?_⟩
  · exact (isUnit_iff_isUnit_det _).mp (IsUnit.of_mul_eq_one _ (Matrix.nonsing_inv_mul P hunit))
  · have h1 : P⁻¹ * A * P = Matrix.diagonal μ := by
      rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hunit,
        Matrix.one_mul]
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hunit
    have h2 : P⁻¹ * A = Matrix.diagonal μ * P⁻¹ := by
      calc P⁻¹ * A = P⁻¹ * A * 1 := by noncomm_ring
        _ = P⁻¹ * A * (P * P⁻¹) := by rw [hPP]
        _ = P⁻¹ * A * P * P⁻¹ := by noncomm_ring
        _ = Matrix.diagonal μ * P⁻¹ := by rw [h1]
    have hmap : A.map (algebraMap K K) = A := by
      ext i j
      simp [Matrix.map_apply]
    rw [hmap, h2]

#print axioms diagOver_of_distinct

/-- **同域版收口**：`charpoly A` 在 `K` 内有 `n` 个互异根 ⟹ `DiagOver A`。

**机制**：每个根给特征向量（`exists_eigenvector_of_isRoot`，`Classical.choose`），
再由 `diagOver_of_distinct` 拼出可逆 `P`。
**用途**：`DiagHyp` 的分裂域版本只差"把 `L` 上的互异根族造出来"。 -/
theorem diagOver_of_roots {A : Matrix (Fin n) (Fin n) K} {μ : Fin n → K}
    (hμ : Function.Injective μ) (hroots : ∀ i, A.charpoly.IsRoot (μ i)) : DiagOver A := by
  choose v hv0 hveig using fun i => exists_eigenvector_of_isRoot (hroots i)
  exact diagOver_of_distinct hμ v hv0 hveig

#print axioms diagOver_of_roots


end DiagOverSameField

/-! ## §74 **`DiagHyp` 机检** —— `(B)` 入口的最后一个硬环落下

`DiagHyp`（§70 具名）就是源文 `:400` 那句"`lem:14.21` 推出存在 `θ : M_n(K) → M_n(L)` 使
`θ(X_1)` 对角"。本节把它**证成定理**：

1. **`exists_distinct_roots_algClosure`**：`charpoly A` 可分且 `natDegree = n` ⟹
   在**代数闭包** `AlgebraicClosure K` 上有 `n` 个**互异**根。机制：
   `IsAlgClosed.splits`（分裂）＋ `Separable.map` ＋ `Polynomial.nodup_roots`（互异）＋
   `Splits.natDegree_eq_card_roots`（个数）＋ `Finset.equivFinOfCardEq`（把 `n` 个根编成 `Fin n`）。
   **用代数闭包而非分裂域**：省掉分裂域构造，且 `IsAlgClosed.splits` 对任意多项式直接可用。
2. **`diagOver_of_separable`**：可分 ＋ `natDegree = n` ⟹ **`DiagOver A`**。
   每根给特征向量（§71）⟹ 互异特征值给可逆 `P`（§72）⟹ 取 `P⁻¹` 得 `DiagOver` 形态（§73）。
3. **`diagHyp`**：对 `genMatKF k` 落地——`charpoly` 可分（§69）＋ `natDegree = n`。

**射程（勿夸大）**：`DiagHyp` 是**"可对角化"**这一条，不含源文 `lem:14.22` 的其余部分
（把 `θ` 写成 `K`-代数同态的自同构形态、`φ : S' → L`、`M_n(φ)ψ = θ` 的单射识别）。
那些**未做**；`lem:14.23/24/25` 与 `prop:14.19` 装配**未做**。 -/

section SplitStep

variable {K : Type} [Field K] {n : ℕ}

/-- **可分 ＋ `natDegree = n` ⟹ 代数闭包上有 `n` 个互异根**。 -/
theorem exists_distinct_roots_algClosure {A : Matrix (Fin n) (Fin n) K}
    (hsep : A.charpoly.Separable) (hnd : A.charpoly.natDegree = n) :
    ∃ μ : Fin n → AlgebraicClosure K, Function.Injective μ ∧
      ∀ i, ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).IsRoot (μ i) := by
  classical
  have hmap : (A.charpoly).map (algebraMap K (AlgebraicClosure K))
      = (A.map (algebraMap K (AlgebraicClosure K))).charpoly :=
    (Matrix.charpoly_map A _).symm
  have hsplit : ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).Splits :=
    IsAlgClosed.splits _
  have hsep' : ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).Separable := by
    rw [← hmap]; exact hsep.map
  have hnodup : ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).roots.Nodup :=
    Polynomial.nodup_roots hsep'
  have hlc : (algebraMap K (AlgebraicClosure K)) (A.charpoly.leadingCoeff) ≠ 0 := by
    rw [(Matrix.charpoly_monic A).leadingCoeff, map_one]
    exact one_ne_zero
  have hcard : ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).roots.card = n := by
    rw [← hsplit.natDegree_eq_card_roots, ← hmap, Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc]
    exact hnd
  have hs : ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnodup]; exact hcard
  have hne : ((A.map (algebraMap K (AlgebraicClosure K))).charpoly) ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  let μ : Fin n → AlgebraicClosure K := fun i => ((Finset.equivFinOfCardEq hs).symm i).1
  refine ⟨μ, ?_, ?_⟩
  · intro i j hij
    have h2 : (Finset.equivFinOfCardEq hs).symm i = (Finset.equivFinOfCardEq hs).symm j :=
      Subtype.ext hij
    simpa [μ] using congrArg (Finset.equivFinOfCardEq hs) h2
  · intro i
    have hmem : μ i ∈ ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).roots.toFinset := by
      simpa [μ] using ((Finset.equivFinOfCardEq hs).symm i).2
    have hmem' : μ i ∈ ((A.map (algebraMap K (AlgebraicClosure K))).charpoly).roots :=
      (Multiset.mem_toFinset).mp hmem
    exact (Polynomial.mem_roots hne).mp hmem'

#print axioms exists_distinct_roots_algClosure

/-- ★★★★★ **`DiagOver A`**：可分 `charpoly`（`natDegree = n`）⟹ 可对角化。

**证明**：代数闭包 `L = AlgebraicClosure K` 上，可分 ⟹ `charpoly` 分裂且互异
（`exists_distinct_roots_algClosure`）⟹ 每个根给特征向量（§71）⟹ 互异特征值给可逆 `P`
（§72）⟹ 取 `P⁻¹` 得 `DiagOver` 形态（§73 同法）。 -/
theorem diagOver_of_separable {A : Matrix (Fin n) (Fin n) K}
    (hsep : A.charpoly.Separable) (hnd : A.charpoly.natDegree = n) : DiagOver A := by
  classical
  obtain ⟨μ, hμ, hroot⟩ := exists_distinct_roots_algClosure hsep hnd
  choose v hv0 hveig using fun i => exists_eigenvector_of_isRoot (hroot i)
  obtain ⟨P, hunit, hAP⟩ := exists_mul_diag_of_distinct hμ v hv0 hveig
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, P⁻¹, ?_, μ, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (IsUnit.of_mul_eq_one _ (Matrix.nonsing_inv_mul P hunit))
  · have h1 : P⁻¹ * (A.map (algebraMap K (AlgebraicClosure K))) * P = Matrix.diagonal μ := by
      rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hunit,
        Matrix.one_mul]
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hunit
    calc P⁻¹ * (A.map (algebraMap K (AlgebraicClosure K)))
        = P⁻¹ * (A.map (algebraMap K (AlgebraicClosure K))) * 1 := by noncomm_ring
      _ = P⁻¹ * (A.map (algebraMap K (AlgebraicClosure K))) * (P * P⁻¹) := by rw [hPP]
      _ = P⁻¹ * (A.map (algebraMap K (AlgebraicClosure K))) * P * P⁻¹ := by noncomm_ring
      _ = Matrix.diagonal μ * P⁻¹ := by rw [h1]

#print axioms diagOver_of_separable


section DiagHypFinal

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`DiagHyp` 机检** —— `(B)` 入口的最后一个硬环落下。

即：`X_k` 在某个扩域上**可对角化**（源文 `:400` 的 "there is an embedding
`θ : M_n(K) → M_n(L)` such that `θ(X_1)` is a diagonal matrix" 的内容）。
**由**：`charpoly (genMatKF k)` 可分（§69）＋ `diagOver_of_separable`（本节）。 -/
theorem diagHyp [NeZero n] (k : Fin r) : DiagHyp F r n k := by
  have hnd : (genMatKF F r n k).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact diagOver_of_separable (separable_charpoly_genMatKF F r n k) hnd

#print axioms diagHyp

end DiagHypFinal

end SplitStep

/-! ## §75 **`DiagHyp` ⟹ 源文的 `θ` 形态** —— `lem:14.22` 的直接输入

源文 `raw/Saltman1999ch14.tex:400–401`（`lem:14.22` 证明开头，逐字）：

> "From Lemma 14.21 it follows that there is an embedding `θ : M_n(K) → M_n(L)` such that
> `θ(X_1)` is a diagonal matrix."

本节把这句**机检成定理**：

1. **`exists_algHom_diagonal_of_diagOver`**：`DiagOver A`（§70 具名、§74 已证）⟹
   存在 `L/K` 与**单射** `θ : M_n(K) →ₐ[K] M_n(L)` 使 `θ A` 对角。
   **构造**：`θ = conj(P) ∘ baseChange`，即 `θ X = P * X_L * P⁻¹`——用本项目**已有**的
   `conjAlgEquiv`（`M ↦ A·M·A⁻¹` 的 `F`-代数自同构，§31 已机检）与
   `AlgHom.mapMatrix (Algebra.ofId K L)`。则
   `θ A = P * A_L * P⁻¹ = diag d * P * P⁻¹ = diag d`。
   单射性：`mapMatrix` 沿单射的 `Algebra.ofId`（`Matrix.map_injective`）＋ `conjAlgEquiv` 是等价。
2. **`exists_algHom_diagonal_genMatKF`**：对 `X_k` 落地（`diagHyp` ＋ 1）。

**射程（勿夸大）**：本节给的是源文那一**句**。`lem:14.22` 的**其余部分**
（用 `θ` 造 `φ : S' → L`、证 `M_n(φ)ψ = θ` 在 `R` 上成立、由此得 `ψ` 单射）**未做**。 -/

section ThetaForm

variable {K : Type} [Field K] {n : ℕ}

/-- **`DiagOver` ⟹ 源文的 `θ` 形态**：存在 `L/K` 与 `K`-代数同态
`θ : M_n(K) →ₐ[K] M_n(L)`（**单射**）使 `θ A` 是对角矩阵。

**构造**：`DiagOver` 给 `P`（`P * A_L = diag d * P`）；取 `θ = conj(P) ∘ baseChange`，
即 `θ X = P * X_L * P⁻¹`（`conjAlgEquiv`，§31 已机检）。则
`θ A = P * A_L * P⁻¹ = diag d * P * P⁻¹ = diag d`。
**这就是**源文 `:400–401` 的 "there is an embedding `θ : M_n(K) → M_n(L)` such that
`θ(X_1)` is a diagonal matrix"，**`lem:14.22` 的直接输入**。 -/
theorem exists_algHom_diagonal_of_diagOver {A : Matrix (Fin n) (Fin n) K} (h : DiagOver A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
      (θ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) L),
      Function.Injective θ ∧ ∃ d : Fin n → L, θ A = Matrix.diagonal d := by
  classical
  obtain ⟨L, hFld, hAlg, P, hunit, d, hPA⟩ := h
  letI := hFld
  letI := hAlg
  have hunitM : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hunit
  obtain ⟨Pu, hPu⟩ := hunitM
  -- `Pu : (Matrix (Fin n) (Fin n) L)ˣ`，`↑Pu = P`
  let φ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) L :=
    AlgHom.mapMatrix (Algebra.ofId K L)
  let θ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) L :=
    (conjAlgEquiv (F := K) Pu).toAlgHom.comp φ
  refine ⟨L, hFld, hAlg, θ, ?_, d, ?_⟩
  · -- 单射：`φ` 单射（`mapMatrix` 沿单射的 `ofId`），`conjAlgEquiv` 是等价
    have hφ : Function.Injective φ := by
      intro X Y hXY
      have hmap : X.map (⇑(Algebra.ofId K L)) = Y.map (⇑(Algebra.ofId K L)) := by
        simpa [φ, AlgHom.mapMatrix_apply] using hXY
      exact Matrix.map_injective (f := ⇑(Algebra.ofId K L)) (Algebra.ofId K L).injective hmap
    intro X Y hXY
    have h2 : φ X = φ Y := (conjAlgEquiv (F := K) Pu).injective hXY
    exact hφ h2
  · -- `θ A = diagonal d`
    show (conjAlgEquiv (F := K) Pu).toAlgHom (φ A) = Matrix.diagonal d
    have hφA : φ A = A.map (algebraMap K L) := by
      ext i j
      simp [φ, AlgHom.mapMatrix_apply, Matrix.map_apply]
    rw [hφA]
    have hconj : (conjAlgEquiv (F := K) Pu).toAlgHom (A.map (algebraMap K L))
        = P * (A.map (algebraMap K L)) * P⁻¹ := by
      show (conjRingEquiv Pu) (A.map (algebraMap K L))
        = P * (A.map (algebraMap K L)) * P⁻¹
      rw [conjRingEquiv]
      simp [hPu]
    rw [hconj, hPA, Matrix.mul_assoc, Matrix.mul_nonsing_inv P hunit, Matrix.mul_one]

#print axioms exists_algHom_diagonal_of_diagOver


section GenMatTheta

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`lem:14.22` 的输入句（对本战役的通用矩阵）**：

存在域扩张 `L/K` 与**单射** `K`-代数同态 `θ : M_n(K) →ₐ[K] M_n(L)`，使 `θ(X_k)` 是对角矩阵。
—— 源文 `:400` 逐字："From Lemma 14.21 it follows that there is an embedding
`θ : M_n(K) → M_n(L)` such that `θ(X_1)` is a diagonal matrix."

**由**：`DiagHyp`（§74 已证）＋ `exists_algHom_diagonal_of_diagOver`（本节）。 -/
theorem exists_algHom_diagonal_genMatKF [NeZero n] (k : Fin r) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (SField F r n) L)
      (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n]
        Matrix (Fin n) (Fin n) L),
      Function.Injective θ ∧ ∃ d : Fin n → L, θ (genMatKF F r n k) = Matrix.diagonal d :=
  exists_algHom_diagonal_of_diagOver (diagHyp F r n k)

#print axioms exists_algHom_diagonal_genMatKF

end GenMatTheta

end ThetaForm

/-! ## §76 **`lem:14.22` 的 `S'`-侧地图 `ψ`** —— `X_k ↦ Y_k` 的 `F`-代数同态

`lem:14.22`（源文 `:404`）要证 `ψ : R(F,n,r) → M_n(S')`（`X_1 ↦ X`、`X_k ↦ Y_k`）是**单射**。
本节把 `ψ` **构造出来**并算出它在生成元上的像：

1. **`evSpr`**：`S → S'` 的特殊化——`x_{ij,k₀} ↦ δ_{ij} x_{ii}`、`x_{ij,k} ↦ y_{ijk}`（`k ≠ k₀`）。
   （`k₀` 需 `k₀.val = 0`，因为 `Spr` 的 `Y`-变量索引是 `{k // k.val ≠ 0}`。）
2. **`psiSpr`**：`ψ = (Matrix.map evSpr) ∘ (R ↪ M_n(S))`——**这是 `AlgHom`**，
   故 `ψ` 的**良定义性免费**（源文在此处未加论证；本工作区用 `AlgHom.comp` 绕开）。
3. **`psiSpr_genMat_self`**：`ψ (X_{k₀}) = xdiag`（对角矩阵）。
4. **`psiSpr_genMat`**：`ψ (X_k) = Y_k`（`k ≠ k₀`）。

**射程（勿夸大）**：本节只给 `ψ` 与其生成元像。**未做**：`φ : S' → L`（把它接到 `θ`）、
`M_n(φ) ∘ ψ = θ ∘ (· ⊗ K)` 的交换性、以及由 `θ` 单射推出 **`ψ` 单射**（`lem:14.22` 本体）。 -/

section PsiSpr

variable (F : Type) [Field F] (r n : ℕ)

/-- 特殊化 `S → S'`：`x_{ij,k₀} ↦ δ_{ij} x_ii`（`k = k₀` 时），否则 `x_{ij,k} ↦ y_{ijk}`。 -/
noncomputable def evSpr (k₀ : Fin r) (hk₀ : k₀.val = 0) : S F r n →ₐ[F] Spr F r n :=
  MvPolynomial.aeval (fun p : Fin r × Fin n × Fin n =>
    if h : p.1 = k₀ then
      (if p.2.1 = p.2.2 then MvPolynomial.X (Sum.inl p.2.1) else 0)
    else
      MvPolynomial.X (Sum.inr (p.2.1, p.2.2, ⟨p.1, by
        intro h0
        exact h (Fin.ext (by rw [h0, hk₀]))⟩)))

#print axioms evSpr

/-- `ψ : R → M_n(S')`：`X_k ↦ Y_k`（`k = k₀` 时 `X` 对角）。 -/
noncomputable def psiSpr (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    ↥(genericMatrixAlgebra F r n) →ₐ[F] Matrix (Fin n) (Fin n) (Spr F r n) :=
  (AlgHom.mapMatrix (evSpr F r n k₀ hk₀)).comp (Subalgebra.val _)

#print axioms psiSpr

/-- `ψ` 在 `X_{k₀}` 上是对角矩阵。 -/
theorem psiSpr_genMat_self (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k₀, genericMatrix_mem F r n k₀⟩
      = xdiag F r n := by
  refine Matrix.ext fun i j => ?_
  show (genericMatrix F r n k₀).map (evSpr F r n k₀ hk₀) i j = xdiag F r n i j
  rw [Matrix.map_apply, genericMatrix, genericEntry, xdiag, Matrix.diagonal, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp [evSpr]
  · simp [evSpr, hij]

#print axioms psiSpr_genMat_self


/-- `ψ` 在其它的 `X_k`（`k ≠ k₀`）上是 `Y_k`。 -/
theorem psiSpr_genMat (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀) :
    psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩
      = ymat F r n ⟨k, by
          intro h0
          exact hk (Fin.ext (by rw [h0, hk₀]))⟩ := by
  refine Matrix.ext fun i j => ?_
  show (genericMatrix F r n k).map (evSpr F r n k₀ hk₀) i j = ymat F r n _ i j
  rw [Matrix.map_apply, genericMatrix, genericEntry, ymat_apply, evSpr, MvPolynomial.aeval_X]
  simp [hk]

#print axioms psiSpr_genMat

end PsiSpr

/-! ## §77 **源文的 `φ : S' → L` 与生成元上的交换性** —— `lem:14.22` 的步骤①②

源文 `raw/Saltman1999ch14.tex:403–404`（`lem:14.22` 证明，逐字）：

> "Define `φ : S' → L` by setting `φ(x_{ii})` to be the `ii` entry of `θ(X_1)` and
> `φ(y_{ijk})` to be the `ij` entry of `θ(X_k)` for `k ≥ 2`. Of course,
> `M_n(φ)(X) = θ(X_1)` and `M_n(φ)(Y_k) = θ(X_k)`."

本节机检这几件：

1. **`phiOfTheta`**：`φ = MvPolynomial.aeval`（`x_ii ↦ (θ X_{k₀})_{ii}`、`y_ijk ↦ (θ X_k)_{ij}`）。
2. `phiOfTheta_inl`／`phiOfTheta_inr`：`φ` 在两族变量上的值。
3. **`mapMatrix_phi_psiSpr_self`**：`(M_n φ)(ψ X_{k₀}) = θ(X_{k₀})`——需
   `θ(X_{k₀})` 是**对角**的（`DiagHyp` 提供的 `hθ`）；这是 `lem:14.21` 在 `lem:14.22` 里
   唯一被用到的地方（源文 "Of course" 背后的实质）。
4. **`mapMatrix_phi_psiSpr`**：`(M_n φ)(ψ X_k) = θ(X_k)`（`k ≠ k₀`），**无条件**。

**射程（勿夸大）**：只到**生成元**。**未做**：把两条生成元等式提升为 `R` 上的 `AlgHom` 等式
（需沿 `R = Algebra.adjoin F (range genMat)` 的 `adjoin_induction` 延拓），
以及由 `θ` 单射推出 **`ψ` 单射**（`lem:14.22` 本体）。
**另注**：本节把 `[Algebra F L]`／`[Algebra (SField F r n) L]` 作**显式参数**，
避免实例合成的不确定性（R100／R107 的教训）。 -/

section PhiTheta

variable (F : Type) [Field F] (r n : ℕ)
variable {L : Type} [Field L] [Algebra F L] [Algebra (SField F r n) L]

/-- **源文的 `φ : S' → L`**（`:403`）：`φ(x_ii) = (θ X_{k₀})_{ii}`、`φ(y_ijk) = (θ X_k)_{ij}`。 -/
noncomputable def phiOfTheta (k₀ : Fin r)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L) :
    Spr F r n →ₐ[F] L :=
  MvPolynomial.aeval (fun v : SprIdx r n =>
    match v with
    | Sum.inl i => θ (genMatKF F r n k₀) i i
    | Sum.inr (i, j, k) => θ (genMatKF F r n k.1) i j)

#print axioms phiOfTheta

theorem phiOfTheta_inl (k₀ : Fin r)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
    (i : Fin n) :
    phiOfTheta F r n k₀ θ (MvPolynomial.X (Sum.inl i)) = θ (genMatKF F r n k₀) i i := by
  rw [phiOfTheta, MvPolynomial.aeval_X]

#print axioms phiOfTheta_inl

theorem phiOfTheta_inr (k₀ : Fin r)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
    (i j : Fin n) (k : {k : Fin r // k.val ≠ 0}) :
    phiOfTheta F r n k₀ θ (MvPolynomial.X (Sum.inr (i, j, k)))
      = θ (genMatKF F r n k.1) i j := by
  rw [phiOfTheta, MvPolynomial.aeval_X]

#print axioms phiOfTheta_inr


/-- **生成元上的交换性（`k = k₀`）**：`(M_n(φ)) (ψ X_{k₀}) = θ (X_{k₀})`。
需 `θ (X_{k₀})` 是对角矩阵（`lem:14.21` 的用法，由 `DiagHyp` 提供）。 -/
theorem mapMatrix_phi_psiSpr_self (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
    {d : Fin n → L} (hθ : θ (genMatKF F r n k₀) = Matrix.diagonal d) :
    (AlgHom.mapMatrix (phiOfTheta F r n k₀ θ))
        (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k₀, genericMatrix_mem F r n k₀⟩)
      = θ (genMatKF F r n k₀) := by
  rw [psiSpr_genMat_self]
  refine Matrix.ext fun i j => ?_
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, xdiag_apply]
  by_cases hij : i = j
  · subst hij
    simp [phiOfTheta_inl]
  · rw [if_neg hij, map_zero]
    rw [hθ, Matrix.diagonal, Matrix.of_apply, if_neg hij]

#print axioms mapMatrix_phi_psiSpr_self

/-- **生成元上的交换性（`k ≠ k₀`）**：`(M_n(φ)) (ψ X_k) = θ (X_k)`。 -/
theorem mapMatrix_phi_psiSpr (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L) :
    (AlgHom.mapMatrix (phiOfTheta F r n k₀ θ))
        (psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩)
      = θ (genMatKF F r n k) := by
  rw [psiSpr_genMat F r n k₀ hk₀ hk]
  refine Matrix.ext fun i j => ?_
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, ymat_apply, phiOfTheta_inr]

#print axioms mapMatrix_phi_psiSpr

end PhiTheta

/-! ## §78 **`lem:14.22` 的两个延拓工具** —— `R` 上的同态相等判据 ＋ `θ` 的 `F`-线性

`lem:14.22` 的最后一步是：把 §77 的**生成元**等式提升为 `R` 上的**整体**等式，
再由 `θ` 单射得 `ψ` 单射。本节给其中两个纯工具：

1. **`algHom_eq_of_genericMatrix`**：两条 `F`-代数同态 out of
   `R = Algebra.adjoin F (Set.range genMat)` 若在每个 `genMat k` 上相等，则相等。
   **机制**：`Algebra.adjoin_induction`，motive 取 `fun y hy => f ⟨y, hy⟩ = g ⟨y, hy⟩`
   （`algebraMap` 分支用 `AlgHom.commutes`，`add`／`mul` 用归纳假设）。
   **注意**：`obtain ⟨y, hy⟩` 后须 `revert hy` 再 `refine ... ?_ ?_ ?_ ?_`，
   让 `adjoin_induction` 的末参数 `∀ {x} (hx), p x hx` 自然吃下 `y, hy`。
2. **`theta_algebraMap_F`**：`θ`（`K`-代数同态）的 `F`-线性——
   `θ (algebraMap F (M_n K) c) = algebraMap F (M_n L) c`。
   **机制**：两次 `IsScalarTower.algebraMap_apply` ＋ `AlgHom.commutes`；
   需 `[IsScalarTower F (SField F r n) L]`（**显式参数**，不赌实例合成）。

**射程（勿夸大）**：本节只有工具。`psiSpr_comm`（把 §77 的生成元交换性沿 `adjoin` 延拓到
`R`）与 **`ψ` 单射**（`lem:14.22` 本体）**仍未完成**——`psiSpr_comm` 的 `algebraMap` 与
`add`／`mul` 分支的 `Matrix.map`／`AlgHom` 重写仍在调试（已定位到
`Matrix.map_add`／`Matrix.map_mul` 的隐式参数与 `AlgHom.commutes` 的应用次序）。 -/

section Helpers1422

variable (F : Type) [Field F] (r n : ℕ)

/-- **`R` 上的同态相等判据**：两条 `F`-代数同态 out of `R = Algebra.adjoin F (range genMat)`
若在每个 `genMat k` 上相等，则相等。 -/
theorem algHom_eq_of_genericMatrix {A : Type} [Semiring A] [Algebra F A]
    {f g : ↥(genericMatrixAlgebra F r n) →ₐ[F] A}
    (h : ∀ k : Fin r,
      f ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩
        = g ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩) : f = g := by
  refine AlgHom.ext fun a => ?_
  obtain ⟨y, hy⟩ := a
  revert hy
  refine Algebra.adjoin_induction (s := Set.range (genericMatrix F r n))
    (p := fun y hy => f ⟨y, hy⟩ = g ⟨y, hy⟩) ?_ ?_ ?_ ?_
  · rintro x ⟨k, rfl⟩
    exact h k
  · intro c
    exact (f.commutes c).trans (g.commutes c).symm
  · intro x y hx hy ihx ihy
    show f ⟨x + y, _⟩ = g ⟨x + y, _⟩
    rw [show (⟨x + y, _⟩ : ↥(genericMatrixAlgebra F r n)) =
      ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add, map_add, ihx, ihy]
  · intro x y hx hy ihx ihy
    show f ⟨x * y, _⟩ = g ⟨x * y, _⟩
    rw [show (⟨x * y, _⟩ : ↥(genericMatrixAlgebra F r n)) =
      ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul, map_mul, ihx, ihy]

#print axioms algHom_eq_of_genericMatrix

variable {L : Type} [Field L] [Algebra F L] [Algebra (SField F r n) L]
  [IsScalarTower F (SField F r n) L]

/-- **`θ` 的 `F`-线性**：`θ (algebraMap F (M_n K) c) = algebraMap F (M_n L) c`。 -/
theorem theta_algebraMap_F
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
    (c : F) :
    θ (algebraMap F (Matrix (Fin n) (Fin n) (SField F r n)) c)
      = algebraMap F (Matrix (Fin n) (Fin n) L) c := by
  rw [IsScalarTower.algebraMap_apply F (SField F r n) (Matrix (Fin n) (Fin n) (SField F r n)),
    AlgHom.commutes,
    IsScalarTower.algebraMap_apply F (SField F r n) (Matrix (Fin n) (Fin n) L)]

#print axioms theta_algebraMap_F

end Helpers1422

/-! ## §79 **`lem:14.22` 机检** —— `ψ : R → M_n(S')` 是单射

源文 `raw/Saltman1999ch14.tex:404`（`lem:14.22` 陈述）：

> "`ψ : R(F,n,r) → M_n(S')` is an injection."

本节把它**证成定理**：

1. **`thetaR`**：把 `θ ∘ (· ⊗ K)` 直接建成 `R` 上的 `F`-代数同态
   （`a ↦ θ (a_K)`，`a_K = a.map (algebraMap S K)`）。
   **为什么用结构字面量**：`AlgHom.comp` 路线的标量不匹配（`M_n(S)` 不是 `K`-代数，
   而 `mapMatrix (ofId S K)` 的标量是 `S`）——结构字面量把四个字段各自证掉，绕开复合与 `restrictScalars`。
   四个字段：`map_one'`／`map_zero'` 用 `simp`；`map_mul'`／`map_add'` 先 `Subalgebra.coe_mul`／`coe_add`
   推 coercion，再 `Matrix.map_mul`／`Matrix.map_add`（后者要显式给可加性证明）；
   `commutes'` 用 `Subalgebra.coe_algebraMap` ＋ `Matrix.map_algebraMap` ＋ `theta_algebraMap_F`（§78）。
2. **`psiSpr_comm`**：`(M_n φ) ∘ ψ = θR` 作为 `R` 上的 `F`-代数同态。
   **机制**：`algHom_eq_of_genericMatrix`（§78）把整体等式归约到生成元，
   生成元上正是 §77 的 `mapMatrix_phi_psiSpr_self`／`mapMatrix_phi_psiSpr`
   （`k = k₀` 分支需先 `subst` 掉 `k = k₀`，否则 `hk₀` 的类型与目标不符——R141）。
3. **`psiSpr_injective`**：`ψ` **单射**。机制：`ψ a = ψ b` ⟹ `θR a = θR b`
   ⟹（`θ` 单射）`a_K = b_K` ⟹（`algebraMap S K` 逐项单射，`IsFractionRing.injective`）
   `a = b`。

**射程（勿夸大）**：`lem:14.22` 到此完成。**下游仍未做**：把 `ψ` 的像识别为
`⟨X, Y_k⟩`（源文 "we may identify `R` with the subalgebra generated by `X` and `Y₂,…,Y_r`" 的
后半句需 `ψ` 的单射 ＋ 生成元像，已具备材料）、`lem:14.23/24/25`、
`prop:14.19` 装配、以及 `ZEqNFixed`。 -/

section ThetaR

variable (F : Type) [Field F] (r n : ℕ)
variable {L : Type} [Field L] [Algebra F L] [Algebra (SField F r n) L]
  [IsScalarTower F (SField F r n) L] [IsScalarTower F (S F r n) (SField F r n)]

/-- `θ ∘ (· ⊗ K)` 作为 `R` 上的 `F`-代数同态（结构字面量）。 -/
noncomputable def thetaR
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L) :
    ↥(genericMatrixAlgebra F r n) →ₐ[F] Matrix (Fin n) (Fin n) L where
  toFun a := θ ((a : Matrix (Fin n) (Fin n) (S F r n)).map
    (algebraMap (S F r n) (SField F r n)))
  map_one' := by simp
  map_mul' := by
    intro a b
    rw [Subalgebra.coe_mul, Matrix.map_mul]
    simp
  map_zero' := by simp
  map_add' := by
    intro a b
    rw [Subalgebra.coe_add,
      Matrix.map_add (algebraMap (S F r n) (SField F r n)) (fun x y => map_add _ x y)]
    simp
  commutes' := by
    intro c
    simp only [Subalgebra.coe_algebraMap]
    have h1 : (algebraMap F (Matrix (Fin n) (Fin n) (S F r n)) c).map
        (algebraMap (S F r n) (SField F r n))
        = algebraMap F (Matrix (Fin n) (Fin n) (SField F r n)) c := by
      rw [Matrix.map_algebraMap c (algebraMap (S F r n) (SField F r n)) (map_zero _)]
      rw [IsScalarTower.algebraMap_apply F (S F r n) (SField F r n)]
    rw [h1]
    exact theta_algebraMap_F F r n θ c

#print axioms thetaR


/-- ★★★★★ **`lem:14.22` 的交换性**：`(M_n φ) ∘ ψ = θ ∘ (· ⊗ K)` 作为 `R` 上的 `F`-代数同态。 -/
theorem psiSpr_comm (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
    {d : Fin n → L} (hθ : θ (genMatKF F r n k₀) = Matrix.diagonal d) :
    (AlgHom.mapMatrix (phiOfTheta F r n k₀ θ)).comp (psiSpr F r n k₀ hk₀)
      = thetaR F r n θ := by
  refine algHom_eq_of_genericMatrix F r n (A := Matrix (Fin n) (Fin n) L) (fun k => ?_)
  rw [AlgHom.comp_apply]
  by_cases hk : k = k₀
  · subst hk
    rw [mapMatrix_phi_psiSpr_self F r n k hk₀ θ hθ]
    rfl
  · rw [mapMatrix_phi_psiSpr F r n k₀ hk₀ hk]
    rfl

#print axioms psiSpr_comm

/-- ★★★★★ **`lem:14.22` 本体**：`ψ : R → M_n(S')` 是**单射**。 -/
theorem psiSpr_injective (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
    {d : Fin n → L} (hθ : θ (genMatKF F r n k₀) = Matrix.diagonal d)
    (hθinj : Function.Injective θ) : Function.Injective (psiSpr F r n k₀ hk₀) := by
  intro a b hab
  have h1 : thetaR F r n θ a = thetaR F r n θ b := by
    rw [← psiSpr_comm F r n k₀ hk₀ θ hθ, AlgHom.comp_apply, AlgHom.comp_apply, hab]
  have h2 : ((a : Matrix (Fin n) (Fin n) (S F r n))).map
      (algebraMap (S F r n) (SField F r n))
      = ((b : Matrix (Fin n) (Fin n) (S F r n))).map
        (algebraMap (S F r n) (SField F r n)) := hθinj h1
  exact Subtype.ext (Matrix.map_injective
    (IsFractionRing.injective (S F r n) (SField F r n)) h2)

#print axioms psiSpr_injective

end ThetaR

/-! ## §80 **`S'`-世界的子代数 `⟨X, Y_k⟩` 与 `ψ` 的生成元像**

源文 `:406`（`lem:14.22` 之后）："we may identify `R` with the subalgebra of `M_n(S')`
generated by `X` and `Y₂,…,Y_r`"。本节把那个子代数**具名**并机检其与 `ψ` 的关系：

1. **`sprGen`**：`S'`-世界的生成元族——`k = k₀` 给对角 `X`，其余给 `Y_k`
   （`k ≠ k₀` 且 `k₀.val = 0` ⟹ `k.val ≠ 0`，故可作 `Spr` 的 `Y`-索引）。
2. **`psiSpr_sprGen`**：`ψ (X_k) = sprGen k`（逐点，综合 §76 的两条）。
3. **`sprAlgebra`**：`⟨X, Y_k⟩ = Algebra.adjoin F (range sprGen)`。
4. **`adjoin_range_psiSpr_eq`**：`Algebra.adjoin F (range (ψ ∘ X_·)) = sprAlgebra`
   ——**由 `psiSpr_sprGen` 一步 `congrArg`**（生成元像的 `range` 相同 ⟹ `adjoin` 相同）。

**射程（勿夸大）**：这只是**生成元层**的识别。**未做**：把 `ψ` 单射（§79）与
"像 ⊇ `sprAlgebra`" 合成 **`R ≃ₐ[F] sprAlgebra`**（需 `Subalgebra.map` 的
`⊤`-形式：`ψ` 的定义域是 **`↥R`**，故 `Subalgebra.map ψ ⊤` 而非 `R.map ψ`——本节踩过此坑，R143）。 -/

section SprImage

variable (F : Type) [Field F] (r n : ℕ)

/-- `S'`-世界的生成元族：`k = k₀` 给对角 `X`，其余给 `Y_k`。 -/
noncomputable def sprGen (k₀ : Fin r) (hk₀ : k₀.val = 0) (k : Fin r) :
    Matrix (Fin n) (Fin n) (Spr F r n) :=
  if h : k = k₀ then xdiag F r n
  else ymat F r n ⟨k, by
    intro h0
    exact h (Fin.ext (by rw [h0, hk₀]))⟩

#print axioms sprGen

theorem psiSpr_sprGen (k₀ : Fin r) (hk₀ : k₀.val = 0) (k : Fin r) :
    psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩
      = sprGen F r n k₀ hk₀ k := by
  rw [sprGen]
  by_cases h : k = k₀
  · rw [dif_pos h, h]
    exact psiSpr_genMat_self F r n k₀ hk₀
  · rw [dif_neg h]
    exact psiSpr_genMat F r n k₀ hk₀ h

#print axioms psiSpr_sprGen


/-- `S'`-世界的子代数 `⟨X, Y_k⟩`（源文的 "subalgebra generated by `X` and `Y₂,…,Y_r`"）。 -/
noncomputable def sprAlgebra (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Subalgebra F (Matrix (Fin n) (Fin n) (Spr F r n)) :=
  Algebra.adjoin F (Set.range (sprGen F r n k₀ hk₀))

#print axioms sprAlgebra

/-- ★★★★ **`ψ` 的生成元像恰好生成 `S'`-世界的 `⟨X, Y_k⟩`**。 -/
theorem adjoin_range_psiSpr_eq (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Algebra.adjoin F (Set.range (fun k : Fin r =>
      psiSpr F r n k₀ hk₀ ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩))
      = sprAlgebra F r n k₀ hk₀ := by
  rw [sprAlgebra]
  exact congrArg (Algebra.adjoin F)
    (show Set.range (fun k : Fin r => psiSpr F r n k₀ hk₀
        ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩)
      = Set.range (sprGen F r n k₀ hk₀)
    from congrArg Set.range (funext (psiSpr_sprGen F r n k₀ hk₀)))

#print axioms adjoin_range_psiSpr_eq


end SprImage

/-! ## §81 **`R ≃ₐ[F] ⟨X, Y_k⟩`** —— 源文 `:406` 的识别机检

源文 `raw/Saltman1999ch14.tex:406`（`lem:14.22` 之后，逐字）：

> "we may identify `R` with the subalgebra of `M_n(S')` generated by `X` and `Y₂,…,Y_r`."

本节把这句话变成 `AlgEquiv`：

1. **`psiSpr_mem_sprAlgebra`**：`ψ a ∈ ⟨X, Y_k⟩`（沿 `adjoin_induction`，生成元用 `psiSpr_sprGen`）。
2. **`psiSpr_sprAlgebra_surj`**：`ψ` 打到 `⟨X, Y_k⟩` 上**满**（沿 `sprAlgebra` 的
   `adjoin_induction`，生成元给原像 `X_k`）。
3. **`psiSprAlgEquiv`**：**`R ≃ₐ[F] ⟨X, Y_k⟩`**（`AlgEquiv.ofBijective`，单射性来自 §79 的
   `psiSpr_injective`）。

**与 §80／§79 的关系**：§79 给单射、§80 给生成元像相同、本节把两者合成为**同构**。
**这是 `(B)` 的 `Z` 半的入口**：`Z` 是 `R` 的中心的分数域，经本同构可搬到
`⟨X, Y_k⟩`（从而搬到 `S'` 世界）上。

**射程（勿夸大）**：同构本身已机检，但**尚未**用它搬 `Z`；
`lem:14.23/24/25`、`prop:14.19` 装配、`ZEqNFixed` **都未做**。 -/

section PsiEquiv

variable (F : Type) [Field F] (r n : ℕ)
variable {L : Type} [Field L] [Algebra F L] [Algebra (SField F r n) L]
  [IsScalarTower F (SField F r n) L] [IsScalarTower F (S F r n) (SField F r n)]

variable (k₀ : Fin r) (hk₀ : k₀.val = 0)
variable (θ : Matrix (Fin n) (Fin n) (SField F r n) →ₐ[SField F r n] Matrix (Fin n) (Fin n) L)
variable {d : Fin n → L} (hθ : θ (genMatKF F r n k₀) = Matrix.diagonal d)

include k₀ hk₀ θ hθ in
/-- `ψ a` 落在 `S'`-世界的 `⟨X, Y_k⟩` 里。 -/
theorem psiSpr_mem_sprAlgebra (a : ↥(genericMatrixAlgebra F r n)) :
    psiSpr F r n k₀ hk₀ a ∈ sprAlgebra F r n k₀ hk₀ := by
  obtain ⟨y, hy⟩ := a
  revert hy
  refine Algebra.adjoin_induction (s := Set.range (genericMatrix F r n))
    (p := fun y hy => psiSpr F r n k₀ hk₀ ⟨y, hy⟩ ∈ sprAlgebra F r n k₀ hk₀) ?_ ?_ ?_ ?_
  · rintro x ⟨k, rfl⟩
    rw [psiSpr_sprGen, sprAlgebra]
    exact Algebra.subset_adjoin (Set.mem_range_self k)
  · intro c
    show psiSpr F r n k₀ hk₀ ⟨algebraMap F ↥(genericMatrixAlgebra F r n) c, _⟩ ∈ _
    rw [(psiSpr F r n k₀ hk₀).commutes c]
    exact Subalgebra.algebraMap_mem _ c
  · intro x y hx hy ihx ihy
    show psiSpr F r n k₀ hk₀ ⟨x + y, _⟩ ∈ sprAlgebra F r n k₀ hk₀
    rw [show (⟨x + y, _⟩ : ↥(genericMatrixAlgebra F r n)) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
    exact add_mem ihx ihy
  · intro x y hx hy ihx ihy
    show psiSpr F r n k₀ hk₀ ⟨x * y, _⟩ ∈ sprAlgebra F r n k₀ hk₀
    rw [show (⟨x * y, _⟩ : ↥(genericMatrixAlgebra F r n)) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
    exact mul_mem ihx ihy

#print axioms psiSpr_mem_sprAlgebra

include k₀ hk₀ θ hθ in
/-- `ψ` 打到 `⟨X, Y_k⟩` 上是满的。 -/
theorem psiSpr_sprAlgebra_surj (y : ↥(sprAlgebra F r n k₀ hk₀)) :
    ∃ a : ↥(genericMatrixAlgebra F r n), psiSpr F r n k₀ hk₀ a = (y : _) := by
  obtain ⟨y, hy⟩ := y
  revert hy
  refine Algebra.adjoin_induction (s := Set.range (sprGen F r n k₀ hk₀))
    (p := fun y hy => ∃ a : ↥(genericMatrixAlgebra F r n),
      psiSpr F r n k₀ hk₀ a = y) ?_ ?_ ?_ ?_
  · rintro x ⟨k, rfl⟩
    exact ⟨⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩, psiSpr_sprGen F r n k₀ hk₀ k⟩
  · intro c
    exact ⟨⟨algebraMap F _ c, _⟩, (psiSpr F r n k₀ hk₀).commutes c⟩
  · intro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb]
  · intro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [map_mul, ha, hb]

#print axioms psiSpr_sprAlgebra_surj


include k₀ hk₀ θ hθ in
/-- ★★★★★ **`R ≃ₐ[F] ⟨X, Y_k⟩`** —— 源文 `:406` 的识别：`R` 可等同于 `S'`-世界里由
`X, Y₂,…,Y_r` 生成的子代数。 -/
noncomputable def psiSprAlgEquiv (hθinj : Function.Injective θ) :
    ↥(genericMatrixAlgebra F r n) ≃ₐ[F] ↥(sprAlgebra F r n k₀ hk₀) :=
  AlgEquiv.ofBijective
    { toFun := fun a => ⟨psiSpr F r n k₀ hk₀ a,
        psiSpr_mem_sprAlgebra F r n k₀ hk₀ θ hθ a⟩
      map_one' := by
        refine Subtype.ext ?_
        exact map_one _
      map_mul' := by
        intro a b
        refine Subtype.ext ?_
        exact map_mul _ _ _
      map_zero' := by
        refine Subtype.ext ?_
        exact map_zero _
      map_add' := by
        intro a b
        refine Subtype.ext ?_
        exact map_add _ _ _
      commutes' := by
        intro c
        refine Subtype.ext ?_
        exact (psiSpr F r n k₀ hk₀).commutes c }
    ⟨fun a b h => psiSpr_injective F r n k₀ hk₀ θ hθ hθinj
        (by simpa using Subtype.ext_iff.mp h),
      fun y => by
        obtain ⟨a, ha⟩ := psiSpr_sprAlgebra_surj F r n k₀ hk₀ θ hθ y
        exact ⟨a, Subtype.ext ha⟩⟩

#print axioms psiSprAlgEquiv

end PsiEquiv

/-! ## §82 **`S_n`-乘积的不变性** —— `lem:14.25` 的关键件

源文 `raw/Saltman1999ch14.tex:466–470`（`lem:14.25` 证明，逐字）：

> "We proved in Lemma 14.20 that there are such `s` and `β'` which are `T` invariant.
> Write `s' = ∏_{σ ∈ S_n} σ(s)` and `s' = s s''`. Then `α' = β' s'' / s'`.
> **`s'` is `N` invariant** and therefore `β' s''` is `N` invariant."

本节机检"`s'` is `N` invariant"的 **`S_n` 部分**：

1. **`sprPerm_comp`**：`sprPerm σ ∘ sprPerm τ = sprPerm (σ * τ)`（层状）。
2. **`sprPermAlgEquiv_apply_mul`**：`σ(τ(s)) = (σ * τ)(s)`——由 `MvPolynomial.rename_rename`
   ＋ `sprPerm_comp`。
3. **`sprPerm_prod_fixed`**：**`∏_{σ} σ(s)` 被 `S_n` 固定**——由 `map_prod` 后
   **`Finset.prod_bij` 重索引** `σ ↦ τ * σ`（注意 `prod_bij` 的参数序是
   `i, hi, i_inj, i_surj, h`，**不是** `i, hi, h, i_inj, i_surj`——R145）。

**⚠ 本轮的重大战略发现（读源文 `:428`–`:450` 所得，已改 `(B)` 的剩余成本估计）**：
`(B)` 的 `lem:14.23`／`lem:14.24` **不是**新数学，而是 `(A)` 世界里 `prop:14.14`／`thm:14.15`
的**同构重放**（源文 `:429` 逐字："the results and methods are very similar to the earlier proof
of Theorem 14.16 … we will only outline some of the proofs"）。
**但本仓的 `thm1415_glue`／`thm1415_capstone` 把 `S F r n` 硬编码了**
（见 §32 的注释），故**不能直接实例化到 `S'`-世界**。
⟹ `(B)` 的剩余 = **把 `prop:14.14`／`thm:14.15`／`lem:14.13`／`lem:14.20` 的类似物在
`Spr`-世界重跑一遍**（约 10 节），而非"几条引理"。

**射程（勿夸大）**：本节只有 `S_n` 部分的乘积不变性；**`T`（环面）部分与 `T ◁ N` 的
正规性论证未做**，故 `s'` 的**完整** `N`-不变性**未证**；`lem:14.25` 本身未做。 -/

section SprPermProd

variable (F : Type) [Field F] (r n : ℕ)

theorem sprPerm_comp (σ τ : Equiv.Perm (Fin n)) :
    (sprPerm r n σ) ∘ (sprPerm r n τ) = sprPerm r n (σ * τ) := by
  ext x
  rcases x with i | ⟨i, j, k⟩ <;> simp [sprPerm]

theorem sprPermAlgEquiv_apply_mul (σ τ : Equiv.Perm (Fin n)) (s : Spr F r n) :
    sprPermAlgEquiv F r n σ (sprPermAlgEquiv F r n τ s)
      = sprPermAlgEquiv F r n (σ * τ) s := by
  rw [sprPermAlgEquiv, sprPermAlgEquiv, sprPermAlgEquiv,
    MvPolynomial.renameEquiv_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename, sprPerm_comp]

#print axioms sprPermAlgEquiv_apply_mul

/-- **`S_n`-乘积是 `S_n`-不变的**（源文 `lem:14.25` 证明里的 "`s'` is `N` invariant" 的 `S_n` 部分）。 -/
theorem sprPerm_prod_fixed (τ : Equiv.Perm (Fin n)) (s : Spr F r n) :
    sprPermAlgEquiv F r n τ
        (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ s)
      = ∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ s := by
  rw [map_prod]
  refine Finset.prod_bij (s := Finset.univ) (t := Finset.univ) (fun σ _ => τ * σ)
    (fun σ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro σ _ σ' _ h
    exact mul_left_cancel h
  · intro σ _
    exact ⟨τ⁻¹ * σ, Finset.mem_univ _, by simp⟩
  · intro σ _
    exact sprPermAlgEquiv_apply_mul F r n τ σ s

#print axioms sprPerm_prod_fixed

end SprPermProd

/-! ## §83 **`T ◁ N` 正规性**：`S_n` 与环面作用的交换律

源文 `lem:14.25` 的证明（`:466`）依赖一步未言明的正规性：`s` 若 `T`-不变，
则 `σ(s)`（`σ ∈ S_n`）**仍** `T`-不变——因为 `T ◁ N`。本节机检其代数形态：

**`sprPerm_sprDiagHom_comp`**：`σ ∘ φ_b = φ_{b'} ∘ σ`，其中 `b'_i = b (σ⁻¹ i)`。
**机制**：`MvPolynomial.algHom_ext` 归约到变量——
* `x_ii`：两边都把它送到 `x_{σi,σi}`（环面固定 `x_ii`，置换按 `i ↦ σ i`）；
* `y_ijk`：两边都送到 `(b_i / b_j) · y_{σi,σj,k}`
  （关键：`b'_i = b(σ⁻¹(σ i)) = b_i`，用 `Equiv.symm_apply_apply`；
  常数 `C c` 被 `rename` 固定，用 `MvPolynomial.rename_C`）。

**射程（勿夸大）**：只有**交换律**。**未做**：由它推出
"`T`-固定 ⟹ `σ(s)` 仍 `T`-固定"（两行推论，本轮末一步的 `calc` 因
`congrArg` 的具体化未过而暂缓）。 -/

section SprNormal

variable (F : Type) [Field F] (r n : ℕ)

/-- **`S_n` 与环面作用的交换律**：`σ(φ_b s) = φ_{b'}(σ s)`，其中 `b'_i = b (σ⁻¹ i)`。 -/
theorem sprPerm_sprDiagHom_comp (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ) :
    (sprPermAlgEquiv F r n σ).toAlgHom.comp (sprDiagHom F r n b)
      = (sprDiagHom F r n (fun i => b (σ⁻¹ i))).comp
          (sprPermAlgEquiv F r n σ).toAlgHom := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  rcases v with i | ⟨i, j, k⟩
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, sprDiagHom_X_inl,
      sprPermAlgEquiv_X_inl]
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, sprDiagHom_X_inr,
      sprPermAlgEquiv_X_inr, map_mul, map_one]
    simp only [MvPolynomial.renameEquiv_apply, sprPermAlgEquiv,
      MvPolynomial.rename_C, Equiv.symm_apply_apply]
    simp

#print axioms sprPerm_sprDiagHom_comp


end SprNormal

/-! ## §84 **`∏_{σ∈S_n} σ(s)` 是 `N`-不变的** —— `lem:14.25` 的核心件

源文 `lem:14.25` 证明（`:466`）的关键一步："**`s'` is `N` invariant** and therefore
`β' s''` is `N` invariant"。本节机检其**完整形态**（`S_n` 与 `T` 两部分都覆盖）：

1. **`sprDiagHom_fixed_sprPerm`**：`s` 若 `T`-固定，则 `σ(s)`（`σ ∈ S_n`）**仍** `T`-固定
   ——即 `T ◁ N` 的正规性。**机制**：§83 的交换律 `σ ∘ φ_c = φ_b ∘ σ`（取 `c j = b (σ j)`）
   ＋ `s` 的 `T`-固定性。
2. **`sprDiagHom_prod_sprPerm_fixed`**：**`∏_{σ∈S_n} σ(s)` 是 `N`-不变的**
   （`s` 为 `T`-固定时）。**机制**：`map_prod` ＋ 逐因子用 1。

配合 §82 的 `sprPerm_prod_fixed`（`S_n` 部分），`s' = ∏_{σ} σ(s)` 的 `N`-不变性是**完整**的。

**射程（勿夸大）**：本节的结论是 `lem:14.25` 的**必要中间件**，**不是** `lem:14.25` 本身——
后者还要 `lem:14.20` 的类似物（"存在 `T`-不变的 `s, β'` 使 `α' = β'/s`"）在 `S'`-世界的证明。
**另**：`lem:14.25` 还需"`M_n(K')` 有 `N`-不变基"这一句。 -/

section SprNormality

variable (F : Type) [Field F] (r n : ℕ)

/-- **`T`-固定 ⟹ `σ(s)` 仍 `T`-固定**（`T ◁ N`；`lem:14.25` 的必要一步）。 -/
theorem sprDiagHom_fixed_sprPerm {s : Spr F r n}
    (hs : ∀ b : Fin n → Fˣ, sprDiagHom F r n b s = s) (σ : Equiv.Perm (Fin n))
    (b' : Fin n → Fˣ) :
    sprDiagHom F r n b' (sprPermAlgEquiv F r n σ s) = sprPermAlgEquiv F r n σ s := by
  have h : sprPermAlgEquiv F r n σ (sprDiagHom F r n (fun j => b' (σ j)) s)
      = sprDiagHom F r n (fun i => (fun j => b' (σ j)) (σ⁻¹ i))
          (sprPermAlgEquiv F r n σ s) := by
    simpa using DFunLike.congr_fun
      (sprPerm_sprDiagHom_comp F r n σ (fun j => b' (σ j))) s
  have hb : (fun i => (fun j => b' (σ j)) (σ⁻¹ i)) = b' := by
    funext i
    exact congrArg b' (Equiv.apply_symm_apply σ i)
  rw [hb] at h
  rw [hs] at h
  exact h.symm

#print axioms sprDiagHom_fixed_sprPerm


/-- **`∏_{σ∈S_n} σ(s)` 是 `N`-不变的**（`s` 为 `T`-固定时）——源文 `lem:14.25` 的
"`s'` is `N` invariant" 的**完整**形态（`S_n` ＋ `T`）。 -/
theorem sprDiagHom_prod_sprPerm_fixed {s : Spr F r n}
    (hs : ∀ b : Fin n → Fˣ, sprDiagHom F r n b s = s) (b : Fin n → Fˣ) :
    sprDiagHom F r n b (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ s)
      = ∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ s := by
  rw [map_prod]
  refine Finset.prod_congr rfl (fun σ _ => ?_)
  have h : sprPermAlgEquiv F r n σ (sprDiagHom F r n (fun j => b (σ j)) s)
      = sprDiagHom F r n (fun i => (fun j => b (σ j)) (σ⁻¹ i))
          (sprPermAlgEquiv F r n σ s) := by
    simpa using DFunLike.congr_fun
      (sprPerm_sprDiagHom_comp F r n σ (fun j => b (σ j))) s
  have hb : (fun i => (fun j => b (σ j)) (σ⁻¹ i)) = b := by
    funext i
    exact congrArg b (Equiv.apply_symm_apply σ i)
  rw [hb] at h
  rw [← h, hs]

#print axioms sprDiagHom_prod_sprPerm_fixed

end SprNormality

/-! ## §85 **源文 `(17)` 的 `S'`-世界形态**：单项式都是 `φ_B` 的特征向量

源文 `lem:14.20` 证明（`:382`，逐字）：

> "if `m ∈ M_r'` and `f'(m) = Σ c(i) u_i` then `φ_B(e(m)) = (∏ b_i^{-c(i)}) e(m)`.
> … for all `m ∈ M_r'` and `B ∈ T_n` there is a `λ ∈ F^*` such that
> `φ_B(e(m)) = λ e(m)`. **(17)**"

本节机检其**多项式环层**的形态：

1. **`sprDiagHom_X_eigen`**：每个变量 `x_ii`／`y_ijk` 都是 `φ_B` 的**特征向量**
   （`x_ii ↦ x_ii`，`y_ijk ↦ (b_i/b_j) y_ijk`——正是 §67 的两条变量引理）。
2. **`sprDiagHom_monomial_eigen`**：**每个单项式** `∏ x_v^{f v}` 都是 `φ_B` 的特征向量
   （特征值 `∏ λ_v^{f v}`），由 `Finset` 归纳 ＋ 乘性。

**射程（勿夸大）**：这是 `(17)` 的**单项式层**。**未做**：
`(17)` 对**一般元素**（单项式的线性组合、即整个 `F[M_r']`）的形态——
那需要"不同单项式对应不同权"的**权分离**（源文 `lem:14.20` 的实质），
以及 `f'(m)` 与权 `∏ b_i^{-c(i)}` 的对应（需要 `M_r'`／`f'` 的结构，在 `SaltmanT.lean`）。 -/

section SprEigen

variable (F : Type) [Field F] (r n : ℕ)

/-- **`(17)` 的变量形态**：每个变量 `x_ii`／`y_ijk` 都是 `φ_B` 的特征向量。 -/
theorem sprDiagHom_X_eigen (b : Fin n → Fˣ) (v : SprIdx r n) :
    ∃ mu : F, sprDiagHom F r n b (MvPolynomial.X v)
      = MvPolynomial.C mu * MvPolynomial.X v := by
  rcases v with i | ⟨i, j, k⟩
  · exact ⟨1, by rw [sprDiagHom_X_inl, map_one, one_mul]⟩
  · exact ⟨(b i : F) * ((b j : F))⁻¹, sprDiagHom_X_inr F r n b k i j⟩

#print axioms sprDiagHom_X_eigen

/-- **`(17)` 的单项式形态**（源文 `lem:14.20` 的 `(17)`）：每个单项式都是 `φ_B` 的特征向量。 -/
theorem sprDiagHom_monomial_eigen (b : Fin n → Fˣ) (s : Finset (SprIdx r n))
    (f : SprIdx r n → ℕ) :
    ∃ mu : F, sprDiagHom F r n b (s.prod (fun v => MvPolynomial.X v ^ f v))
      = MvPolynomial.C mu * s.prod (fun v => MvPolynomial.X v ^ f v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_⟩
    simp
  | insert v s hv ih =>
    obtain ⟨lam1, h1⟩ := sprDiagHom_X_eigen F r n b v
    obtain ⟨lam2, h2⟩ := ih
    refine ⟨lam1 ^ f v * lam2, ?_⟩
    simp only [Finset.prod_insert hv, map_mul, map_pow, h1, h2]
    ring

#print axioms sprDiagHom_monomial_eigen

end SprEigen

/-! ## §86 **单项式的权（显式）** —— `(17)` 的一般层的准备

§85 只给了"单项式是特征向量"的**存在式**。本节把**权显式化**：

1. **`sprWt`**：环面权函数——`x_ii ↦ 1`、`y_ijk ↦ b_i/b_j`；
2. `sprWt_inl`／`sprWt_inr`：在两类变量上的值；
3. **`sprDiagHom_monomial_weight`**：
   `φ_B(∏_v x_v^{f v}) = C(∏_v λ_v^{f v}) · ∏_v x_v^{f v}`
   ——**权的可乘性**（单项式的权 ＝ 各因子权的幂积）。

**射程（勿夸大）**：本节的权是**形式上的可乘函数**。**未做**：
（i）"单项式被固定 ⟹ 权为 `1`"（本轮末一步的消去法因 `mul_right_cancel₀` 的实例卡住而未过）；
（ii）"权为 `1` ⟺ `f'(m) = 0`"（需 `SaltmanT.lean` 的 `M_r'`／`f'` 桥）；
（iii）由 (i)(ii) 得 `F[M_r] = F[M_r']^T` 的**基展开**论证（需单项式的**线性无关性**）。 -/

section SprWeight

variable (F : Type) [Field F] (r n : ℕ)

/-- 环面权：`x_ii` 的权为 `1`，`y_ijk` 的权为 `b_i / b_j`。 -/
noncomputable def sprWt (b : Fin n → Fˣ) : SprIdx r n → F
  | Sum.inl _ => 1
  | Sum.inr (i, j, _) => (b i : F) * ((b j : F))⁻¹

#print axioms sprWt

theorem sprWt_inl (b : Fin n → Fˣ) (i : Fin n) : sprWt F r n b (Sum.inl i) = 1 := rfl

theorem sprWt_inr (b : Fin n → Fˣ) (i j : Fin n) (k : {k : Fin r // k.val ≠ 0}) :
    sprWt F r n b (Sum.inr (i, j, k)) = (b i : F) * ((b j : F))⁻¹ := rfl

#print axioms sprWt_inl
#print axioms sprWt_inr

/-- **单项式的权（显式）**：`φ_B(∏ x_v^{f v}) = C(∏ λ_v^{f v}) · ∏ x_v^{f v}`。 -/
theorem sprDiagHom_monomial_weight (b : Fin n → Fˣ) (s : Finset (SprIdx r n))
    (f : SprIdx r n → ℕ) :
    sprDiagHom F r n b (s.prod (fun v => MvPolynomial.X v ^ f v))
      = MvPolynomial.C (s.prod (fun v => sprWt F r n b v ^ f v))
        * s.prod (fun v => MvPolynomial.X v ^ f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sprWt]
  | insert v s hv ih =>
    have hX : sprDiagHom F r n b (MvPolynomial.X v)
        = MvPolynomial.C (sprWt F r n b v) * MvPolynomial.X v := by
      rcases v with i | ⟨i, j, k⟩
      · rw [sprWt_inl, sprDiagHom_X_inl, map_one, one_mul]
      · rw [sprWt_inr, sprDiagHom_X_inr]
    simp only [Finset.prod_insert hv, map_mul, map_pow, hX, ih, Finset.prod_insert hv]
    ring

#print axioms sprDiagHom_monomial_weight



/-! ## §86b **`(17)` 的三件收口**：`Finsupp` 形态 ＋ 逆读 ＋ 「权全 1 ⟹ 固定」（第 646 轮）

§86 的射程登记了两个缺口：(i)「单项式被固定 ⟹ 权为 `1`」、以及单项式的**基展开**论证所需的
`Finsupp` 形态。本节把它们机检：

| 件 | 内容 |
|---|---|
| ★★★★★ `sprDiagHom_monomial_finsupp` | `(17)` 的 **`Finsupp` 形态**：`φ_B(monomial s a) = C(∏_v λ_v^{s v}) · monomial s a` |
| ★★★★★ `sprWt_prod_eq_one_of_monomial_fixed` | **逆读**（缺口 (i)）：单项式被固定 ⟹ 各因子权的幂积 `= 1` |
| ★★★★★ `sprDiagHom_eq_self_of_weight` | 「每个单项式权为 `1` ⟹ 整个多项式被固定」（基展开的 `⟸` 半） |

**机制**：`MvPolynomial.monomial_eq`（`monomial s a = C a * ∏ x_v^{s v}`）＋ §86 的权可乘性；
逆读用 `MvPolynomial` 是整环（`X_ne_zero` ＋ `prod_ne_zero_iff`）＋ `C` 的单射性
（`GenericInv` §86 原记「`mul_right_cancel₀` 实例卡住」——根因是 `MvPolynomial.X v` 的**系数环 `F`
未定**，须写 `(MvPolynomial.X (R := F) v)` 再 `C_inj (σ := SprIdx r n)`）。

**射程（勿夸大）**：**未做**——`⟹` 方向（「多项式的每个单项式权为 `1`」）需要系数比较
（可由 `as_sum` ＋ `Finset.sum_eq_single` 得到，`⟸` 已给）；「权为 `1` ⟺ `f'(m) = 0`」
（需 `SprIdx` → `Mprime` 的桥，本仓尚未建）；`F[M_r] = F[M_r']^T` 的**整体等式**；
`K'^N = Frac(SprFixed)`；`SaltmanZEqNFixed`；`hZ`；H2 仍不是定理。 -/

/-- `(17)` 的 **`Finsupp` 形态**：单项式是特征向量，特征值 ＝ 各因子权的幂积。 -/
theorem sprDiagHom_monomial_finsupp (b : Fin n → Fˣ) (s : SprIdx r n →₀ ℕ) (a : F) :
    sprDiagHom F r n b (MvPolynomial.monomial s a)
      = MvPolynomial.C (s.support.prod (fun v => sprWt F r n b v ^ s v))
        * MvPolynomial.monomial s a := by
  conv_lhs => rw [MvPolynomial.monomial_eq (a := a) (s := s)]
  rw [map_mul]
  have hC : sprDiagHom F r n b (MvPolynomial.C a) = MvPolynomial.C a := by
    simpa using (sprDiagHom F r n b).commutes a
  rw [hC]
  rw [show s.prod (fun n e => MvPolynomial.X n ^ e)
      = s.support.prod (fun v => MvPolynomial.X v ^ s v) from rfl]
  rw [sprDiagHom_monomial_weight]
  rw [MvPolynomial.monomial_eq (a := a) (s := s)]
  rw [show s.prod (fun n e => MvPolynomial.X (R := F) n ^ e)
      = s.support.prod (fun v => MvPolynomial.X (R := F) v ^ s v) from rfl]
  ring

#print axioms sprDiagHom_monomial_finsupp

/-- ★★★★★ **单项式被固定 ⟹ 权为 `1`**（`(17)` 的逆读；§86 缺件 (i)）。 -/
theorem sprWt_prod_eq_one_of_monomial_fixed (b : Fin n → Fˣ) (s : Finset (SprIdx r n))
    (f : SprIdx r n → ℕ)
    (h : sprDiagHom F r n b (s.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v))
          = s.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v)) :
    s.prod (fun v => sprWt F r n b v ^ f v) = 1 := by
  classical
  rw [sprDiagHom_monomial_weight] at h
  have hm : s.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun v _ => pow_ne_zero _ (MvPolynomial.X_ne_zero (R := F) (σ := SprIdx r n) v))
  have h1 : MvPolynomial.C (s.prod (fun v => sprWt F r n b v ^ f v))
      * s.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v)
      = 1 * s.prod (fun v => (MvPolynomial.X (R := F) v) ^ f v) := by
    rw [h, one_mul]
  exact (MvPolynomial.C_inj (σ := SprIdx r n) F _ _).mp (mul_right_cancel₀ hm h1)

#print axioms sprWt_prod_eq_one_of_monomial_fixed

/-- **权全为 `1` ⟹ 固定**（`(17)` 的「⟸」方向）：若 `f` 的每个单项式权为 `1`，则 `f` 被 `φ_B` 固定。 -/
theorem sprDiagHom_eq_self_of_weight (b : Fin n → Fˣ) (f : Spr F r n)
    (hw : ∀ m ∈ f.support, m.support.prod (fun v => sprWt F r n b v ^ m v) = 1) :
    sprDiagHom F r n b f = f := by
  classical
  rw [MvPolynomial.as_sum f, map_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [sprDiagHom_monomial_finsupp, hw m hm, map_one, one_mul]

#print axioms sprDiagHom_eq_self_of_weight

/-- ★★★★★ **(17) 的 `⟹` 方向**：`f` 被 `φ_B` 固定 ⟹ 其支撑上每个单项式的权为 `1`。 -/
theorem sprWt_prod_eq_one_of_mem_support (b : Fin n → Fˣ) (f : Spr F r n)
    (h : sprDiagHom F r n b f = f) {m : SprIdx r n →₀ ℕ} (hm : m ∈ f.support) :
    m.support.prod (fun v => sprWt F r n b v ^ m v) = 1 := by
  classical
  set W : (SprIdx r n →₀ ℕ) → F :=
    fun m' => m'.support.prod (fun v => sprWt F r n b v ^ m' v) with hW
  have hsplit : sprDiagHom F r n b f
      = ∑ m' ∈ f.support, MvPolynomial.C (W m') * MvPolynomial.monomial m' (f.coeff m') := by
    conv_lhs => rw [MvPolynomial.as_sum f]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [sprDiagHom_monomial_finsupp]
  have hcoeff : (sprDiagHom F r n b f).coeff m = W m * f.coeff m := by
    rw [hsplit, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single m]
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, ite_eq_left rfl]
    · intro m' _ hmne
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
        ite_eq_right hmne, mul_zero]
    · intro hnot
      exact absurd hm hnot
  rw [h] at hcoeff
  have hc : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h2 : W m * f.coeff m = 1 * f.coeff m := by rw [← hcoeff, one_mul]
  exact mul_right_cancel₀ hc h2

#print axioms sprWt_prod_eq_one_of_mem_support

/-- ★★★★★★ **(17) 的 `⟺` 形态**（`S'`-世界的 `torusScale_fixed_iff`）：
`f` 被 `φ_B` 固定 **⟺** 支撑上每个单项式的权为 `1`。 -/
theorem sprDiagHom_fixed_iff (b : Fin n → Fˣ) (f : Spr F r n) :
    sprDiagHom F r n b f = f
      ↔ ∀ m ∈ f.support, m.support.prod (fun v => sprWt F r n b v ^ m v) = 1 :=
  ⟨fun h m hm => sprWt_prod_eq_one_of_mem_support F r n b f h hm,
   fun hw => sprDiagHom_eq_self_of_weight F r n b f hw⟩

#print axioms sprDiagHom_fixed_iff

/-- **被整个环面固定 ⟺ 支撑上每个单项式对每个 `b` 权为 `1`**（`SprFixed` 的 `T` 半刻画）。 -/
theorem sprDiagHom_all_fixed_iff (f : Spr F r n) :
    (∀ b : Fin n → Fˣ, sprDiagHom F r n b f = f)
      ↔ ∀ (b : Fin n → Fˣ) (m : SprIdx r n →₀ ℕ), m ∈ f.support →
          m.support.prod (fun v => sprWt F r n b v ^ m v) = 1 :=
  ⟨fun h b m hm => sprWt_prod_eq_one_of_mem_support F r n b f (h b) hm,
   fun h b => sprDiagHom_eq_self_of_weight F r n b f (fun m hm => h b m hm)⟩

#print axioms sprDiagHom_all_fixed_iff



end SprWeight

/-! ## §87 **环面作用的群律** —— `T` 真的"作用"

§67 只逐条给了 `sprDiagHom b` 的变量公式。本节补上**群律**，使 `T`-不变性成为
"作用的不动点"而非一堆零散等式：

1. **`sprDiagHom_mul`**：`φ_b ∘ φ_{b'} = φ_{b · b'}`（逐变量验证；`y_ijk` 那支的关键是
   域的交换性：`b'_i b'_j⁻¹ · b_i b_j⁻¹ = (b_i b'_i)(b_j b'_j)⁻¹`）。
2. **`sprDiagHom_one`**：`φ_1 = id`。

**用途（下游）**：`T`-固定集是**作用的不动点**，故"`T`-不变"是良定义的代数性质；
配合 §83（`S_n` 与环面交换律）与 §84（乘积 `N`-不变），`N`-作用的结构已齐。
**射程**：只有 `T` 部分；`N`（含 `S_n`）的完整群律（`sprPermAlgEquiv` 与 `sprDiagHom` 的
半直积结构）**未做成一个作用**——目前只有 §83 的交换律。 -/

section SprTorusLaw

variable (F : Type) [Field F] (r n : ℕ)

/-- **环面作用的群律**：`φ_b ∘ φ_{b'} = φ_{b · b'}`。 -/
theorem sprDiagHom_mul (b b' : Fin n → Fˣ) :
    (sprDiagHom F r n b).comp (sprDiagHom F r n b')
      = sprDiagHom F r n (fun i => b i * b' i) := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  rcases v with i | ⟨i, j, k⟩
  · simp only [AlgHom.comp_apply, sprDiagHom_X_inl]
  · rw [AlgHom.comp_apply, sprDiagHom_X_inr, map_mul, sprDiagHom_X_inr, sprDiagHom_X_inr]
    have hc : (sprDiagHom F r n b) (MvPolynomial.C ((b' i : F) * ((b' j : F))⁻¹))
        = MvPolynomial.C ((b' i : F) * ((b' j : F))⁻¹) := by
      simp
    rw [hc, ← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    push_cast
    ring

#print axioms sprDiagHom_mul

/-- 环面作用的单位律：`φ_1 = id`。 -/
theorem sprDiagHom_one :
    sprDiagHom F r n (fun _ => 1) = AlgHom.id F (Spr F r n) := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  rcases v with i | ⟨i, j, k⟩
  · rw [sprDiagHom_X_inl]; rfl
  · rw [sprDiagHom_X_inr]
    simp

#print axioms sprDiagHom_one

end SprTorusLaw

/-! ## §88 **权的逆元律**

**`sprWt_inv`**：`λ_{b⁻¹}(v) = λ_b(v)⁻¹`。

**用途**：把"`φ_b` 在特征向量 `e(m)` 上乘 `λ`"升级为"`φ_{b⁻¹}` 乘 `λ⁻¹`"，
从而使 **`T`-不变性 ⟺ 权为 `1`** 成为纯代数命题（不再是"对所有 `b` 的等式族"）：

> 若 `φ_b x = λ x`（`x ≠ 0`），则 `x` 被 `φ_b` 固定 ⟺ `λ = 1`。
> 且 `φ_b x = λ x` ⟺ `x` 被 `φ_{b⁻¹} b` 固定——后者与 `b` 无关（§87 的群律）。

**射程**：只有权函数层面的一条等式。**未做**：上式两行的形式化（"⟺" 那两步），
以及最终需要的"权为 `1` ⟹ 指数向量为零"。 -/

section SprWtInv

variable (F : Type) [Field F] (r n : ℕ)

/-- **权的逆元律**：`λ_{b⁻¹}(v) = λ_b(v)⁻¹`。

**用途**：把"`φ_b` 在 `e(m)` 上乘 `λ`"升级为"`φ_{b⁻¹}` 乘 `λ⁻¹`"，
从而使 `T`-不变性等价于"权为 `1`"（`φ_b x = x ⟺ λ = 1`，当 `x` 是特征向量时）。 -/
theorem sprWt_inv (b : Fin n → Fˣ) (v : SprIdx r n) :
    sprWt F r n (fun i => (b i)⁻¹) v = (sprWt F r n b v)⁻¹ := by
  rcases v with i | ⟨i, j, k⟩
  · rw [sprWt_inl, sprWt_inl, inv_one]
  · rw [sprWt_inr, sprWt_inr, mul_inv, inv_inv]
    simp

#print axioms sprWt_inv

end SprWtInv

/-! ## §89 **权的乘积：拆成 `x`／`y` 两部分**

1. **`sprWt_prod_univ`**：`∏_v λ_v^{f v}` 中 `x`-部分的权恒为 `1`，故整个乘积等于
   `∏_{(i,j,k)} (b_i / b_j)^{f(i,j,k)}`（`Fintype.prod_sum_type` 拆 `SprIdx = Fin n ⊕ …`）。
2. **`sprWt_prod_one`**：`b = 1` 时乘积为 `1`。

**射程（勿夸大）**：**指数形式本身未完成**——即
`∏_v λ_v^{f v} = ∏_i b_i^{A_i} · ∏_i (b_i^{B_i})⁻¹`（`A_i`／`B_i` 为"出／入"计数）。
本轮的证明卡在**三重乘积的重排**：`Fintype.prod_prod_type` 把
`∏_{(i,j,k)}` 拆成 `∏_{(i,j)} ∏_k`（而非 `∏_i ∏_{(j,k)}`），再拆一次后目标形态与
`Finset.prod_pow_eq_pow_sum` 的输入不符。**下一轮的明确修法**：改用
`Finset.prod_sigma'`／先在 `Fin n × (Fin n × {k})` 上做 `Fintype.prod_prod_type`，
或直接对 `Fin n` 用 `Finset.prod_fiberwise`。 -/

section SprWeightSplit

variable (F : Type) [Field F] (r n : ℕ)

/-- **权的乘积拆成 `x`／`y` 两部分**（`x`-部分的权为 `1`，故只剩 `y` 部分）。 -/
theorem sprWt_prod_univ (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) :
    (Finset.univ.prod fun v : SprIdx r n => sprWt F r n b v ^ f v)
      = (Finset.univ.prod fun p : Fin n × Fin n × {k : Fin r // k.val ≠ 0} =>
          ((b p.1 : F) * ((b p.2.1 : F))⁻¹) ^ f (Sum.inr p)) := by
  rw [Fintype.prod_sum_type]
  have hx : (Finset.univ.prod fun i : Fin n => sprWt F r n b (Sum.inl i) ^ f (Sum.inl i)) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [sprWt_inl, one_pow]
  rw [hx, one_mul]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [sprWt_inr]

#print axioms sprWt_prod_univ

/-- 单位元处的权为 `1`，故乘积为 `1`。 -/
theorem sprWt_prod_one (f : SprIdx r n → ℕ) :
    (Finset.univ.prod fun v : SprIdx r n => sprWt F r n (fun _ => (1 : Fˣ)) v ^ f v) = 1 := by
  refine Finset.prod_eq_one (fun v _ => ?_)
  rcases v with i | ⟨i, j, k⟩
  · rw [sprWt_inl, one_pow]
  · rw [sprWt_inr]
    simp

#print axioms sprWt_prod_one


end SprWeightSplit

/-! ## §90 **权的乘积按第一个坐标分层**（修 §89 的卡点）

§89 记下的卡点：`Fintype.prod_prod_type` **只做一层右结合拆分**，故
`∏_{p : Fin n × Fin n × {k}}` 被拆成 `∏_{(i,j)} ∏_k` 而非 `∏_i ∏_{(j,k)}`。

**修法（本节机检）**：给 `prod_prod_type` **显式类型参数**
`(α₁ := Fin n) (α₂ := Fin n × {k})`，即可得到按第一个坐标的分层。

**`sprWt_prod_fiberwise`**：
`∏_{p} (b_{p.1} b_{p.2.1}⁻¹)^{f_p} = ∏_i ∏_{q : Fin n × {k}} (b_i b_{q.1}⁻¹)^{f(i,q.1,q.2)}`。

**射程（勿夸大）**：只到**分层**。下一层（每行 `i` 的计算
`= (b_i)^{A_i} · (∏_j (b_j)^{Σ_k f_ijk})⁻¹`）**未完成**——本轮在该步的
`mul_pow`／`inv_pow` 上遇到 **stuck instance**（`rw` 与 `simp only` 两法皆卡），
已按 L47③ 停止。**下一轮的明确修法**：先把 `b_i * b_j⁻¹` 改写成 `b_i / b_j`
（`← div_eq_mul_inv`），再用 `div_pow` ＋ `Finset.prod_div_distrib`，
把 `F` 的 `DivisionMonoid` 实例钉在 `F` 上（不在 `Fˣ` 的强制转换层）。 -/

section SprFiber

variable (F : Type) [Field F] (r n : ℕ)

/-- 把 `∏_{(i,j,k)}` 按**第一个坐标**分层。 -/
theorem sprWt_prod_fiberwise (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) :
    (Finset.univ.prod fun p : Fin n × Fin n × {k : Fin r // k.val ≠ 0} =>
        ((b p.1 : F) * ((b p.2.1 : F))⁻¹) ^ f (Sum.inr p))
      = ∏ i : Fin n, ∏ q : Fin n × {k : Fin r // k.val ≠ 0},
          ((b i : F) * ((b q.1 : F))⁻¹) ^ f (Sum.inr (i, q.1, q.2)) := by
  rw [Fintype.prod_prod_type (α₁ := Fin n) (α₂ := Fin n × {k : Fin r // k.val ≠ 0})]

#print axioms sprWt_prod_fiberwise

end SprFiber

/-! ## §91 **`n = 1` 时环面作用平凡**（一个必要的健全性检查）

1. **`sprWt_one_index`**：`n = 1` 时每个权都是 `1`（`b_0 · b_0⁻¹ = 1`，用
   `Subsingleton.elim` ＋ `Units.mul_inv`）。
2. **`sprDiagHom_eq_id_one`**：**`n = 1` 时 `φ_b = id`**。

**为何值得记**：这条说明 `T`-作用在 `n = 1` 时**完全退化**，故 `lem:14.20`／`lem:14.25` 的
`T`-不变性论证**只在 `n ≥ 2` 时有内容**——本战役的 `n = 9` 情形当然满足，
但**任何 `n = 1` 的"验证"都不会检验到权论证**（这是一个容易自欺的点，值得显式记下）。

**射程**：只到 `n = 1` 的平凡性。`n ≥ 2` 的权分离（`lem:14.20` 的实质）**仍未完成**——
本轮的意欲目标（每行的 `div_pow` 计算）在 `rw [mul_pow]` 上遇
**`CommMonoid ?m` stuck instance**（`rw`／`simp only`／显式命名参数三法皆卡），
已按 L47③ 停止；**下一轮修法**：把该计算改成**对 `q` 的 `Finset` 归纳**
（`Finset.induction_on` ＋ `Finset.prod_insert`，完全绕开 `prod_congr`／`prod_mul_distrib`
的 `CommMonoid` 元变量），即"逐因子乘进去"而非"整体分配律"。 -/

section SprOne

variable (F : Type) [Field F] (r : ℕ)

/-- `n = 1` 时权的每个值都是 `1`（`b_0 * b_0⁻¹ = 1`）。 -/
theorem sprWt_one_index (b : Fin 1 → Fˣ) (v : SprIdx r 1) : sprWt F r 1 b v = 1 := by
  rcases v with i | ⟨i, j, k⟩
  · rw [sprWt_inl]
  · rw [sprWt_inr]
    have hij : i = j := Subsingleton.elim i j
    subst hij
    rw [← Units.val_inv_eq_inv_val]
    exact Units.mul_inv (b i)

#print axioms sprWt_one_index

/-- **`n = 1` 时环面作用平凡**：`φ_b = id`。 -/
theorem sprDiagHom_eq_id_one (b : Fin 1 → Fˣ) :
    sprDiagHom F r 1 b = AlgHom.id F (Spr F r 1) := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  rcases v with i | ⟨i, j, k⟩
  · rw [sprDiagHom_X_inl]; rfl
  · rw [sprDiagHom_X_inr]
    have h : ((b i : F) * ((b j : F))⁻¹) = 1 := by
      simpa [sprWt_inr] using sprWt_one_index F r b (Sum.inr (i, j, k))
    rw [h, map_one, one_mul]
    rfl

#print axioms sprDiagHom_eq_id_one

end SprOne

/-! ## §92 **缺口 ⑤ 不再是独立输入** —— `KPFixedLeZ` 由 `(A)` ＋ `thm:14.5` 中心形态推出

源文 `thm:14.5` 的证明（`:176–186`）用 `lem:14.7` 得 `R·K = M_n(K)`，从而
`C ⊂ K`、`Z ⊂ K`；再由 `UD ⊗_Z K ≅ M_n(K)` 得 **`UD` 是 `Z` 上次数 `n` 的中心单代数**。
最后一步推出 `K^{PGL} ⊆ Z`（缺口 ⑤）：`PGL`-固定的 `f ∈ K` 与 `R` 交换 ⟹ `f ∈ Z(UD) = Z`。

本节把**这一步机检化**：

1. **`CentreUDLeZ D`**：`thm:14.5` 的**中心形态**（比缺口 ⑤ 更原始的具名输入）——
   `UD` 中与 `UD` 全交换的元素都是 `Z` 的纯量矩阵；
2. **`kPFixedLeZ_of_centreUD`**：**缺口 ⑤ 由 `(A)` 的反向包含 ＋ `CentreUDLeZ` 推出**。
   证明：`f ∈ K^{PGL}` ⟹ `scalar f` 是 `PGL`-固定（`psiK_scalar` ＋ `phiKAlgEquiv` 固定）⟹
   `scalar f ∈ UD`（`(A)` 的反向包含）⟹ `scalar f` 中心（纯量矩阵与一切交换）⟹
   （`CentreUDLeZ`）`scalar f = scalar (z)` ⟹ `f = z`（`Matrix.scalar_inj`）。

**意义**：`(A)` 的输入从**三条**降到**两条**——`KPFixedLeZ`（缺口 ⑤）**不再是独立输入**：
它由 `thm1416` 的反向包含（即 `(M_n(K))^{PGL} = UD`，`(A)`）＋ `thm:14.5` 的中心形态合出。
**射程（勿夸大）**：`CentreUDLeZ` **未证**（它仍是 PI 理论层，属 Rowen）；
本节的贡献是把"缺口 ⑤ 独立"改成"缺口 ⑤ 可导"，从而**缩小 T3 的目标**。 -/

section KPFixedReduce

variable (F : Type) [Field F] (r n : ℕ) [Nonempty (Fin n)]

/-- ★★★ **`thm:14.5` 的中心形态**（比缺口 ⑤ 更原始的具名输入）。 -/
def CentreUDLeZ (D : GenericDivisionData F r n) : Prop :=
  ∀ c ∈ UDCanon F r n D, (∀ u ∈ UDCanon F r n D, c * u = u * c) →
    ∃ z : ↥(ZCanon F r n D),
      c = Matrix.scalar (Fin n) (algebraMap ↥(ZCanon F r n D) (SField F r n) z)

#print axioms CentreUDLeZ

/-- ★★★★★ **缺口 ⑤ 由 `(A)` ＋ `thm:14.5` 的中心形态推出**。 -/
theorem kPFixedLeZ_of_centreUD (D : GenericDivisionData F r n)
    (hA : ∀ x ∈ fixedByPGL F r n, x ∈ UDCanon F r n D)
    (hC : CentreUDLeZ F r n D) : KPFixedLeZ F r n D := by
  intro x hx
  have hsc : Matrix.scalar (Fin n) x ∈ fixedByPGL F r n := by
    intro A
    rw [psiK_scalar]
    show Matrix.scalar (Fin n) ((phiKAlgEquiv F r n A) x) = Matrix.scalar (Fin n) x
    rw [show (phiKAlgEquiv F r n A) x = x from hx A]
  have hUD := hA _ hsc
  have hcent : ∀ u ∈ UDCanon F r n D,
      Matrix.scalar (Fin n) x * u = u * Matrix.scalar (Fin n) x :=
    fun u _ => Matrix.scalar_comm x (fun r' => mul_comm x r') u
  obtain ⟨z, hz⟩ := hC _ hUD hcent
  refine ⟨z, ?_⟩
  exact (Matrix.scalar_inj).mp hz.symm

#print axioms kPFixedLeZ_of_centreUD

end KPFixedReduce

/-! ## §93 **权改到单位群 `Fˣ` 里** —— 指数代数的正确设置

§90／§91 的卡点是 `rw [mul_pow]`／`inv_pow` 上的 **`CommMonoid ?m` stuck instance**。
根因是**乘积的类型未被钉住**。本节给出治本设置：

1. **`sprWtU`**：权的**单位群形态**——`x_ii ↦ 1`、`y_ijk ↦ b_i * b_j⁻¹`，取值在 `Fˣ`；
2. `sprWtU_inl`／`sprWtU_inr`：在两类变量上的值（都是 `rfl`）；
3. **`sprWt_eq_coe_sprWtU`**：`sprWt` 是 `sprWtU` 的**强制转换**。

**为何这是治本**：在群 `Fˣ` 里 `^`／`⁻¹` 的类型实例**唯一**（`Group`／`DivInvMonoid` 的实例
由 `Fˣ` 决定），而 `F` 上的 `^`／`⁻¹` 会与 `Field`／`DivisionRing`／`CommRing` 多条路径竞争。
**故后续所有权代数都应在 `Fˣ` 里做，最后经 3 强制到 `F`。**

**射程（勿夸大）**：**每行的计算仍未完成**——即使在 `Fˣ` 里，
`rw [mul_pow, inv_pow]` 在该 `hfac` 上下文仍报 stuck instance（**四处上下文同卡**），
已按 L47③ 停止。**下一轮的明确修法**：给 `hfac` 的等式**两侧都加类型标注**
（`((b i * (b q.1)⁻¹ : Fˣ)) ^ m = ((b i : Fˣ) ^ m * ((b q.1 : Fˣ) ^ m)⁻¹)`），
或用 `show` 把目标固定成 `Fˣ` 的等式再 `rw`——**本轮未试此两手**（先记下，不盲试）。 -/

section SprWtUnits

variable {F : Type} [Field F] {r n : ℕ}

/-- **单位群形态的权**：`x_ii ↦ 1`、`y_ijk ↦ b_i * b_j⁻¹`（取值在 `Fˣ`）。 -/
noncomputable def sprWtU (r n : ℕ) (b : Fin n → Fˣ) : SprIdx r n → Fˣ
  | Sum.inl _ => 1
  | Sum.inr (i, j, _) => b i * (b j)⁻¹

theorem sprWtU_inl (r n : ℕ) (b : Fin n → Fˣ) (i : Fin n) :
    sprWtU r n b (Sum.inl i) = 1 := rfl

theorem sprWtU_inr (r n : ℕ) (b : Fin n → Fˣ) (i j : Fin n)
    (k : {k : Fin r // k.val ≠ 0}) :
    sprWtU r n b (Sum.inr (i, j, k)) = b i * (b j)⁻¹ := rfl

#print axioms sprWtU
#print axioms sprWtU_inl
#print axioms sprWtU_inr

end SprWtUnits

section SprWtCoe

variable (F : Type) [Field F] (r n : ℕ)

/-- `sprWt` 是 `sprWtU` 的**强制转换**。 -/
theorem sprWt_eq_coe_sprWtU (b : Fin n → Fˣ) (v : SprIdx r n) :
    sprWt F r n b v = ((sprWtU r n b v : Fˣ) : F) := by
  rcases v with i | ⟨i, j, k⟩
  · rw [sprWt_inl, sprWtU_inl]
    rfl
  · rw [sprWt_inr, sprWtU_inr]
    simp

#print axioms sprWt_eq_coe_sprWtU


end SprWtCoe

/-! ## §94 **单位群版的乘积拆分**（§89 的 `Fˣ` 对应物）

**`sprWtU_prod_univ`**：
`∏_{v : SprIdx r n} (sprWtU b v)^{f v} = ∏_{p:(i,j,k)} (b_i b_j⁻¹)^{f(inr p)}`
——`x`-部分的权恒为 `1`（`sprWtU_inl` ＋ `one_pow`），故只剩 `y` 部分。

**为何在 `Fˣ` 里再做一遍**：§89 的版本在 `F` 上；§93 已把权搬到 `Fˣ`（实例唯一）。
后续的指数代数与权分离都要在 `Fˣ` 里进行，故需要本节的 `Fˣ` 版拆分。

**射程（勿夸大）**：**每行计算仍未完成**（第 5 轮尝试）。**卡点已精确定位**：
`Finset.prod_mul_distrib` 在**该目标形态**上报 `CommMonoid ?m` stuck instance，
而**同一重写在独立 `example` 里成功**（`∏ i, f i * g i = (∏ i, f i) * ∏ i, g i`，`Fˣ` 与 `F` 皆可）。
**差异是目标形态，不是类型**——这是 R49 族里最难的一类（记法/elaboration 层）。
**下一轮应做**：把该目标先 `conv` 到最简形态，或**改用 `Finset.prod_mul_distrib` 的
`Finset.prod_comm`-free 替代**——即在**乘法顺序**上重构目标（把 `∏ q, X_q * Y_q` 先写成
`∏ q, (fun q => X_q) q * (fun q => Y_q) q`），使 rw 的模式匹配一次性命中。 -/

section SprWtUProd

variable {F : Type} [Field F] {r n : ℕ}

/-- 单位群形态的乘积拆分（§89 的 `Fˣ` 对应物）。 -/
theorem sprWtU_prod_univ (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) :
    (Finset.univ.prod fun v : SprIdx r n => sprWtU r n b v ^ f v)
      = (Finset.univ.prod fun p : Fin n × Fin n × {k : Fin r // k.val ≠ 0} =>
          (b p.1 * (b p.2.1)⁻¹) ^ f (Sum.inr p)) := by
  classical
  rw [Fintype.prod_sum_type]
  have hx : (Finset.univ.prod fun i : Fin n => sprWtU r n b (Sum.inl i) ^ f (Sum.inl i)) = 1 := by
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [sprWtU_inl, one_pow]
  rw [hx, one_mul]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [sprWtU_inr]

#print axioms sprWtU_prod_univ

end SprWtUProd

/-! ## §95 **每行的权计算** —— 卡了 7 轮的引理终于机检

**`sprWtU_row`**：`∏_{q:(j,k)} (b_i b_j⁻¹)^{f(i,j,k)} = b_i^{A_i} · (∏_j b_j^{Σ_k f(i,j,k)})⁻¹`。

**为何卡了 7 轮（第 249–256 轮）与最终破法**：
源文风格的证明是「对 `q` 的乘积用分配律」——但在 Lean 里 `Finset.prod_mul_distrib`／
`mul_left_comm`／`mul_pow` 等在**大目标**里反复报 `CommMonoid ?m` **stuck instance**，
而**同一引理在独立 `example` 里全部成功**（第 255 轮四例实测）。
⟹ **差异是目标形态（elaboration 层），不是类型**。

**破法 = 换证明形态 ＋ 分而治之**（三个小件 ＋ 一个装配）：

1. **`sprWtU_row_split`**：把 `∏_{q : Fin n × {k}}` 改写成 `∏_j ∏_k`
   （`Fintype.prod_prod_type`，**显式类型参数**——§90 已验证的修法）；
2. **`sprWtU_row_inner`**：内层 `∏_k (b_i b_j⁻¹)^{f} = (b_i b_j⁻¹)^{Σ_k f}`
   （`Finset.prod_pow_eq_pow_sum`）；
3. **`sprWtU_prod_ratio`**：单积层 `∏_j (b_i b_j⁻¹)^{c_j} = b_i^{Σ c_j} · (∏_j b_j^{c_j})⁻¹`
   ——**对 `Finset` 归纳**（`prod_insert` 逐因子），关键末步是
   **`simp only [mul_left_comm, mul_assoc]`**（`ac_rfl` 与 `exact mul_left_comm` 都因把 `⁻¹`
   当非二元运算而失败）；
4. **`sprWtU_row`**：三者装配 ＋ `Fintype.sum_prod_type` 对齐求和下标。

**工艺总结（本战役最贵的一课，8 轮代价）**：
**当 `CommMonoid ?m` stuck instance 反复出现时，不是加类型参数，而是把证明拆成
"能用 `prod_insert` 归纳的小件"**——小件里的目标形态简单、实例可定，大目标自然拼得起来。
配合"先在独立 `example` 里证伪最简形态"（第 255 轮），这类卡点可在 1–2 轮内定位。 -/

section SprWtURowSplit

variable {F : Type} [Field F] {r n : ℕ}

/-- 行乘积写成 `∏_j ∏_k` 的双重积形态。 -/
theorem sprWtU_row_split (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) (i : Fin n) :
    (Finset.univ.prod (fun q : Fin n × {k : Fin r // k.val ≠ 0} =>
        (b i * (b q.1)⁻¹) ^ f (Sum.inr (i, q.1, q.2))))
      = (∏ j : Fin n, ∏ k : {k : Fin r // k.val ≠ 0},
          (b i * (b j)⁻¹) ^ f (Sum.inr (i, j, k))) := by
  classical
  rw [Fintype.prod_prod_type (α₁ := Fin n) (α₂ := {k : Fin r // k.val ≠ 0})]

#print axioms sprWtU_row_split


/-- 内层：`∏_k (b_i b_j⁻¹)^{f_k} = (b_i b_j⁻¹)^{Σ_k f_k}`。 -/
theorem sprWtU_row_inner (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) (i j : Fin n) :
    (∏ k : {k : Fin r // k.val ≠ 0}, (b i * (b j)⁻¹) ^ f (Sum.inr (i, j, k)))
      = (b i * (b j)⁻¹) ^ (Finset.univ.sum (fun k : {k : Fin r // k.val ≠ 0} =>
          f (Sum.inr (i, j, k)))) :=
  Finset.prod_pow_eq_pow_sum _ _ _

#print axioms sprWtU_row_inner


/-- 单积层的核心恒等式：`∏_j (b_i b_j⁻¹)^{c_j} = (b_i)^{Σ c_j} · (∏_j b_j^{c_j})⁻¹`。 -/
theorem sprWtU_prod_ratio (b : Fin n → Fˣ) (c : Fin n → ℕ) (i : Fin n) :
    (∏ j : Fin n, (b i * (b j)⁻¹) ^ c j)
      = (b i) ^ (Finset.univ.sum c)
        * (∏ j : Fin n, (b j) ^ c j)⁻¹ := by
  classical
  have key : ∀ s : Finset (Fin n),
      (∏ j ∈ s, (b i * (b j)⁻¹) ^ c j)
        = (b i) ^ (∑ j ∈ s, c j) * (∏ j ∈ s, (b j) ^ c j)⁻¹ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j₀ s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj, ih,
        mul_pow, inv_pow, mul_inv, pow_add]
      simp only [mul_left_comm, mul_assoc]
  exact key Finset.univ

#print axioms sprWtU_prod_ratio


/-- ★★★★★ **每行的权计算**：`∏_{q:(j,k)} (b_i b_j⁻¹)^{f} = b_i^{A_i} · (∏_j b_j^{Σ_k f})⁻¹`。 -/
theorem sprWtU_row (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) (i : Fin n) :
    (Finset.univ.prod (fun q : Fin n × {k : Fin r // k.val ≠ 0} =>
        (b i * (b q.1)⁻¹) ^ f (Sum.inr (i, q.1, q.2))))
      = (b i) ^ (Finset.univ.sum (fun q : Fin n × {k : Fin r // k.val ≠ 0} =>
            f (Sum.inr (i, q.1, q.2))))
        * (∏ j : Fin n, ((b j) ^ (Finset.univ.sum (fun k : {k : Fin r // k.val ≠ 0} =>
            f (Sum.inr (i, j, k))))))⁻¹ := by
  classical
  rw [sprWtU_row_split]
  rw [show (∏ j : Fin n, ∏ k : {k : Fin r // k.val ≠ 0},
        (b i * (b j)⁻¹) ^ f (Sum.inr (i, j, k)))
      = (∏ j : Fin n, (b i * (b j)⁻¹) ^ (Finset.univ.sum
          (fun k : {k : Fin r // k.val ≠ 0} => f (Sum.inr (i, j, k))))) from
    Finset.prod_congr rfl (fun j _ => sprWtU_row_inner b f i j)]
  rw [sprWtU_prod_ratio]
  congr 2
  rw [Fintype.sum_prod_type]

#print axioms sprWtU_row

end SprWtURowSplit

/-! ## §96 **权的指数形式** —— 权分离的最后一台机器

**`sprWtU_prod_exp`**：
`∏_{v} λ_v^{f v} = (∏_i b_i^{A_i}) · (∏_j b_j^{B_j})⁻¹`，其中
`A_i = Σ_{(j,k)} f(i,j,k)`（"**出**"计数）、`B_j = Σ_i Σ_k f(i,j,k)`（"**入**"计数）。

这就是源文 `lem:14.20` 的 `(17)`（`φ_B(e(m)) = (∏ b_i^{-c(i)}) e(m)`）的**指数形态**：
`λ` 只通过 `A_i - B_j` 依赖于 `f`。**权分离**（`λ = 1` ⟺ 指数全零）由此成为纯指数陈述。

**装配用的四个件**：
1. **`sprWtU_prod_univ`**（§94）：`x`-部分权为 `1`；
2. **`sprWtU_prod_fiberwise`**：按第一坐标分层（`prod_prod_type` 显式类型参数）；
3. **`sprWtU_row`**（§95）：每行的权；
4. **`prod_mul_inv_prod`**：`∏ (X_i Y_i⁻¹) = (∏ X_i)(∏ Y_i)⁻¹`；
5. **`prod_swap_pow`**：`∏_i ∏_j (b_j)^{c_ij} = ∏_j (b_j)^{Σ_i c_ij}`（`prod_comm` ＋ `prod_pow_eq_pow_sum`）。

**口径选择（本轮的一个实用决定）**：`B_j` 用**级联求和** `Σ_i Σ_k` 而非扁平求和
`Σ_{p : Fin n×{k}}`——因为后者要多一次 `Fintype.sum_prod_type` 重索引，而该步在
`rw` 形态下报 stuck instance。**级联形态与 `prod_swap_pow` 的输出天然一致**，故零成本。

**射程（勿夸大）**：本节的等式是**权函数层**。**未做**：权分离本身
（"`∏_v λ_v^{f v} = 1` 对所有 `b` ⟹ `A_i = B_i` 对所有 `i`"）——
那需要 `F` 无限 ＋ 选取合适的 `b`，**是下一步**。 -/

section SprWtUExp

variable {F : Type} [Field F] {r n : ℕ}

/-- `Fˣ` 版的按第一坐标分层（§90 的单位群对应物）。 -/
theorem sprWtU_prod_fiberwise (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) :
    (Finset.univ.prod fun p : Fin n × Fin n × {k : Fin r // k.val ≠ 0} =>
        (b p.1 * (b p.2.1)⁻¹) ^ f (Sum.inr p))
      = (∏ i : Fin n, ∏ q : Fin n × {k : Fin r // k.val ≠ 0},
          (b i * (b q.1)⁻¹) ^ f (Sum.inr (i, q.1, q.2))) := by
  classical
  rw [Fintype.prod_prod_type (α₁ := Fin n) (α₂ := Fin n × {k : Fin r // k.val ≠ 0})]

#print axioms sprWtU_prod_fiberwise


/-- `∏ (X_i · Y_i⁻¹) = (∏ X_i) · (∏ Y_i)⁻¹`。 -/
theorem prod_mul_inv_prod (X Y : Fin n → Fˣ) :
    (∏ i : Fin n, X i * (Y i)⁻¹) = (∏ i : Fin n, X i) * (∏ i : Fin n, Y i)⁻¹ := by
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

#print axioms prod_mul_inv_prod

/-- 双重积换序 ＋ 收幂：`∏_i ∏_j (b_j)^{c_ij} = ∏_j (b_j)^{Σ_i c_ij}`。 -/
theorem prod_swap_pow (b : Fin n → Fˣ) (c : Fin n → Fin n → ℕ) :
    (∏ i : Fin n, ∏ j : Fin n, (b j) ^ c i j)
      = (∏ j : Fin n, (b j) ^ (Finset.univ.sum (fun i : Fin n => c i j))) := by
  classical
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl (fun j _ => Finset.prod_pow_eq_pow_sum _ _ _)

#print axioms prod_swap_pow


/-- ★★★★★ **权的指数形式**（级联求和版）：`∏_v λ_v^{f v} = (∏_i b_i^{A_i}) · (∏_j b_j^{B_j})⁻¹`，
`A_i = Σ_{(j,k)} f`、`B_j = Σ_i Σ_k f`。 -/
theorem sprWtU_prod_exp (b : Fin n → Fˣ) (f : SprIdx r n → ℕ) :
    (Finset.univ.prod fun v : SprIdx r n => sprWtU r n b v ^ f v)
      = (∏ i : Fin n, (b i) ^ (Finset.univ.sum
            (fun q : Fin n × {k : Fin r // k.val ≠ 0} => f (Sum.inr (i, q.1, q.2)))))
        * (∏ j : Fin n, (b j) ^ (Finset.univ.sum (fun i : Fin n => Finset.univ.sum
            (fun k : {k : Fin r // k.val ≠ 0} => f (Sum.inr (i, j, k))))))⁻¹ := by
  classical
  have hrow : (∏ i : Fin n, ∏ q : Fin n × {k : Fin r // k.val ≠ 0},
        (b i * (b q.1)⁻¹) ^ f (Sum.inr (i, q.1, q.2)))
      = ∏ i : Fin n, (b i) ^ (Finset.univ.sum
            (fun q : Fin n × {k : Fin r // k.val ≠ 0} => f (Sum.inr (i, q.1, q.2))))
          * (∏ j : Fin n, (b j) ^ (Finset.univ.sum
              (fun k : {k : Fin r // k.val ≠ 0} => f (Sum.inr (i, j, k)))))⁻¹ :=
    Finset.prod_congr rfl (fun i _ => sprWtU_row b f i)
  rw [sprWtU_prod_univ, sprWtU_prod_fiberwise, hrow, prod_mul_inv_prod, prod_swap_pow]

#print axioms sprWtU_prod_exp

end SprWtUExp

/-! ## §97 **权分离的归约步** —— 从乘积等式到逐坐标的幂等式

权分离的目标是：若 `∏_{v} λ_v^{f v} = 1` 对所有 `b` 成立，则"出／入"计数相抵。
§96 已把它化为 `∏_i b_i^{A_i} = ∏_i b_i^{B_i}`（对所有 `b`）。本节把它再**降一维**：

1. **`prod_pow_update_one`**：取 `b` 为"`i₀` 处 `t`、其余 `1`"，则
   `∏_i b_i^{A_i} = t^{A_{i₀}}`（`Finset.prod_eq_single` ＋ `Function.update_self`／`update_of_ne`）；
2. **`coord_of_prod_eq`**：由"所有 `b` 的乘积等式"得
   **`∀ i₀ t, t^{A_{i₀}} = t^{B_{i₀}}`**（把 1 代入即可）。

**射程（勿夸大）**：**最后一步未做**——由"`t^m = t^k` 对所有 `t : Fˣ`"得 `m = k`。
该步需 `F` 无限 ＋ 多项式根数论证：`X^d − 1`（`d > 0`）只有有限个根，
故不能在无限多个 `t` 上为 `1`。
**本轮试过但未成**（按 L47③ 停止）：`Polynomial.eq_zero_of_infinite_isRoot`
＋ `Set.Infinite.image` ＋ `Set.Infinite.mono` 的组装中出现三处技术障碍
（`Set.Infinite.mono` 的参数序、`simp only` 后目标形态、`Set.infinite_univ.image` 的
`Injective` 实例）。**下一轮的明确修法**：改用**单项式线性无关**（`Polynomial.monomial_injective`）
或 `Polynomial.natDegree_eq_of_degree_eq_some`，避免根集无穷性的集合论包装。 -/

section SprWtSep

variable {F : Type} [Field F] {r n : ℕ}

/-- **坐标归约**：取 `b` 为"`i₀` 处为 `t`、其余为 `1`"，则 `∏_i b_i^{A_i} = t^{A_{i₀}}`。 -/
theorem prod_pow_update_one (A : Fin n → ℕ) (i₀ : Fin n) (t : Fˣ) :
    (∏ i : Fin n, ((Function.update (fun _ : Fin n => (1 : Fˣ)) i₀ t) i) ^ A i)
      = t ^ A i₀ := by
  classical
  rw [Finset.prod_eq_single i₀]
  · rw [Function.update_self]
  · intro i _ hi
    rw [Function.update_of_ne hi, one_pow]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

#print axioms prod_pow_update_one



/-- ★★★★ **权分离的归约步**：若 `∏_i b_i^{A_i} = ∏_i b_i^{B_i}` 对**所有** `b : Fin n → Fˣ` 成立，
则对每个坐标 `i₀` 与每个 `t` 有 `t^{A_{i₀}} = t^{B_{i₀}}`。 -/
theorem coord_of_prod_eq (A B : Fin n → ℕ)
    (h : ∀ b : Fin n → Fˣ, (∏ i : Fin n, (b i) ^ A i) = ∏ i : Fin n, (b i) ^ B i) :
    ∀ (i₀ : Fin n) (t : Fˣ), t ^ A i₀ = t ^ B i₀ := by
  intro i₀ t
  have := h (Function.update (fun _ : Fin n => (1 : Fˣ)) i₀ t)
  rwa [prod_pow_update_one A i₀ t, prod_pow_update_one B i₀ t] at this

#print axioms coord_of_prod_eq

end SprWtSep

/-! ## §98 **权分离完成** —— 幂等式 ⟹ 指数相等

**`pow_eq_of_forall_unit`**：若 `t^m = t^k` 对所有 `t : Fˣ` 成立（`F` 无限），则 **`m = k`**。
配合 §97 的 `coord_of_prod_eq`，**权分离的整条链机检完毕**：

> `∏_v λ_v^{f v} = 1`（对所有 `b`）⟹ `∏_i b_i^{A_i} = ∏_i b_i^{B_i}`（§96 指数形式）
> ⟹ `t^{A_i} = t^{B_i}`（§97 坐标归约）⟹ **`A_i = B_i`**（本节）。

**证明结构**（两件）：
1. **`exists_pow_ne_one`**：无限域中总存在非零 `x` 使 `x^d ≠ 1`（`d ≠ 0`）。
   机制：`X^d − 1 ≠ 0`（在 `0` 处求值即得），故**根集有限**（`Polynomial.finite_setOfPred_isRoot`）；
   而根集含 `F \ {0}`，故 `F = 根集 ∪ {0}` 有限——与 `Infinite F` 矛盾。
   **关键绕法**：不走 `Set.Infinite.image`／`mono`（上一轮的卡点），
   而走 **`Set.Finite.union` ＋ `Set.Finite.subset` ＋ `Set.infinite_univ`**——
   **只操作有限集**，避免无穷集的集合论包装。
2. **`pow_eq_of_forall_unit`**：先由 1 得 `m = 0 ↔ k = 0`；两支都正时
   `Polynomial.funext`（`X^m` 与 `X^k` 在 `F` 上处处相等，含 `0`）＋ `natDegree` 比较。

**射程（勿夸大）**：本节与 §96／§97 合起来给的是**权函数层的分离**。
`lem:14.20`／`lem:14.25` 的**整体**仍未完成——它们的 `S'`-世界重放
（`prop:14.14`／`thm:14.15` 的类似物，约 10 节）**未做**。 -/

section SprWtSep3

variable {F : Type} [Field F] [Infinite F]

/-- **无限域中总存在非零 `x` 使 `x^d ≠ 1`**（`d ≠ 0`）。 -/
theorem exists_pow_ne_one {d : ℕ} (hd : d ≠ 0) : ∃ x : F, x ≠ 0 ∧ x ^ d ≠ 1 := by
  by_contra h
  push_neg at h
  have hpoly : (Polynomial.X ^ d - 1 : Polynomial F) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval (0 : F)) h0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_zero] at h1
    rw [zero_pow hd, zero_sub] at h1
    exact neg_ne_zero.mpr one_ne_zero h1
  have hfin : {x : F | (Polynomial.X ^ d - 1 : Polynomial F).IsRoot x}.Finite :=
    Polynomial.finite_setOfPred_isRoot hpoly
  -- 根集含 `F \ {0}`，故 `F = 根集 ∪ {0}` 有限，与 `Infinite F` 矛盾
  have hsub : ∀ x : F, x ≠ 0 → (Polynomial.X ^ d - 1 : Polynomial F).IsRoot x := by
    intro x hx
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    rw [h x hx, sub_self]
  have huniv : (Set.univ : Set F)
      ⊆ {x : F | (Polynomial.X ^ d - 1 : Polynomial F).IsRoot x} ∪ {0} := by
    intro x _
    by_cases hx : x = 0
    · exact Or.inr (by simp [hx])
    · exact Or.inl (hsub x hx)
  have hfinall : (Set.univ : Set F).Finite :=
    (hfin.union (Set.finite_singleton 0)).subset huniv
  exact Set.infinite_univ hfinall

#print axioms exists_pow_ne_one


/-- ★★★★★ **权分离的最后一步**：若 `t^m = t^k` 对所有 `t : Fˣ` 成立（`F` 无限），则 `m = k`。

**机制**：先由 `exists_pow_ne_one` 得 `m = 0 ↔ k = 0`（否则取 `x` 使 `x^d ≠ 1` 得矛盾）；
两支都正时 `X^m` 与 `X^k` 在 `F` 上处处相等（含 `0`），`Polynomial.funext` ⟹ 相等 ⟹
`natDegree` 比较得 `m = k`。 -/
theorem pow_eq_of_forall_unit {m k : ℕ}
    (h : ∀ t : Fˣ, (t : F) ^ m = (t : F) ^ k) : m = k := by
  have hne : ∀ x : F, x ≠ 0 → x ^ m = x ^ k := by
    intro x hx
    have := h (Units.mk0 x hx)
    simpa using this
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact hk.symm
    · obtain ⟨x, hx0, hxk⟩ := exists_pow_ne_one (F := F) hk.ne'
      refine absurd ?_ hxk
      exact (hne x hx0).symm.trans (pow_zero _)
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · obtain ⟨x, hx0, hxm⟩ := exists_pow_ne_one (F := F) hm.ne'
      refine absurd ?_ hxm
      rw [hne x hx0, hk, pow_zero]
    · have hpoly : (Polynomial.X ^ m : Polynomial F) = Polynomial.X ^ k := by
        refine Polynomial.funext (fun x => ?_)
        rcases eq_or_ne x 0 with rfl | hx
        · simp [hm.ne', hk.ne']
        · simpa using hne x hx
      have hdeg := congrArg Polynomial.natDegree hpoly
      simpa using hdeg

#print axioms pow_eq_of_forall_unit

end SprWtSep3

/-! ## §99 **`lem:14.23` 的矩阵层基础件** —— `S'` 世界的 `D_b` 与 `ψ_b`

`lem:14.23`（源文 `:432`）要证：`α ∈ M_n(S')` 若 `N`-不变，则 `ψ_{A(σ)}(α) = α`
（`A(σ) = P_σ D`，`D` 为对角）。其 `ψ` 是**矩阵层**的共轭
`ψ_A(α) = A · (M_n(φ_A)(α)) · A⁻¹`。本节建其对角部分：

1. **`sprDiagMat b`**：`D_b = diagonal (b_i)`（取值在 `S'`）；
2. `sprDiagMat_apply`：逐项形态；
3. **`sprDiagMat_mul_inv`**：`D_b · D_{b⁻¹} = 1`（`diagonal_mul_diagonal` ＋ 在 `F` 层用
   `Units.mul_inv` 收口）；
4. **`sprPsiD b α`**：`ψ_b(α) = D_b · (α 逐项经 φ_b) · D_b⁻¹`
   （用 `sprDiagMat_mul_inv` 给的显式逆，**不用 `nonsing_inv`**）；
5. `sprPsiD_apply`：展开式（`rfl`）。

**射程（勿夸大）**：本节只有**对角部分**的矩阵层动作。
**未做**：`ψ_b` 的**单位律**（`ψ_1 = id`，本轮末步因 `Matrix.map (AlgHom.id)` 与
`Matrix.one` 的 `MvPolynomial` 形态问题未过，按 L47③ 停止）、**复合律**、
置换部分 `ψ_{P_σ}`、以及 `lem:14.23` 本体的**特化论证**（`F` 无限 ⟹ 常值对角已足够）。 -/

section SprPsiD

variable {F : Type} [Field F] {r n : ℕ}

/-- 对角矩阵 `D_b = diagonal (b_i)`（取值在 `S'` 里）。 -/
noncomputable def sprDiagMat (b : Fin n → Fˣ) : Matrix (Fin n) (Fin n) (Spr F r n) :=
  Matrix.diagonal (fun i => algebraMap F (Spr F r n) (b i : F))

theorem sprDiagMat_apply (b : Fin n → Fˣ) (i j : Fin n) :
    sprDiagMat (r := r) b i j
      = if i = j then algebraMap F (Spr F r n) (b i : F) else 0 := by
  rw [sprDiagMat, Matrix.diagonal, Matrix.of_apply]

#print axioms sprDiagMat
#print axioms sprDiagMat_apply

/-- `D_b · D_{b⁻¹} = 1`。 -/
theorem sprDiagMat_mul_inv (b : Fin n → Fˣ) :
    sprDiagMat (r := r) b * sprDiagMat (r := r) (fun i => (b i)⁻¹) = 1 := by
  have h : (fun i => algebraMap F (Spr F r n) ((b i : Fˣ) : F)
        * algebraMap F (Spr F r n) ((((b i)⁻¹ : Fˣ)) : F)) = fun _ => 1 := by
    funext i
    rw [← map_mul]
    simp
  rw [sprDiagMat, sprDiagMat, Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_one]

#print axioms sprDiagMat_mul_inv


/-- **`S'`-世界的共轭作用**：`ψ_b(α) = D_{b⁻¹} · (α 逐项经 φ_b) · D_b`，
即 `ψ_A` 取 `A = diag(b⁻¹)`（源文 `lem:14.23` 的 `ψ_{A(σ)}` 的对角部分）。

⚠ **约定（第 262／263 轮修正，R156）**：本定义的前身写成 `D_b · map(φ_b) · D_b⁻¹`，
而 `φ_b = sprDiagHom b` 实为 **`φ_{diag(b⁻¹)}`**（源文 `φ_A(y_ijk) = (d_j/d_i) y_ijk`，
而 `sprDiagHom` 的系数是 `b_i/b_j`）⟹ **`D_b` 与 `φ_{diag(b⁻¹)}` 不配对，那不是共轭**。
正确配对是 `A = diag(b⁻¹)`，其逆为 `D_{b⁻¹}⁻¹ = D_b`。**凡写 `A·M(φ_A)·A⁻¹`，必须核 `A` 与 `φ_A`
是同一个矩阵**（§102 的 `sprPsiDiagR_point` 机检本式与通用形态一致）。 -/
noncomputable def sprPsiD (b : Fin n → Fˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) : Matrix (Fin n) (Fin n) (Spr F r n) :=
  sprDiagMat (fun i => (b i)⁻¹) * α.map (sprDiagHom F r n b) * sprDiagMat b

theorem sprPsiD_apply (b : Fin n → Fˣ) (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiD b α = sprDiagMat (fun i => (b i)⁻¹) * α.map (sprDiagHom F r n b)
      * sprDiagMat b := rfl

#print axioms sprPsiD
#print axioms sprPsiD_apply

end SprPsiD

/-! ## §100 **`lem:14.23` 的参数环 `L` 与"`F` 无限"步** —— 重放 `prop:14.14` 的同一句话

`lem:14.23`（源文 `:429`）的第一个陈述取 `A(σ) = P_σ D`，其中
`D = diag(x_1,…,x_n)`，而 `x_1,…,x_n` 是 **`S'` 上的新未定元**
（源文 `:428` 逐字：`S'' = S[x_1,…,x_n](1/s)`，`s = x_1⋯x_n`）。
故第一个陈述是 **generic 陈述**；第二个陈述（`S'' ⊃ S'` 任意、`D'` 任意对角）由**特化**得。

其证明（源文 `:434` 逐字）只有一句：

> "The fact that `F` is infinite shows `ψ_{A(σ)}(α) = α` just as in Proposition 14.14."

`prop:14.14` 的那句（源文 `:292` 逐字）：

> "Let `t ∈ T` be a nonzero coefficient appearing in `s'`. Since `F` is infinite,
> there is an `F` algebra map `η : T → F` such that `η(t) ≠ 0`."

本节把**对角参数版**的这句话机检，为 §101 的 generic `ψ` 备好唯一非平凡的分析输入：

1. **`sprDiagVar`**：`s = d_1⋯d_n`（参数环的分母）；
2. `sprDiagVar_ne_zero`：`s ≠ 0`（在 `d = 1` 处取值 `1`）；
3. **`Ldiag`**：参数环 `L = F[d_1,…,d_n](1/s)`；
4. `Ldiag_isDomain`／`algebraMap_Ldiag_injective`／`algebraMap_Ldiag_powers_isUnit`／
   `Ldiag_num_ne_zero`：§7 `Tloc` 版的**逐条对应物**（只是 `det` 换成 `∏ d_i`）；
5. **`exists_algHom_ne_zero_Ldiag`**：`t ≠ 0` ⟹ 存在 `η : L →ₐ[F] F` 使 `η t ≠ 0`
   （§7 的 `exists_algHom_ne_zero` 的对角对应物）——**"`F` 无限"步**；
6. `isUnit_algebraMap_X`：每个 `d_i` 在 `L` 中是单位（故任何 `F`-点 `η` 都给
   `η(d_i) ∈ Fˣ`，即落到环面 `T` 上）；
7. ★ **`exists_map_ne_zero`**：`z ∈ S'[d]` 非零 ⟹ 存在 `F`-点 `f : L → F` 使 `z` 的像非零。
   这是 `prop:14.14` 论证的**Lean 形态**：把"所有 `F`-点都满足"升到"generic 点满足"
   （反设 ⟹ 取非零系数 ⟹ 6 给点 ⟹ 把反设打到 `F`-点上矛盾）。

**射程（勿夸大）**：本节只给**参数环与分析输入**。`ψ_{A(σ)}` 本身、
`lem:14.23` 的两个陈述、`lem:14.24/25`、`prop:14.19` 装配 —— **全部未做**。

**与 §7 的关系**：两节结构**逐条同构**，差别只在参数空间（`prop:14.14` 用**全部**
`n²` 个矩阵元 —— 因为那里的不变性是 `PGL_n(F)` 的；`lem:14.23` 只需**对角** `n` 个
—— 因为 `N`-不变性只覆盖 `T ⋊ S_n`）。 -/

section SprDiagParam



variable (F : Type) [Field F] (n : ℕ)

set_option linter.style.haveILetI false

noncomputable def sprDiagVar : MvPolynomial (Fin n) F :=
  Finset.univ.prod (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) F))

lemma sprDiagVar_ne_zero : sprDiagVar F n ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval (fun _ : Fin n => (1 : F))) h
  simp [sprDiagVar] at h1

abbrev Ldiag : Type := Localization.Away (sprDiagVar F n)

lemma Ldiag_isDomain : IsDomain (Ldiag F n) :=
  IsLocalization.Away.isDomain (S := Ldiag F n) (sprDiagVar_ne_zero F n)

lemma algebraMap_Ldiag_injective : Function.Injective
    (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) :=
  IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (sprDiagVar_ne_zero F n))

lemma algebraMap_Ldiag_powers_isUnit {n : ℕ} {s : Submonoid.powers (sprDiagVar F n)} :
    IsUnit (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)
      (s : MvPolynomial (Fin n) F)) := by
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff (s : MvPolynomial (Fin n) F)
    (sprDiagVar F n)).mp s.2
  rw [← hm, map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Ldiag F n) (sprDiagVar F n)).pow m

lemma Ldiag_num_ne_zero {n : ℕ} {t : Ldiag F n} (ht : t ≠ 0)
    {p : MvPolynomial (Fin n) F} {s : Submonoid.powers (sprDiagVar F n)}
    (h : t * algebraMap (MvPolynomial (Fin n) F) (Ldiag F n) (s : _) = algebraMap _ _ p) :
    p ≠ 0 := by
  haveI : IsDomain (Ldiag F n) := Ldiag_isDomain F n
  intro hp
  have h0 : t * algebraMap (MvPolynomial (Fin n) F) (Ldiag F n) (s : _) = 0 := by
    rw [h, hp, map_zero]
  exact ht ((mul_eq_zero.mp h0).resolve_right (algebraMap_Ldiag_powers_isUnit F (s := s)).ne_zero)

theorem exists_algHom_ne_zero_Ldiag [Infinite F] {n : ℕ} {t : Ldiag F n} (ht : t ≠ 0) :
    ∃ η : Ldiag F n →ₐ[F] F, η t ≠ 0 := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (sprDiagVar F n)) t
  have hp : p ≠ 0 := Ldiag_num_ne_zero F ht hs
  have hq : p * sprDiagVar F n ≠ 0 := mul_ne_zero hp (sprDiagVar_ne_zero F n)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero F hq
  have hxp : MvPolynomial.eval x p ≠ 0 := fun h => hx (by rw [map_mul, h, zero_mul])
  have hxd : MvPolynomial.eval x (sprDiagVar F n) ≠ 0 := fun h => hx (by rw [map_mul, h, mul_zero])
  set g : MvPolynomial (Fin n) F →ₐ[F] F :=
    { toRingHom := MvPolynomial.eval x
      commutes' := fun c => by simp } with hgdef
  have hgval : ∀ q, g q = MvPolynomial.eval x q := fun q => rfl
  have hgunit : IsUnit (g (sprDiagVar F n)) := by
    rw [hgval]; exact isUnit_iff_ne_zero.mpr hxd
  refine ⟨IsLocalization.Away.liftAlgHom (S := Ldiag F n) (sprDiagVar F n) hgunit, ?_⟩
  have hcoe : ∀ q : MvPolynomial (Fin n) F,
      (IsLocalization.Away.liftAlgHom (S := Ldiag F n) (sprDiagVar F n) hgunit)
        ((algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) q) = g q := by
    intro q
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq (x := sprDiagVar F n) (g := g.toRingHom) hgunit q
  intro htz
  have hkey : (IsLocalization.Away.liftAlgHom (S := Ldiag F n) (sprDiagVar F n) hgunit) t
      * g (s : MvPolynomial (Fin n) F) = g p := by
    have h := congrArg (IsLocalization.Away.liftAlgHom (S := Ldiag F n) (sprDiagVar F n) hgunit) hs
    rw [map_mul, hcoe (s : MvPolynomial (Fin n) F), hcoe p] at h
    exact h
  rw [htz, zero_mul] at hkey
  exact hxp (by rw [← hgval p]; exact hkey.symm)

#print axioms sprDiagVar
#print axioms sprDiagVar_ne_zero
#print axioms Ldiag
#print axioms Ldiag_isDomain
#print axioms algebraMap_Ldiag_injective
#print axioms algebraMap_Ldiag_powers_isUnit
#print axioms Ldiag_num_ne_zero
#print axioms exists_algHom_ne_zero_Ldiag

/-- 每个 `d_i` 在 `L` 中是单位（`d_i ∣ ∏_j d_j`，而后者是单位）。 -/
lemma isUnit_algebraMap_X (i : Fin n) :
    IsUnit (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n) (MvPolynomial.X i)) := by
  set P : MvPolynomial (Fin n) F :=
    (Finset.univ.erase i).prod (fun j => (MvPolynomial.X j : MvPolynomial (Fin n) F)) with hP
  have h : IsUnit (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n) (sprDiagVar F n)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Ldiag F n) (sprDiagVar F n)
  have hsplit : sprDiagVar F n = P * MvPolynomial.X i := by
    rw [sprDiagVar, hP]
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  have hmul : (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) (sprDiagVar F n)
      = (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) P
        * (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) (MvPolynomial.X i) := by
    simp only [hsplit, map_mul]
  have h2 : IsUnit ((algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) P
      * (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n)) (MvPolynomial.X i)) := by
    rw [← hmul]
    exact h
  exact isUnit_of_mul_isUnit_right h2

#print axioms isUnit_algebraMap_X

/-- ★★★ **多项式恒等式步（对角参数版）**：`z ∈ S'[d]` 非零 ⟹ 存在 `F`-点 `f : L → F`
使 `z` 的像非零。**用途**：`lem:14.23` 的"`F` 无限"步——
把"所有 `F`-点都满足"升到"generic 点满足"（`prop:14.14` 的同一句话）。 -/
theorem exists_map_ne_zero [Infinite F] {σ : Type*} {z : MvPolynomial σ (Ldiag F n)}
    (hz : z ≠ 0) : ∃ f : Ldiag F n →ₐ[F] F, MvPolynomial.map f.toRingHom z ≠ 0 := by
  obtain ⟨ν, hν⟩ := MvPolynomial.support_nonempty.mpr hz
  rw [MvPolynomial.mem_support_iff] at hν
  obtain ⟨f, hf⟩ := exists_algHom_ne_zero_Ldiag F hν
  refine ⟨f, fun h => hf ?_⟩
  have hc : (MvPolynomial.map f.toRingHom z).coeff ν = 0 := by
    rw [h]
    simp
  rw [MvPolynomial.coeff_map] at hc
  exact hc

#print axioms exists_map_ne_zero
end SprDiagParam

/-! ## §101 **对角作用的通用形态** —— `lem:14.23` 的 `φ_A` 与自然性

源文 `:363` 定义（逐字）：

> "define `ψ_A : M_n(S') → M_n(S')` by setting `ψ_A(α) = A(M_n(φ_A)(α))A⁻¹`"

而 `φ_A` 由 `A⁻¹XA`、`A⁻¹Y_kA` 的逐项给出。本节给**对角** `A = D = diag(d)` 的形态
（源文 `:428` 的 `A(σ) = P_σ D` 的 `D` 那一半）：

$$
φ_D(x_{ii}) = x_{ii},\qquad φ_D(y_{ijk}) = (d_j/d_i)\, y_{ijk}.
$$

**设计（三条，皆为可复用）**：

1. **通用形态**：`sprDiagAeval R xi yv c` 对**任意** `F`-代数 `R`、**任意**变量赋值
   `xi : Fin n → R`／`yv : YIdx → R`、**任意**单位族 `c : Fin n → Rˣ` 定义 `φ_c`。
   这样一处定义服务三种用途：generic（`R = S'[d]`）、`F`-点（`R = S'`）、
   任意 `S'`-扩环（`R = S''`）——**不需要三份重放**。
2. **系数写在 `Rˣ` 里**：`(c_j · c_i⁻¹ : Rˣ)` 再 coercion 到 `R`。**理由**：在 `CommRing` 里
   `·⁻¹` 是 `Ring.inverse`（非单位时是垃圾值），而 `Rˣ` 里的 `⁻¹` 是真逆元。
   本战役 R151／R153 的教训在此提前规避。
3. **`xi`／`yv` 分开**（不用 `SprIdx` 上的 `match`）：`Sum.elim` 让 `aeval` 的赋值可逐分支写，
   `cases` 后 `rfl` 即闭合——避免 R140／R144 一族的目标形态问题。

**核心件**：`sprDiagAeval_comp` = **自然性**
`φ.comp (sprDiagAeval R xi yv c) = sprDiagAeval R' (φ∘xi) (φ∘yv) (φ∘c)`
（`MvPolynomial.comp_aeval`）。它是 `lem:14.23` **第二陈述（特化）**的唯一引擎：
generic 恒等式沿任意 `F`-代数映射推出特化恒等式。

**射程（勿夸大）**：本节只有 `φ`（环层）与对角矩阵 `D` 的**乘法逆律**。
`ψ` 的矩阵层本体（`sprPsiDiagR`）、`lem:14.23` 的两个陈述、`lem:14.24/25`、
`prop:14.19` 装配 —— **全部未做**。 -/

section SprDiagGen



variable (F : Type) [Field F]

/-- 对角作用的通用形态：`x_ii ↦ xi i`、`y_ijk ↦ (c_j/c_i) · yv (i,j,k)`。 -/
noncomputable def sprDiagAeval (r n : ℕ) (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (c : Fin n → Rˣ) : Spr F r n →ₐ[F] R :=
  MvPolynomial.aeval (Sum.elim xi
    (fun ijk : YIdx r n => ((c ijk.2.1 * (c ijk.1)⁻¹ : Rˣ) : R) * yv ijk))

theorem sprDiagAeval_X_inl {r n : ℕ} {R : Type} [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (c : Fin n → Rˣ) (i : Fin n) :
    sprDiagAeval F r n R xi yv c (MvPolynomial.X (Sum.inl i)) = xi i := by
  rw [sprDiagAeval, MvPolynomial.aeval_X]
  rfl

theorem sprDiagAeval_X_inr {r n : ℕ} {R : Type} [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (c : Fin n → Rˣ)
    (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    sprDiagAeval F r n R xi yv c (MvPolynomial.X (Sum.inr (i, j, k)))
      = ((c j * (c i)⁻¹ : Rˣ) : R) * yv (i, j, k) := by
  rw [sprDiagAeval, MvPolynomial.aeval_X]
  rfl

lemma coe_units_mul_inv {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R') (u v : Rˣ) :
    φ (↑(u * v⁻¹)) = ↑(Units.map φ.toMonoidHom u * (Units.map φ.toMonoidHom v)⁻¹) := by
  have h : Units.map φ.toMonoidHom (u * v⁻¹)
      = Units.map φ.toMonoidHom u * (Units.map φ.toMonoidHom v)⁻¹ := by
    rw [map_mul, map_inv]
  calc φ (↑(u * v⁻¹)) = ↑(Units.map φ.toMonoidHom (u * v⁻¹)) := (Units.coe_map _ _).symm
    _ = ↑(Units.map φ.toMonoidHom u * (Units.map φ.toMonoidHom v)⁻¹) := by rw [h]

/-- ★★★ **自然性**：`ψ`／`φ` 对目标环的映射是自然的（`MvPolynomial.comp_aeval`）。
**用途**：generic 陈述 ⟹ 任意 `F`-点／任意 `S'`-代数上的特化（`lem:14.23` 的第二陈述）。 -/
theorem sprDiagAeval_comp {r n : ℕ} {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R') (xi : Fin n → R) (yv : YIdx r n → R)
    (c : Fin n → Rˣ) :
    φ.comp (sprDiagAeval F r n R xi yv c)
      = sprDiagAeval F r n R' (fun i => φ (xi i)) (fun ijk => φ (yv ijk))
          (fun i => Units.map φ.toMonoidHom (c i)) := by
  rw [sprDiagAeval, MvPolynomial.comp_aeval, sprDiagAeval]
  congr 1
  funext v
  cases v with
  | inl i => rfl
  | inr ijk =>
      show φ (((c ijk.2.1 * (c ijk.1)⁻¹ : Rˣ) : R) * yv ijk) = _
      rw [map_mul, coe_units_mul_inv]
      rfl

/-- 点版＝§68 的 `sprDiagHom`（`sprDiagHom b` 对应 `diag(b⁻¹)`：源文 `φ_A(y_ijk) = (d_j/d_i)y_ijk`
而 `sprDiagHom` 的系数是 `b_i/b_j`）。 -/
theorem sprDiagAeval_point {r n : ℕ} (b : Fin n → Fˣ) :
    sprDiagAeval F r n (Spr F r n) (fun i => MvPolynomial.X (Sum.inl i))
        (fun ijk => MvPolynomial.X (Sum.inr ijk))
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))
      = sprDiagHom F r n b := by
  rw [sprDiagAeval, sprDiagHom]
  congr 1
  funext v
  cases v with
  | inl i => rfl
  | inr ijk =>
      obtain ⟨i, j, k⟩ := ijk
      show ((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b j)⁻¹)
            * (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹
            : (Spr F r n)ˣ) : Spr F r n) * MvPolynomial.X (Sum.inr (i, j, k))
          = MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) * MvPolynomial.X (Sum.inr (i, j, k))
      have hcoe : ((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b j)⁻¹)
            * (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹
            : (Spr F r n)ˣ) : Spr F r n)
          = MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) := by
        have hunit : Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b j)⁻¹)
            * (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹
            = Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i) * (b j)⁻¹) := by
          rw [← map_inv, inv_inv, ← map_mul]
          congr 1
          exact mul_comm _ _
        rw [hunit, Units.coe_map]
        have h2 : (↑((b i) * (b j)⁻¹) : F) = (b i : F) * ((b j : F))⁻¹ := by
          rw [Units.val_mul, Units.val_inv_eq_inv_val]
        rw [h2]
        rfl
      rw [hcoe]

/-- 对角矩阵 `diag (↑(c i))`（取值在任意 `F`-代数里）。 -/
noncomputable def sprDiagMatR {n : ℕ} (R : Type) [CommSemiring R] (c : Fin n → Rˣ) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal (fun i => (c i : R))

theorem sprDiagMatR_apply {n : ℕ} {R : Type} [CommSemiring R] (c : Fin n → Rˣ)
    (i j : Fin n) : sprDiagMatR (n := n) R c i j = if i = j then (c i : R) else 0 := by
  rw [sprDiagMatR, Matrix.diagonal, Matrix.of_apply]

theorem sprDiagMatR_mul_inv {n : ℕ} {R : Type} [CommSemiring R] (c : Fin n → Rˣ) :
    sprDiagMatR (n := n) R c * sprDiagMatR (n := n) R (fun i => (c i)⁻¹) = 1 := by
  have h : (fun i => (c i : R) * (((c i)⁻¹ : Rˣ) : R)) = fun _ => 1 := by
    funext i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [sprDiagMatR, sprDiagMatR, Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_one]

#print axioms sprDiagAeval
#print axioms sprDiagAeval_X_inl
#print axioms sprDiagAeval_X_inr
#print axioms coe_units_mul_inv
#print axioms sprDiagAeval_comp
#print axioms sprDiagAeval_point
#print axioms sprDiagMatR
#print axioms sprDiagMatR_apply
#print axioms sprDiagMatR_mul_inv
end SprDiagGen

/-! ## §102 **`ψ` 的矩阵层本体**（对角 `A = D_c`）—— 通用形态 ＋ 自然性 ＋ 点版

源文 `:363`（逐字）：

> "define `ψ_A : M_n(S') → M_n(S')` by setting `ψ_A(α) = A(M_n(φ_A)(α))A⁻¹`"

本节把 §101 的 `φ_c` 组装成**共轭作用** `ψ_c`：

$$
ψ_c(α) = D_c · (α\text{ 逐项经 }φ_c) · D_c^{-1}.
$$

**为何用通用形态**：`R`／`xi`／`yv` 三个参数一放，generic、`F`-点、任意 `S'`-扩环
**三种用途共一处定义**，且自然性（`sprPsiDiagR_comp`）一次证完、处处可用。

**★ R156（第 262 轮预研抓到的约定错误）**：§99 的 `sprPsiD` 前身写成
`D_b · map(φ_b) · D_b⁻¹`，但 `φ_b = sprDiagHom b` 实为 **`φ_{diag(b⁻¹)}`**
（源文 `φ_A(y_ijk) = (d_j/d_i)y_ijk`，而 `sprDiagHom` 的系数是 `b_i/b_j`）——
**`D_b` 与 `φ_{diag(b⁻¹)}` 不配对，那不是共轭**。`sprPsiDiagR_point` 是本节的**接口校验**：
它机检"通用形态在 `R = S'`、`c = b⁻¹` 处恰是 §99 的 `sprPsiD b`"，从而 §99 的约定
与本节一致（`sprPsiD` 已同时改正文档与定义）。

**射程（勿夸大）**：本节只有**对角** `A = D_c` 的 `ψ`。
置换部分 `ψ_{P_σ}`、`lem:14.23` 的两个陈述（generic 与特化）、`lem:14.24/25`、
`prop:14.19` 装配 —— **全部未做**。 -/

section SprPsiDiagGen



variable (F : Type) [Field F]

section T1

variable {r n : ℕ}

/-- `ψ_c(α) = D_c · (α 逐项经 φ_c) · D_c⁻¹`（源文 `:363` 的 `ψ_A` 取 `A = D_c`）。 -/
noncomputable def sprPsiDiagR (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (c : Fin n → Rˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) : Matrix (Fin n) (Fin n) R :=
  sprDiagMatR (n := n) R c * α.map (sprDiagAeval F r n R xi yv c)
    * sprDiagMatR (n := n) R (fun i => (c i)⁻¹)

theorem sprPsiDiagR_apply (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (c : Fin n → Rˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiDiagR (F := F) (r := r) (n := n) R xi yv c α
      = sprDiagMatR (n := n) R c * α.map (sprDiagAeval F r n R xi yv c)
        * sprDiagMatR (n := n) R (fun i => (c i)⁻¹) := rfl

theorem sprDiagMatR_map {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R') (c : Fin n → Rˣ) :
    (sprDiagMatR (n := n) R c).map φ
      = sprDiagMatR (n := n) R' (fun i => Units.map φ.toMonoidHom (c i)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, sprDiagMatR_apply, sprDiagMatR_apply]
  split_ifs with h
  · exact Units.coe_map _ _
  · exact map_zero φ

theorem sprPsiDiagR_comp {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R')
    (xi : Fin n → R) (yv : YIdx r n → R) (c : Fin n → Rˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    (sprPsiDiagR (F := F) (r := r) (n := n) R xi yv c α).map φ
      = sprPsiDiagR (F := F) (r := r) (n := n) R' (fun i => φ (xi i)) (fun ijk => φ (yv ijk))
          (fun i => Units.map φ.toMonoidHom (c i)) α := by
  have hc : (fun i => Units.map φ.toMonoidHom ((c i)⁻¹))
      = fun i => (Units.map φ.toMonoidHom (c i))⁻¹ := by
    funext i
    rw [map_inv]
  rw [sprPsiDiagR, Matrix.map_mul, Matrix.map_mul, sprDiagMatR_map, sprDiagMatR_map, hc]
  have hmid : (α.map ⇑(sprDiagAeval F r n R xi yv c)).map ⇑φ
      = α.map ⇑(φ.comp (sprDiagAeval F r n R xi yv c)) := by
    rw [Matrix.map_map]
    rfl
  rw [hmid, sprDiagAeval_comp, sprPsiDiagR]

end T1

section T2

variable {r n : ℕ}

lemma sprDiagMatR_eq_sprDiagMat (b : Fin n → Fˣ) :
    sprDiagMatR (n := n) (Spr F r n)
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom (b i))
      = sprDiagMat (F := F) (r := r) b := by
  rw [sprDiagMatR, sprDiagMat]
  congr 1

/-- 点版：`sprPsiDiagR` 在 `R = S'`、`c = b⁻¹` 处就是 §99 的 `sprPsiD b`。 -/
theorem sprPsiDiagR_point (b : Fin n → Fˣ) (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiDiagR (F := F) (r := r) (n := n) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk))
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α
      = sprPsiD b α := by
  rw [sprPsiDiagR, sprDiagAeval_point, sprDiagMatR_eq_sprDiagMat]
  have h : (fun i => (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹)
      = fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom (b i) := by
    funext i
    rw [← map_inv, inv_inv]
  rw [h, sprDiagMatR_eq_sprDiagMat]
  rfl

end T2

#print axioms sprPsiDiagR
#print axioms sprPsiDiagR_apply
#print axioms sprDiagMatR_map
#print axioms sprPsiDiagR_comp
#print axioms sprDiagMatR_eq_sprDiagMat
#print axioms sprPsiDiagR_point
end SprPsiDiagGen

/-! ## §103 **`lem:14.23` 对角 generic 陈述** —— "`F` 无限"论证的收口

源文 `:434`（逐字）：

> "The fact that `F` is infinite shows `ψ_{A(σ)}(α) = α` just as in Proposition 14.14."

`prop:14.14` 的论证（源文 `:290–296`）分两步：反设 `ψ_Y(α) - α ≠ 0` ⟹ 取非零系数 `t` ⟹
`F` 无限给 `F`-点 `η` 使 `η(t) ≠ 0` ⟹ 特化后与"所有 `F`-点都固定"矛盾。
本节把这两步在**对角参数**上机检成

$$
(∀ b : (F^×)^n,\; ψ_b(α) = α)\quad⟹\quad ψ_{d_{gen}}(α) = α
$$

其中 `d_gen` 是泛对角（`d_i` 为 `S'` 上**新的**未定元，取值在 `L = F[d](1/∏d_i)`）。

**件**：
1. `sprDiagGenUnit`：泛对角单位 `d_i`（`L` 中的单位，来自 §100 的 `isUnit_algebraMap_X`）；
2. `sprDiagGenCoef`：把它搬到 `S'[d]`（常数多项式）——`sprDiagAeval` 的 `Rˣ` 参数要这个形态；
3. `sprCoeffMap f : S'[d] →ₐ[F] S'`：`MvPolynomial.map f` 的 `AlgHom` 包装（`f : L →ₐ[F] F`）；
4. `sprCoeffMap_X`：变量不动；5. `sprCoeffMap_map_algebraMap`：`f ∘ (F → L) = id` ⟹ 把
   `α` 的系数扩张压回来得 `α` 本身；
6. `sprDiagGenCoef_map_units`：单位族沿 `f` 的搬运律（**R140 教训**：`ext` 在
   `MvPolynomial` 上会顺手套 `MvPolynomial.ext`，故用 **`Units.ext`**）;
7. ★★★★★ **`sprPsiDiag_generic_fixed`**：主结论。

**证明骨架**（与源文同构）：反设 `G ≠ E`（`G` = 泛对角共轭，`E` = 系数扩张的 `α`）⟹
取非零元 `z = (G−E)_{i₀j₀}` ⟹ §100 的 `exists_map_ne_zero` 给 `F`-点 `f` 使 `f(z) ≠ 0` ⟹
沿 `f` 压过去：`G ↦ ψ_{d_f}(α)`（`sprPsiDiagR_comp` ＋ `sprDiagGenCoef_map_units` ＋
`sprPsiDiagR_point`）而 `E ↦ α`（`sprCoeffMap_map_algebraMap`）⟹ 两边相等 ⟹
`f(z) = 0`，矛盾。

**射程（勿夸大）**：本节只是 `lem:14.23` 的 **`σ = id`** 情形（纯对角）。
**置换部分 `ψ_{P_σ}`、`lem:14.23` 的两个陈述本体（含 `A(σ) = P_σ D` 与任意 `S''`）、
`lem:14.24/25`、`prop:14.19` 装配 —— 全部未做**。`ZEqNFixed` 仍未证。 -/

section Lem1423Diag



variable (F : Type) [Field F]
variable {r n : ℕ}

/-- 泛对角单位族 `d_i`（在参数环 `L` 里）。 -/
noncomputable def sprDiagGenUnit (i : Fin n) : (Ldiag F n)ˣ := (isUnit_algebraMap_X F n i).unit

#print axioms sprDiagGenUnit

/-- 泛对角单位族搬到 `S'[d]` 里（常数多项式）。 -/
noncomputable def sprDiagGenCoef (i : Fin n) : (MvPolynomial (SprIdx r n) (Ldiag F n))ˣ :=
  Units.map (algebraMap (Ldiag F n) (MvPolynomial (SprIdx r n) (Ldiag F n))).toMonoidHom
    (sprDiagGenUnit (F := F) i)

#print axioms sprDiagGenCoef

/-- `MvPolynomial.map f` 作为 `F`-代数同态（`S'[d] → S'`，系数沿 `f` 压回）。 -/
noncomputable def sprCoeffMap (f : Ldiag F n →ₐ[F] F) :
    MvPolynomial (SprIdx r n) (Ldiag F n) →ₐ[F] MvPolynomial (SprIdx r n) F where
  toFun := MvPolynomial.map f.toRingHom
  map_one' := by simp
  map_mul' p q := by simp
  map_zero' := by simp
  map_add' p q := by simp
  commutes' a := by
    show MvPolynomial.map f.toRingHom
      (algebraMap F (MvPolynomial (SprIdx r n) (Ldiag F n)) a)
      = algebraMap F (MvPolynomial (SprIdx r n) F) a
    simp

#print axioms sprCoeffMap

theorem sprCoeffMap_X (f : Ldiag F n →ₐ[F] F) (v : SprIdx r n) :
    sprCoeffMap (F := F) (r := r) (n := n) f (MvPolynomial.X v) = MvPolynomial.X v := by
  show MvPolynomial.map f.toRingHom (MvPolynomial.X v) = MvPolynomial.X v
  rw [MvPolynomial.map_X]

#print axioms sprCoeffMap_X

theorem sprCoeffMap_map_algebraMap (f : Ldiag F n →ₐ[F] F) (p : Spr F r n) :
    sprCoeffMap (F := F) (r := r) (n := n) f
      (MvPolynomial.map (algebraMap F (Ldiag F n)) p) = p := by
  show MvPolynomial.map f.toRingHom (MvPolynomial.map (algebraMap F (Ldiag F n)) p) = p
  rw [MvPolynomial.map_map]
  have h : f.toRingHom.comp (algebraMap F (Ldiag F n)) = RingHom.id F := by
    ext x
    rw [RingHom.comp_apply, RingHom.id_apply]
    simp
  rw [h, MvPolynomial.map_id]

#print axioms sprCoeffMap_map_algebraMap


lemma sprDiagGenCoef_map_units (f : Ldiag F n →ₐ[F] F) (i : Fin n) :
    Units.map (sprCoeffMap (F := F) (r := r) (n := n) f).toMonoidHom
        (sprDiagGenCoef (F := F) (r := r) i)
      = Units.map (algebraMap F (Spr F r n)).toMonoidHom
          (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i)) := by
  refine Units.ext ?_
  rw [Units.coe_map, Units.coe_map, sprDiagGenCoef, Units.coe_map, Units.coe_map]
  show MvPolynomial.map f.toRingHom
      (algebraMap (Ldiag F n) (MvPolynomial (SprIdx r n) (Ldiag F n))
        (↑((isUnit_algebraMap_X F n i).unit)))
    = algebraMap F (MvPolynomial (SprIdx r n) F) (f ↑((isUnit_algebraMap_X F n i).unit))
  rw [IsUnit.unit_spec, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq,
    MvPolynomial.map_C]
  congr 1

#print axioms sprDiagGenCoef_map_units

/-- ★★★★★ `lem:14.23` 的**对角 generic 陈述**（`σ = id`）：`α` 若被**所有 `F`-点**的对角共轭
固定，则被**泛对角**共轭固定。证明 = `prop:14.14` 的同一句话的 Lean 形态。 -/
theorem sprPsiDiag_generic_fixed [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ b : Fin n → Fˣ, sprPsiD b α = α) :
    sprPsiDiagR (F := F) (r := r) (n := n) (MvPolynomial (SprIdx r n) (Ldiag F n))
        (fun i => MvPolynomial.X (Sum.inl i))
        (fun ijk => MvPolynomial.X (Sum.inr ijk))
        (sprDiagGenCoef (F := F) (r := r)) α
      = α.map (MvPolynomial.map (algebraMap F (Ldiag F n))) := by
  by_contra hEq
  set Rg := MvPolynomial (SprIdx r n) (Ldiag F n) with hRg
  set G : Matrix (Fin n) (Fin n) Rg :=
    sprPsiDiagR (F := F) (r := r) (n := n) Rg
      (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk))
      (sprDiagGenCoef (F := F) (r := r)) α with hG
  set E : Matrix (Fin n) (Fin n) Rg :=
    α.map (MvPolynomial.map (algebraMap F (Ldiag F n))) with hE
  have hGE : G ≠ E := by rw [hG, hE]; exact hEq
  have hne : G - E ≠ 0 := sub_ne_zero.mpr hGE
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, (G - E) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by
      refine Matrix.ext fun i j => ?_
      rw [hcon i j, Matrix.zero_apply])
  obtain ⟨f, hf⟩ := exists_map_ne_zero F n hij
  have hphi : (⇑(sprCoeffMap (F := F) (r := r) (n := n) f)) = MvPolynomial.map f.toRingHom := rfl
  have hGmap : G.map (MvPolynomial.map f.toRingHom)
      = sprPsiDiagR (F := F) (r := r) (n := n) (Spr F r n)
          (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk))
          (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom
            (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i))) α := by
    rw [hG, ← hphi]
    rw [sprPsiDiagR_comp (φ := sprCoeffMap (F := F) (r := r) (n := n) f)]
    simp only [sprCoeffMap_X, sprDiagGenCoef_map_units]
  have hEmap : E.map (MvPolynomial.map f.toRingHom) = α := by
    rw [hE, Matrix.map_map]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    exact sprCoeffMap_map_algebraMap (F := F) (r := r) (n := n) f (α i j)
  set b : Fin n → Fˣ :=
    fun i => (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i))⁻¹ with hb
  have hunit : (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom
        (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i)))
      = fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹) := by
    funext i
    rw [hb]
    simp
  have hGalpha : G.map (MvPolynomial.map f.toRingHom) = α := by
    rw [hGmap, hunit, sprPsiDiagR_point, hα b]
  have hzero : (G - E).map (MvPolynomial.map f.toRingHom) = 0 := by
    rw [Matrix.map_sub (MvPolynomial.map f.toRingHom) (fun a b => map_sub _ _ _),
      hGalpha, hEmap, sub_self]
  have hcontra : (G - E).map (MvPolynomial.map f.toRingHom) i₀ j₀ ≠ 0 := by
    rw [Matrix.map_apply]
    exact hf
  rw [hzero] at hcontra
  exact hcontra (by rw [Matrix.zero_apply])

#print axioms sprPsiDiag_generic_fixed
end Lem1423Diag

/-! ## §104 **置换矩阵 `P_σ`** —— `lem:14.23` 的 `A(σ) = P_σ D` 的 `P_σ` 那一半

源文 `:355`（逐字）：

> "For each `σ ∈ S_n`, let `P_σ ∈ GL_n(F)` be the matrix `(p_{ij})` such that
> `p_{σ(i)i} = 1` and `p_{ij} = 0` for all other `i` and `j`."

本节只给**载体与逐项形态**（`R` 为任意交换半环，故可直接用于 `S'`、`S'[d]`、任意 `S''`）。

**射程（勿夸大）**：**乘积律 `P_σ · P_σ⁻¹ = 1` 本轮未证**（第 268 轮按 L47③ 停止，
两条路线各试到第 3 次未过：① `Finset.sum_eq_single` 分支的 `if` 改写；
② 显式 `by_cases` 后仍卡在 `σ⁻¹` 下的改写）。
**已定的下一步路线（更稳）**：用 `MatrixUnits.lean` 里**已机检**的乘法表
`stdMU_mul : stdMU i j * stdMU k l = if j = k then stdMU i l else 0`，把
`P_σ` 写成 `∑ j, stdMU (σ j) j`，则乘积律化约为该表 ＋ `∑ i, stdMU i i = 1`
——**不再碰 `if` 分支的改写**。 -/

section SprPmatSec

/-- 置换矩阵 `P_σ`：`(P_σ)_{ij} = 1` 当且仅当 `i = σ j`（源文 `:355` 的约定
`p_{σ(i)i} = 1`）。 -/
noncomputable def sprPmat (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of (fun i j => if i = σ j then 1 else 0)

#print axioms sprPmat

theorem sprPmat_apply (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin n) :
    sprPmat R σ i j = if i = σ j then (1 : R) else 0 := rfl

#print axioms sprPmat_apply

end SprPmatSec

/-! ## §105 **`P_σ` 的乘积律** —— 走 `Matrix.submatrix_mul`，不碰 `if` 改写

源文 `:355` 的 `P_σ` 满足 `P_σ P_τ = P_{στ}`；本节只证**逆元律**
`P_σ · P_σ⁻¹ = 1`（`P_σ ∈ GL_n`，为 `lem:14.23` 的 `A(σ) = P_σ D` 服务）。

**为何换路线（R158，第 270 轮）**：第 268／269 轮在 `Finset.sum_eq_single` ＋ `if`
上三试不过（详见 `wiki/deadend-sprPmat-mul-symm.md`）。根因是 **`if` 的条件不是命题位置**
（条件的 `Decidable` 实例是额外参数，`rw`／`by_cases` 都打不进去）。
**正解**：把 `P_σ` 认成**结构化的 submatrix**
`P_σ = (1 : M_n(R)).submatrix id σ`（`P_{σ⁻¹}` 同理用 `σ.id` 一侧），
乘积律就由 **`Matrix.submatrix_mul`**（带 `Bijective` 侧条件）给出：
`(1 * 1).submatrix id id = 1.submatrix id σ * 1.submatrix σ id`。
两处 `if` 的等价（`σ i = j ↔ i = σ⁻¹ j`）用 **`if_congr`** 一次收口——
`if_congr` 是**定理层**的 `if` 等式，不经过 `rw`，故不受实例干扰。

**射程（勿夸大）**：本节只给**逆元律**。`P_σ` 与对角矩阵的交换律、`P_σ P_τ = P_{στ}`、
`ψ_{P_σ}`、`lem:14.23` 的两陈述 —— **全部未做**。 -/

section SprPmatMul

variable (F : Type) [Field F]

/-- ★★ **`P_σ · P_σ⁻¹ = 1`**（源文 `:355` 的 `P_σ ∈ GL_n(F)`）。 -/
theorem sprPmat_mul_symm (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    sprPmat R σ * sprPmat (n := n) R σ⁻¹ = 1 := by
  have h1 : sprPmat (n := n) R σ = (1 : Matrix (Fin n) (Fin n) R).submatrix id ⇑σ := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    rfl
  have h2 : (1 : Matrix (Fin n) (Fin n) R).submatrix ⇑σ id = sprPmat (n := n) R σ⁻¹ := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    show (if σ i = j then (1 : R) else 0) = (if i = σ⁻¹ j then 1 else 0)
    exact if_congr (Equiv.eq_symm_apply σ).symm rfl rfl
  have hmul := Matrix.submatrix_mul (1 : Matrix (Fin n) (Fin n) R) 1
    (id : Fin n → Fin n) (⇑σ) (id : Fin n → Fin n) σ.bijective
  rw [h1, ← h2, ← hmul, Matrix.one_mul, Matrix.submatrix_id_id]

#print axioms sprPmat_mul_symm

/-- `P_σ⁻¹ · P_σ = 1`（另一侧，由对称性）。 -/
theorem sprPmat_symm_mul (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    sprPmat (n := n) R σ⁻¹ * sprPmat R σ = 1 := by
  have h := sprPmat_mul_symm (n := n) R σ⁻¹
  rwa [inv_inv] at h

#print axioms sprPmat_symm_mul

end SprPmatMul

/-! ## §106 **`P_σ` 的两个逐项取值** —— 为"置换＝矩阵共轭"的生成元计算备料

`P_σ` 的两条**无 `if` 的取值律**：

1. `sprPmat_apply_self`：`(P_σ)_{σ j, j} = 1`；
2. `sprPmat_apply_of_ne`：`i ≠ σ j` 时 `(P_σ)_{i j} = 0`。

**为何单独成节**：后续要证 `M(φ_{P_σ})(α) = P_σ⁻¹ α P_σ`（源文 `:363` 的作用与矩阵共轭
的一致性），其生成元计算只需**这两条取值**——把 "`if` 的真值"**一次性**在入口处消掉，
下游所有矩阵运算就都**不碰 `if`**（R158 的落实：`if` 只允许出现在"入口两行"）。

**射程（勿夸大）**：本节只有两条取值。`P_σ · D_c = D_{c'} · P_σ`（与对角的交换律）
**本轮未证**（第 271 轮：入口两条已过，但合并式在两处 `show`／`rw` 上未过，
按 L47③ 停止并只落已证部分）。`lem:14.23` 两陈述仍全未做。 -/

section SprPmatEval

variable (F : Type) [Field F]

/-- `(P_σ)_{σ j, j} = 1`（源文 `:355` 的 `p_{σ(i)i} = 1`）。 -/
theorem sprPmat_apply_self (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (j : Fin n) : sprPmat R σ (σ j) j = 1 := by
  show (if σ j = σ j then (1 : R) else 0) = 1
  simp

#print axioms sprPmat_apply_self

/-- `i ≠ σ j` 时 `(P_σ)_{i j} = 0`（源文 `:355` 的 `p_{ij} = 0` for all other `i, j`）。 -/
theorem sprPmat_apply_of_ne (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (h : i ≠ σ j) : sprPmat R σ i j = 0 := by
  show (if i = σ j then (1 : R) else 0) = 0
  simp [h]

#print axioms sprPmat_apply_of_ne

end SprPmatEval

/-! ## §107 **`P_σ` 与对角的交换律** —— 入口消 `if` 的完成形态

源文 `:355`／`:363` 的作用是"置换矩阵 ＋ 对角矩阵"的积。本节给它的**交换律**：

$$
P_σ · D_c = D_{c'} · P_σ,\\qquad c'_i = c_{σ^{-1}(i)}.
$$

逐项验证：`(P_σ D_c)_{ij} = [i = σ j] · d_j`，而 `(D_{c'} P_σ)_{ij} = d'_{i} · [i = σ j]`，
两者相等当且仅当 `i = σ j` 时 `d'_i = d_j`，即 `d'_i = d_{σ^{-1}(i)}`。

**工艺（R158 的完成形态，本轮定型）**：**`if` 只允许出现在"入口引理"里**。
本节先补一条入口件 `sprDiagMatR_apply_of_ne`（与 §106 的 `sprPmat_apply_of_ne` 同形），
于是交换律的证明里**一个 `if` 都不出现**：两个 `Finset.sum_eq_single` 的旁支
一律 `rw [入口引理, zero_mul / mul_zero]` 收口。
**对比**：第 271 轮直接在 `simp [hk]` 上收口，`simp` 把乘积式归一成**蕴含式**
（`k = σ j → i = k → … = 0`）而非所需等式，遂卡住；改用入口引理后**一次通过**。

**射程（勿夸大）**：本节只给交换律。`P_σ P_τ = P_{στ}`、`ψ_{P_σ}`、
`map(φ_{P_σ})(α) = P_σ⁻¹ α P_σ`、`lem:14.23` 两陈述、`lem:14.24/25`、`prop:14.19` 装配
—— **全部未做**。 -/

section SprPmatDiag

variable (F : Type) [Field F]

/-- ★ **`D_c` 的非对角项为零**（**入口引理**：此后再不必碰 `if`）。 -/
theorem sprDiagMatR_apply_of_ne (R : Type) [CommSemiring R] {n : ℕ} (c : Fin n → Rˣ)
    {k j : Fin n} (h : k ≠ j) : sprDiagMatR (n := n) R c k j = 0 := by
  show (if k = j then ((c k : Rˣ) : R) else 0) = 0
  simp [h]

#print axioms sprDiagMatR_apply_of_ne

/-- ★★ **`P_σ · D_c = D_{c'} · P_σ`**（`c'_i = c_{σ⁻¹ i}`）——
置换矩阵把对角矩阵"拉过去"时**重排对角元**。 -/
theorem sprPmat_mul_diag (R : Type) [CommSemiring R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (c : Fin n → Rˣ) :
    sprPmat R σ * sprDiagMatR (n := n) R c
      = sprDiagMatR (n := n) R (fun i => c (σ⁻¹ i)) * sprPmat R σ := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp only [sprPmat_apply, sprDiagMatR_apply]
      by_cases h : i = σ j
      · subst h
        simp
      · simp [h]
    · intro k _ hk
      rw [sprDiagMatR_apply_of_ne R (c := fun i => c (σ⁻¹ i)) (Ne.symm hk), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro k _ hk
    rw [sprDiagMatR_apply_of_ne R c hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

#print axioms sprPmat_mul_diag

end SprPmatDiag

/-! ## §108 **单项（置换×对角）作用的通用形态** —— `A(σ) = P_σ D` 的 `φ` 那一半

源文 `:363` 的 `φ_A` 取 `A = P_σ D` 时（逐项算）：

$$
φ_{P_σ D}(x_{ii}) = x_{σ i, σ i},\qquad
φ_{P_σ D}(y_{ijk}) = (d_j/d_i)\, y_{σ i, σ j, k}.
$$

本节给它的**通用形态**（与 §101 同工艺：任意 `F`-代数 `R`、任意变量赋值 `xi`／`yv`、
任意单位族 `c`），于是 generic／`F`-点／任意 `S''` 三用途共用一处定义。

**件**：
1. `sprMonoAeval`：`x_ii ↦ xi (σ i)`、`y_ijk ↦ (c_j·c_i⁻¹) · yv (σ i, σ j, k)`；
2. `sprMonoAeval_X_inl`／`_X_inr`：生成元取值；
3. ★ **`sprMonoAeval_comp`**：**自然性**（`MvPolynomial.comp_aeval` ＋ §101 的
   `coe_units_mul_inv`）——`lem:14.23` 第二陈述的引擎。

**未完成（诚实边界）**：**点版** `sprMonoAeval_point`
（`σ` 固定、`c = b⁻¹` 时 ＝ `(sprPermAlgEquiv σ) ∘ (sprDiagHom b)`）**本轮未证**：
两个分支各卡在**形态层**——`inl` 分支的 `show` 不匹配（`Units.map` coercion 的显示形态），
`inr` 分支出现 `synthInstanceFailed`（`Rˣ` 的实例在 `Units.map` 嵌套下未定）。
按 **L47③** 停止。**下一轮的做法**：不要用 `show` 硬指，先立两条**单位 coercion 引理**
（`↑(Units.map (algebraMap F Spr) u) = algebraMap (↑u)`，以及
`↑((Units.map g u)⁻¹) = ↑(Units.map g u⁻¹)`），把形态归一后再 `rw`；
或用 `MvPolynomial.algHom_ext` ＋ `simp only [生成元律]` 一次归一。
`lem:14.23` 两陈述、`lem:14.24/25`、`prop:14.19` 装配 —— **全部未做**。 -/

section SprMonoAevalSec



variable (F : Type) [Field F]
variable {r n : ℕ}

/-- 单项（置换×对角）作用的通用形态：`x_ii ↦ xi (σ i)`，
`y_ijk ↦ (c_j/c_i) · yv (σ i, σ j, k)`。 -/
noncomputable def sprMonoAeval (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ) :
    Spr F r n →ₐ[F] R :=
  MvPolynomial.aeval (Sum.elim (fun i => xi (σ i))
    (fun ijk : YIdx r n =>
      ((c ijk.2.1 * (c ijk.1)⁻¹ : Rˣ) : R) * yv (σ ijk.1, σ ijk.2.1, ijk.2.2)))

#print axioms sprMonoAeval

theorem sprMonoAeval_X_inl (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ)
    (i : Fin n) :
    sprMonoAeval (F := F) (r := r) R xi yv σ c (MvPolynomial.X (Sum.inl i)) = xi (σ i) := by
  rw [sprMonoAeval, MvPolynomial.aeval_X]
  rfl

#print axioms sprMonoAeval_X_inl

theorem sprMonoAeval_X_inr (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ)
    (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    sprMonoAeval (F := F) (r := r) R xi yv σ c (MvPolynomial.X (Sum.inr (i, j, k)))
      = ((c j * (c i)⁻¹ : Rˣ) : R) * yv (σ i, σ j, k) := by
  rw [sprMonoAeval, MvPolynomial.aeval_X]
  rfl

#print axioms sprMonoAeval_X_inr

theorem sprMonoAeval_comp {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R')
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ) :
    φ.comp (sprMonoAeval (F := F) (r := r) R xi yv σ c)
      = sprMonoAeval (F := F) (r := r) R' (fun i => φ (xi i)) (fun ijk => φ (yv ijk)) σ
          (fun i => Units.map φ.toMonoidHom (c i)) := by
  rw [sprMonoAeval, MvPolynomial.comp_aeval, sprMonoAeval]
  congr 1
  funext v
  cases v with
  | inl i => rfl
  | inr ijk =>
      obtain ⟨i, j, k⟩ := ijk
      show φ (((c j * (c i)⁻¹ : Rˣ) : R) * yv (σ i, σ j, k)) = _
      rw [map_mul, coe_units_mul_inv]
      rfl

#print axioms sprMonoAeval
#print axioms sprMonoAeval_X_inl
#print axioms sprMonoAeval_X_inr
#print axioms sprMonoAeval_comp
end SprMonoAevalSec

/-! ## §109 **点版系数的形态归一** —— `sprMonoAeval_point` 的第 1 步

§108 的点版 `sprMonoAeval_point`（`σ` 固定、`c = b⁻¹` 时
＝ `(sprPermAlgEquiv σ) ∘ (sprDiagHom b)`）卡在**形态层**。本节先完成任务书里写定的**第 1 步**：
把点版系数的两种写法归一。

**归一式**：
`↑((b_j⁻¹)·(b_i⁻¹)⁻¹ : (S')ˣ) = C (b_i · b_j⁻¹)`。

**为何需要它**：`sprMonoAeval` 的系数写在 `Rˣ` 里（§101 的设计），
而 `sprDiagHom` 的系数是 `C (b_i/b_j)`（§68 的设计）。两者的**数学内容相同**，
但 Lean 里的**显示形态不同**（`↑(Units.map …)` 嵌套 `⁻¹` vs `C (…)`）。
不归一，`rw` 就找不到落点（R127／R140／R146／R149 族的**第七次**复发位置）。

**证明**：`← map_inv` ＋ `inv_inv` ＋ `← map_mul` 把单位式收成
`Units.map … (b_i · b_j⁻¹)`，再 `Units.coe_map` 落到 `algebraMap`，
最后 `Units.val_mul`／`Units.val_inv_eq_inv_val` ＋ `F` 中的交换律。

**射程（勿夸大）**：本节只有**系数归一**。`sprMonoAeval_point` 本体
（`MvPolynomial.algHom_ext` 的两个分支）**仍未证**：两分支的 `rw` 仍报
"pattern not found"——**卡点已从"系数"缩小到"分支内的 `rw` 落点"**。
下一轮：分支内不要连续 `rw`，改为 `show` 出**目标形态**（用本节归一式后的形态）
再单步 `rw`；或对 `inl`／`inr` 各写一条**专用取值引理**（入口引理，R158）。 -/

section SprMonoPointCoef

variable (F : Type) [Field F]
variable {r n : ℕ}

/-- **点版系数的形态归一**：`↑((b_j⁻¹)·(b_i⁻¹)⁻¹ : (S')ˣ) = C (b_i · b_j⁻¹)`。 -/
theorem sprMonoCoeff_point (b : Fin n → Fˣ) (i j : Fin n) :
    ((Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b j)⁻¹)
        * (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹
        : (Spr F r n)ˣ) : Spr F r n)
      = MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) := by
  have hunit : Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b j)⁻¹)
      * (Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))⁻¹
      = Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i) * (b j)⁻¹) := by
    rw [← map_inv, inv_inv, ← map_mul]
    congr 1
    exact mul_comm _ _
  rw [hunit, Units.coe_map]
  have h2 : (↑((b i) * (b j)⁻¹) : F) = (b i : F) * ((b j : F))⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [h2]
  rfl

#print axioms sprMonoCoeff_point

end SprMonoPointCoef

/-! ## §110 **点版的入口引理** —— `sprMonoAeval` 在生成元上的归一群值

§109 把点版**系数**归一了；本节把 §108 的**两条生成元取值**也归一成
"已经代入点值"的形态（R158 的入口引理模式）：

1. `sprMonoAeval_pt_X_inl`：`φ_{P_σ D}(x_ii) = X (σ i)`；
2. `sprMonoAeval_pt_X_inr`：`φ_{P_σ D}(y_ijk) = C (b_i · b_j⁻¹) · X (σ i, σ j, k)`
   （`c = b⁻¹` 时；用 §109 的 `sprMonoCoeff_point` 收口）。

**用途**：`sprMonoAeval_point`（＝ `(sprPermAlgEquiv σ) ∘ (sprDiagHom b)`）
的 `algHom_ext` 证明只需 `rw [这两条]` 一次，**不再在分支里连续 `rw` 生成元律**。

**射程（勿夸大）**：本节**只有入口引理**。`sprMonoAeval_point` 本体**仍未证**。

**第 276 轮的精确诊断（留给下一轮，勿重复摸索）**：把 `inr` 分支改成
`simp only [map_mul, (sprPermAlgEquiv σ).commutes, sprPermAlgEquiv_X_inr]` 后，
**失败点转移到了 `inl` 分支**（`unsolved goals`）——说明两分支需要**分别固定形态**，
不能共用一个 `simp only` 集合。而 `inr` 分支在 `rw [.. , map_mul]` 后的实际目标是

```
C ↑(b i) * C (↑(b j))⁻¹ * X (inr (σ i, σ j, k))
  = (sprPermAlgEquiv σ) (C ↑(b i) * C (↑(b j))⁻¹ * X (inr (i, j, k)))
```

即 **`map_mul` 对三因子乘积没有按预期披进外层**（`C a * C a' * X` 是左结合，
而 `rw [map_mul]` 只在能统一到 `f (a * b)` 的最外层时才触发），
且左边的两个 `C` **未合并**成 `C (a * a')`。
**下一轮的做法（按此顺序）**：① 先 `rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]`
把左边两个 `C` 合成一个；② 再 `rw [map_mul, map_mul]` 把右边逐层披开
（三因子要**两次** `map_mul`）；③ 最后 `commutes` ＋ `sprPermAlgEquiv_X_inr`。
**教训**：`rw [map_mul]` **只作用一层**；三因子乘积要写两次（R144／R145 同族：
"参数个数／层数" 类错误）。

`lem:14.23` 两陈述、`lem:14.24/25`、`prop:14.19` 装配 —— **全部未做**。 -/

section SprMonoPtEntrance

variable (F : Type) [Field F]
variable {r n : ℕ}

/-- `φ_{P_σ D}(x_ii) = X (σ i)`。 -/
theorem sprMonoAeval_pt_X_inl (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ) (i : Fin n) :
    sprMonoAeval (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))
        (MvPolynomial.X (Sum.inl i))
      = MvPolynomial.X (Sum.inl (σ i)) := by
  rw [sprMonoAeval_X_inl]

#print axioms sprMonoAeval_pt_X_inl

/-- `φ_{P_σ D}(y_ijk) = C (b_i · b_j⁻¹) · X (σ i, σ j, k)`（入口引理）。 -/
theorem sprMonoAeval_pt_X_inr (σ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ)
    (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    sprMonoAeval (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹))
        (MvPolynomial.X (Sum.inr (i, j, k)))
      = MvPolynomial.C ((b i : F) * ((b j : F))⁻¹) * MvPolynomial.X (Sum.inr (σ i, σ j, k)) := by
  rw [sprMonoAeval_X_inr, sprMonoCoeff_point]

#print axioms sprMonoAeval_pt_X_inr

end SprMonoPtEntrance

/-! ## §111 **单项共轭 `ψ_{P_σ D}`**（矩阵层）＋ 自然性

源文 `:363`（逐字）：

> "define `ψ_A : M_n(S') → M_n(S')` by setting `ψ_A(α) = A(M_n(φ_A)(α))A⁻¹`"

本节取 `A = P_σ D`（源文 `:428` 的 `A(σ)`）：

$$
ψ_{P_σ D}(α) = P_σ D · (α\text{ 逐项经 }φ_{P_σ D}) · D^{-1} P_σ^{-1},
$$

其中 `φ_{P_σ D}` 是 §108 的 `sprMonoAeval`，`P_σ` 是 §104 的 `sprPmat`。

**件**：
1. `sprPmat_map`：`P_σ` 的常值项沿任意 `φ` 不动（0/1 都在 `F` 里）——
   用 **`apply_ite`**（不是 `map_ite`：后者不存在），故**不经 `if` 实例**（R158）；
2. **`sprPsiMonoR`**：`ψ_{P_σ D}` 的通用形态（`R`／`xi`／`yv`／`σ`／`c` 全参数化）；
3. `sprPsiMonoR_apply`：展开式（`rfl`）；
4. ★★ **`sprPsiMonoR_comp`**：**矩阵层自然性**——
   `(ψ_R(α)).map φ = ψ_{R'}(α)`（`φ : R →ₐ[F] R'`）。四个 `Matrix.map_mul` 逐个披开，
   `sprPmat_map`／`sprDiagMatR_map`（§102）／`sprMonoAeval_comp`（§108）三件收口，
   外加单位逆元搬运 `hc`（`map_inv`）。

**为何这是关键件**：§103 的"`F` 无限"反证只需两样东西——**矩阵层自然性**与**点版**。
**按第 277 轮的战略决定（R159）**，点版**不再**经 `sprPermAlgEquiv ∘ sprDiagHom` 的桥，
而是**直接用 `sprPsiMonoR` 在 `R = S'`、`c = b⁻¹` 处定义** `N`-不变性假设；
故本节的自然性**就是**§103 收口所需的全部接口。

**射程（勿夸大）**：本节只有 `ψ_{P_σ D}` 的定义与自然性。
**`lem:14.23` 的两条陈述本体仍未证**；`lem:14.24/25`、`prop:14.19` 装配、
`ZEqNFixed` —— 全部未做。 -/

section SprPsiMonoSec



variable (F : Type) [Field F]
variable {r n : ℕ}

theorem sprPmat_map {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R') (σ : Equiv.Perm (Fin n)) :
    (sprPmat (n := n) R σ).map φ = sprPmat (n := n) R' σ := by
  refine Matrix.ext fun i j => ?_
  show φ (if i = σ j then (1 : R) else 0) = (if i = σ j then (1 : R') else 0)
  rw [apply_ite (⇑φ), map_one, map_zero]

#print axioms sprPmat_map

/-- 单项共轭 `ψ_{P_σ D}(α) = P_σ D · (α 经 φ) · D⁻¹ · P_σ⁻¹`。 -/
noncomputable def sprPsiMonoR (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) : Matrix (Fin n) (Fin n) R :=
  sprPmat (n := n) R σ * sprDiagMatR (n := n) R c * α.map (sprMonoAeval (F := F) (r := r) R xi yv σ c)
    * sprDiagMatR (n := n) R (fun i => (c i)⁻¹) * sprPmat (n := n) R σ⁻¹

#print axioms sprPsiMonoR

theorem sprPsiMonoR_apply (R : Type) [CommSemiring R] [Algebra F R]
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiMonoR (F := F) (r := r) R xi yv σ c α
      = sprPmat (n := n) R σ * sprDiagMatR (n := n) R c
        * α.map (sprMonoAeval (F := F) (r := r) R xi yv σ c)
        * sprDiagMatR (n := n) R (fun i => (c i)⁻¹) * sprPmat (n := n) R σ⁻¹ := rfl

#print axioms sprPsiMonoR_apply

theorem sprPsiMonoR_comp {R R' : Type} [CommSemiring R] [CommSemiring R']
    [Algebra F R] [Algebra F R'] (φ : R →ₐ[F] R')
    (xi : Fin n → R) (yv : YIdx r n → R) (σ : Equiv.Perm (Fin n)) (c : Fin n → Rˣ)
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    (sprPsiMonoR (F := F) (r := r) R xi yv σ c α).map φ
      = sprPsiMonoR (F := F) (r := r) R' (fun i => φ (xi i)) (fun ijk => φ (yv ijk)) σ
          (fun i => Units.map φ.toMonoidHom (c i)) α := by
  have hc : (fun i => Units.map φ.toMonoidHom ((c i)⁻¹))
      = fun i => (Units.map φ.toMonoidHom (c i))⁻¹ := by
    funext i
    rw [map_inv]
  have hmid : (α.map ⇑(sprMonoAeval (F := F) (r := r) R xi yv σ c)).map ⇑φ
      = α.map ⇑(φ.comp (sprMonoAeval (F := F) (r := r) R xi yv σ c)) := by
    rw [Matrix.map_map]
    rfl
  rw [sprPsiMonoR, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    sprPmat_map, sprDiagMatR_map, sprDiagMatR_map, hc, hmid, sprMonoAeval_comp,
    sprPmat_map, sprPsiMonoR]

#print axioms sprPsiMonoR_comp
end SprPsiMonoSec

/-! ## §112 **`lem:14.23` 的单项 generic 陈述**（`σ` 任意）—— 置换半的收口

源文 `:434`（逐字）：

> "The fact that `F` is infinite shows `ψ_{A(σ)}(α) = α` just as in Proposition 14.14."

`prop:14.14` 的论证有两根支柱：**参数空间**与**`F` 无限**。本节把 `σ` 任意时的两根都落实：

- **参数空间**：源文的 `η : T → F` 可取遍 `GL_n(F)`，因为那里的假设是 `α` 对**整个** `PGL_n(F)`
  不变；`lem:14.23` 的不变性只覆盖 `N = T ⋊ S_n`，故 `η` 只能落在**单项矩阵**
  `{P_σ D_b}` 上——这正是本节的 `hα`（对**所有** `σ` 与**所有** `b` 的参数化假设）。
  **核对文献**：见 [[proj-h2-literature-anchor-2026-10-19]]。
- **`F` 无限**：由 §100 的 `exists_map_ne_zero` 提供。

**证明骨架与 §103 逐句同构**（反设 ⟹ 取非零元 ⟹ `F`-点 ⟹ 矛盾），
差别只在用 §111 的 `sprPsiMonoR_comp`（矩阵层自然性）替代 §102 的对角版；
单位族仍由 §103 的 `sprDiagGenCoef_map_units` 与 `hun​it` 处置。

**★ R159 的兑现已见**：点版**没有**经过 `sprPermAlgEquiv ∘ sprDiagHom` 的桥——
`hα` 直接用 `sprPsiMonoR` 在 `R = S'`、`c = b⁻¹` 处陈述，
故整条证明**只需自然性**，不再需要任何形态修补（对比第 276–277 轮的四次失败）。

**射程（勿夸大）**：本节是 `lem:14.23` 的 **generic 陈述**。
其**第二陈述**（任意 `S'' ⊃ S'`、任意对角 `D'`）由特化得到，**尚未做**；
`lem:14.24/25`、`prop:14.19` 装配、`ZEqNFixed` —— **全部未做/未证**。 -/

section Lem1423MonoSec



variable (F : Type) [Field F]
variable {r n : ℕ}

/-- ★★★★★ **`lem:14.23` 的单项（`σ` 任意）generic 陈述**：`α` 若被**所有 `F`-点的
单项共轭** `ψ_{P_σ D_b}` 固定，则被**泛对角**的单项共轭 `ψ_{P_σ D_gen}` 固定。 -/
theorem sprPsiMono_generic_fixed [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (σ : Equiv.Perm (Fin n)) :
    sprPsiMonoR (F := F) (r := r) (MvPolynomial (SprIdx r n) (Ldiag F n))
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
        (sprDiagGenCoef (F := F) (r := r)) α
      = α.map (MvPolynomial.map (algebraMap F (Ldiag F n))) := by
  by_contra hEq
  set Rg := MvPolynomial (SprIdx r n) (Ldiag F n) with hRg
  set G : Matrix (Fin n) (Fin n) Rg :=
    sprPsiMonoR (F := F) (r := r) Rg
      (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
      (sprDiagGenCoef (F := F) (r := r)) α with hG
  set E : Matrix (Fin n) (Fin n) Rg :=
    α.map (MvPolynomial.map (algebraMap F (Ldiag F n))) with hE
  have hGE : G ≠ E := by rw [hG, hE]; exact hEq
  have hne : G - E ≠ 0 := sub_ne_zero.mpr hGE
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, (G - E) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by
      refine Matrix.ext fun i j => ?_
      rw [hcon i j, Matrix.zero_apply])
  obtain ⟨f, hf⟩ := exists_map_ne_zero F n hij
  have hphi : (⇑(sprCoeffMap (F := F) (r := r) (n := n) f)) = MvPolynomial.map f.toRingHom := rfl
  have hGmap : G.map (MvPolynomial.map f.toRingHom)
      = sprPsiMonoR (F := F) (r := r) (Spr F r n)
          (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) σ
          (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom
            (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i))) α := by
    rw [hG, ← hphi, sprPsiMonoR_comp (φ := sprCoeffMap (F := F) (r := r) (n := n) f)]
    simp only [sprCoeffMap_X, sprDiagGenCoef_map_units]
  have hEmap : E.map (MvPolynomial.map f.toRingHom) = α := by
    rw [hE, Matrix.map_map]
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    exact sprCoeffMap_map_algebraMap (F := F) (r := r) (n := n) f (α i j)
  set b : Fin n → Fˣ :=
    fun i => (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i))⁻¹ with hb
  have hunit : (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom
        (Units.map f.toMonoidHom (sprDiagGenUnit (F := F) i)))
      = fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹) := by
    funext i
    rw [hb]
    simp
  have hGalpha : G.map (MvPolynomial.map f.toRingHom) = α := by
    rw [hGmap, hunit, hα σ b]
  have hzero : (G - E).map (MvPolynomial.map f.toRingHom) = 0 := by
    rw [Matrix.map_sub (MvPolynomial.map f.toRingHom) (fun a b => map_sub _ _ _),
      hGalpha, hEmap, sub_self]
  have hcontra : (G - E).map (MvPolynomial.map f.toRingHom) i₀ j₀ ≠ 0 := by
    rw [Matrix.map_apply]
    exact hf
  rw [hzero] at hcontra
  exact hcontra (by rw [Matrix.zero_apply])

#print axioms sprPsiMono_generic_fixed
end Lem1423MonoSec

/-! ## §113 **特化映射 `S'[d] → S''`** —— `lem:14.23` 第二陈述的引擎（第 1 步）

源文 `lem:14.23` 的第二句（`:429` 后段，逐字）：

> "Suppose `S'' ⊃ S'` is a commutative ring containing `S'` and `D' ∈ GL_n(S'')` is a
> diagonal matrix. Set `A' = P_σ D'`. Then `ψ_{A'}(α) = α`."

源文 `:435`（逐字）："The second statement follows by **specialization** just as in
Proposition 14.14." 而 `prop:14.14` 的特化步（`:295`）是：

> "Define `η : T → S''` by letting `η(y_{ij})` be the `i,j` entry of `A`.
> The point is that `M_n(η)(Y) = A`. Applying this `η` to the equation `ψ_Y(α) = α`
> yields `ψ_A(α) = α`."

本节给这条特化的**载体**：把 `S'[d]`（＝ §100 的 `Rg`）映到任意 `S''` 的映射
`eval₂Hom lam (Sum.elim xi yv)`：

* **`sprSpecMap`**：系数沿 `lam : L →ₐ[F] S''`（即 `d_i ↦ D'_i` 处的那条：
  `IsLocalization.Away.liftAlgHom` 给），变量沿 `xi`／`yv`（即 `S'` 在 `S''` 里的像）；
* `sprSpecMap_X_inl`：变量取值。

**射程（勿夸大）**：本节**只有载体**。第二陈述本体（`sprPsiMono_specialize`）
**未证**——第 281 轮两处形态未过（`sprSpecAlg` 作为结构字面量不能被 `rw` 展开；
`eval₂Hom_C`／`eval₂Hom_map` 的**正确引理名未核**）。按 L47③ 停止，只落已证部分。
**下一轮做法**：① 先 `#check` 核 `MvPolynomial.eval₂Hom` 族的引理名
（`eval₂Hom_C`／`map_eval₂Hom` 之类）；② `sprSpecAlg` 的两个分支用 `show`＋`rfl`
（结构字面量的字段是 defeq 的）而不是 `rw`；③ 单位块的 `hcoe` 用 §109 已备的模式。

`lem:14.24/25`、`prop:14.19` 装配、`ZEqNFixed` —— **全部未做/未证**。 -/

section SprSpecSec

variable (F : Type) [Field F]
variable {r n : ℕ}



variable (F : Type) [Field F]
variable {r n : ℕ}

/-- 沿参数环 `L` 到目标环 `S''` 的特化映射 `S'[d] → S''`。 -/
noncomputable def sprSpecMap (S'' : Type) [CommRing S''] [Algebra F S'']
    (lam : Ldiag F n →ₐ[F] S'') (xi : Fin n → S'') (yv : YIdx r n → S'') :
    MvPolynomial (SprIdx r n) (Ldiag F n) →+* S'' :=
  MvPolynomial.eval₂Hom lam.toRingHom (Sum.elim xi yv)

#print axioms sprSpecMap

theorem sprSpecMap_X_inl (S'' : Type) [CommRing S''] [Algebra F S'']
    (lam : Ldiag F n →ₐ[F] S'') (xi : Fin n → S'') (yv : YIdx r n → S'') (i : Fin n) :
    sprSpecMap (F := F) (n := n) S'' lam xi yv
      (MvPolynomial.X (Sum.inl i) : MvPolynomial (SprIdx r n) (Ldiag F n)) = xi i := by
  rw [sprSpecMap, MvPolynomial.eval₂Hom_X']
  rfl

#print axioms sprSpecMap_X_inl
end SprSpecSec

/-! ## §114 **特化映射作为 `F`-代数同态** —— 第二陈述的第 2 步

§113 给了特化映射的**环同态**形态（`sprSpecMap`）。本节把它升成 **`F`-代数同态**
`sprSpecAlg`，这是 `sprPsiMonoR_comp`（§111，要求 `φ : R →ₐ[F] R'`）能消费的形态。

**构造**：`toRingHom := sprSpecMap`；`commutes'` 只需核 `C c` 的去向：
`eval₂ lam g (C (algebraMap F L c)) = lam (algebraMap F L c) = algebraMap F S'' c`
（`eval₂_C` ＋ `lam.commutes`）。

**射程（勿夸大）**：本节**只有 `sprSpecAlg` 本体**。它的一条**系数相容引理**
（`sprSpecAlg (map (algebraMap F L) a) = aeval (Sum.elim xi yv) a`）**本轮未过**：
`MvPolynomial.eval₂_map` 在本形态下 `rw` 找不到落点（试过实名参数 `(f := …) (φ := …)`，仍不过）。
按 **L47③** 停止。

**★ 下一轮的正确设计（本轮末尾已定，比修补更省）**：**改用 `L`-代数结构**。
把 `S''` 装备成 `L`-代数（`lam` 就是结构映射），于是
* `sprSpecAlg = MvPolynomial.aeval (Sum.elim xi yv)`（作为 `L`-代数同态），
* 系数相容引理**直接是 §101 用过的 `MvPolynomial.aeval_map_algebraMap`**
  （需 `[Algebra (Ldiag F n) S'']` 与 `IsScalarTower F (Ldiag F n) S''`），
* 最后用 `AlgHom.restrictScalars F` 回到 `F`-代数同态喂给 `sprPsiMonoR_comp`。
**理由**：`eval₂`／`eval₂Hom` 的 `rw` 落点是本轮第四次踩的同一坑；
**换表征（R142）比继续修 `rw` 便宜**，且 `aeval_map_algebraMap` 是**已机检可用**的现成引理。

`lem:14.24/25`、`prop:14.19` 装配、`ZEqNFixed` —— **全部未做/未证**。 -/

section SprSpecAlgSec

variable (F : Type) [Field F]
variable {r n : ℕ}

/-- 特化映射作为 `F`-代数同态（`sprPsiMonoR_comp` 的接口形态）。 -/
noncomputable def sprSpecAlg (S'' : Type) [CommRing S''] [Algebra F S'']
    (lam : Ldiag F n →ₐ[F] S'') (xi : Fin n → S'') (yv : YIdx r n → S'') :
    MvPolynomial (SprIdx r n) (Ldiag F n) →ₐ[F] S'' where
  toRingHom := sprSpecMap (F := F) (n := n) S'' lam xi yv
  commutes' c := by
    show MvPolynomial.eval₂ lam.toRingHom (Sum.elim xi yv)
      (MvPolynomial.C (algebraMap F (Ldiag F n) c)) = algebraMap F S'' c
    rw [MvPolynomial.eval₂_C]
    exact lam.commutes c

#print axioms sprSpecAlg

end SprSpecAlgSec

/-! ## §115 **`lem:14.23` 第二陈述（特化）机检** —— 置换半收尾

源文 `lem:14.23` 第二句（`:429` 后段，逐字）：

> "Suppose `S'' ⊃ S'` is a commutative ring containing `S'` and `D' ∈ GL_n(S'')` is a
> diagonal matrix. Set `A' = P_σ D'`. Then `ψ_{A'}(α) = α`."

源文 `:435`（逐字）："The second statement follows by **specialization** just as in
Proposition 14.14."

**形式化口径（一处诚实的偏离，必须写明）**：右端保持**沿 `Φ` 推前**的形态
`(α.map 系数扩张).map Φ`，而**不是** `α.map (aeval …)`。两者相等，但那条等式
（`sprSpecAlg (map (algebraMap F L) a) = aeval … a`）**四试不过**（`eval₂_map` 无落点，
见 §114 docstring）。按 **R159** 不再修桥：**该形态正是下游要用的**——
`lem:14.24` 里 `S''` 本来就带着 `S'`-代数结构（由同一个 `Φ` 给），故推前形态**够用**。

**证明**：§112 的 generic 恒等式沿 `Φ := sprSpecAlg S'' lam xi yv` 推前
（`congrArg` ＋ `sprPsiMonoR_comp`），再核三件事：
① `Φ (X (inl i)) = xi i`（§113 `sprSpecMap_X_inl`）；
② `Φ (X (inr ijk)) = yv ijk`（`eval₂Hom_X'`）；
③ `Units.map Φ (sprDiagGenCoef i) = d' i`（`eval₂Hom_C` ＋ 假设 `hlam`）。

**射程（勿夸大）**：`lem:14.23` 的**两条陈述**至此都有了机检形态。
但 `lem:14.24`（`thm:14.15` 的 `S'`-类似物）、`lem:14.25`、`prop:14.19` 装配、
`ZEqNFixed` —— **全部未做/未证**。 -/

section Lem1423SpecSec

variable (F : Type) [Field F]
variable {r n : ℕ}



variable (F : Type) [Field F]
variable {r n : ℕ}

/-- ★★ **`lem:14.23` 第二陈述（特化，右端保持沿 `Φ` 推前的形态）**：
`α` 若 `N`-不变，则对**任意** `S''`、**任意**对角 `d'`（只要 `d'` 是泛对角元沿 `lam` 的像），
`ψ_{P_σ D'}(α)` 等于 `α` 沿 `Φ` 的像。 -/
theorem sprPsiMono_specialize [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (σ : Equiv.Perm (Fin n))
    (S'' : Type) [CommRing S''] [Algebra F S'']
    (xi : Fin n → S'') (yv : YIdx r n → S'')
    (lam : Ldiag F n →ₐ[F] S'') (d' : Fin n → S''ˣ)
    (hlam : ∀ i, lam (↑((isUnit_algebraMap_X F n i).unit)) = ↑(d' i)) :
    sprPsiMonoR (F := F) (r := r) S'' xi yv σ d' α
      = (α.map (MvPolynomial.map (algebraMap F (Ldiag F n)))).map
          (sprSpecAlg (F := F) (r := r) (n := n) S'' lam xi yv) := by
  have hgen := sprPsiMono_generic_fixed (F := F) (r := r) α hα σ
  set Φ := sprSpecAlg (F := F) (r := r) (n := n) S'' lam xi yv with hΦ
  have hxi : (fun i => Φ (MvPolynomial.X (Sum.inl i) : MvPolynomial (SprIdx r n) (Ldiag F n)))
      = xi := by
    funext i
    exact sprSpecMap_X_inl (F := F) (n := n) S'' lam xi yv i
  have hyv : (fun ijk => Φ (MvPolynomial.X (Sum.inr ijk) : MvPolynomial (SprIdx r n) (Ldiag F n)))
      = yv := by
    funext ijk
    show MvPolynomial.eval₂Hom lam.toRingHom (Sum.elim xi yv)
      (MvPolynomial.X (Sum.inr ijk) : MvPolynomial (SprIdx r n) (Ldiag F n)) = yv ijk
    rw [MvPolynomial.eval₂Hom_X']
    rfl
  have hc : (fun i => Units.map Φ.toMonoidHom (sprDiagGenCoef (F := F) (r := r) i)) = d' := by
    funext i
    refine Units.ext ?_
    rw [Units.coe_map, sprDiagGenCoef, Units.coe_map, hΦ]
    show MvPolynomial.eval₂Hom lam.toRingHom (Sum.elim xi yv)
      (MvPolynomial.C (↑((isUnit_algebraMap_X F n i).unit))) = ↑(d' i)
    rw [MvPolynomial.eval₂Hom_C]
    exact hlam i
  have hmap := congrArg (fun M => M.map ⇑Φ) hgen
  simp only [sprPsiMonoR_comp, hxi, hyv, hc] at hmap
  exact hmap

#print axioms sprPsiMono_specialize
end Lem1423SpecSec

/-! ## §116 **`lem:14.24` 的粘合步（`S'`-世界）** —— 关键发现：重放 ≠ 必需

源文 `lem:14.24`（`:440`）只给了一个**提纲**（"Just as in Theorem 14.15…"），
其第 3 步的实质是：若 `θ₁` 保标准矩阵单位、`θ₂` 共轭后保标准矩阵单位，
则存在 `η₁ η₂ : S' →ₐ[F] T` 使 `θ₁ β = β.map η₁`、`A θ₂ β A⁻¹ = β.map η₂`。

**★ 交接件 v9／v10／v11 都把它估为"最重的未完成块（约 10 节重放）"。本轮实测推翻了这个估计。**

`thm1415_glue`／`exists_eta1_std`／`exists_eta2_conj` 看着是 `S`-专属的，但**它们的核心**——
`exists_algHom_of_preserves_stdMU`（`Procesi/MatrixUnits.lean:749`）——**对一般 `R`, `R'` 陈述**：

```
形如「`θ : Matrix n n R →ₐ[F] Matrix n n R'`，`hθ : θ (stdMU i j) = stdMU i j` ⟹
`∃ η : R →ₐ[F] R', ∀ β, θ β = β.map η`」——`R` 是**一般变量**。
```

故 `S`-世界的三条只是**包装**；`S'`-世界只需**换 `R` 再调一次**。
本节三条共约 60 行，**一次通过**（`sprEta1_std`／`sprEta2_conj`／`sprGlue`）。

**工艺（R160，本轮新得，价值高于这三条本身）**：
**"重放一节"之前，先 `grep` 该节的每条依赖，看谁是 `R`-通用的。**
若核心泛型、包装专属，则**重放 = 换参数实例化**（本轮的代价：60 行 vs 估计的 10 节）。
判别动作：看结论里被硬编码的变量是**在前提里**还是在**类型参数里**——
`exists_eta1_std` 的 `S F r n` 只在**结论的应用位置**出现，故它是包装而非实质。
这与 **L47（库内已有优先于自建）** 同族，但更精确：**库内已有的可能是"通用版"，
而"专属版"只是它的一个实例。**

**射程（勿夸大）**：本节只给 `lem:14.24` 的**粘合步（第 3 步）**。
`lem:14.24` 的其余步（局部化、`C` 生成对角环、幂等元论证、`A = P_σ A'`、
`θ₁' = θ₂' ψ_A`）**仍未做**；`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section SprGlueSec



variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `S'`-世界的 `η₁`：`θ₁` 保标准矩阵单位 ⟹ `θ₁ = M_n(η₁)`。 -/
theorem sprEta1_std [Nonempty (Fin n)]
    (θ₁ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ i j, θ₁ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)) :
    ∃ η₁ : Spr F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁ :=
  exists_algHom_of_preserves_stdMU (F := F) (R := Spr F r n) (R' := T) (n := Fin n) θ₁ h₁

#print axioms sprEta1_std

/-- `S'`-世界的 `η₂`：`θ₂^A = A θ₂ A⁻¹` 保标准矩阵单位 ⟹ `θ₂^A = M_n(η₂)`。 -/
theorem sprEta2_conj [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
        * (AT : Matrix (Fin n) (Fin n) T)) :
    ∃ η₂ : Spr F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
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
  exact exists_algHom_of_preserves_stdMU (F := F) (R := Spr F r n) (R' := T) (n := Fin n)
    ((conjAlgEquiv (F := F) AT).toAlgHom.comp θ₂) h₂A

#print axioms sprEta2_conj

/-- ★★★ **`lem:14.24` 的粘合步**（`thm:14.15` 的 `S'`-类似物，第 3 步）：
给定 `θ₁ θ₂` 与 `A` 使 `θ₁` 保标准单位、`θ₂` 共轭后保标准单位，产出 `η₁ η₂`。 -/
theorem sprGlue [Nonempty (Fin n)]
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (AT : (Matrix (Fin n) (Fin n) T)ˣ)
    (h₁ : ∀ i j, θ₁ (stdMU (n := Fin n) i j)
      = (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T))
    (h₂ : ∀ i j, θ₂ (stdMU (n := Fin n) i j)
      = (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (stdMU (n := Fin n) i j : Matrix (Fin n) (Fin n) T)
        * (AT : Matrix (Fin n) (Fin n) T)) :
    ∃ η₁ η₂ : Spr F r n →ₐ[F] T,
      (∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁) ∧
      (∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
        (AT : Matrix (Fin n) (Fin n) T) * θ₂ β
          * (((AT⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) = β.map η₂) := by
  obtain ⟨η₁, hη₁⟩ := sprEta1_std F r n T θ₁ h₁
  obtain ⟨η₂, hη₂⟩ := sprEta2_conj F r n T θ₂ AT h₂
  exact ⟨η₁, η₂, hη₁, hη₂⟩

#print axioms sprGlue
end SprGlueSec

/-! ## §117 **`lem:14.24` 的可用件清单（R160 系统施用）** ＋ `S'` 世界的矩阵单位系

§116 用 R160 发现"粘合步"只需实例化。本节把 R160 **系统施用**到 `lem:14.24` 的其余步：
逐条 `grep` 该步所需件，判断其**硬编码的环**出现在**类型参数**里还是只在**应用位置**上。

| `lem:14.24` 的步（源文 `:440`） | 现成件 | 通用性 |
|---|---|---|
| 局部化 ＋ `S''` 局部 | `thm1415_local`／`thm1415_general_nontrivial` | ✗ **`S`-专属**（用 `genericMatrix`／`psiA`），须重做 |
| `θ (e_ij)` 是矩阵单位系 | `IsMatrixUnitSystem` 判据＋**本节一条** | ✓ **逐字复制**（见下） |
| 局部环里共轭成标准单位 | `exists_unit_conj_stdMU_of_isLocalRing`（`MatrixUnits.lean:496`） | ✓ **完全通用**（`{T} [IsLocalRing T] {n} {g}`，一行不改） |
| `A θ β A⁻¹` 的共轭工具 | `conjAlgEquiv`／`mul_inv_conj_mul` | ✓ 通用 |
| 粘合出 `η₁ η₂` | §116 的 `sprGlue` | ✓ **本轮已做** |
| `C` 生成对角环（`Δ` 非零因子） | — | ✗ **须新建**（判别式论证） |
| 幂等元论证（`S''` 局部） | — | ✗ **须新建** |
| `A = P_σ A'` | — | ✗ 须新建（用幂等元论证 ＋ `P_σ` 代数 §104–§107） |
| `θ₁' = θ₂' ψ_A` 后收口 | §115 `sprPsiMono_specialize` ＋ §243 的 `sprPerm_sprDiagHom_comp` | ✓ 可复用 |

**结论**：`lem:14.24` 的重放**不是 10 节**——**9 步里有 5 步的件已就位**（其中 2 步"一行不改"），
只剩 **3 步须新建**：`C` 生成对角环（判别式）、幂等元论证、`A = P_σ A'`。
**下一轮入口** = 判别式那一步（源文 `:441`："the discriminant `η₁(Δ)` of `C` is nonzero,
an easy exercise shows that `C` generates, over `S''`, the ring `T'` of all diagonal matrices"）。

本节交付其中的 **1 条**（矩阵单位系，逐字复制即可）。

**射程（勿夸大）**：`lem:14.24` 的其余 3 步未做；`lem:14.25`、`prop:14.19` 装配、
`ZEqNFixed` —— 未做/未证。 -/

section SprMUInvSec

variable (F : Type) [Field F] (r n : ℕ) (T : Type) [CommRing T] [Algebra F T]

/-- `θ` 把 `stdMU` 送到矩阵单位系（`S'` 世界；`S` 版逐字复制，
证明只用到 `stdMU` 的乘法表与 `θ` 的同态性，**从不提及定义域环**）。 -/
lemma isMatrixUnitSystem_theta_stdMU_spr
    (θ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
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

#print axioms isMatrixUnitSystem_theta_stdMU_spr

end SprMUInvSec

/-! ## §118 **`lem:14.24` 步三的核**："与全部 `e_ii` 交换 ⟹ 对角"（不造桥）

源文 `:441`（逐字）：

> "Set `A' = P_σ^{-1} A`. Then `A' f_1(i,i) A'^{-1} = … = f_1(i,i)` for all `i`.
> As before, we conclude that `A'` is a **diagonal** matrix and we can write `A = P_σ A'`."

本节机检其中"as before"所指的那条代数事实：
`B · e_ii = e_ii · B`（∀`i`）⟹ `B` 是对角矩阵（`B = diagonal (fun i => B i i)`）。

**工艺（R159 第三次兑现，本轮定型）**：**不要造 `stdMU ↦ diagonal (Pi.single …)` 的桥**。
第 288–289 轮为这座桥试了 `simp`／四支穷举，均不过（`single_apply` 的 `j = a ∧ j = b`
与 `Pi.single` 的 `if` 互相缠）。**正解是根本不换形态**：

* `Matrix.mul_apply` 展开，得到两条和；
* LHS 的和用 `Finset.sum_eq_single j`（唯一贡献项 `k = j`）；
* RHS 的和用 `Finset.sum_eq_zero`（因 `i ≠ j`，条件 `j = i ∧ …` 恒假）；
* 收口只用 `Matrix.diagonal_apply_eq`／`diagonal_apply_ne`（**避开 `if`**，R158）。

**教训（已写进 `proj-lem1424-plan`）**：**下游要的是等式，不是指定形态**；
桥的代价全在"改写形态"上，**能算条目就不改写**。

**射程（勿夸大）**：本节只给"交换 ⟹ 对角"。`lem:14.24` 的步一／步二、局部化与收口
仍未做；`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section SprCommuteDiagSec

variable (F : Type) [Field F]



variable (F : Type) [Field F]

/-- 与全部 `stdMU i i` 交换 ⟹ 对角（`lem:14.24` 步三的核；**按条目直接算，不造桥**）。 -/
theorem sprCommute_diag {T : Type} [CommRing T] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) T)
    (h : ∀ i, B * stdMU (n := Fin n) (R := T) i i = stdMU (n := Fin n) (R := T) i i * B) :
    B = Matrix.diagonal (fun i => B i i) := by
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hc := congrFun (congrFun (h j) i) j
    rw [Matrix.mul_apply, Matrix.mul_apply] at hc
    rw [Finset.sum_eq_single j] at hc
    · rw [Finset.sum_eq_zero] at hc
      · simpa [stdMU, Matrix.single_apply] using hc
      · intro k _
        simp [stdMU, Matrix.single_apply, Ne.symm hij]
    · intro k _ hk
      simp [stdMU, Matrix.single_apply, Ne.symm hk]
    · intro hmem
      exact absurd (Finset.mem_univ j) hmem

#print axioms sprCommute_diag
end SprCommuteDiagSec

/-! ## §119 **`lem:14.24` 步三**：`A = P_σ · A'`（`A'` 对角）—— 拼装完成

源文 `:441`（逐字）：

> "Set `A' = P_σ^{-1} A`. Then `A' f_1(i,i) A'^{-1} = … = f_1(i,i)` for all `i`.
> As before, we conclude that `A'` is a **diagonal** matrix and we can write `A = P_σ A'`."

§118 已给"与全部 `e_ii` 交换 ⟹ 对角"（`sprCommute_diag`）。本节补**它前面那一步**：
把 `A'` 与 `e_ii` 的交换性算出来。源文的四步等号

`A' f_1(i,i) A'^{-1} = A' f_2(σ i,σ i) A'^{-1} = P_σ^{-1}(A f_2(σ i,σ i) A^{-1})P_σ
 = P_σ^{-1} f_1(σ i,σ i) P_σ = f_1(i,i)`

在 `f_1 = stdMU` 时就是本节的 `sprStepThree_assemble`：假设
`A e_ii A⁻¹ = e_{σi,σi}`，取 `A' = P_σ⁻¹ A`，则 `A' e_ii A'⁻¹ = e_ii`。

**两座桥按 R159 处理（`if` 只许出现在入口引理）**：
1. `sprPmat_mul_apply`／`sprPmat_mul_apply_right` 把 `P_σ M`／`M P_σ` 的**每个条目**
   写成 `M` 的条目（行／列置换），于是下游**一个 `if` 都不出现**；
2. `sprPmat_conj_stdMU` 是 `P_σ e_{ij} P_σ⁻¹ = e_{σi,σj}`。它的证明**不做 `if` 代数**：
   先用 `σ` 的满射把指标 `a,b` 换成 `σ a', σ b'`（`obtain ⟨a', rfl⟩`），
   此时 `σ⁻¹ (σ a')` 由 `simp` 归约，两侧都化成 `if i = a' ∧ j = b'`。
   **对比**：直接对 `i = σ⁻¹ a` 做 `if_congr` 需要处理 `Decidable` 实例的参数位置（R158），
   换指标后这一步整个消失。

**射程（勿夸大）**：本节只给 `lem:14.24` 的**步三拼装**。步一（判别式 ⟹ `C` 生成对角环）
与步二（局部环的幂等元论证）仍未做；局部化与收口、`lem:14.25`、`prop:14.19` 装配、
`ZEqNFixed` —— 未做/未证。 -/

section StepThree

variable {T : Type} [CommRing T] {n : ℕ}

/-- `(P_σ · M)_{ij} = M_{σ⁻¹(i), j}`（`P_σ` 是**行置换**；入口引理，消 `if`）。 -/
theorem sprPmat_mul_apply (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) T)
    (i j : Fin n) : (sprPmat T σ * M) i j = M (σ⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ⁻¹ i)]
  · simp [sprPmat_apply]
  · intro k _ hk
    have hne : ¬ (i = σ k) := by
      intro h
      exact hk ((Equiv.symm_apply_eq (e := σ) (x := i) (y := k)).mpr h).symm
    rw [sprPmat_apply, if_neg hne, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ (σ⁻¹ i)) hmem

#print axioms sprPmat_mul_apply

/-- `(M · P_τ)_{ij} = M_{i, τ(j)}`（`P_τ` 是**列置换**；入口引理，消 `if`）。 -/
theorem sprPmat_mul_apply_right (τ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) T)
    (i j : Fin n) : (M * sprPmat T τ) i j = M i (τ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ j)]
  · rw [sprPmat_apply, if_pos rfl, mul_one]
  · intro k _ hk
    rw [sprPmat_apply, if_neg hk, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ (τ j)) hmem

#print axioms sprPmat_mul_apply_right

/-- ★★ `P_σ · e_{ij} · P_σ⁻¹ = e_{σ i, σ j}`（`P_σ` 按 `σ` **重排矩阵单位**）。 -/
theorem sprPmat_conj_stdMU (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    sprPmat T σ * stdMU (n := Fin n) (R := T) i j * sprPmat T σ⁻¹
      = stdMU (n := Fin n) (R := T) (σ i) (σ j) := by
  refine Matrix.ext fun a b => ?_
  obtain ⟨a', rfl⟩ := σ.surjective a
  obtain ⟨b', rfl⟩ := σ.surjective b
  rw [Matrix.mul_assoc, sprPmat_mul_apply, sprPmat_mul_apply_right]
  simp [stdMU, Matrix.single_apply]

#print axioms sprPmat_conj_stdMU

/-- ★★★ **`lem:14.24` 步三的拼装**：若 `A · e_ii · A⁻¹ = e_{σi,σi}`（∀`i`），
则 `A = P_σ · A'`，其中 `A'` 是对角矩阵。

**证明**：取 `A' = P_σ⁻¹ A`。则
`A' e_ii A'⁻¹ = P_σ⁻¹ (A e_ii A⁻¹) P_σ = P_σ⁻¹ e_{σi,σi} P_σ = e_ii`
（末步用 `sprPmat_conj_stdMU` 取 `σ⁻¹`），故 `A' e_ii = e_ii A'`，
由 §118 的 `sprCommute_diag` 得 `A'` 对角；再 `A = P_σ (P_σ⁻¹ A)`。 -/
theorem sprStepThree_assemble (σ : Equiv.Perm (Fin n))
    (A : (Matrix (Fin n) (Fin n) T)ˣ)
    (hA : ∀ i, (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = stdMU (n := Fin n) (R := T) (σ i) (σ i)) :
    ∃ B : Matrix (Fin n) (Fin n) T,
      B = Matrix.diagonal (fun i => B i i) ∧
      (A : Matrix (Fin n) (Fin n) T) = sprPmat T σ * B := by
  refine ⟨sprPmat T σ⁻¹ * (A : Matrix (Fin n) (Fin n) T), ?_, ?_⟩
  · have hAinv : (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
        * (A : Matrix (Fin n) (Fin n) T) = 1 := by
      simp
    have hPA' : ∀ i, (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
        = stdMU (n := Fin n) (R := T) (σ i) (σ i) * (A : Matrix (Fin n) (Fin n) T) := by
      intro i
      calc (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
          = ((A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i) * 1 :=
              (mul_one _).symm
        _ = ((A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i)
              * ((((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
                * (A : Matrix (Fin n) (Fin n) T)) := by rw [hAinv]
        _ = (((A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i)
              * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T))
              * (A : Matrix (Fin n) (Fin n) T) := by simp only [Matrix.mul_assoc]
        _ = stdMU (n := Fin n) (R := T) (σ i) (σ i) * (A : Matrix (Fin n) (Fin n) T) := by
              rw [hA i]
    have hPconj : ∀ i, sprPmat T σ⁻¹ * stdMU (n := Fin n) (R := T) (σ i) (σ i)
        = stdMU (n := Fin n) (R := T) i i * sprPmat T σ⁻¹ := by
      intro i
      have h : sprPmat T σ⁻¹ * stdMU (n := Fin n) (R := T) (σ i) (σ i)
          * sprPmat T σ = stdMU (n := Fin n) (R := T) i i := by
        simpa using sprPmat_conj_stdMU (T := T) (σ := σ⁻¹) (i := σ i) (j := σ i)
      calc sprPmat T σ⁻¹ * stdMU (n := Fin n) (R := T) (σ i) (σ i)
          = (sprPmat T σ⁻¹ * stdMU (n := Fin n) (R := T) (σ i) (σ i)
              * sprPmat T σ) * sprPmat T σ⁻¹ := by
              rw [Matrix.mul_assoc, sprPmat_mul_symm, mul_one]
        _ = stdMU (n := Fin n) (R := T) i i * sprPmat T σ⁻¹ := by rw [h]
    refine sprCommute_diag (sprPmat T σ⁻¹ * (A : Matrix (Fin n) (Fin n) T)) (fun i => ?_)
    calc (sprPmat T σ⁻¹ * (A : Matrix (Fin n) (Fin n) T))
          * stdMU (n := Fin n) (R := T) i i
        = sprPmat T σ⁻¹ * ((A : Matrix (Fin n) (Fin n) T)
            * stdMU (n := Fin n) (R := T) i i) := by rw [Matrix.mul_assoc]
      _ = sprPmat T σ⁻¹ * (stdMU (n := Fin n) (R := T) (σ i) (σ i)
            * (A : Matrix (Fin n) (Fin n) T)) := by rw [hPA' i]
      _ = (sprPmat T σ⁻¹ * stdMU (n := Fin n) (R := T) (σ i) (σ i))
            * (A : Matrix (Fin n) (Fin n) T) := by rw [Matrix.mul_assoc]
      _ = (stdMU (n := Fin n) (R := T) i i * sprPmat T σ⁻¹)
            * (A : Matrix (Fin n) (Fin n) T) := by rw [hPconj i]
      _ = stdMU (n := Fin n) (R := T) i i
            * (sprPmat T σ⁻¹ * (A : Matrix (Fin n) (Fin n) T)) := by
            rw [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, sprPmat_mul_symm, Matrix.one_mul]

#print axioms sprStepThree_assemble

end StepThree

/-! ## §120 **`lem:14.24` 步一**：与 `C = diagonal c` 交换 ⟹ 对角（判别式的**直接**用法）

源文 `:440`（逐字）：

> "Since the discriminant `η_1(Δ)` of `C` is nonzero, an easy exercise shows that `C`
> generates, over `S''`, the ring `T'` of all diagonal matrices in `M_n(S'')`.
> Also, the `f_2(i,i)` commute with `C` because `e(i,i)` commutes with `X`.
> Thus `f_2(i,i) ∈ T'`."

**★ 本轮砍掉了 Lagrange 幂等元（诚实记录）**：`proj-lem1424-plan` §2 把这一步估为
80–150 行（"须建 `∏_{j≠i}` 的 Lagrange 幂等元"）。但**下游只需 `f_2(i,i)` 是对角矩阵**，
而这一条**不需要** "`C` 生成 `T'`"：

$$
B\,C = C\,B,\ C = \mathrm{diagonal}(c),\ c_j - c_i \text{ 可逆}\
\implies B_{ij}(c_j-c_i) = (BC)_{ij} - (CB)_{ij} = 0 \implies B_{ij} = 0\ (i \ne j).
$$

即"与 `C` 交换 ⟹ 对角"，**逐项一步**（`Matrix.mul_diagonal` ＋ `Matrix.diagonal_mul`
＋ `IsUnit.mul_right_cancel`）。Lagrange 幂等元是源文"easy exercise"的原件，
但**本战役不使用**，故按奥卡姆剃刀**不入库**（拟建版本实测卡在
`Finset.prod` 需要 `CommMonoid` 而矩阵环非交换；正解是乘法留在 `Fin n → T` 里，
但那正是**下游不用**的东西）。

**射程（勿夸大）**：本节只给"交换 ⟹ 对角"。步二（局部环幂等元论证 ⟹ 存在 `σ`）
仍未做；局部化与收口、`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section StepOne

variable {T : Type} [CommRing T] {n : ℕ}

/-- ★★★ **`lem:14.24` 步一（直接形态）**：与对角矩阵 `diagonal c` 交换的矩阵是对角的，
只要 `c` 的**差皆可逆**（判别式 `∏_{i<j}(c_i − c_j)` 可逆的直接后果）。

**证明**：逐项 `B_{ij}·c_j = c_i·B_{ij}` ⟹ `B_{ij}·(c_j − c_i) = 0`；`c_j − c_i` 可逆 ⟹ `B_{ij} = 0`。 -/
theorem sprCommute_diag_of_isUnit_sub (c : Fin n → T) (B : Matrix (Fin n) (Fin n) T)
    (hc : ∀ i j, i ≠ j → IsUnit (c j - c i))
    (h : B * Matrix.diagonal c = Matrix.diagonal c * B) :
    B = Matrix.diagonal (fun i => B i i) := by
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have hentry : B i j * c j = c i * B i j := by
      have h' := congrFun (congrFun h i) j
      rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h'
    have hzero : B i j * (c j - c i) = 0 := by
      rw [mul_sub, hentry, mul_comm (B i j) (c i), sub_self]
    obtain ⟨u, hu⟩ := hc i j hij
    have hunit : IsUnit ((u : Tˣ) : T) := by rw [hu]; exact hc i j hij
    have h2 : B i j * ((u : Tˣ) : T) = 0 := by rw [hu]; exact hzero
    exact IsUnit.mul_right_cancel hunit (by rw [h2, zero_mul])

#print axioms sprCommute_diag_of_isUnit_sub

/-- 变体：假设写成 `c i − c j` 可逆（与判别式 `∏_{i<j}(c_i − c_j)` 同向）。 -/
theorem sprCommute_diag_of_isUnit_sub' (c : Fin n → T) (B : Matrix (Fin n) (Fin n) T)
    (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (h : B * Matrix.diagonal c = Matrix.diagonal c * B) :
    B = Matrix.diagonal (fun i => B i i) := by
  refine sprCommute_diag_of_isUnit_sub c B (fun i j hij => ?_) h
  have h' : c j - c i = -(c i - c j) := by ring
  rw [h']
  exact (hc i j hij).neg

#print axioms sprCommute_diag_of_isUnit_sub'

end StepOne

/-! ## §121 **`lem:14.24` 步二**：局部环的幂等元论证 ⟹ 存在置换 `σ`

源文 `:441`（逐字）：

> "`S''` is a local ring and so has no nontrivial idempotents. It follows that the only
> idempotents of `T'` are the `f_1(i,i)`. Thus there is a `σ ∈ S_n` such that
> `f_2(σ(i),σ(i)) = f_1(i,i)` for all `i`."

本节把源文的三句话逐句落地为 `sprExistsPerm_of_diagIdem`（见其 docstring 的五步证明）。
三条辅助件：`sprIdem_eq_zero_or_one`（局部环的幂等元只有 `0,1`）、
`sprDiag_single`（`diagonal (if · = j then 1 else 0) = e_jj`）、`sprDiag_sum`（`diagonal` 保有限和）。

**★ `f_2(i,i) ≠ 0` 是必要前提（本轮勘出，须登记）**：源文没提，但**没有它 `σ` 未必是置换**
—— 若某 `f_2(i,i) = 0`，则 `n` 列只有 `< n` 个非零行，"唯一 `1`"的映照 `k ↦ i_k` 不是满射。
它来自 **`θ_2` 非零即单**（`M_n(S')` 是单环），属**收口层**（`θ_2` 的具体形态），
故本节把它作为**显式假设** `hne : ∀ i, F i ≠ 0` 登记——**不得**把它当"显然"。

**工艺**：`finite ⟹ 满射即单` 用 `Finite.injective_iff_surjective`；
`Equiv.ofBijective` 造置换；`Matrix.diagonal_single`（mathlib 已有！）本可省掉
`sprDiag_single`，但后者给的是 `if` 形态（下游 `v (σ i) k = if k = i then 1 else 0` 直接落这里），
故保留。

**射程（勿夸大）**：本节只给"存在 `σ`"。局部化与收口（`η₁ η₂`、`θ_1' = θ_2' ψ_A`）、
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section StepTwo

variable {T : Type} [CommRing T] {n : ℕ}

/-- 局部环中的幂等元只有 `0` 与 `1`（`IsLocalRing.isUnit_or_isUnit_one_sub_self`）。 -/
theorem sprIdem_eq_zero_or_one [IsLocalRing T] {x : T} (h : x * x = x) :
    x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hx | hx
  · right
    exact IsUnit.mul_left_cancel hx (by rw [h, mul_one])
  · left
    refine IsUnit.mul_right_cancel hx ?_
    rw [mul_sub, mul_one, h, sub_self, zero_mul]

#print axioms sprIdem_eq_zero_or_one

/-- `diagonal (if · = j then 1 else 0) = e_jj`（R159 的桥；本节唯一需要它的地方）。 -/
theorem sprDiag_single (j : Fin n) :
    Matrix.diagonal (fun k => if k = j then (1 : T) else 0)
      = stdMU (n := Fin n) (R := T) j j := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.diagonal_apply, stdMU, Matrix.single_apply]
  by_cases ha : a = j
  · rw [ha]; simp
  · rw [if_neg ha]; simp [Ne.symm ha]

#print axioms sprDiag_single

/-- `diagonal` 保有限和（`Matrix.diagonalRingHom` 的 `map_sum`）。 -/
theorem sprDiag_sum (v : Fin n → Fin n → T) :
    (∑ i, Matrix.diagonal (v i)) = Matrix.diagonal (∑ i, v i) :=
  (map_sum (Matrix.diagonalRingHom (Fin n) T) v Finset.univ).symm

#print axioms sprDiag_sum

/-- ★★★ **`lem:14.24` 步二**：`T` 局部、`F` 是一族**对角**的**正交幂等元**、和为 `1`、
每个非零 ⟹ 存在置换 `σ` 使 `F (σ i) = e_ii`。

**证明（源文三句的逐句落地）**：
1. `F i = diagonal (v i)`（`v i k = F i k k`），故 `v i k * v i k = v i k`、`v i k * v j k = 0`（`i ≠ j`）；
2. **局部环** ⟹ 每个 `v i k ∈ {0,1}`（`sprIdem_eq_zero_or_one`）；
3. `∑ i, v i = 1`（逐列）⟹ 每列**恰有一个** `1`（至少一个：否则和为 `0`；
   至多一个：两个 `1` 的积为 `0` 又为 `1`）⟹ 定义 `σ k :=` 该列的那个 `i`；
4. `σ` **满**射（若 `i` 不在像中则 `v i = 0`，与 `F i ≠ 0` 矛盾）⟹ `Fin n` 有限故 `σ` 是置换；
5. `v (σ i) k = if k = i then 1 else 0` ⟹ `F (σ i) = diagonal (if · = i then 1 else 0) = e_ii`。 -/
theorem sprExistsPerm_of_diagIdem [IsLocalRing T]
    (F : Fin n → Matrix (Fin n) (Fin n) T)
    (hdiag : ∀ i, F i = Matrix.diagonal (fun k => F i k k))
    (hidem : ∀ i, F i * F i = F i)
    (horth : ∀ i j, i ≠ j → F i * F j = 0)
    (hsum : ∑ i, F i = 1)
    (hne : ∀ i, F i ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, F (σ i) = stdMU (n := Fin n) (R := T) i i := by
  classical
  set v : Fin n → Fin n → T := fun i k => F i k k with hv
  have hFv : ∀ i, F i = Matrix.diagonal (v i) := fun i => hdiag i
  have hidem_v : ∀ i, v i * v i = v i := by
    intro i
    have h := hidem i
    rw [hFv i, Matrix.diagonal_mul_diagonal] at h
    exact Matrix.diagonal_injective h
  have horth_v : ∀ i j, i ≠ j → v i * v j = 0 := by
    intro i j hij
    have h := horth i j hij
    rw [hFv i, hFv j, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero] at h
    exact Matrix.diagonal_injective h
  have h01 : ∀ i k, v i k = 0 ∨ v i k = 1 := fun i k =>
    sprIdem_eq_zero_or_one (congrFun (hidem_v i) k)
  have hsum_v : (∑ i, v i) = (1 : Fin n → T) := by
    refine Matrix.diagonal_injective ?_
    calc Matrix.diagonal (∑ i, v i) = ∑ i, Matrix.diagonal (v i) := (sprDiag_sum v).symm
      _ = ∑ i, F i := Finset.sum_congr rfl (fun i _ => (hFv i).symm)
      _ = 1 := hsum
      _ = Matrix.diagonal (1 : Fin n → T) :=
            (Matrix.diagonal_one (n := Fin n) (α := T)).symm
  have hcol : ∀ k, ∃! i, v i k = 1 := by
    intro k
    have hk : ∑ i, v i k = 1 := by
      simpa [Finset.sum_apply] using congrFun hsum_v k
    have hex : ∃ i, v i k = 1 := by
      by_contra hcon
      have hzero : ∀ i, v i k = 0 := by
        intro i
        rcases h01 i k with h0 | h1
        · exact h0
        · exact absurd ⟨i, h1⟩ hcon
      have h0sum : (∑ i, v i k) = 0 := Finset.sum_eq_zero (fun i _ => hzero i)
      rw [h0sum] at hk
      exact zero_ne_one hk
    obtain ⟨i₀, hi₀⟩ := hex
    refine ⟨i₀, hi₀, fun j hj => ?_⟩
    by_contra hne'
    have hz : v i₀ k * v j k = 0 := congrFun (horth_v i₀ j (fun hh => hne' hh.symm)) k
    rw [hi₀, hj, one_mul] at hz
    exact one_ne_zero hz
  let σ : Fin n → Fin n := fun k => (hcol k).choose
  have hσ : ∀ k, v (σ k) k = 1 := fun k => (hcol k).choose_spec.1
  have hσu : ∀ k i, v i k = 1 → i = σ k := fun k i hi => (hcol k).choose_spec.2 i hi
  have hveq : ∀ i k, v i k = if i = σ k then (1 : T) else 0 := by
    intro i k
    by_cases h : i = σ k
    · rw [if_pos h, h]
      exact hσ k
    · rw [if_neg h]
      rcases h01 i k with h0 | h1
      · exact h0
      · exact absurd (hσu k i h1) h
  have hsurj : Function.Surjective σ := by
    intro i
    by_contra hcon
    have hzero : v i = 0 := by
      funext k
      rcases h01 i k with h0 | h1
      · exact h0
      · exact absurd ⟨k, (hσu k i h1).symm⟩ hcon
    have hFi : F i = 0 := by
      rw [hFv i, hzero]
      simp
    exact hne i hFi
  have hinj : Function.Injective σ := Finite.injective_iff_surjective.mpr hsurj
  let σe : Equiv.Perm (Fin n) := Equiv.ofBijective σ ⟨hinj, hsurj⟩
  refine ⟨σe, fun i => ?_⟩
  have hσe : ∀ k, σe k = σ k := fun _ => rfl
  have key : F (σe i) = Matrix.diagonal (fun k => if k = i then (1 : T) else 0) := by
    rw [hFv (σe i)]
    congr 1
    funext k
    rw [hveq (σe i) k, hσe i]
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hk, if_neg]
      intro h
      exact hk (hinj h).symm
  rw [key, sprDiag_single]

#print axioms sprExistsPerm_of_diagIdem

end StepTwo

/-! ## §122 **`lem:14.24` 步三的单位形态**（`A = P_σ · D_c`，`c : Fin n → Tˣ`）

§119 只给 `A = P_σ · B`（`B` 对角矩阵）。**收口层要的是 `B = D_c`（对角元为 `Tˣ`）**——
因为 `lem:14.23` 的 `ψ` 族 `sprPsiMonoR`（§111）以 `(σ, c : Fin n → Tˣ)` 参数化。
本节补这条接口：`A` 可逆 ＋ 对角 ⟹ 对角元可逆。

**件**：
1. `sprDiag_isUnit_entries`：`[CommRing T]`、`IsUnit (diagonal b)` ⟹ 每个 `b i` 可逆
   （逆元显式取 `(B⁻¹) i i`，两条乘式由 `Matrix.diagonal_mul`／`mul_diagonal` 给出）；
2. `sprExistsDiagUnits`：`diagonal b = sprDiagMatR T c`（`c : Fin n → Tˣ`）——
   **`sprDiagMatR` 的定义就是 `diagonal (↑c)`**，故收口是 `rfl`；
3. `sprPmatUnit`：`P_σ` 作为 `(M_n(T))ˣ`（`sprPmat_mul_symm`／`sprPmat_symm_mul` 打包）；
4. ★★★ `sprStepThree_units`：`A e_ii A⁻¹ = e_{σi,σi}`（∀`i`）＋ `A` 可逆 ⟹ `A = P_σ · D_c`。

**工艺**：`B` 的单位性不靠"对角元逐个证"而靠**结构化**：`B = (P_σ)⁻¹ · A`（由 `hAeq` 反转），
是单位的积；再用 2 得到 `c`。**单位性的两个方向**（`b i * inv = 1` 与 `inv * b i = 1`）
都必须给，`IsUnit` 在本形态下要 `isUnit_iff_exists` 的双侧形式。

**射程（勿夸大）**：本节是**接口**。`lem:14.24` 的**收口层**（`θ_1' = θ_2' ψ_A` 的
"same calculation"）**仍未做**；`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section StepThreeUnits

variable {T : Type} [CommRing T] {n : ℕ}

/-- ★ **对角且可逆 ⟹ 每个对角元可逆**（逆元显式：`(B⁻¹) i i`）。 -/
theorem sprDiag_isUnit_entries (b : Fin n → T) (hunit : IsUnit (Matrix.diagonal b))
    (i : Fin n) : IsUnit (b i) := by
  obtain ⟨u, hu⟩ := hunit
  have hmul : ((u : Matrix (Fin n) (Fin n) T))
      * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) = 1 :=
    Units.mul_inv u
  rw [hu] at hmul
  have hmul' : (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      * ((u : Matrix (Fin n) (Fin n) T)) = 1 :=
    Units.inv_mul u
  rw [hu] at hmul'
  have h1 : b i * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) i i = 1 := by
    have h := congrFun (congrFun hmul i) i
    rwa [Matrix.diagonal_mul, Matrix.one_apply_eq] at h
  have h2 : (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) i i * b i = 1 := by
    have h := congrFun (congrFun hmul' i) i
    rwa [Matrix.mul_diagonal, Matrix.one_apply_eq] at h
  exact isUnit_iff_exists.mpr
    ⟨((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) i i, h1, h2⟩

#print axioms sprDiag_isUnit_entries

/-- ★★ **对角可逆矩阵 ＝ `D_c`（`c : Fin n → Tˣ`）** —— 收口层用 `sprPsiMonoR` 的接口形态。 -/
theorem sprExistsDiagUnits (b : Fin n → T) (hunit : IsUnit (Matrix.diagonal b)) :
    ∃ c : Fin n → Tˣ, Matrix.diagonal b = sprDiagMatR (n := n) T c := by
  obtain ⟨u, hu⟩ := hunit
  have hmul : ((u : Matrix (Fin n) (Fin n) T))
      * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) = 1 :=
    Units.mul_inv u
  rw [hu] at hmul
  have hmul' : (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      * ((u : Matrix (Fin n) (Fin n) T)) = 1 :=
    Units.inv_mul u
  rw [hu] at hmul'
  have h1 : ∀ i, b i * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) i i
      = 1 := by
    intro i
    have h := congrFun (congrFun hmul i) i
    rwa [Matrix.diagonal_mul, Matrix.one_apply_eq] at h
  have h2 : ∀ i, (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) i i * b i
      = 1 := by
    intro i
    have h := congrFun (congrFun hmul' i) i
    rwa [Matrix.mul_diagonal, Matrix.one_apply_eq] at h
  exact ⟨fun i => ⟨b i, _, h1 i, h2 i⟩, rfl⟩

#print axioms sprExistsDiagUnits

/-- `P_σ` 作为**单位**（`sprPmat_mul_symm`／`sprPmat_symm_mul` 打包）。 -/
noncomputable def sprPmatUnit (R : Type) [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Matrix (Fin n) (Fin n) R)ˣ where
  val := sprPmat R σ
  inv := sprPmat (n := n) R σ⁻¹
  val_inv := sprPmat_mul_symm R σ
  inv_val := sprPmat_symm_mul R σ

#print axioms sprPmatUnit

/-- ★★★ **`lem:14.24` 步三（单位形态）**：`A · e_ii · A⁻¹ = e_{σi,σi}`（∀`i`）、`A` 可逆
⟹ `A = P_σ · D_c`，其中 `c : Fin n → Tˣ`。

**用途**：收口层的 `ψ_A`（`sprPsiMonoR`）正是以 `(σ, c)` 参数化的，故这条是
`lem:14.23` 与步三之间的**唯一接口**。 -/
theorem sprStepThree_units (σ : Equiv.Perm (Fin n)) (A : (Matrix (Fin n) (Fin n) T)ˣ)
    (hA : ∀ i, (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = stdMU (n := Fin n) (R := T) (σ i) (σ i)) :
    ∃ c : Fin n → Tˣ, (A : Matrix (Fin n) (Fin n) T) = sprPmat T σ * sprDiagMatR (n := n) T c := by
  obtain ⟨B, hdiag, hAeq⟩ := sprStepThree_assemble σ A hA
  have hB : B = (((sprPmatUnit T σ)⁻¹ * A : (Matrix (Fin n) (Fin n) T)ˣ) :
      Matrix (Fin n) (Fin n) T) := by
    show B = (sprPmat (n := n) T σ⁻¹) * (A : Matrix (Fin n) (Fin n) T)
    rw [hAeq, ← Matrix.mul_assoc, sprPmat_symm_mul, Matrix.one_mul]
  have hunitB : IsUnit B := by
    rw [hB]
    exact ⟨((sprPmatUnit T σ)⁻¹ * A : (Matrix (Fin n) (Fin n) T)ˣ), rfl⟩
  have hunitD : IsUnit (Matrix.diagonal (fun i => B i i)) := by
    rw [← hdiag]
    exact hunitB
  obtain ⟨c, hc⟩ := sprExistsDiagUnits (n := n) (T := T) (fun i => B i i) hunitD
  exact ⟨c, by rw [hAeq, hdiag, hc]⟩

#print axioms sprStepThree_units

end StepThreeUnits

/-! ## §123 **源文 `:442` 的 "same calculation"** —— 收口层的最后一块数学内容

源文（`:442`，逐字）：

> "The same calculation as in Theorem 14.15 shows that `θ_1' = θ_2' ψ_A`
> and Lemma 14.24 follows from Lemma 14.23."

本节把这条"same calculation"**落到生成元并打包**：设 `A = P_σ D_c`、`θ_1 β = β.map η_1`、
`A θ_2 β A⁻¹ = β.map η_2`，且 `θ_1, θ_2` 在 `R(F,n,r)` 上一致，则

$$
η_1 = \mathrm{sprMonoAeval}\ T\ ξ\ υ\ σ\ c,\qquad
ξ = η_2 ∘ x_{\cdot},\quad υ = η_2 ∘ y_{\cdot},
$$

即 `η_1(x_ii) = η_2(x_{σi,σi})`、`η_1(y_ijk) = c_i^{-1} c_j · η_2(y_{σi,σj,k})`。
**数学来源**：`C = Σ c_ii e_ii = Σ d_ii f_2(i,i)` 与 `C_k = Σ c_ijk e_ij = Σ d_ijk f_2(i,j)`
比较系数（`A e_ij A⁻¹ = (c_i/c_j) e_{σi,σj}`）。

**件（10 条）**：
1. `sprUnits_conj_cancel`／`sprUnits_solve`：交换环里单位共轭与"解单位方程"；
2. ★ `sprPmat_sandwich`：`(P_σ M P_σ⁻¹)_{ij} = M_{σ⁻¹ i, σ⁻¹ j}`（§119 两条入口引理的合成）；
3. ★ `sprDiag_sandwich`：`(D_c M D_c⁻¹)_{ij} = c_i M_{ij} c_j⁻¹`；
4. ★★ `sprMonoS_apply`：`(A M A⁻¹)_{ij}`（`A = P_σ D_c`）的**完整逐项式**；
5. `sprXdiag_map`／`sprYmat_map_apply`：`xdiag`／`ymat` 沿 `η` 的像；
6. ★★ `sprSameCalc_x`／`sprSameCalc_y`：两个生成元族上的恒等式；
7. ★★★★ `sprSameCalc`：**打包形态 `η_1 = μ`**——正是收口层要的接口。

**工艺（两条）**：
* **R159 又一次兑现**：`sprMonoS_apply` 不逐项展开 `Finset.sum`，而是**把 5 重积按
  `mul_assoc` 重排成 `P_σ · (D_c M D_c⁻¹) · P_σ⁻¹`**，再各用一条 3 重积的 sandwich——
  5 重积的 `rw` 落点问题就此消失（`h1` 由 `simp only [Matrix.mul_assoc]` 一次给出）。
* **`Equiv.symm_apply_apply` 在 `MvPolynomial.X` 的参数里 `rw` 打不进**，但 `simp only` 能；
  故用 `have hentry := …; simp only [...] at hentry; simpa using hentry`——
  **`simpa` 收尾比 `rw` 稳**（本 pin 的 `Matrix`-当函数显示的已知怪癖）。

**射程（勿夸大）**：本节给的是"same calculation"的**生成元恒等式**。收口层还差
**组装**：`sprPsiMono_specialize`（§115）＋本节 `sprSameCalc` ＋ `sprGlue`（§116）
拼成 `θ_1(α) = θ_2(α)`；`lem:14.24` 的**陈述本身**（`S''`／`θ₁ θ₂`／`Δ`）尚未写出。
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section SameCalc

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `↑u * x * ↑u⁻¹ = x`（交换环里单位共轭是恒等）。 -/
theorem sprUnits_conj_cancel (u : Tˣ) (x : T) :
    ((u : Tˣ) : T) * x * (((u⁻¹ : Tˣ)) : T) = x := by
  rw [mul_comm ((u : Tˣ) : T) x, mul_assoc]
  simp

#print axioms sprUnits_conj_cancel

/-- 解 `↑u · (M · ↑v⁻¹) = R` 得 `M = ↑u⁻¹ · R · ↑v`（两个单位不同的情形）。 -/
theorem sprUnits_solve (u v : Tˣ) (M R : T)
    (h : ((u : Tˣ) : T) * (M * (((v⁻¹ : Tˣ)) : T)) = R) :
    M = (((u⁻¹ : Tˣ)) : T) * R * ((v : Tˣ) : T) := by
  have hu : (((u⁻¹ : Tˣ)) : T) * ((u : Tˣ) : T) = 1 := by simp
  have hv : (((v⁻¹ : Tˣ)) : T) * ((v : Tˣ) : T) = 1 := by simp
  have h1 : (((u⁻¹ : Tˣ)) : T) * R = M * (((v⁻¹ : Tˣ)) : T) := by
    rw [← h, ← mul_assoc, hu, one_mul]
  calc M = M * 1 := (mul_one M).symm
    _ = M * ((((v⁻¹ : Tˣ)) : T) * ((v : Tˣ) : T)) := by rw [hv]
    _ = (M * (((v⁻¹ : Tˣ)) : T)) * ((v : Tˣ) : T) := by rw [mul_assoc]
    _ = ((((u⁻¹ : Tˣ)) : T) * R) * ((v : Tˣ) : T) := by rw [h1]
    _ = (((u⁻¹ : Tˣ)) : T) * R * ((v : Tˣ) : T) := by rw [mul_assoc]

#print axioms sprUnits_solve

/-- ★★ `(P_σ · M · P_σ⁻¹)_{ij} = M_{σ⁻¹ i, σ⁻¹ j}`（§119 两条入口引理的合成）。 -/
theorem sprPmat_sandwich (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) T)
    (i j : Fin n) :
    (sprPmat (n := n) T σ * M * sprPmat (n := n) T σ⁻¹) i j = M (σ⁻¹ i) (σ⁻¹ j) := by
  rw [Matrix.mul_assoc, sprPmat_mul_apply, sprPmat_mul_apply_right]

#print axioms sprPmat_sandwich

/-- ★★ `(D_c · M · D_c⁻¹)_{ij} = c_i · M_{ij} · c_j⁻¹`（对角的共轭）。 -/
theorem sprDiag_sandwich (c : Fin n → Tˣ) (M : Matrix (Fin n) (Fin n) T)
    (i j : Fin n) :
    (sprDiagMatR (n := n) T c * M * sprDiagMatR (n := n) T (fun i => (c i)⁻¹)) i j
      = (((c i : Tˣ)) : T) * M i j * ((((c j)⁻¹ : Tˣ)) : T) := by
  simp only [sprDiagMatR]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

#print axioms sprDiag_sandwich

/-- ★★★ `A · M · A⁻¹`（`A = P_σ D_c`）的逐项式（`sprPsiMonoR` 的核的入口引理）。 -/
theorem sprMonoS_apply (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (M : Matrix (Fin n) (Fin n) T) (i j : Fin n) :
    (sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * M
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹) i j
      = (((c (σ⁻¹ i) : Tˣ)) : T) * M (σ⁻¹ i) (σ⁻¹ j) * ((((c (σ⁻¹ j))⁻¹ : Tˣ)) : T) := by
  have h1 : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * M
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = sprPmat (n := n) T σ
        * (sprDiagMatR (n := n) T c * M
            * sprDiagMatR (n := n) T (fun i => (c i)⁻¹)) * sprPmat (n := n) T σ⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [h1, sprPmat_sandwich, sprDiag_sandwich]

#print axioms sprMonoS_apply

/-- `xdiag` 沿 `η` 的像：`diagonal (η ∘ x_·)`。 -/
theorem sprXdiag_map (η : Spr F r n →ₐ[F] T) :
    (xdiag F r n).map η
      = Matrix.diagonal (fun j => η (MvPolynomial.X (Sum.inl j))) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, xdiag, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact map_zero η

#print axioms sprXdiag_map

/-- `ymat k` 沿 `η` 的像（逐项）。 -/
theorem sprYmat_map_apply (η : Spr F r n →ₐ[F] T)
    (k : {k : Fin r // k.val ≠ 0}) (i j : Fin n) :
    ((ymat F r n k).map η) i j = η (MvPolynomial.X (Sum.inr (i, j, k))) := by
  rw [Matrix.map_apply]
  rfl

#print axioms sprYmat_map_apply

/-- ★★★ **"same calculation"，`x` 部分**（源文 `:442`）。

**假设已收窄（第 297 轮修正）**：源文的"`θ₁ θ₂` 在 `R(F,n,r)` 上一致"**只给生成元上的等式**，
给不出 `∀ β` 的等式；故本条的假设**只取 `β = xdiag`**（生成元 `X`）。 -/
theorem sprSameCalc_x (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (η₁ η₂ : Spr F r n →ₐ[F] T)
    (h : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((xdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (xdiag F r n).map η₂)
    (i : Fin n) :
    η₁ (MvPolynomial.X (Sum.inl i)) = η₂ (MvPolynomial.X (Sum.inl (σ i))) := by
  have hentry := congrFun (congrFun h (σ i)) (σ i)
  simp only [sprMonoS_apply, sprXdiag_map, Equiv.symm_apply_apply,
    Matrix.diagonal_apply_eq, sprUnits_conj_cancel] at hentry
  simpa using hentry

#print axioms sprSameCalc_x

/-- ★★★ **"same calculation"，`y` 部分**（源文 `:442`；假设只取 `β = ymat k`，见 `_x` 的说明）。 -/
theorem sprSameCalc_y (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (η₁ η₂ : Spr F r n →ₐ[F] T) (k : {k : Fin r // k.val ≠ 0})
    (h : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((ymat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (ymat F r n k).map η₂)
    (i j : Fin n) :
    η₁ (MvPolynomial.X (Sum.inr (i, j, k)))
      = ((((c i)⁻¹ : Tˣ)) : T) * η₂ (MvPolynomial.X (Sum.inr (σ i, σ j, k)))
        * (((c j : Tˣ)) : T) := by
  have hentry := congrFun (congrFun h (σ i)) (σ j)
  simp only [sprMonoS_apply, sprYmat_map_apply] at hentry
  have hh := sprUnits_solve (u := c (σ⁻¹ (σ i))) (v := c (σ⁻¹ (σ j)))
    (M := η₁ (MvPolynomial.X (Sum.inr (σ⁻¹ (σ i), σ⁻¹ (σ j), k))))
    (R := η₂ (MvPolynomial.X (Sum.inr (σ i, σ j, k)))) (by rw [← mul_assoc]; exact hentry)
  simpa using hh

#print axioms sprSameCalc_y

/-- ★★★★ **"same calculation"（打包形态，假设收窄到两个生成元族）**：`η_1 = μ`，其中
`μ = sprMonoAeval T ξ υ σ c`（`ξ = η_2 ∘ x_·`、`υ = η_2 ∘ y_·`）——**这正是收口层要的形状**
（配合 `sprPsiMono_specialize`：`A (α.map μ) A⁻¹ = α.map Φ`，`Φ` 以 `(ξ, υ)` 为值）。 -/
theorem sprSameCalc (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (η₁ η₂ : Spr F r n →ₐ[F] T)
    (hx : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((xdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (xdiag F r n).map η₂)
    (hy : ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((ymat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (ymat F r n k).map η₂) :
    η₁ = sprMonoAeval (F := F) (r := r) T
      (fun i => η₂ (MvPolynomial.X (Sum.inl i)))
      (fun ijk => η₂ (MvPolynomial.X (Sum.inr ijk))) σ c := by
  refine MvPolynomial.algHom_ext (fun idx => ?_)
  rcases idx with i | ⟨i, j, k⟩
  · rw [sprMonoAeval_X_inl]
    exact sprSameCalc_x F σ c η₁ η₂ hx i
  · rw [sprMonoAeval_X_inr, Units.val_mul]
    rw [sprSameCalc_y F σ c η₁ η₂ k (hy k) i j]
    ring

#print axioms sprSameCalc

end SameCalc

/-! ## §124 **`lem:14.24` 的收口链（四步）**

源文 `:442`（逐字）：

> "The same calculation as in Theorem 14.15 shows that `θ_1' = θ_2' ψ_A`
> and Lemma 14.24 follows from Lemma 14.23."

`thm:14.15` 的同型链（源文 `:324–326`，逐字）：

> "`θ₁(α) = θ₁'(α) = θ₂'ψ_A(α) =` (by Proposition 14.14) `θ₂'(α) = θ₂(α)`."

本节把它在 `S'`-世界机检：**唯一非代数输入** = `ψ_A(α) = α`（`lem:14.23` 的特化，§115）
＋ `η₁ = μ`（"同一计算"，§123）。

**★ 本轮的一处修正（必须登记）**：§123 原先三条定理的假设是 `∀ β, A(β.map η₁)A⁻¹ = β.map η₂`，
但源文的"`θ₁ θ₂` 在 `R(F,n,r)` 上一致"**只给两个生成元族上的等式**（`X` 与 `Y_k`），
**给不出 `∀ β`**。故本轮把 §123 的假设**收窄**为 `β = xdiag` 与 `β = ymat k`
（证明逐字不变，只是不再假装有全矩阵等式）。

**工艺**：收口靠 `sprMonoS_cancel`（共轭 `A·M·A⁻¹` 可消）——它的证明走**逐项式**
`sprMonoS_apply` ＋ 单位可消 `sprUnits_cancel`，**不做矩阵求逆**（R158／R161）。

**射程（勿夸大）**：本节给四步链。**还差**把 `sprPsiMono_specialize`（§115）的右端
`(α.map (MvPolynomial.map …)).map (sprSpecAlg …)` 认成 `α.map η₂`
（需 `MvPolynomial.mapAlgHom`／`Matrix.map_map` 的形态工作，`rw` 落点未过）；
`lem:14.24` 的**陈述本身**（`S''`／`θ₁ θ₂`／`Δ` 非零因子）尚未写出。
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section Chain

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `↑a · x · ↑b⁻¹ = ↑a · y · ↑b⁻¹ ⟹ x = y`（单位可消）。 -/
theorem sprUnits_cancel (a b : Tˣ) {x y : T}
    (h : ((a : Tˣ) : T) * x * (((b⁻¹ : Tˣ)) : T)
      = ((a : Tˣ) : T) * y * (((b⁻¹ : Tˣ)) : T)) : x = y := by
  have hu : IsUnit ((a : Tˣ) : T) := ⟨a, rfl⟩
  have hv : IsUnit ((((b⁻¹ : Tˣ)) : T)) := ⟨b⁻¹, rfl⟩
  exact IsUnit.mul_left_cancel hu (IsUnit.mul_right_cancel hv h)

#print axioms sprUnits_cancel

/-- ★★ **共轭 `A · M · A⁻¹`（`A = P_σ D_c`）可消**：两矩阵若共轭后相等则本身相等。 -/
theorem sprMonoS_cancel (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    {X Y : Matrix (Fin n) (Fin n) T}
    (h : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * X
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * Y
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹) :
    X = Y := by
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h (σ i)) (σ j)
  rw [sprMonoS_apply, sprMonoS_apply] at hij
  have hXY : X (σ⁻¹ (σ i)) (σ⁻¹ (σ j)) = Y (σ⁻¹ (σ i)) (σ⁻¹ (σ j)) :=
    sprUnits_cancel (c (σ⁻¹ (σ i))) (c (σ⁻¹ (σ j))) hij
  simpa using hXY

#print axioms sprMonoS_cancel

/-- ★★★★ **`lem:14.24` 的收口链（四步）**，以两次"同一计算"为输入：

* `hcalc`：`η₁ = μ`（`μ = sprMonoAeval T ξ υ σ c`，§123）；
* `hψ`：`ψ_A(α) = α 沿 Φ`（`lem:14.23` 的特化，§115；`Φ` 的变量值即 `(ξ, υ)`）。

**证明（与源文四步同型）**：
`θ₂ α = A⁻¹ (α.map η₂) A`（`h₂` 反转）
`= A⁻¹ (ψ_A(α)) A`（`hψ`）
`= A⁻¹ (A (α.map μ) A⁻¹) A`（`ψ_A` 的定义）
`= α.map μ = α.map η₁`（`hcalc`）。
末步用 `sprMonoS_cancel`（共轭可消）。 -/
theorem lem1424_chain (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (η₁ η₂ : Spr F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (ξ : Fin n → T) (υ : YIdx r n → T)
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hcalc : η₁ = sprMonoAeval (F := F) (r := r) T ξ υ σ c)
    (hψ : sprPsiMonoR (F := F) (r := r) T ξ υ σ c α = α.map η₂) :
    θ₂ α = α.map η₁ := by
  refine sprMonoS_cancel σ c ?_
  rw [h₂ α, hcalc, ← sprPsiMonoR_apply, hψ]

#print axioms lem1424_chain

end Chain

/-! ## §125 **收口的最后两座桥 ＋ `lem:14.24` 全装**（`θ₂ α = α.map η₁` 机检）

§124 的四步链还差两件事，本节补上：

1. **`sprMapAlgHom_X`／`sprSpecAlg_comp_map_eq`**：`MvPolynomial.map` 是 **`RingHom` 而非 `AlgHom`**
   （第 297 轮 `.comp` 因此被拒），正解是 `MvPolynomial.mapAlgHom (Algebra.ofId F (Ldiag F n))`
   ＋ `MvPolynomial.algHom_ext`；
2. **`sprSpecAlg_map_apply`**：把它搬到 `Matrix.map` 能吃的**逐项**形态。

于是 §115 的 `sprPsiMono_specialize` 右端 `(α.map (map …)).map (sprSpecAlg …)`
**被认成 `α.map η₂`**，与 §123 的 `η₁ = μ` 一起喂给 §124 的链。

**★★★★★ `lem1424_closing`** 是本节与 §123／§124／§115／§116 的总装：
$$
h_2\ (\text{sprGlue}) + \text{生成元一致性} + N\text{-不变} + \text{对角参数}
\;\Longrightarrow\; θ_2 α = α.map η_1 .
$$

**射程（勿夸大）**：本条的结论是 `θ₂ α = α.map η₁`。**`lem:14.24` 的陈述本身**
（`S''`／`Δ`／`θ_i(Δ)` 非零因子，以及从 `sprGlue` 与"在 `R(F,n,r)` 上一致"**推出**本节的三条假设）
仍未写出；`θ₁ α = α.map η₁` 的一半（`sprEta1_std`）尚未接起来。
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section SpecAlgBridge

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `MvPolynomial.mapAlgHom (Algebra.ofId F L)` 在生成元上取 `X`。 -/
theorem sprMapAlgHom_X (idx : SprIdx r n) :
    MvPolynomial.mapAlgHom (Algebra.ofId F (Ldiag F n))
        (MvPolynomial.X idx : Spr F r n)
      = (MvPolynomial.X idx : MvPolynomial (SprIdx r n) (Ldiag F n)) := by
  simp

#print axioms sprMapAlgHom_X

/-- ★★★ **`sprSpecAlg` 与系数扩张的复合 ＝ `η`**（若 `η` 在生成元上取 `(xi, yv)` 的值）。 -/
theorem sprSpecAlg_comp_map_eq (η : Spr F r n →ₐ[F] T) (lam : Ldiag F n →ₐ[F] T)
    (xi : Fin n → T) (yv : YIdx r n → T)
    (hxi : ∀ i, xi i = η (MvPolynomial.X (Sum.inl i)))
    (hyv : ∀ ijk, yv ijk = η (MvPolynomial.X (Sum.inr ijk))) :
    (sprSpecAlg (F := F) (r := r) (n := n) T lam xi yv).comp
        (MvPolynomial.mapAlgHom (Algebra.ofId F (Ldiag F n))) = η := by
  refine MvPolynomial.algHom_ext (fun idx => ?_)
  rw [AlgHom.comp_apply, sprMapAlgHom_X]
  rcases idx with i | ⟨i, j, k⟩
  · show sprSpecMap (F := F) (n := n) T lam xi yv
      (MvPolynomial.X (Sum.inl i) : MvPolynomial (SprIdx r n) (Ldiag F n)) = η _
    rw [sprSpecMap_X_inl]
    exact hxi i
  · show sprSpecMap (F := F) (n := n) T lam xi yv
      (MvPolynomial.X (Sum.inr (i, j, k)) : MvPolynomial (SprIdx r n) (Ldiag F n)) = η _
    show MvPolynomial.eval₂Hom lam.toRingHom (Sum.elim xi yv)
      (MvPolynomial.X (Sum.inr (i, j, k)) : MvPolynomial (SprIdx r n) (Ldiag F n)) = η _
    rw [MvPolynomial.eval₂Hom_X']
    simpa using hyv (i, j, k)

#print axioms sprSpecAlg_comp_map_eq

/-- ★★★ **逐项形态**（`Matrix.map` 能吃的形态）。 -/
theorem sprSpecAlg_map_apply (η : Spr F r n →ₐ[F] T) (lam : Ldiag F n →ₐ[F] T)
    (xi : Fin n → T) (yv : YIdx r n → T)
    (hxi : ∀ i, xi i = η (MvPolynomial.X (Sum.inl i)))
    (hyv : ∀ ijk, yv ijk = η (MvPolynomial.X (Sum.inr ijk)))
    (α : Matrix (Fin n) (Fin n) (Spr F r n)) :
    (α.map (MvPolynomial.map (algebraMap F (Ldiag F n)))).map
        (sprSpecAlg (F := F) (r := r) (n := n) T lam xi yv) = α.map η := by
  have hΦ := sprSpecAlg_comp_map_eq (F := F) (r := r) (n := n) (T := T) η lam xi yv hxi hyv
  rw [Matrix.map_map]
  congr 1
  funext p
  exact DFunLike.congr_fun hΦ p

#print axioms sprSpecAlg_map_apply

end SpecAlgBridge

section Closing

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★★★ **`lem:14.24` 的收口（全装）**：把 `lem:14.23` 的特化（§115）、
"s same calculation"（§123）、`sprGlue`（§116）与四步链（§124）拼成
`θ₂ α = α.map η₁`（当 `θ₁ = M_n(η₁)` 时为 `θ₂ α = θ₁ α`）。

**输入（逐条对应源文）**：
* `h₂`：`A θ₂(·) A⁻¹ = M_n(η₂)`（`sprGlue`，源文 "there is an `A` such that `A⁻¹f₁A = f₂`"）；
* `hxA`／`hyA`：两个**生成元族**上的一致性（源文 "`θ₁` and `θ₂` agree on `R(F,n,r)`"）；
* `hα`：`N`-不变（`lem:14.23` 的假设）；
* `hlam`：对角参数 `d_i ↦ c_i`。

**射程**：本条的结论是 `θ₂ α = α.map η₁`。**`lem:14.24` 的陈述本身**（`S''`／`Δ` 非零因子／
`θ_i(Δ)` 非零因子）与 `θ₁ α = α.map η₁` 的一半（`sprEta1_std`）尚未接起来。 -/
theorem lem1424_closing [Infinite F] (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (η₁ η₂ : Spr F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hxA : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((xdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (xdiag F r n).map η₂)
    (hyA : ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((ymat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (ymat F r n k).map η₂)
    (lam : Ldiag F n →ₐ[F] T)
    (hlam : ∀ i, lam (↑((isUnit_algebraMap_X F n i).unit)) = ↑(c i)) :
    θ₂ α = α.map η₁ := by
  have hspec := sprPsiMono_specialize (F := F) (r := r) α hα σ T
    (fun i => η₂ (MvPolynomial.X (Sum.inl i)))
    (fun ijk => η₂ (MvPolynomial.X (Sum.inr ijk))) lam c hlam
  have hmap := sprSpecAlg_map_apply (F := F) (r := r) (n := n) (T := T) η₂ lam
    (fun i => η₂ (MvPolynomial.X (Sum.inl i)))
    (fun ijk => η₂ (MvPolynomial.X (Sum.inr ijk)))
    (fun _ => rfl) (fun _ => rfl) α
  have hψ : sprPsiMonoR (F := F) (r := r) T
      (fun i => η₂ (MvPolynomial.X (Sum.inl i)))
      (fun ijk => η₂ (MvPolynomial.X (Sum.inr ijk))) σ c α = α.map η₂ := by
    rw [hspec, hmap]
  exact lem1424_chain F α η₁ η₂ σ c _ _ θ₂ h₂
    (sprSameCalc F σ c η₁ η₂ hxA hyA) hψ

#print axioms lem1424_closing

end Closing

/-! ## §126 **`lem:14.24` 的结论**（`θ₁ α = θ₂ α`）＋ 三条假设的来处

源文 `lem:14.24`（`:431–434`，逐字）：

> "Assume `α ∈ M_n(S')` is `N` invariant and `S'' ⊃ S'` a commutative ring. Let
> `θ_1, θ_2 : M_n(S') → M_n(S'')` be `F` algebra homomorphisms such that `θ_1` and `θ_2`
> agree on `R(F,n,r)`. Let `Δ = ∏_{i<j}(x_ii − x_jj)` be the discriminant of `X` and assume
> that `θ_i(Δ)` is a nonzero divisor for `i=1,2`. Then `θ_1(α) = θ_2(α)`."

本节交付**结论本身** `lem1424_concl`，并把 §125 的四条假设各自的**来处**写成定理：

| 假设 | 来处 | 件 |
|---|---|---|
| `h₁ : θ₁ = M_n(η₁)` | `sprGlue`／`exists_algHom_of_preserves_stdMU` | §116 `sprEta1_std` |
| `h₂ : A θ₂ A⁻¹ = M_n(η₂)` | 同上 | §116 `sprEta2_conj` |
| `hxA` | "`θ₁ θ₂` 在 `R` 上一致"在 `X = xdiag` 处 | **本节** `sprSameCalc_hxA` |
| `hyA` | 同上在 `Y_k = ymat k` 处 | **本节** `sprSameCalc_hyA` |

另两条把"在生成元族 `sprGen` 上一致"翻译成 `xdiag`／`ymat` 上的等式：
`sprGen_k0_eq`、`sprGen_ne_eq`。

**射程（勿夸大）**：本节的 `lem1424_concl` 仍是**条件**定理——它假设了 `h₁`／`h₂`／`hxA`／`hyA`。
**未做**：(1) 从**未归一的** `θ₁, θ₂`（不保标准矩阵单位）走到 `h₁`／`h₂`：即
"`[2.11]` 取共轭单位 `u`／`A`"那一步（`thm:14.15` 的 §36–§37 有同型件，但那是 `S`-世界）；
(2) **局部化 ＋ `S''` 局部**的归约；(3) `Δ` 与 `θ_i(Δ)` 非零因子的**使用**
（即判别式条件如何进入 §120 的 `isUnit_sub` 假设）。`lem:14.25`、`prop:14.19` 装配、
`ZEqNFixed` —— 未做/未证。 -/

section Final

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★★★ **`lem:14.24` 的结论**：`θ₁ α = θ₂ α`。

**接法**：`θ₁ = M_n(η₁)`（`sprGlue`／`sprEta1_std` 给的 `h₁`）＋ §125 的全装。
**这是源文 `lem:14.24` 的结论本身**；其**假设**（`h₂`／`hxA`／`hyA`）如何从
"`θ₁ θ₂` 在 `R(F,n,r)` 上一致 ＋ `θ_i(Δ)` 非零因子"推出，见下一节。 -/
theorem lem1424_concl [Infinite F] (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (η₁ η₂ : Spr F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hxA : sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((xdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (xdiag F r n).map η₂)
    (hyA : ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((ymat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (ymat F r n k).map η₂)
    (lam : Ldiag F n →ₐ[F] T)
    (hlam : ∀ i, lam (↑((isUnit_algebraMap_X F n i).unit)) = ↑(c i)) :
    θ₁ α = θ₂ α := by
  rw [h₁ α, lem1424_closing F α hα η₁ η₂ σ c θ₂ h₂ hxA hyA lam hlam]

#print axioms lem1424_concl

/-- ★★★ `sprGen` 在 `k = k₀` 处是 `xdiag`（生成元 `X`）。 -/
theorem sprGen_k0_eq (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    sprGen F r n k₀ hk₀ k₀ = xdiag F r n := by
  rw [sprGen, dif_pos rfl]

#print axioms sprGen_k0_eq

/-- ★★★ `sprGen` 在 `k ≠ k₀` 处是 `ymat`（生成元 `Y_k`）。 -/
theorem sprGen_ne_eq (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀) :
    sprGen F r n k₀ hk₀ k
      = ymat F r n ⟨k, by
          intro h0
          exact hk (Fin.ext (by rw [h0, hk₀]))⟩ := by
  rw [sprGen, dif_neg hk]

#print axioms sprGen_ne_eq

/-- ★★ **`hxA` 的来处**：从 `θ₁ xdiag = θ₂ xdiag` 与 `h₁`／`h₂` 推出。 -/
theorem sprSameCalc_hxA (η₁ η₂ : Spr F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n))
    (c : Fin n → Tˣ)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n)) :
    sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((xdiag F r n).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (xdiag F r n).map η₂ := by
  rw [← h₁ (xdiag F r n), hX, h₂ (xdiag F r n)]

#print axioms sprSameCalc_hxA

/-- ★★ **`hyA` 的来处**：从 `∀ k, θ₁ (ymat k) = θ₂ (ymat k)` 与 `h₁`／`h₂` 推出。 -/
theorem sprSameCalc_hyA (η₁ η₂ : Spr F r n →ₐ[F] T) (σ : Equiv.Perm (Fin n))
    (c : Fin n → Tˣ)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂)
    (hY : ∀ k : {k : Fin r // k.val ≠ 0},
      θ₁ (ymat F r n k) = θ₂ (ymat F r n k)) :
    ∀ k : {k : Fin r // k.val ≠ 0},
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * ((ymat F r n k).map η₁)
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = (ymat F r n k).map η₂ := by
  intro k
  rw [← h₁ (ymat F r n k), hY k, h₂ (ymat F r n k)]

#print axioms sprSameCalc_hyA

end Final

/-! ## §127 **`lem:14.24` 的归一步**（局部环；源文引 `[2.11]`）

源文 `lem:14.24` 证明第二段（`:437`，逐字）：

> "By `[saltman1999lectures, 2.11]` we may assume the `f_1(i,j)` are standard. By that same
> result, there is an `A ∈ GL_n(S'')` such that `A^{-1} f_1(i,j) A = f_2(i,j)` for all `i,j`."

`T = S''` 局部时，`[2.11]` 的机检件是 **`exists_unit_conj_stdMU_of_isLocalRing`**
（`Procesi/MatrixUnits.lean:496`，**完全通用**：`{T} [IsLocalRing T] {n} {g}`，
不提及 `S`／`S'`——R160 的肯定答案）。本节只做**参数化实例化**：

* `sprExistsEta1_local`：`∃ u, ∃ η₁, ∀ β, ↑u⁻¹ · θ₁ β · ↑u = β.map η₁`
  （源文 "we may assume the `f_1(i,j)` are standard" ＋ `sprEta1_std`）；
* `sprExistsEta2_local`：`∃ A, ∃ η₂, ∀ β, ↑A · θ₂ β · ↑A⁻¹ = β.map η₂`
  （源文 "there is an `A` such that `A⁻¹f₁A = f₂`" ＋ `sprEta2_conj`，§116）。

**用 `u⁻¹` 而非 `u` 的方向（易错点，本轮实测）**：`[2.11]` 给的是
`↑u · e_ij · ↑u⁻¹ = θ(e_ij)`，故 `Ad_{u⁻¹} ∘ θ` 才保标准单位
（`mul_inv_conj_mul u⁻¹` 而非 `u`）；`θ₂` 侧则把 `A` 取成 `u⁻¹`，`sprEta2_conj` 的 `h₂` 形状
恰是 `θ(e_ij) = ↑A⁻¹ e_ij ↑A`，与 `(hu i j).symm` 对上。

**射程（勿夸大）**：本节只给**局部环**下的归一化。**未做**：`S''` 一般的**局部化归约**
（"Any commutative ring embeds in a product of local rings"，`thm:14.15` 的 §37
`thm1415_general` 有逐素局部化替代，`S'`-世界须重做）；把归一化与 §126 的
`lem1424_concl` 拼成"未归一"的 `θ₁ α = θ₂ α`；判别式条件的使用。
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section Normalize

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★ **归一化（`θ₁` 侧）**：`T` 局部时，共轭 `Ad_{u⁻¹}` 后 `θ₁` 变成 `M_n(η₁)`。

**用途**：这正是源文 "we may assume the `f_1(i,j)` are standard" 的机检形态。 -/
theorem sprExistsEta1_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₁ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
    ∃ u : (Matrix (Fin n) (Fin n) T)ˣ, ∃ η₁ : Spr F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
        (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₁ β
          * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
        = β.map η₁ := by
  obtain ⟨u, hu⟩ := exists_unit_conj_stdMU_of_isLocalRing (n := Fin n) (T := T)
    (isMatrixUnitSystem_theta_stdMU_spr F r n T θ₁)
  have h₁ : ∀ i j, ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁)
      (stdMU (n := Fin n) (R := Spr F r n) i j)
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
  obtain ⟨η₁, hη₁⟩ := exists_algHom_of_preserves_stdMU (F := F) (R := Spr F r n) (R' := T)
    (n := Fin n) ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) h₁
  exact ⟨u, η₁, fun β => hη₁ β⟩

#print axioms sprExistsEta1_local

/-- ★★★ **归一化（`θ₂` 侧）**：`T` 局部时，存在 `A` 使 `A θ₂ A⁻¹ = M_n(η₂)`
（即 `sprEta2_conj`／`sprGlue` 的 `h₂` 形态）。 -/
theorem sprExistsEta2_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) :
    ∃ A : (Matrix (Fin n) (Fin n) T)ˣ, ∃ η₂ : Spr F r n →ₐ[F] T,
      ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
        ((A : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) * θ₂ β
          * ((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
        = β.map η₂ := by
  obtain ⟨u, hu⟩ := exists_unit_conj_stdMU_of_isLocalRing (n := Fin n) (T := T)
    (isMatrixUnitSystem_theta_stdMU_spr F r n T θ₂)
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
  obtain ⟨η₂, hη₂⟩ := sprEta2_conj F r n T θ₂ u⁻¹ h₂
  exact ⟨u⁻¹, η₂, fun β => by simpa using hη₂ β⟩

#print axioms sprExistsEta2_local

end Normalize

/-! ## §128 **`S' ⊂ S` 的截面**（`V1`：`Spr` 与 `S` 是同一数学对象的两半）

`Spr F r n` 与 `S F r n` 在 Lean 层是**两个独立的**多项式环，但数学上 `S' ⊂ S`：
`S'` 由 `X` 的**对角元**与 `Y_k` 的**全部**条目生成（源文 `:420` 的 "`S'`"）。

本节的 `sprToS` 把 `Spr` 映进 `S`，并证明它是既有映射 `evSpr`（`S →ₐ Spr`，`GenericInv.lean:5804`）
的**截面**：`evSpr ∘ sprToS = id`。故 `Frac(Spr)` 是 `Frac(S)` 的**缩回**（retract）——
即 `K' ⊂ K`（这在终局接口里是 `V1`）。

**为何需要它（一处必须先说清的事实）**：`S`-世界的 `ψ` 把 `X_{k₀}` 送到**完整**通用矩阵
（**含非对角元** `x_{k₀,i,j}`，`i ≠ j`），而 `(B)` 层的工作空间 `Spr` 里 `X` 是**对角**的
（只有 `x_ii`）。两者的差别正是 `evSpr` 的作用（**把 `X_{k₀}` 的非对角元杀掉**），
而 `psiSpr = AlgHom.mapMatrix evSpr ∘ psi`（源文 `lem:14.22` 的 `ψ : R → M_n(S')`
就是这条**对角化后**的映射，本仓已机检其单射性 `psiSpr_injective`）。

**射程（勿夸大）**：本节只给 `Spr → S` 的截面与缩回（`V1` 的一半）。
**未做**：把它提升到分式域（`Frac(Spr) →ₐ[F] Frac(S)`，须 `IsFractionRing.liftAlgHom` 一族）；
`ZCanon ⊆ K'`（终局接口 `V2'`，**见 `wiki/proj-h2-endgame-2026-10-19.md` 的修正版分析**）；
`K'^N` 与 `NFixedAlg` 的接线（`V3'`）；`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed`。 -/

section V1

variable (F : Type) [Field F] {r : ℕ} {n : ℕ}

/-- `S' → S` 的截面：`x_ii ↦ X (k₀,i,i)`、`y_ijk ↦ X (k,i,j)`。 -/
noncomputable def sprToS (k₀ : Fin r) : Spr F r n →ₐ[F] S F r n :=
  MvPolynomial.aeval (Sum.elim (fun i : Fin n => MvPolynomial.X (k₀, i, i))
    (fun ijk : YIdx r n => MvPolynomial.X ((ijk.2.2 : Fin r), ijk.1, ijk.2.1)))

#print axioms sprToS

/-- ★★★ **`sprToS` 是 `evSpr` 的截面**：`evSpr ∘ sprToS = id`（故 `S' ⊂ S`）。 -/
theorem evSpr_comp_sprToS (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    (evSpr F r n k₀ hk₀).comp (sprToS F k₀)
      = AlgHom.id F (Spr F r n) := by
  refine MvPolynomial.algHom_ext (fun idx => ?_)
  rcases idx with i | ⟨i, j, k⟩
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, sprToS, evSpr, MvPolynomial.aeval_X,
      Sum.elim_inl]
    simp
  · have hne : ((k : Fin r)) ≠ k₀ := fun h => k.2 (by rw [h, hk₀])
    simp only [AlgHom.comp_apply, AlgHom.id_apply, sprToS, evSpr, MvPolynomial.aeval_X,
      Sum.elim_inr]
    simp [hne]

#print axioms evSpr_comp_sprToS

end V1

/-! ## §129 **判别式 `Δ` 的使用**：从"`θ(Δ)` 可逆"到 §120 的 `IsUnit (c_j − c_i)`

源文 `lem:14.24` 证明首句（`:437`，逐字）：

> "By localizing we may assume the `θ_i(Δ)` are **invertible**."

而 §120（`sprCommute_diag_of_isUnit_sub`）的假设是**每个差** `c_j − c_i` 可逆。
两者的桥：`Δ = ∏_{i<j}(x_ii − x_jj)` ⟹ `θ(Δ) = ∏_{i<j}(c_i − c_j)`；
**乘积可逆 ⟹ 每个因子可逆**；再补上 `i > j` 的一侧（`c_j − c_i = −(c_i − c_j)`）。

**件**：
1. `sprDiscrIdx`：指标集 `{(i,j) | i < j}`；
2. `sprIsUnit_of_prod_eq`：**乘积可逆 ⟹ 每个因子可逆**
   （`isUnit_of_dvd_unit` ＋ `Finset.dvd_prod_of_mem`——**一行**，比自造双侧单位方程省）；
3. `sprIsUnit_sub_of_discr`：把 `i < j` 的因子扩到**全部** `i ≠ j`；
4. `sprDiscr`／`sprDiscr_map`：`S'`-世界的 `Δ` 与其沿 `η` 的像；
5. ★★★ `sprIsUnit_sub_of_discr_map`：**`η(Δ)` 可逆 ⟹ 每个 `η(x_jj) − η(x_ii)` 可逆**
   ——这正是 §120 在 `c = η ∘ x_·` 处所需的假设。

**工艺（R161 又一次兑现）**：本轮的"乘积的因子可逆"先写成 `isUnit_iff_exists` 的双侧单位方程
（约 15 行、两次 `mul_comm` 重排），`#check` 后发现**库内已有**
`isUnit_of_dvd_unit` ＋ `Finset.dvd_prod_of_mem` ⟹ **1 行**。

**射程（勿夸大）**：本节只做**局部化之后**的那一步（"可逆 ⟹ 每个差可逆"）。
**局部化本身**（`S'' → S''[1/θ_i(Δ)]` 与"非零因子 ⟹ 局部化后可逆"）**未做**；
`lem:14.24` 的一般 `S''` 归约、`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section Discr

variable {T : Type} [CommRing T] {n : ℕ}

/-- 判别式的指标集：`{(i,j) | i < j}`。 -/
def sprDiscrIdx (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)

#print axioms sprDiscrIdx

/-- ★ **乘积可逆 ⟹ 每个因子可逆**（`isUnit_of_dvd_unit` ＋ `Finset.dvd_prod_of_mem`）。 -/
theorem sprIsUnit_of_prod_eq {ι : Type*} (s : Finset ι) (f : ι → T) {a : ι} (ha : a ∈ s)
    (h : IsUnit (∏ x ∈ s, f x)) : IsUnit (f a) :=
  isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f ha) h

#print axioms sprIsUnit_of_prod_eq

/-- ★★ **乘积可逆 ⟹ 每个差可逆**（把 `i < j` 的因子扩到全部 `i ≠ j`，用 `c_j − c_i = −(c_i − c_j)`）。 -/
theorem sprIsUnit_sub_of_discr (c : Fin n → T)
    (h : IsUnit (∏ p ∈ sprDiscrIdx n, (c p.1 - c p.2))) {i j : Fin n} (hij : i ≠ j) :
    IsUnit (c j - c i) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hmem : (i, j) ∈ sprDiscrIdx n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    have h1 := sprIsUnit_of_prod_eq (sprDiscrIdx n) (fun p => c p.1 - c p.2) hmem h
    have h2 : c j - c i = -(c i - c j) := by ring
    rw [h2]
    exact h1.neg
  · have hmem : (j, i) ∈ sprDiscrIdx n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
    exact sprIsUnit_of_prod_eq (sprDiscrIdx n) (fun p => c p.1 - c p.2) hmem h

#print axioms sprIsUnit_sub_of_discr

end Discr

section DiscrSpr

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- 源文的判别式 `Δ`（`S'`-世界）：`∏_{i<j}(x_ii − x_jj)`。 -/
noncomputable def sprDiscr : Spr F r n :=
  ∏ p ∈ sprDiscrIdx n, (MvPolynomial.X (Sum.inl p.1) - MvPolynomial.X (Sum.inl p.2)
    : Spr F r n)

#print axioms sprDiscr

/-- `Δ` 沿 `η` 的像（`map_prod` ＋ `map_sub`）。 -/
theorem sprDiscr_map (η : Spr F r n →ₐ[F] T) :
    η (sprDiscr F) = ∏ p ∈ sprDiscrIdx n, (η (MvPolynomial.X (Sum.inl p.1))
      - η (MvPolynomial.X (Sum.inl p.2))) := by
  rw [sprDiscr, map_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [map_sub]

#print axioms sprDiscr_map

/-- ★★★ **判别式条件 ⟹ §120 的假设**：`η(Δ)` 可逆 ⟹ 每个 `η(x_jj) − η(x_ii)` 可逆。 -/
theorem sprIsUnit_sub_of_discr_map (η : Spr F r n →ₐ[F] T)
    (h : IsUnit (η (sprDiscr F))) {i j : Fin n} (hij : i ≠ j) :
    IsUnit (η (MvPolynomial.X (Sum.inl j)) - η (MvPolynomial.X (Sum.inl i))) := by
  rw [sprDiscr_map] at h
  exact sprIsUnit_sub_of_discr (fun i => η (MvPolynomial.X (Sum.inl i))) h hij

#print axioms sprIsUnit_sub_of_discr_map

end DiscrSpr

/-! ## §130 **`lam : Ldiag F n →ₐ[F] T` 的构造**（局部化的万有性质）

§125 的 `lem1424_closing` 需要 `lam : Ldiag F n →ₐ[F] T` 与 `hlam : lam (d_i) = c_i`
（`c : Fin n → Tˣ` 是 `A` 的对角）。在应用里 `c` 是**由 §122 产出**的，
故 `lam` 必须**构造**，不能当输入——本节补这一块。

**构造**：`d_i ↦ c_i` 给 `f := MvPolynomial.aeval (fun i => ↑(c i)) : F[d] →ₐ[F] T`；
`f (∏ d_i) = ∏ c_i` 是**单位**，故由 `Localization.Away` 的万有性质下降到
`IsLocalization.Away.liftAlgHom`，得 `sprLamOfUnits c : Ldiag F n →ₐ[F] T`。

**件**：
1. `sprAeval_sprDiagVar_isUnit`：`aeval c (∏ d_i) = ∏ c_i` 是单位；
2. `sprLamOfUnits`：`Away.liftAlgHom` 构造；
3. `sprLamOfUnits_algebraMap`：在 `F[d]` 的像上就是 `aeval c`
   （`IsLocalization.Away.lift_comp` ＋ `RingHom.congr_fun`）；
4. ★★★ `sprLamOfUnits_hlam`：**`lam (d_i) = c_i`**——正是 `lem1424_closing` 的 `hlam` 形状。

**工艺（一处形态陷阱）**：`MvPolynomial.aeval c` 要求 `c : Fin n → T`；
对 `c : Fin n → Tˣ` 必须先 coerce（`fun i => ((c i : Tˣ) : T)`），
否则 `aeval` 会把**系数环**推断成 `Tˣ`（报 `CommSemiring Tˣ` 失败）——
**`aeval` 的显式参数是"变量赋值"，不是"单位族"**。

**射程（勿夸大）**：本节只给 `lam` 的构造与其两条取值律。
`lem:14.24` 的局部情形**仍未总装**（须把 §127 的归一化 ＋ §120–§122 ＋ §123 ＋ §124／§125
串起来，且需要 `f_2(i,i) ≠ 0`）；一般 `S''` 的局部化归约、`lem:14.25`、
`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section Lam

variable (F : Type) [Field F] {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `d_i ↦ c_i` 诱导的 `F[d] →ₐ[F] T` 把 `∏ d_i` 送到单位（故可下降到 `Ldiag`）。 -/
theorem sprAeval_sprDiagVar_isUnit (c : Fin n → Tˣ) :
    IsUnit (MvPolynomial.aeval (fun i => ((c i : Tˣ) : T)) (sprDiagVar F n)) := by
  have h : MvPolynomial.aeval (fun i => ((c i : Tˣ) : T)) (sprDiagVar F n)
      = ∏ i, ((c i : Tˣ) : T) := by
    simp [sprDiagVar, MvPolynomial.aeval_X]
  rw [h]
  exact ⟨∏ i, c i, by simp⟩

#print axioms sprAeval_sprDiagVar_isUnit

/-- ★★★ **`lam : Ldiag F n →ₐ[F] T`**（由单位族 `c` 的万有性质构造）。 -/
noncomputable def sprLamOfUnits (c : Fin n → Tˣ) : Ldiag F n →ₐ[F] T :=
  IsLocalization.Away.liftAlgHom (sprDiagVar F n)
    (f := MvPolynomial.aeval (fun i => ((c i : Tˣ) : T))) (sprAeval_sprDiagVar_isUnit F c)

#print axioms sprLamOfUnits

/-- `lam` 在 `F[d]` 的像上就是 `aeval c`。 -/
theorem sprLamOfUnits_algebraMap (c : Fin n → Tˣ) (p : MvPolynomial (Fin n) F) :
    sprLamOfUnits (F := F) c (algebraMap (MvPolynomial (Fin n) F) (Ldiag F n) p)
      = MvPolynomial.aeval (fun i => ((c i : Tˣ) : T)) p := by
  rw [sprLamOfUnits]
  have h := IsLocalization.Away.lift_comp (S := Ldiag F n) (sprDiagVar F n)
    (g := (MvPolynomial.aeval (fun i => ((c i : Tˣ) : T))).toRingHom)
    (sprAeval_sprDiagVar_isUnit F c)
  exact RingHom.congr_fun h p

#print axioms sprLamOfUnits_algebraMap

/-- ★★★ **`hlam`**：`lam (d_i) = c_i`（`d_i` 在 `Ldiag` 中的像是单位，取 `IsUnit.unit`）。 -/
theorem sprLamOfUnits_hlam (c : Fin n → Tˣ) (i : Fin n) :
    sprLamOfUnits (F := F) c (↑((isUnit_algebraMap_X F n i).unit)) = ↑(c i) := by
  rw [IsUnit.unit_spec, sprLamOfUnits_algebraMap]
  simp [MvPolynomial.aeval_X]

#print axioms sprLamOfUnits_hlam

end Lam

/-! ## §131 **`f(i,i) ≠ 0` 从矩阵单位系公理推出**（补第 294 轮的缺口）

第 294 轮勘出：§121 的 `sprExistsPerm_of_diagIdem` 需要 `hne : ∀ i, F i ≠ 0`，
当时把它登记为**显式假设**（源文未提），并注明"它来自 `θ₂` 非零即单，属收口层"。
本节给出**更廉的来处**——**不需要**单性：

若 `g` 是矩阵单位系（`IsMatrixUnitSystem`）且环非平凡，则**每个** `g i i ≠ 0`。
**证明（三行代数）**：若 `g i i = 0`，则由 `g j i * g i i = g j i` 得 `g j i = 0`；
再由 `g j l = g j i * g i l = 0` 得**全部** `g j l = 0`；与 `∑ j, g j j = 1` 矛盾
（取 `(i,i)` 项得 `0 = 1`）。

**⟹ 结论**：`lem:14.24` 里的 `f_2(i,i) ≠ 0` **不是新假设**，而是
`isMatrixUnitSystem_theta_stdMU_spr`（§117）＋ `T` 非平凡的**推论**
（`sprTheta_diag_ne_zero`）。第 294 轮把它当假设登记是**保守的**，现在可以撤掉。

**工艺**：`zero_ne_one` 对**矩阵环**要求 `NeZero (1 : Matrix n n T)`（`[Nonempty n]` ＋
`NeZero (1 : T)`），本形态下拿不到；正解是**降一个层级**——从矩阵等式 `0 = 1`
取 `(i,i)` 项得 `T` 中的 `0 = 1`，再用 `T` 的 `zero_ne_one`。

**射程（勿夸大）**：本节只补 `hne` 的来处。`lem:14.24` 的局部总装（§127→§120–§122→§123→§124／§125）、
一般 `S''` 的局部化归约、`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section DiagNZ

variable {T : Type} [CommRing T] {n : Type} [Fintype n] [DecidableEq n]

/-- ★★★ **矩阵单位系的对角元非零**（`Nontrivial` 环上）。 -/
theorem sprIsMatrixUnitSystem_diag_ne_zero [Nontrivial T]
    {g : n → n → Matrix n n T} (hg : IsMatrixUnitSystem g) (i : n) : g i i ≠ 0 := by
  intro h
  have hji : ∀ j : n, g j i = 0 := by
    intro j
    have h' := hg.mul_mem j i i i
    rw [h, mul_zero, if_pos rfl] at h'
    exact h'.symm
  have hall : ∀ j l : n, g j l = 0 := by
    intro j l
    have h2 := hg.mul_mem j i i l
    rw [if_pos rfl, hji j, zero_mul] at h2
    exact h2.symm
  have hsum := hg.sum_mem
  rw [Finset.sum_eq_zero (fun j _ => hall j j)] at hsum
  have h01 : (0 : T) = 1 := by
    have h' := congrFun (congrFun hsum i) i
    simpa using h'
  exact zero_ne_one h01

#print axioms sprIsMatrixUnitSystem_diag_ne_zero

end DiagNZ

section Apply

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- §121 的 `hne` 在 `θ` 的像上**自动成立**（`f i i = θ(e_ii)` 是矩阵单位系的对角元）。 -/
theorem sprTheta_diag_ne_zero [Nontrivial T] [Nonempty (Fin n)]
    (θ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T) (i : Fin n) :
    θ (stdMU (n := Fin n) (R := Spr F r n) i i) ≠ 0 :=
  sprIsMatrixUnitSystem_diag_ne_zero
    (isMatrixUnitSystem_theta_stdMU_spr F r n T θ) i

#print axioms sprTheta_diag_ne_zero

end Apply

/-! ## §132 **`lem:14.24` 局部总装（一）**：`C` 对角 ＋ 步一 ＋ 步二

源文 `lem:14.24` 证明（`:438–441`，逐字）：

> "Since the `f_1(i,j)` are standard, and just as in Theorem 14.15, `θ_1` has the form
> `M_n(η_1)`. … Moreover, `M_n(η_1)` preserves the diagonal matrices so **`C` is a diagonal
> matrix**. … Also, the `f_2(i,i)` commute with `C` because `e(i,i)` commutes with `X`.
> Thus `f_2(i,i) ∈ T'` [= 对角]. `S''` is a local ring and so has no nontrivial idempotents.
> It follows that the only idempotents of `T'` are the `f_1(i,i)`. **Thus there is a `σ ∈ S_n`** …"

本节把 **§120／§121 接到 `θ₂` 的像上**（此前两者是抽象陈述，尚未落地到 `lem:14.24` 的数据）：

1. `sprStdMU_diag_comm`：`e_ii` 与任意对角矩阵交换（经 `sprDiag_single` 写成对角形）；
2. `sprTheta_xdiag_eq`：`θ₂(X) = θ₂(θ₁^{-1}(…)) = diagonal (η₁ ∘ x_·)`——**`C` 是对角矩阵**；
3. ★★★ `sprStepOne_local`：`θ₂(e_ii)` 是**对角**矩阵
   （交换性 ＋ 判别式给的 `IsUnit (c_j − c_i)` ＋ §120）；
4. ★★★★ `sprStepTwo_local`：**存在置换 `σ`** 使 `θ₂(e_{σ i, σ i}) = e_ii`
   ——**`hne` 由 §131 的 `sprTheta_diag_ne_zero` 自动成立**（第 305 轮撤掉的假设）。

**装配要点（两处形态）**：
* `θ₂(e_ii) * θ₂(X) = θ₂(e_ii * X) = θ₂(X * e_ii)`（`← map_mul` 两次）——交换性在 **`Spr` 里**证，
  故 `xdiag` 须先 `rw [xdiag]` 展开成 `diagonal` 才能用 `sprStdMU_diag_comm`；
* `hidem`／`horth`／`hsum` 全是 `← map_mul`／`← map_sum` ＋ `stdMU_mul`／`stdMU_sum` 的一行改写
  ——即"**矩阵单位系的像仍是矩阵单位系**"的逐条显式化。

**射程（勿夸大）**：本节给步一／步二。步三（`A = P_σ D_c`，§122）的接线、
`η₁ = μ`（§123）、收口（§124／§125／§126）**仍未接**；
一般 `S''` 的局部化归约、`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section LocalAssembly

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `e_ii` 与任意对角矩阵**交换**（`stdMU i i` 写成 `diagonal (if · = i then 1 else 0)`）。 -/
theorem sprStdMU_diag_comm (c : Fin n → T) (i : Fin n) :
    stdMU (n := Fin n) (R := T) i i * Matrix.diagonal c
      = Matrix.diagonal c * stdMU (n := Fin n) (R := T) i i := by
  rw [← sprDiag_single (T := T) i, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i
  · rw [hk]; simp
  · simp [hk, mul_comm]

#print axioms sprStdMU_diag_comm

/-- ★ `θ₂(X) = θ₁(X)` 是**对角**矩阵（`= M_n(η₁)` 的对角）。 -/
theorem sprTheta_xdiag_eq (η₁ : Spr F r n →ₐ[F] T)
    (θ₁ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁)
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n)) :
    θ₂ (xdiag F r n) = Matrix.diagonal (fun i => η₁ (MvPolynomial.X (Sum.inl i))) := by
  rw [← hX, h₁, sprXdiag_map]

#print axioms sprTheta_xdiag_eq

/-- ★★★ **步一（局部总装版）**：`f₂(i,i) = θ₂(e_ii)` 是**对角**矩阵。

**证明**：`θ₂(e_ii)` 与 `θ₂(X) = diagonal c` 交换（因 `e_ii` 与 `X` 交换），
`c_j − c_i` 可逆（判别式，§129），故由 §120 `sprCommute_diag_of_isUnit_sub` 得对角。 -/
theorem sprStepOne_local (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : Spr F r n →ₐ[F] T)
    (hC : θ₂ (xdiag F r n) = Matrix.diagonal (fun i => η₁ (MvPolynomial.X (Sum.inl i))))
    (hc : ∀ i j : Fin n, i ≠ j →
      IsUnit (η₁ (MvPolynomial.X (Sum.inl j)) - η₁ (MvPolynomial.X (Sum.inl i))))
    (i : Fin n) :
    θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i)
      = Matrix.diagonal (fun k => θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i) k k) := by
  refine sprCommute_diag_of_isUnit_sub (fun k => η₁ (MvPolynomial.X (Sum.inl k)))
    (θ₂ (stdMU (n := Fin n) i i)) hc ?_
  rw [← hC, ← map_mul, ← map_mul, xdiag, sprStdMU_diag_comm]

#print axioms sprStepOne_local

/-- ★★★★ **步二（局部总装版）**：`T` 局部时，`f₂ = θ₂ ∘ e` 的对角族有**唯一 1**，
故存在**置换 `σ`** 使 `θ₂(e_{σ i, σ i}) = e_ii`。 -/
theorem sprStepTwo_local [IsLocalRing T] [Nonempty (Fin n)]
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : Spr F r n →ₐ[F] T)
    (hC : θ₂ (xdiag F r n) = Matrix.diagonal (fun i => η₁ (MvPolynomial.X (Sum.inl i))))
    (hc : ∀ i j : Fin n, i ≠ j →
      IsUnit (η₁ (MvPolynomial.X (Sum.inl j)) - η₁ (MvPolynomial.X (Sum.inl i)))) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i, θ₂ (stdMU (n := Fin n) (R := Spr F r n) (σ i) (σ i))
        = stdMU (n := Fin n) (R := T) i i := by
  have hdiag : ∀ i, θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i)
      = Matrix.diagonal (fun k => θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i) k k) :=
    fun i => sprStepOne_local F θ₂ η₁ hC hc i
  have hidem : ∀ i, θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i)
      * θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i)
      = θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i) := by
    intro i
    rw [← map_mul, stdMU_mul, if_pos rfl]
  have horth : ∀ i j, i ≠ j → θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i)
      * θ₂ (stdMU (n := Fin n) (R := Spr F r n) j j) = 0 := by
    intro i j hij
    rw [← map_mul, stdMU_mul, if_neg hij, map_zero]
  have hsum : (∑ i, θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i))
      = 1 := by
    rw [← map_sum, stdMU_sum, map_one]
  have hne : ∀ i, θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i) ≠ 0 :=
    fun i => sprTheta_diag_ne_zero F θ₂ i
  exact sprExistsPerm_of_diagIdem (fun i => θ₂ (stdMU (n := Fin n) (R := Spr F r n) i i))
    hdiag hidem horth hsum hne

#print axioms sprStepTwo_local

end LocalAssembly

/-! ## §133 **`lem:14.24` 局部总装（二）**：步三的单位形态 ＋ 两种共轭形态的转换

**问题形状（本轮的实际卡点）**：§127 的 `sprExistsEta2_local` 给的是 **`A`-形态**
`∀ β, ↑A * θ₂ β * ↑A⁻¹ = β.map η₂`，而 §124／§125 的收口链要 **`P_σ D_c`-形态**
`∀ β, ↑P_σ * D_c * θ₂ β * D_c⁻¹ * ↑P_σ⁻¹ = β.map η₂`。
两者的桥需要 **`↑A⁻¹ = D_c⁻¹ * P_σ⁻¹`**——而 `A` 只以**矩阵**形式出现（`↑A = P_σ D_c`），
其逆的形态**不能靠 `rw` 自动给出**。

**正解（R159：不造桥，换表征）**：把步三的结论**升到单位层**
（`sprStepThree_unitsUnit : A = sprPmatUnit σ * sprDiagMatRUnit c`），
于是 `A⁻¹ = (D_c单位)⁻¹ * (P_σ单位)⁻¹` 由 **`mul_inv_rev`** 一步给出，**无需矩阵求逆**。

**件**：
1. `sprDiagMatRUnit`：`D_c` 作为单位（`val = D_c`、`inv = D_{c⁻¹}`）；
2. `sprStdMU_map`：`stdMU` 沿任意 `F`-代数同态的像仍是 `stdMU`（收口层的"`e_ii.map η₂ = e_ii`"）；
3. `sprStepThree_unitsUnit`：步三的**单位形态**结论；
4. ★★★★ `sprConjForm_of_units`：**`A`-形态 ⟹ `P_σ D_c`-形态**。

**工艺（三处形态）**：
* `Matrix.single_apply` 给的条件是 **`i = a ∧ j = b`**（不是 `a = i ∧ j = b`）——
  `by_cases` 的方向写错会得到"改写找不到落点"，而目标里其实**已经有** `if`；
* `mul_inv_rev` 有**两个**（`_root_.mul_inv_rev` 群版 与 `Matrix.mul_inv_rev` 矩阵版），
  在 `Units` 上要用**群版**，须显式限定 `_root_.`（否则 "Ambiguous term"）；
* `↑(u * v) = ↑u * ↑v` 是 `rfl`，而 `↑(D_c单位) = sprDiagMatR T c` 也是 `rfl`（按定义），
  故单位层的转换**不需要额外引理**。

**射程（勿夸大）**：本节是**接线**。`lem:14.24` 的**局部总装本体**（把 §127 →§120–§122 →
§123 →§124／§125 →§126 串成 `θ₁ α = θ₂ α`）**仍未写**；一般 `S''` 的局部化归约、
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section DiagUnit

variable {T : Type} [CommRing T] {n : ℕ}

/-- ★ `D_c` 作为**单位**（`val = D_c`、`inv = D_{c⁻¹}`）。 -/
noncomputable def sprDiagMatRUnit (c : Fin n → Tˣ) : (Matrix (Fin n) (Fin n) T)ˣ where
  val := sprDiagMatR (n := n) T c
  inv := sprDiagMatR (n := n) T (fun i => (c i)⁻¹)
  val_inv := by
    rw [sprDiagMatR, sprDiagMatR, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => ((c i : Tˣ) : T) * (((c i)⁻¹ : Tˣ) : T)) = fun _ => (1 : T) := by
      funext i
      simp
    rw [hfun, Matrix.diagonal_one]
  inv_val := by
    rw [sprDiagMatR, sprDiagMatR, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => (((c i)⁻¹ : Tˣ) : T) * ((c i : Tˣ) : T)) = fun _ => (1 : T) := by
      funext i
      simp
    rw [hfun, Matrix.diagonal_one]

#print axioms sprDiagMatRUnit

end DiagUnit

section StepThreeWired

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- `stdMU` 沿任意 `F`-代数同态的像仍是 `stdMU`（常系数矩阵）。 -/
theorem sprStdMU_map {S : Type} [CommRing S] [Algebra F S]
    (η : Spr F r n →ₐ[F] S) (i j : Fin n) :
    (stdMU (n := Fin n) (R := Spr F r n) i j).map η = stdMU (n := Fin n) (R := S) i j := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply]
  show η (stdMU (n := Fin n) (R := Spr F r n) i j a b) = stdMU (n := Fin n) (R := S) i j a b
  simp only [stdMU, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · rw [if_pos h, if_pos h, map_one]
  · rw [if_neg h, if_neg h, map_zero]

#print axioms sprStdMU_map

/-- ★★★ **步三（单位形态）**：`A e_ii A⁻¹ = e_{σi,σi}` ⟹ `A = P_σ · D_c`（作为**单位**）。 -/
theorem sprStepThree_unitsUnit (σ : Equiv.Perm (Fin n)) (A : (Matrix (Fin n) (Fin n) T)ˣ)
    (hA : ∀ i, (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = stdMU (n := Fin n) (R := T) (σ i) (σ i)) :
    ∃ c : Fin n → Tˣ, A = sprPmatUnit T σ * sprDiagMatRUnit (T := T) c := by
  obtain ⟨c, hc⟩ := sprStepThree_units σ A hA
  refine ⟨c, ?_⟩
  refine Units.ext ?_
  show (A : Matrix (Fin n) (Fin n) T)
    = (sprPmat T σ) * (sprDiagMatR (n := n) T c)
  exact hc

#print axioms sprStepThree_unitsUnit

/-- ★★★★ **`A`-形态 ⟹ `P_σ D_c`-形态**（收口链要的形态）。 -/
theorem sprConjForm_of_units (σ : Equiv.Perm (Fin n)) (c : Fin n → Tˣ)
    (A : (Matrix (Fin n) (Fin n) T)ˣ)
    (hAU : A = sprPmatUnit T σ * sprDiagMatRUnit (T := T) c)
    (θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₂ : Spr F r n →ₐ[F] T)
    (h₂ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      (A : Matrix (Fin n) (Fin n) T) * θ₂ β
        * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = β.map η₂) :
    ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
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
  have hassoc2 : ((sprPmat (n := n) T σ * sprDiagMatR (n := n) T c) * θ₂ β
        * (sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹))
      = (((sprPmat (n := n) T σ * sprDiagMatR (n := n) T c) * θ₂ β)
        * (sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹)) := rfl
  rw [hassoc]
  exact h

#print axioms sprConjForm_of_units

end StepThreeWired

/-! ## §134 ★★★★★ **`lem:14.24` 的局部总装**：`θ₁ α = θ₂ α`

源文 `lem:14.24`（`:431–434`，逐字）：

> "Assume `α ∈ M_n(S')` is `N` invariant and `S'' ⊃ S'` a commutative ring. Let
> `θ_1, θ_2 : M_n(S') → M_n(S'')` be `F` algebra homomorphisms such that `θ_1` and `θ_2`
> agree on `R(F,n,r)`. Let `Δ = ∏_{i<j}(x_ii − x_jj)` be the discriminant of `X` and assume
> that `θ_i(Δ)` is a nonzero divisor for `i=1,2`. **Then `θ_1(α) = θ_2(α)`.**"

**本节把第 292–307 轮的十一件串成一条定理**（"`S''` 局部 ＋ `θ₁` 已归一"的情形）：

| 步 | 件 | 节 |
|---|---|---|
| `C = θ₂(X)` 对角 | `sprTheta_xdiag_eq` | §132 |
| 判别式 ⟹ `IsUnit (c_j − c_i)` | `sprIsUnit_sub_of_discr_map` | §129 |
| 步二：`∃ σ` | `sprStepTwo_local` | §132 |
| 归一化 `θ₂`（`∃ A η₂`） | `sprExistsEta2_local` | §127 |
| 步三：`A = P_σ D_c`（单位） | `sprStepThree_unitsUnit` | §133 |
| `A`-形态 → `P_σD_c`-形态 | `sprConjForm_of_units` | §133 |
| `hxA`／`hyA`（生成元一致性） | `sprSameCalc_hxA`／`_hyA` | §126 |
| `η₁ = μ`（"same calculation"） | `sprSameCalc` | §123 |
| `lam` 的构造 | `sprLamOfUnits`／`_hlam` | §130 |
| 全装收口 | `lem1424_closing` | §125 |
| 结论 | — | 本节 |

**射程（逐条，勿夸大）**：
1. 本节是**局部环**情形（`[IsLocalRing T]`）。**一般 `S''` 的局部化归约未做**
   （源文首句 "By localizing we may assume the `θ_i(Δ)` are invertible"；
   `thm:14.15` 的 §37 `thm1415_general` 有逐素局部化替代，`S'`-世界须重做）；
2. 本节假设 **`θ₁` 已归一**（`h₁ : θ₁ = M_n(η₁)`）与 **`η₁(Δ)` 可逆**——
   两者由 §127（`[2.11]`）与 §129 在局部化后**可生产**，但**本节尚未接线**；
3. **`f_2(i,i) ≠ 0` 已不需要假设**（§131 推出）；
4. `lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 **H2 仍不是定理。** -/

section FullAssembly

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★★★ **`lem:14.24`（局部环、`θ₁` 已归一的情形）**：`θ₁ α = θ₂ α`。

**假设**：`T` 局部、`T` 非平凡（`IsLocalRing` 给）、`F` 无限、`α` 是 `N`-不变、
`θ₁ = M_n(η₁)`（归一后的形态）、`θ₁ θ₂` 在两个**生成元族**上一致、`η₁(Δ)` 可逆。

**结论**：`θ₁ α = θ₂ α`。 -/
theorem lem1424_local [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : Spr F r n →ₐ[F] T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0}, θ₁ (ymat F r n k) = θ₂ (ymat F r n k))
    (hΔ : IsUnit (η₁ (sprDiscr F))) :
    θ₁ α = θ₂ α := by
  -- ① `C = θ₂(X)` 是对角矩阵；判别式给 `IsUnit (c_j − c_i)`
  have hC : θ₂ (xdiag F r n) = Matrix.diagonal (fun i => η₁ (MvPolynomial.X (Sum.inl i))) :=
    sprTheta_xdiag_eq F η₁ θ₁ h₁ θ₂ hX
  have hc : ∀ i j : Fin n, i ≠ j →
      IsUnit (η₁ (MvPolynomial.X (Sum.inl j)) - η₁ (MvPolynomial.X (Sum.inl i))) :=
    fun i j hij => sprIsUnit_sub_of_discr_map F η₁ hΔ hij
  -- ② 步二：存在置换 σ
  obtain ⟨σ, hσ⟩ := sprStepTwo_local F θ₂ η₁ hC hc
  -- ③ 归一化 θ₂：存在单位 A 与 η₂
  obtain ⟨A, η₂, h₂⟩ := sprExistsEta2_local F θ₂
  -- ④ 步三：`A = P_σ D_c`（单位形态）
  have hA : ∀ i, (A : Matrix (Fin n) (Fin n) T) * stdMU (n := Fin n) (R := T) i i
      * (((A⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = stdMU (n := Fin n) (R := T) (σ i) (σ i) := by
    intro i
    have h := h₂ (stdMU (n := Fin n) (R := Spr F r n) (σ i) (σ i))
    rw [hσ i, sprStdMU_map F η₂] at h
    exact h
  obtain ⟨c, hAU⟩ := sprStepThree_unitsUnit σ A hA
  -- ⑤ 把 `h₂` 换成 `P_σ D_c`-形态
  have h₂' : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n),
      sprPmat (n := n) T σ * sprDiagMatR (n := n) T c * θ₂ β
        * sprDiagMatR (n := n) T (fun i => (c i)⁻¹) * sprPmat (n := n) T σ⁻¹
      = β.map η₂ :=
    sprConjForm_of_units F σ c A hAU θ₂ η₂ h₂
  -- ⑥ "same calculation"：`η₁ = μ`（§123）
  have hxA := sprSameCalc_hxA F η₁ η₂ σ c θ₁ θ₂ h₁ h₂' hX
  have hyA := sprSameCalc_hyA F η₁ η₂ σ c θ₁ θ₂ h₁ h₂' hY
  -- ⑦ 收口（§125，`lam` 由 §130 构造）
  have hres : θ₂ α = α.map η₁ :=
    lem1424_closing F α hα η₁ η₂ σ c θ₂ h₂' hxA hyA
      (sprLamOfUnits (F := F) c) (sprLamOfUnits_hlam (F := F) c)
  rw [h₁ α, hres]

#print axioms lem1424_local

end FullAssembly

/-! ## §135 **判别式条件的内蕴形态**（`sprDiscrUnit`）—— 局部化归约的前置

`lem1424_local`（§134）的判别式假设是 `IsUnit (η₁ (sprDiscr F))`，它**依赖归一化**（`η₁`）。
而**局部化归约**要**先**假设判别式条件（再逐素局部化），此时**还没有** `η₁`。
故须把条件改写成**不依赖归一化**的内蕴形态：

> `sprDiscrUnit θ Δ`：`θ(Δ·1)` 是**纯量矩阵**且该纯量**可逆**。

（源文 `[2.9]`：任意 `θ : M_n(S') → M_n(S'')` 满足 `θ(S') ⊂ S''`——故纯量性自动；
本定义把它显式化，以便在**没有归一化**的层上陈述。）

**件**：
1. `sprScalar_map`：`(scalar Δ).map η = scalar (η Δ)`；
2. `sprDiscrUnit`：内蕴形态的定义；
3. `sprIsUnit_discr_of_discrUnit`：内蕴形态 ⟹ 归一形态（用 `h₁ : θ₁ = M_n(η₁)`）；
4. ★★★ **`lem1424_local'`**：`lem1424_local` 的**内蕴假设版**——局部化归约直接消费这一条。

**工艺（三处形态）**：
* `Matrix.scalar` 的定义是 `diagonalRingHom ∘ Pi.constRingHom` 的**复合**，直接 `rw [Matrix.scalar]`
  会得到不可读形态；用 **`Matrix.scalar_apply` 再 `Matrix.diagonal_apply`** 才落到 `if a = b`；
* `Matrix.scalar_inj` 需要 `[Nonempty (Fin n)]`（纯量矩阵的**单射性**要指标非空），
  且它是 **`↔`**（`.mp` 而非直接应用）；
* `Matrix.map_apply` 之后目标是 `η (M a b) = N a b`，故 `h : a = b` 的分支能用 `map_one`／`map_zero`。

**射程（勿夸大）**：本节只做**假设形态的重写**（＋把 §134 重述一遍）。
**局部化归约本体**（"nonzero divisor ⟹ 局部化后可逆" ＋ 逐素局部化）**未做**；
`lem:14.25`、`prop:14.19` 装配、`ZEqNFixed` —— 未做/未证。 -/

section DiscrIntrinsic

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- 纯量矩阵沿 `F`-代数同态的像是纯量矩阵（`Matrix.scalar` 的 `map`）。 -/
theorem sprScalar_map {S : Type} [CommRing S] [Algebra F S]
    (η : Spr F r n →ₐ[F] S) (Δ : Spr F r n) :
    (Matrix.scalar (Fin n) Δ).map η = Matrix.scalar (Fin n) (η Δ) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : a = b
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact map_zero η

#print axioms sprScalar_map

/-- ★★ **判别式条件的**内蕴**形态**：`θ(Δ·1)` 的纯量可逆。 -/
def sprDiscrUnit (θ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (Δ : Spr F r n) : Prop :=
  ∃ x : T, θ (Matrix.scalar (Fin n) Δ) = Matrix.scalar (Fin n) x ∧ IsUnit x

#print axioms sprDiscrUnit

/-- 内蕴形态 ⟹ 归一形态（`θ₁ = M_n(η₁)` 时，`θ₁(Δ·1) = scalar (η₁ Δ)`）。 -/
theorem sprIsUnit_discr_of_discrUnit [Nonempty (Fin n)]
    (θ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η : Spr F r n →ₐ[F] T)
    (hη : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ β = β.map η)
    {Δ : Spr F r n} (h : sprDiscrUnit F θ Δ) : IsUnit (η Δ) := by
  obtain ⟨x, hx, hxu⟩ := h
  rw [hη, sprScalar_map] at hx
  have hx' : η Δ = x := Matrix.scalar_inj.mp hx
  rw [hx']
  exact hxu

#print axioms sprIsUnit_discr_of_discrUnit

/-- ★★★ **`lem:14.24` 局部情形（内蕴判别式假设版）** —— 局部化归约要的形态。 -/
theorem lem1424_local' [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (η₁ : Spr F r n →ₐ[F] T)
    (h₁ : ∀ β : Matrix (Fin n) (Fin n) (Spr F r n), θ₁ β = β.map η₁)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0}, θ₁ (ymat F r n k) = θ₂ (ymat F r n k))
    (hΔ : sprDiscrUnit F θ₁ (sprDiscr F)) :
    θ₁ α = θ₂ α :=
  lem1424_local F α hα θ₁ θ₂ η₁ h₁ hX hY
    (sprIsUnit_discr_of_discrUnit F θ₁ η₁ h₁ hΔ)

#print axioms lem1424_local'

end DiscrIntrinsic

/-! ## §136 ★★★★★ **`lem:14.24` 局部情形（无需归一化）**：撤掉 `h₁`

§134／§135 的 `lem1424_local'` 假设 `h₁ : ∀ β, θ₁ β = β.map η₁`，即 **`θ₁` 已归一**。
源文没有这条——它由 `[2.11]`（"we may assume the `f₁(i,j)` are standard"）**取得**。
本节把 `h₁` **撤掉**：

1. `[2.11]`（§127 `sprExistsEta1_local`）给 `u, η₁` 使 `Ad_{u⁻¹}∘θ₁ = M_n(η₁)`；
2. 对 `(Ad_{u⁻¹}θ₁, Ad_{u⁻¹}θ₂)` 套 `lem1424_local'`——**假设逐条传输**：
   * `hX`／`hY`：由 `Ad_{u⁻¹}` 作用（`congrArg` 级别）；
   * `hΔ`：**纯量矩阵是中心元**，故共轭不动（`sprScalar_conj`）；
3. 结论用 `Ad_u` 的**单射性**推回（`sprConj_unit_cancel`）。

**⟹ `lem:14.24` 的剩余只剩两件**：① 局部化归约（一般 `S''` ⟹ 局部环）；
② "非零因子 ⟹ 可逆"（`Localization.Away`）。

**工艺（一处 coercion 陷阱）**：`(u⁻¹ : (Matrix …)ˣ).val` **不可写**——Lean 会先把 `u⁻¹`
**coerce 成矩阵**再找 `.val`（报 "Invalid field `val`"）。正解是写**完整 coercion**
`(((u⁻¹ : (Matrix …)ˣ)) : Matrix … T)`。

**射程（勿夸大）**：本节仍限**局部环**（`[IsLocalRing T]`）。局部化归约与
"非零因子 ⟹ 可逆"**未做**；`lem:14.20`（`S'` 版）、`lem:14.25`、`prop:14.19` 装配、
`ZEqNFixed` —— 未做/未证。**H2 仍不是定理。** -/

section Basic

variable {T : Type} [CommRing T] {n : ℕ}

/-- ★ **纯量矩阵与单位共轭不动**（`↑u · scalar x · ↑u⁻¹ = scalar x`）。 -/
theorem sprScalar_conj (u : (Matrix (Fin n) (Fin n) T)ˣ) (x : T) :
    (u : Matrix (Fin n) (Fin n) T) * Matrix.scalar (Fin n) x
      * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = Matrix.scalar (Fin n) x := by
  have hcomm : Matrix.scalar (Fin n) x * (u : Matrix (Fin n) (Fin n) T)
      = (u : Matrix (Fin n) (Fin n) T) * Matrix.scalar (Fin n) x :=
    Matrix.scalar_comm x (fun _ => Commute.all _ _) _
  rw [← hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

#print axioms sprScalar_conj

/-- ★ **单位共轭可消**：`↑u · X · ↑u⁻¹ = ↑u · Y · ↑u⁻¹ ⟹ X = Y`。 -/
theorem sprConj_unit_cancel (u : (Matrix (Fin n) (Fin n) T)ˣ)
    {X Y : Matrix (Fin n) (Fin n) T}
    (h : (u : Matrix (Fin n) (Fin n) T) * X
        * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)
      = (u : Matrix (Fin n) (Fin n) T) * Y
        * (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T)) :
    X = Y :=
  IsUnit.mul_left_cancel ⟨u, rfl⟩ (IsUnit.mul_right_cancel ⟨u⁻¹, rfl⟩ h)

#print axioms sprConj_unit_cancel

end Basic

section NoNorm

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★★ **`lem:14.24` 局部情形（**无需** `θ₁` 已归一）**。

**证明**：`[2.11]`（§127）给 `u, η₁` 使 `Ad_{u⁻¹}∘θ₁ = M_n(η₁)`；
对 `(Ad_{u⁻¹}θ₁, Ad_{u⁻¹}θ₂)` 套 `lem1424_local'`（假设逐条传输：`hX`／`hY` 由 `Ad` 作用，
`hΔ` 由**纯量矩阵中心性**）；再把结论用 `Ad_u` 的**单射性**（＝共轭可消）推回。 -/
theorem lem1424_localNoNorm [IsLocalRing T] [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0}, θ₁ (ymat F r n k) = θ₂ (ymat F r n k))
    (hΔ : sprDiscrUnit F θ₁ (sprDiscr F)) :
    θ₁ α = θ₂ α := by
  obtain ⟨u, η₁, h₁⟩ := sprExistsEta1_local F θ₁
  -- 传输 `hX`／`hY`／`hΔ` 到共轭后的对
  have hX' : ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) (xdiag F r n)
      = ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂) (xdiag F r n) := by
    show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₁ (xdiag F r n) * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
      = (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₂ (xdiag F r n) * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
    rw [hX]
  have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
      ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁) (ymat F r n k)
        = ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂) (ymat F r n k) := by
    intro k
    show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₁ (ymat F r n k) * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
      = (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₂ (ymat F r n k) * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
    rw [hY k]
  have hΔ' : sprDiscrUnit F ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁)
      (sprDiscr F) := by
    obtain ⟨x, hx, hxu⟩ := hΔ
    refine ⟨x, ?_, hxu⟩
    show (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₁ (Matrix.scalar (Fin n) (sprDiscr F))
        * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) = Matrix.scalar (Fin n) x
    rw [hx]
    exact sprScalar_conj u⁻¹ x
  have hres := lem1424_local' F α hα
    ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₁)
    ((conjAlgEquiv (F := F) u⁻¹).toAlgHom.comp θ₂) η₁ (fun β => h₁ β) hX' hY' hΔ'
  -- 推回：`↑u⁻¹ θ₁ α ↑u = ↑u⁻¹ θ₂ α ↑u`
  show θ₁ α = θ₂ α
  have hres' : (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₁ α * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T)
      = (((u⁻¹ : (Matrix (Fin n) (Fin n) T)ˣ)) : Matrix (Fin n) (Fin n) T) * θ₂ α * ((u : (Matrix (Fin n) (Fin n) T)ˣ) : Matrix (Fin n) (Fin n) T) := hres
  have hc := sprConj_unit_cancel (u⁻¹) (X := θ₁ α) (Y := θ₂ α) ?_
  · exact hc
  · simpa using hres'

#print axioms lem1424_localNoNorm

end NoNorm

/-! ## §137 **`lem:14.24` 的一般 `S''`**：局部化归约（"非零因子 ⟹ 可逆" ＋ 逐素局部化）

源文 `lem:14.24` 的证明首两句（`raw/Saltman1999ch14.tex:437`，逐字）：

> "By localizing we may assume the `θ_i(Δ)` are **invertible**. Just as in Theorem 14.15,
> we may assume `S''` is **local**."

§134／§135／§136 已把"`S''` 局部 ＋ `Δ` 可逆"的核证成定理（`lem1424_localNoNorm`）。
本节照原文那**两句话、两个步骤**把它推到一般 `S''`：

1. **"`S''` 局部"**（`lem1424_of_discrUnit`）：与 `thm:14.15` 的 §36
   `thm1415_general_nontrivial` **同一路线**——反设 `θ₁α − θ₂α` 有非零条目，则
   `exists_isPrime_algebraMap_ne_zero`（§36）给素理想 `m`，使该条目在 `T_m` 中仍非零；
   在局部环 `T_m` 上套 `lem1424_localNoNorm`，再用 `T → T_m` 的单射性关闭。
   判别式条件沿 `T → T_m` 的传输由 `sprDiscrUnit_mapMatrix` 供给（`scalar x ↦ scalar (φ x)`）。
2. **"`Δ` 可逆"**（`lem1424_general`）：倒掉判别式。取 `x` ＝ `θ₁(Δ·1)` 的纯量，
   在 `T[1/x]` 中 `x` 是单位（`IsLocalization.Away.algebraMap_isUnit`），套步骤 1，
   再用 `sprAway_injective`（**非零因子 ⟹ `T → T[1/x]` 单射**）落回 `T`。

**⚠ 一条必须点名的已发表输入（`[2.9]`）**：`sprDiscrNonZeroDiv` 的**纯量形态**
（`θ(Δ·1) = scalar x`，即"`θ` 把纯量送成纯量"）**不是**本节推出的，它是 Saltman 讲义
**`[2.9]`**（"任意 `θ : M_n(S') → M_n(S'')` 满足 `θ(S') ⊂ S''`"）的内容，与 `lem:14.24`
陈述前的那句注释同源（源文 `:434`）。本库**尚未**形式化 `[2.9]`，故它作为
`sprDiscrNonZeroDiv` 的**字段**显式登记，**不隐藏**。
（局部环里它可以由 §127 的 `sprExistsEta1_local` 推出：`θ = Ad_u ∘ M_n(η)` ⟹
`θ(scalar a) = u · scalar (η a) · u⁻¹ = scalar (η a)`；一般 `S''` 上仍需 `[2.9]`。）

**工艺（一处实例陷阱，实案）**：在 `lem1424_general` 里**不要**用 `haveI` 钉
`Algebra T (Localization.Away x)` 之类实例——`Localization.Away` 上同时存在
`OreLocalization.instAlgebra` 等多个候选，钉住其中一条会**切断**后续
`IsScalarTower F T T'` 与 `IsLocalization.Away x T'` 的实例链（报错落在毫不相干的类上）。
**删掉这些 `haveI`、交给默认实例搜索**即通。

**射程（勿夸大）**：本节使 `lem:14.24` **在原文口径下成为定理**（一般 `S''`，
假设 ＝ `[2.9]` ＋ `θ₁(Δ)` 非零因子）。`lem:14.20`（`S'` 版）、`lem:14.25`、
`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section AwayPow

variable {T : Type} [CommRing T]

/-- 非零因子的幂乘零 ⟹ 零（`Away` 单射性的代数核）。 -/
theorem sprPow_mul_eq_zero {s : T}
    (hnd : ∀ y : T, s * y = 0 → y = 0) :
    ∀ (k : ℕ) (y : T), s ^ k * y = 0 → y = 0 := by
  intro k
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    refine hnd y (ih (s * y) ?_)
    rw [← mul_assoc, ← pow_succ]
    exact hy

#print axioms sprPow_mul_eq_zero

/-- ★★ **非零因子在 `Away` 局部化中不损失信息**：`T → T[1/s]` 单射。

原文首句"By localizing we may assume the `θ_i(Δ)` are invertible"的**代价**就在这里：
倒掉判别式后要能落回 `T`，靠的正是"`θ(Δ)` 非零因子"。 -/
theorem sprAway_injective {s : T}
    (hnd : ∀ y : T, s * y = 0 → y = 0)
    (T' : Type) [CommRing T'] [Algebra T T'] [IsLocalization.Away s T'] :
    Function.Injective (algebraMap T T') := by
  intro a b hab
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (S := T') s hab
  have hz : s ^ k * (a - b) = 0 := by rw [mul_sub, hk, sub_self]
  have h0 : a - b = 0 := sprPow_mul_eq_zero hnd k (a - b) hz
  exact sub_eq_zero.mp h0

#print axioms sprAway_injective

end AwayPow

section DiscrNonZeroDiv

set_option linter.style.haveILetI false

variable (F : Type) [Field F] {r : ℕ} {n : ℕ} {T : Type} [CommRing T] [Algebra F T]

/-- ★★ **`lem:14.24` 的判别式假设（原文口径：`θ(Δ)` 是非零因子）**。

纯量形态 `θ(Δ·1) = scalar x` 是已发表输入 **`[2.9]`**（Saltman 讲义）的内容，
**不是**本文推出来的——见本节头的登记。 -/
def sprDiscrNonZeroDiv
    (θ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (Δ : Spr F r n) : Prop :=
  ∃ x : T, θ (Matrix.scalar (Fin n) Δ) = Matrix.scalar (Fin n) x ∧
    ∀ y : T, x * y = 0 → y = 0

#print axioms sprDiscrNonZeroDiv

/-- 纯量矩阵沿**系数环**的 `F`-代数同态：`(scalar x).map φ = scalar (φ x)`。 -/
theorem sprScalar_mapGen {T' : Type} [CommRing T'] [Algebra F T']
    (φ : T →ₐ[F] T') (x : T) :
    (Matrix.scalar (Fin n) x).map (⇑φ) = Matrix.scalar (Fin n) (φ x) := by
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ)]

#print axioms sprScalar_mapGen

/-- ★★ **判别式条件沿系数环局部化传输**：`sprDiscrUnit` 沿 `φ : T →ₐ[F] T'` 保持。 -/
theorem sprDiscrUnit_mapMatrix {T' : Type} [CommRing T'] [Algebra F T']
    (φ : T →ₐ[F] T')
    (θ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    {Δ : Spr F r n} (h : sprDiscrUnit F θ Δ) :
    sprDiscrUnit F (φ.mapMatrix.comp θ) Δ := by
  obtain ⟨x, hx, hxu⟩ := h
  refine ⟨φ x, ?_, hxu.map φ⟩
  show φ.mapMatrix (θ (Matrix.scalar (Fin n) Δ)) = Matrix.scalar (Fin n) (φ x)
  rw [hx]
  exact sprScalar_mapGen F φ x

#print axioms sprDiscrUnit_mapMatrix

/-- ★★★★ **`lem:14.24`：逐素局部化归约**（判别式条件已是**可逆**的内蕴形态）。

与 `thm1415_general_nontrivial`（§36）同一路线；`hΔ` 沿局部化的传输 = `sprDiscrUnit_mapMatrix`。 -/
theorem lem1424_of_discrUnit [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0}, θ₁ (ymat F r n k) = θ₂ (ymat F r n k))
    (hΔ : sprDiscrUnit F θ₁ (sprDiscr F)) :
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
    set φ : T →ₐ[F] Localization.AtPrime m :=
      IsScalarTower.toAlgHom F T (Localization.AtPrime m) with hφ
    have hX' : ((φ.mapMatrix).comp θ₁) (xdiag F r n)
        = ((φ.mapMatrix).comp θ₂) (xdiag F r n) := by
      show φ.mapMatrix (θ₁ (xdiag F r n)) = φ.mapMatrix (θ₂ (xdiag F r n))
      rw [hX]
    have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
        ((φ.mapMatrix).comp θ₁) (ymat F r n k)
          = ((φ.mapMatrix).comp θ₂) (ymat F r n k) := by
      intro k
      show φ.mapMatrix (θ₁ (ymat F r n k)) = φ.mapMatrix (θ₂ (ymat F r n k))
      rw [hY k]
    have hloc : ((φ.mapMatrix).comp θ₁) α = ((φ.mapMatrix).comp θ₂) α :=
      lem1424_localNoNorm F α hα ((φ.mapMatrix).comp θ₁) ((φ.mapMatrix).comp θ₂)
        hX' hY' (sprDiscrUnit_mapMatrix F φ θ₁ hΔ)
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

#print axioms lem1424_of_discrUnit

/-- ★★★★★ **`lem:14.24`（一般 `S''`，原文口径）**：`α` `N`-不变、`θ₁ θ₂` 在 `R(F,n,r)` 上
一致、`θ₁(Δ)` 是非零因子 ⟹ `θ₁ α = θ₂ α`。

证明 ＝ 原文那两句：先把判别式倒掉（`Localization.Away` ＋ `sprAway_injective`），
再逐素局部化到局部环（`lem1424_of_discrUnit`）。 -/
theorem lem1424_general [Nonempty (Fin n)] [Infinite F]
    (α : Matrix (Fin n) (Fin n) (Spr F r n))
    (hα : ∀ (τ : Equiv.Perm (Fin n)) (b : Fin n → Fˣ),
      sprPsiMonoR (F := F) (r := r) (Spr F r n)
        (fun i => MvPolynomial.X (Sum.inl i)) (fun ijk => MvPolynomial.X (Sum.inr ijk)) τ
        (fun i => Units.map (algebraMap F (Spr F r n)).toMonoidHom ((b i)⁻¹)) α = α)
    (θ₁ θ₂ : Matrix (Fin n) (Fin n) (Spr F r n) →ₐ[F] Matrix (Fin n) (Fin n) T)
    (hX : θ₁ (xdiag F r n) = θ₂ (xdiag F r n))
    (hY : ∀ k : {k : Fin r // k.val ≠ 0}, θ₁ (ymat F r n k) = θ₂ (ymat F r n k))
    (hΔ : sprDiscrNonZeroDiv F θ₁ (sprDiscr F)) :
    θ₁ α = θ₂ α := by
  classical
  by_cases hT : Nontrivial T
  · haveI : Nontrivial T := hT
    obtain ⟨x, hx, hnd⟩ := hΔ
    set φ : T →ₐ[F] Localization.Away x :=
      IsScalarTower.toAlgHom F T (Localization.Away x) with hφ
    have hΔ' : sprDiscrUnit F ((φ.mapMatrix).comp θ₁) (sprDiscr F) := by
      refine ⟨φ x, ?_, ?_⟩
      · show φ.mapMatrix (θ₁ (Matrix.scalar (Fin n) (sprDiscr F)))
          = Matrix.scalar (Fin n) (φ x)
        rw [hx]
        exact sprScalar_mapGen F φ x
      · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x
    have hX' : ((φ.mapMatrix).comp θ₁) (xdiag F r n)
        = ((φ.mapMatrix).comp θ₂) (xdiag F r n) := by
      show φ.mapMatrix (θ₁ (xdiag F r n)) = φ.mapMatrix (θ₂ (xdiag F r n))
      rw [hX]
    have hY' : ∀ k : {k : Fin r // k.val ≠ 0},
        ((φ.mapMatrix).comp θ₁) (ymat F r n k)
          = ((φ.mapMatrix).comp θ₂) (ymat F r n k) := by
      intro k
      show φ.mapMatrix (θ₁ (ymat F r n k)) = φ.mapMatrix (θ₂ (ymat F r n k))
      rw [hY k]
    have hloc : ((φ.mapMatrix).comp θ₁) α = ((φ.mapMatrix).comp θ₂) α :=
      lem1424_of_discrUnit F α hα ((φ.mapMatrix).comp θ₁) ((φ.mapMatrix).comp θ₂) hX' hY' hΔ'
    have hinj : Function.Injective (algebraMap T (Localization.Away x)) :=
      sprAway_injective hnd (Localization.Away x)
    ext i j
    apply hinj
    have hφapp : ⇑φ = algebraMap T (Localization.Away x) := rfl
    have hentry' := congrFun (congrFun hloc i) j
    simpa [AlgHom.mapMatrix_apply, hφapp] using hentry'
  · haveI : Subsingleton T := not_nontrivial_iff_subsingleton.mp hT
    exact Subsingleton.elim _ _

#print axioms lem1424_general

end DiscrNonZeroDiv

/-! ## §138 **`(B)` 世界的分式域 `K' = Frac(S')` 与 `N`-作用** —— `lem:14.25` 的地基

源文 `raw/Saltman1999ch14.tex:363`（逐字，`N`-作用的定义之后）：

> "…we have an action of `N` on `S'` and `M_n(S')`. Of course, we then have **induced actions on
> the field of fractions `K'` of `S'`** and `M_n(K') = M_n(S') ⊗_{S'} K'`."

`prop:14.19`（`:368`）的右端 `K'^N` 与 `lem:14.25`（`:448`）全都在 `K'` 里陈述。而 §67／§85–§98
只做到**多项式层**（`Spr` 上的 `sprPermAlgEquiv`／`sprDiagHom`，`SprFixed` 子代数）。
本节补上**分式域层**（＝源文 `:363` 那一步），以及 `lem:14.25` 的两条技术引理。

**件**：

1. **`SprField F r n = FractionRing (Spr F r n)`**（`K'`；源文 `:363`）；
2. `sprDiagEquiv`／`sprPermAlgEquiv` ⟹ `sprDiagFieldEquiv`／`sprPermFieldEquiv`：
   两个作用提升到 `K'`（`IsFractionRing.ringEquivOfRingEquiv`，与 `KAction.lean` 的
   `phiKEquiv` **同一手法**）；
3. `sprFieldTFixed`／`sprFieldSFixed`／**`sprFieldNFixed`**：`K'^T`、`K'^{S_n}`、`K'^N`；
4. **比值论证的三件**（`sprDiag_mul_eq_of_fixed`／`sprDiag_dvd_of_fixed`／
   `sprDiag_exists_unit_mul_of_fixed`）：`lem:14.13`（`FixedRatio.lean` 的
   `exists_unit_mul_of_fixed`）的 **`S'`-世界对应物**——`f/g` 被 `φ_b` 固定 ＋ `f,g` 互素
   ⟹ `φ_b(g) = c·g` 且 `c` 是**单位**。

**工艺**：原文 `lem:14.13` 用**次数论证**（"`φ_A` 是线性换元故保持总次数"）。本库改用
**对偶整除**（`exists_unit_mul_of_fixed` 的原始发现）：对 `b` 与 `b⁻¹` 各用一次 `g ∣ φ(g)`，
两次相消即得 `c` 可逆——**不需要总次数**。这里逐字照搬该手法（R163：库内已有，不自造）。

**射程（勿夸大）**：本节只到"`φ_b(g) = c·g`，`c` 可逆"。`lem:14.25` 的**结论**
（`s, β'` 皆 `N`-不变）还需两步：①把特征标 `c` 从单位**提升为单项式权**并乘上权的逆
（`T` 部分）；②源文 `:453` 的**轨道积** `s' = ∏_{σ ∈ S_n} σ(s)`（`S_n` 部分）。
`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprFieldWorld

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `(B)` 世界的 `K' = Frac(S')`（源文 `:363`："the field of fractions `K'` of `S'`"）。 -/
abbrev SprField := FractionRing (Spr F r n)

#print axioms SprField

/-- ★ **环面作用的 `AlgEquiv` 包装**（群律 §87 ＋ `sprDiagHom_one`）。 -/
noncomputable def sprDiagEquiv (b : Fin n → Fˣ) : Spr F r n ≃ₐ[F] Spr F r n :=
  AlgEquiv.ofAlgHom (sprDiagHom F r n b) (sprDiagHom F r n (fun i => (b i)⁻¹))
    (by
      rw [sprDiagHom_mul]
      have h : (fun i => b i * (b i)⁻¹) = fun _ => 1 := by
        funext i; exact mul_inv_cancel (b i)
      rw [h, sprDiagHom_one])
    (by
      rw [sprDiagHom_mul]
      have h : (fun i => (b i)⁻¹ * b i) = fun _ => 1 := by
        funext i; exact inv_mul_cancel (b i)
      rw [h, sprDiagHom_one])

#print axioms sprDiagEquiv

/-- `sprDiagEquiv` 在多项式层就是 `sprDiagHom`（供 `simp`／`rfl` 落点）。 -/
theorem sprDiagEquiv_apply (b : Fin n → Fˣ) (x : Spr F r n) :
    sprDiagEquiv F r n b x = sprDiagHom F r n b x := rfl

#print axioms sprDiagEquiv_apply

/-- ★★ **`T` 在 `K'` 上的作用**（源文 `:363` 的"induced actions on `K'`"；`T` 部分）。 -/
noncomputable def sprDiagFieldEquiv (b : Fin n → Fˣ) :
    SprField F r n ≃+* SprField F r n :=
  IsFractionRing.ringEquivOfRingEquiv (sprDiagEquiv F r n b).toRingEquiv

#print axioms sprDiagFieldEquiv

/-- `sprDiagFieldEquiv` 在 `S'` 的像上就是 `sprDiagHom`。 -/
theorem sprDiagFieldEquiv_algebraMap (b : Fin n → Fˣ) (x : Spr F r n) :
    sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) x)
      = algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

#print axioms sprDiagFieldEquiv_algebraMap

/-- ★★ **`S_n` 在 `K'` 上的作用**（源文 `:363` 的"induced actions on `K'`"；`S_n` 部分）。 -/
noncomputable def sprPermFieldEquiv (σ : Equiv.Perm (Fin n)) :
    SprField F r n ≃+* SprField F r n :=
  IsFractionRing.ringEquivOfRingEquiv (sprPermAlgEquiv F r n σ).toRingEquiv

#print axioms sprPermFieldEquiv

/-- `sprPermFieldEquiv` 在 `S'` 的像上就是 `sprPermAlgEquiv`。 -/
theorem sprPermFieldEquiv_algebraMap (σ : Equiv.Perm (Fin n)) (x : Spr F r n) :
    sprPermFieldEquiv F r n σ (algebraMap (Spr F r n) (SprField F r n) x)
      = algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

#print axioms sprPermFieldEquiv_algebraMap

/-- `K'` 的 `T`-固定点（`K'^T`）。 -/
def sprFieldTFixed (x : SprField F r n) : Prop :=
  ∀ b : Fin n → Fˣ, sprDiagFieldEquiv F r n b x = x

#print axioms sprFieldTFixed

/-- `K'` 的 `S_n`-固定点（`K'^{S_n}`）。 -/
def sprFieldSFixed (x : SprField F r n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), sprPermFieldEquiv F r n σ x = x

#print axioms sprFieldSFixed

/-- ★★★ **`K'^N`**（源文 `prop:14.19` 的右端）：`N = T ⋊ S_n` 的固定点。 -/
def sprFieldNFixed (x : SprField F r n) : Prop :=
  sprFieldTFixed F r n x ∧ sprFieldSFixed F r n x

#print axioms sprFieldNFixed

/-- `T`-不变的多项式（经 `algebraMap` 进 `K'`）在 `K'` 中仍是 `T`-不变的。 -/
theorem sprFieldTFixed_algebraMap {x : Spr F r n}
    (hx : ∀ b : Fin n → Fˣ, sprDiagHom F r n b x = x) :
    sprFieldTFixed F r n (algebraMap (Spr F r n) (SprField F r n) x) := by
  intro b
  rw [sprDiagFieldEquiv_algebraMap, hx]

#print axioms sprFieldTFixed_algebraMap

/-- `S_n`-不变的多项式在 `K'` 中仍是 `S_n`-不变的。 -/
theorem sprFieldSFixed_algebraMap {x : Spr F r n}
    (hx : ∀ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ x = x) :
    sprFieldSFixed F r n (algebraMap (Spr F r n) (SprField F r n) x) := by
  intro σ
  rw [sprPermFieldEquiv_algebraMap, hx]

#print axioms sprFieldSFixed_algebraMap

end SprFieldWorld

section SprRatio

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★ **交叉等式**：`f/g` 被 `φ_b` 固定 ⟹ `φ_b(f)·g = f·φ_b(g)`
（`lem:14.13` 证明的第二句；`FixedRatio.lean` 的 `phiA_mul_eq_of_fixed` 的 `S'`-版）。 -/
theorem sprDiag_mul_eq_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n} (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    sprDiagHom F r n b f * g = f * sprDiagHom F r n b g := by
  have hinjA : Function.Injective (sprDiagHom F r n b) := (sprDiagEquiv F r n b).injective
  have hinj : Function.Injective (algebraMap (Spr F r n) (SprField F r n)) :=
    IsFractionRing.injective _ _
  have hφg : sprDiagHom F r n b g ≠ 0 := fun h => hg (hinjA (by simpa using h))
  have h1 : sprDiagFieldEquiv F r n b
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b f)
        / algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b g) := by
    rw [map_div₀, sprDiagFieldEquiv_algebraMap, sprDiagFieldEquiv_algebraMap]
  rw [h1] at hfix
  have hnum : algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b f)
      * algebraMap (Spr F r n) (SprField F r n) g
      = algebraMap (Spr F r n) (SprField F r n) f
        * algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b g) :=
    (div_eq_div_iff (by simpa using hinj.ne hφg) (by simpa using hinj.ne hg)).mp hfix
  have h2 : algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b f * g)
      = algebraMap (Spr F r n) (SprField F r n) (f * sprDiagHom F r n b g) := by
    rw [map_mul, map_mul]
    exact hnum
  exact hinj h2

#print axioms sprDiag_mul_eq_of_fixed

/-- ★★ **整除步**（`lem:14.13`："As `f` and `g` have no common divisors, `g` divides `φ_A(g)`"）：
`f, g` 互素 ＋ `f/g` 被 `φ_b` 固定 ⟹ `g ∣ φ_b(g)`。 -/
theorem sprDiag_dvd_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    g ∣ sprDiagHom F r n b g := by
  have hcross := sprDiag_mul_eq_of_fixed F r n b hg hfix
  refine IsRelPrime.dvd_of_dvd_mul_right hcop.symm ⟨sprDiagHom F r n b f, ?_⟩
  rw [mul_comm (sprDiagHom F r n b g) f, mul_comm g (sprDiagHom F r n b f)]
  exact hcross.symm

#print axioms sprDiag_dvd_of_fixed

/-- ★★★ **特征向量步**：对 `b` 与 `b⁻¹` 各用一次 `g ∣ φ(g)`，**对偶整除**把
`φ_b(g) = c·g` 里的 `c` 逼成**单位**（替代原文 `lem:14.13` 的总次数论证）。 -/
theorem sprDiag_exists_unit_mul_of_fixed (b : Fin n → Fˣ) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprDiagFieldEquiv F r n b
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
    (hfixinv : sprDiagFieldEquiv F r n (fun i => (b i)⁻¹)
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ c : Spr F r n, IsUnit c ∧ sprDiagHom F r n b g = c * g := by
  obtain ⟨h, hh⟩ := sprDiag_dvd_of_fixed F r n b hcop hg hfix
  obtain ⟨k, hk⟩ := sprDiag_dvd_of_fixed F r n (fun i => (b i)⁻¹) hcop hg hfixinv
  have hcomp : ∀ x : Spr F r n,
      sprDiagHom F r n (fun i => (b i)⁻¹) (sprDiagHom F r n b x) = x := by
    intro x
    have h : (sprDiagHom F r n (fun i => (b i)⁻¹)).comp (sprDiagHom F r n b)
        = AlgHom.id F (Spr F r n) := by
      rw [sprDiagHom_mul]
      have hfun : (fun i => (b i)⁻¹ * b i) = fun _ => 1 := by
        funext i; exact inv_mul_cancel (b i)
      rw [hfun, sprDiagHom_one]
    have := congrArg (fun (f : Spr F r n →ₐ[F] Spr F r n) => f x) h
    simpa using this
  have hAcomp : ∀ x : Spr F r n,
      sprDiagHom F r n b (sprDiagHom F r n (fun i => (b i)⁻¹) x) = x := by
    intro x
    have h : (sprDiagHom F r n b).comp (sprDiagHom F r n (fun i => (b i)⁻¹))
        = AlgHom.id F (Spr F r n) := by
      rw [sprDiagHom_mul]
      have hfun : (fun i => b i * (b i)⁻¹) = fun _ => 1 := by
        funext i; exact mul_inv_cancel (b i)
      rw [hfun, sprDiagHom_one]
    have := congrArg (fun (f : Spr F r n →ₐ[F] Spr F r n) => f x) h
    simpa using this
  have hkey : g = g * (k * sprDiagHom F r n (fun i => (b i)⁻¹) h) := by
    calc g = sprDiagHom F r n (fun i => (b i)⁻¹) (sprDiagHom F r n b g) := (hcomp g).symm
      _ = sprDiagHom F r n (fun i => (b i)⁻¹) (g * h) := by rw [hh]
      _ = sprDiagHom F r n (fun i => (b i)⁻¹) g
            * sprDiagHom F r n (fun i => (b i)⁻¹) h := map_mul _ _ _
      _ = (g * k) * sprDiagHom F r n (fun i => (b i)⁻¹) h := by rw [hk]
      _ = g * (k * sprDiagHom F r n (fun i => (b i)⁻¹) h) := by rw [mul_assoc]
  have hone : k * sprDiagHom F r n (fun i => (b i)⁻¹) h = 1 := by
    have h1 : g * (k * sprDiagHom F r n (fun i => (b i)⁻¹) h) = g * 1 := by
      rw [mul_one, ← hkey]
    exact mul_left_cancel₀ hg h1
  have hunit_inv : IsUnit (sprDiagHom F r n (fun i => (b i)⁻¹) h) := by
    refine isUnit_iff_exists_inv.mpr ⟨k, ?_⟩
    rw [mul_comm]
    exact hone
  have hunit : IsUnit h := by
    have hm := hunit_inv.map (sprDiagHom F r n b).toRingHom
    simpa [hAcomp h] using hm
  exact ⟨h, hunit, by rw [hh, mul_comm]⟩

#print axioms sprDiag_exists_unit_mul_of_fixed

end SprRatio

/-! ## §139 **`S_n`-侧的比值论证** —— `lem:14.25` 的第 4 步（`u_σ^{n!} = 1`）

`lem:14.25`（源文 `:447–453`）的证明最后一句（`:453` 逐字）：

> "Write `s' = ∏_{σ ∈ S_n} σ(s)` … `s'` is `N` invariant and therefore `β' s''` is `N` invariant."

`S_n` 部分与 `T` 部分**同构**：`lem:14.13` 的比值论证对**任意**群元成立，故对 `σ ∈ S_n`
给出 `φ_σ(g) = C(u_σ)·g`。与环面不同，`S_n` 是**有限群**，故特征标 `u : S_n → Fˣ`
满足 `u_σ^{|S_n|} = 1`（`|S_n| = n!`）——正是 `lem:14.13` 里 `λ(A)^k = 1` 那一步的
**结构对应物**。于是 `s := g^{n!}`、`β := f·g^{n!-1}` 皆 `S_n`-不变、`α' = β/s`。

§138 已给 `T` 侧的三件（`sprDiag_*`）；本节给**完全相同**的 `S_n` 侧三件，外加它所需的
**群律**（§87 只给了环面的；`sprPermAlgEquiv` 的函子性此前**缺失**）。

**件**：
1. `sprPerm_trans`／`sprPerm_refl`：`sprPerm` 的函子性（`S_n` 作为**置换群**的群律）；
2. `sprPermAlgEquiv_trans`／`sprPermAlgEquiv_refl`：`sprPermAlgEquiv` 的函子性 ＋ 单位律
   （`MvPolynomial.renameEquiv_trans` ＋ `MvPolynomial.renameEquiv_refl`）；
3. `sprPerm_mul_eq_of_fixed`／`sprPerm_dvd_of_fixed`／**`sprPerm_exists_unit_mul_of_fixed`**
   ——§138 三件的 `S_n` 对应物（逐字同构；消去步用 2 的群律）。

**工艺（一处 `ext` 陷阱）**：证 `σ.trans σ⁻¹ = Equiv.refl` 时，`ext i` 会**落到 `Fin.ext`**
（把目标变成 `ℕ` 里的等式，`i` 也不再是 `Fin n`），于是 `Equiv.symm_apply_apply` 类型不符；
正解是显式写 `Equiv.ext (fun i => Equiv.symm_apply_apply σ i)`（R170：`simpa`／显式形式比
`rw` 稳）。

**射程（勿夸大）**：本节只到"`φ_σ(g) = c·g`，`c` 可逆"（＝与 `T` 侧同一块）。
`lem:14.25` 的**结论**仍缺：特征标的提取（打包成 `→* Fˣ`）、**特征标杀死**（`T` 侧 `c_b = 1`，
见 [[proj-lem1425-plan-2026-10-19]] §3）、矩阵层归约。
`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprPermRatio

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)



/-- `sprPerm` 的函子性。 -/
theorem sprPerm_trans (σ τ : Equiv.Perm (Fin n)) :
    (sprPerm r n σ).trans (sprPerm r n τ) = sprPerm r n (σ.trans τ) := by
  ext v
  rcases v with i | ⟨i, j, k⟩ <;> simp [sprPerm]

#print axioms sprPerm_trans

/-- `sprPermAlgEquiv` 的函子性（`S_n` 群律）。 -/
theorem sprPermAlgEquiv_trans (σ τ : Equiv.Perm (Fin n)) :
    (sprPermAlgEquiv F r n σ).trans (sprPermAlgEquiv F r n τ)
      = sprPermAlgEquiv F r n (σ.trans τ) := by
  rw [sprPermAlgEquiv, sprPermAlgEquiv, sprPermAlgEquiv, MvPolynomial.renameEquiv_trans,
    sprPerm_trans]

#print axioms sprPermAlgEquiv_trans

/-- `sprPerm` 在单位元上平凡。 -/
theorem sprPerm_refl : sprPerm r n (Equiv.refl (Fin n)) = Equiv.refl (SprIdx r n) := by
  ext v
  rcases v with i | ⟨i, j, k⟩ <;> rfl

#print axioms sprPerm_refl

/-- 单位律。 -/
theorem sprPermAlgEquiv_refl :
    sprPermAlgEquiv F r n (Equiv.refl (Fin n)) = AlgEquiv.refl := by
  rw [sprPermAlgEquiv, sprPerm_refl, MvPolynomial.renameEquiv_refl]

#print axioms sprPermAlgEquiv_refl




/-- ★★ **交叉等式（`S_n` 侧）**：`f/g` 被 `φ_σ` 固定 ⟹ `φ_σ(f)·g = f·φ_σ(g)`。 -/
theorem sprPerm_mul_eq_of_fixed (σ : Equiv.Perm (Fin n)) {f g : Spr F r n} (hg : g ≠ 0)
    (hfix : sprPermFieldEquiv F r n σ
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    sprPermAlgEquiv F r n σ f * g = f * sprPermAlgEquiv F r n σ g := by
  have hinjA : Function.Injective (sprPermAlgEquiv F r n σ) :=
    (sprPermAlgEquiv F r n σ).injective
  have hinj : Function.Injective (algebraMap (Spr F r n) (SprField F r n)) :=
    IsFractionRing.injective _ _
  have hφg : sprPermAlgEquiv F r n σ g ≠ 0 := fun h => hg (hinjA (by simpa using h))
  have h1 : sprPermFieldEquiv F r n σ
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ f)
        / algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ g) := by
    rw [map_div₀, sprPermFieldEquiv_algebraMap, sprPermFieldEquiv_algebraMap]
  rw [h1] at hfix
  have hnum : algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ f)
      * algebraMap (Spr F r n) (SprField F r n) g
      = algebraMap (Spr F r n) (SprField F r n) f
        * algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ g) :=
    (div_eq_div_iff (by simpa using hinj.ne hφg) (by simpa using hinj.ne hg)).mp hfix
  have h2 : algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ f * g)
      = algebraMap (Spr F r n) (SprField F r n) (f * sprPermAlgEquiv F r n σ g) := by
    rw [map_mul, map_mul]
    exact hnum
  exact hinj h2

#print axioms sprPerm_mul_eq_of_fixed

/-- ★★ **整除步（`S_n` 侧）**。 -/
theorem sprPerm_dvd_of_fixed (σ : Equiv.Perm (Fin n)) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprPermFieldEquiv F r n σ
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    g ∣ sprPermAlgEquiv F r n σ g := by
  have hcross := sprPerm_mul_eq_of_fixed F r n σ hg hfix
  refine IsRelPrime.dvd_of_dvd_mul_right hcop.symm ⟨sprPermAlgEquiv F r n σ f, ?_⟩
  rw [mul_comm (sprPermAlgEquiv F r n σ g) f, mul_comm g (sprPermAlgEquiv F r n σ f)]
  exact hcross.symm

#print axioms sprPerm_dvd_of_fixed

/-- ★★★ **特征向量步（`S_n` 侧）**：对 `σ` 与 `σ⁻¹` 各用一次 `g ∣ φ(g)`。 -/
theorem sprPerm_exists_unit_mul_of_fixed (σ : Equiv.Perm (Fin n)) {f g : Spr F r n}
    (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : sprPermFieldEquiv F r n σ
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
    (hfixinv : sprPermFieldEquiv F r n σ⁻¹
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ c : Spr F r n, IsUnit c ∧ sprPermAlgEquiv F r n σ g = c * g := by
  obtain ⟨h, hh⟩ := sprPerm_dvd_of_fixed F r n σ hcop hg hfix
  obtain ⟨k, hk⟩ := sprPerm_dvd_of_fixed F r n σ⁻¹ hcop hg hfixinv
  have hcomp : ∀ x : Spr F r n,
      sprPermAlgEquiv F r n σ⁻¹ (sprPermAlgEquiv F r n σ x) = x := by
    intro x
    have h : (sprPermAlgEquiv F r n σ).trans (sprPermAlgEquiv F r n σ⁻¹) = AlgEquiv.refl := by
      rw [sprPermAlgEquiv_trans,
        show (σ : Equiv.Perm (Fin n)).trans σ⁻¹ = Equiv.refl (Fin n) from
          Equiv.ext (fun i => Equiv.symm_apply_apply σ i),
        sprPermAlgEquiv_refl]
    have := congrArg (fun (e : Spr F r n ≃ₐ[F] Spr F r n) => e x) h
    simpa using this
  have hAcomp : ∀ x : Spr F r n,
      sprPermAlgEquiv F r n σ (sprPermAlgEquiv F r n σ⁻¹ x) = x := by
    intro x
    have h : (sprPermAlgEquiv F r n σ⁻¹).trans (sprPermAlgEquiv F r n σ) = AlgEquiv.refl := by
      rw [sprPermAlgEquiv_trans,
        show (σ⁻¹ : Equiv.Perm (Fin n)).trans σ = Equiv.refl (Fin n) from
          Equiv.ext (fun i => Equiv.apply_symm_apply σ i),
        sprPermAlgEquiv_refl]
    have := congrArg (fun (e : Spr F r n ≃ₐ[F] Spr F r n) => e x) h
    simpa using this
  have hkey : g = g * (k * sprPermAlgEquiv F r n σ⁻¹ h) := by
    calc g = sprPermAlgEquiv F r n σ⁻¹ (sprPermAlgEquiv F r n σ g) := (hcomp g).symm
      _ = sprPermAlgEquiv F r n σ⁻¹ (g * h) := by rw [hh]
      _ = sprPermAlgEquiv F r n σ⁻¹ g * sprPermAlgEquiv F r n σ⁻¹ h := map_mul _ _ _
      _ = (g * k) * sprPermAlgEquiv F r n σ⁻¹ h := by rw [hk]
      _ = g * (k * sprPermAlgEquiv F r n σ⁻¹ h) := by rw [mul_assoc]
  have hone : k * sprPermAlgEquiv F r n σ⁻¹ h = 1 := by
    have h1 : g * (k * sprPermAlgEquiv F r n σ⁻¹ h) = g * 1 := by
      rw [mul_one, ← hkey]
    exact mul_left_cancel₀ hg h1
  have hunit_inv : IsUnit (sprPermAlgEquiv F r n σ⁻¹ h) := by
    refine isUnit_iff_exists_inv.mpr ⟨k, ?_⟩
    rw [mul_comm]
    exact hone
  have hunit : IsUnit h := by
    have hm := hunit_inv.map (sprPermAlgEquiv F r n σ).toRingHom
    simpa [hAcomp h] using hm
  exact ⟨h, hunit, by rw [hh, mul_comm]⟩

#print axioms sprPerm_exists_unit_mul_of_fixed

end SprPermRatio

/-! ## §140 **特征标的提取** —— `lem:14.25` 的任务表第 3 项（`→* Fˣ` 打包）

[[proj-lem1425-plan-2026-10-19]] 的任务表第 3 项。§138／§139 已把 `lem:14.13` 的比值论证
在 `T` 侧与 `S_n` 侧各机检一遍，结论形状是"**对每个**群元 `A` 存在**单位** `c_A` 使
`φ_A(g) = c_A·g`"。本节把这件事**打包成群同态** `lam : N → Fˣ`：

`φ_A(g) = C(lam A)·g`，且 `lam` 是**乘性**的（`lam (A·B) = lam A · lam B`）。

**为何必须打包**：后续两步只对"**群同态**"成立——
* **`T` 侧杀掉特征标**（计划 §3 第 2 步）：需把 `φ_σ` 作用到 `φ_b(g) = C(c_b)g` 上并用
  §83 的半直积 `σ ∘ φ_b = φ_{σ·b} ∘ σ`；这要求 `c_{σ·b} = c_b`，而**乘性**给出
  `c_{σ·b} =??`——正交用的是 `lam : (Fin n → Fˣ) →* Fˣ` 的乘性，而不是逐个单位。
* **`S_n` 侧**：`lam : S_n →* Fˣ` 是**有限群**的同态 ⟹ `lam σ^{n!} = 1`
  （`MonoidHom` 的像落在有限群中，用 `lam (σ^{n!}) = lam 1 = 1`）。

**件**：
1. `sprDiagHom_C`／`sprPermAlgEquiv_C`：两个作用都**固定常数**（`AlgHom` 与 `algebraMap` 交换）；
2. `sprDiagHom_const`：**常数环面元作用平凡**（`T` 是 `PGL` 的环面，不是 `GL` 的——
   `y_ijk ↦ (u/u)y_ijk = y_ijk`）；
3. ★★★ **`sprDiag_exists_char`**：`f/g` 被整个 `T` 固定 ⟹ `∃ lam : (Fin n → Fˣ) →* Fˣ`，
   `∀ b, φ_b(g) = C(lam b)·g`；
4. ★★★ **`sprPerm_exists_char`**：同上，`S_n` 侧。

**工艺（三处形态陷阱，本批次实测）**：
* `MvPolynomial.isUnit_iff_eq_C_of_isReduced`（样板 `FixedRatio.lean` 的 `exists_lambda_hom`）
  把 `IsUnit c` 化成 `c = C x` 且 `x` 可逆——这是"单位在多项式环里必为常数"的**唯一**正解；
* 乘性步的比较要在**系数环**里做：`mul_right_cancel₀ hg` ＋ `MvPolynomial.C_injective`，
  最后 `Units.ext`。**注意 `Units.val_mul` 的方向**，以及 `Fˣ` 交换故末步可 `mul_comm`；
* **`Equiv.Perm` 的乘法是"反序"**：`(σ * τ : Equiv.Perm (Fin n)) = τ.trans σ`（`rfl`，
  本批次实测）。故 `φ_{σ*τ} = φ_σ ∘ φ_τ`，而 `sprPermAlgEquiv_trans σ τ` 给的是
  `(e_σ).trans (e_τ) = e_{σ.trans τ}`——**rewrite 方向必须取 `← sprPermAlgEquiv_trans τ σ`**，
  否则构造出 `.toMulEquiv.toMulHom.comp` 的怪形态（一次实测即踩）。

**射程（勿夸大）**：本节只**打包**已有结论，不产生新数学。
`lem:14.25` 仍缺：**特征标杀死**（`T` 侧 `c_b = 1`，计划 §3 的第 1、2 步＝系数比较 ＋ 半直积）
与矩阵层归约。`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprChar

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `φ_b` 固定常数（`AlgHom` 与 `algebraMap` 交换）。 -/
theorem sprDiagHom_C (b : Fin n → Fˣ) (c : F) :
    sprDiagHom F r n b (MvPolynomial.C c) = MvPolynomial.C c := by
  simp

#print axioms sprDiagHom_C

/-- 常数环面元作用平凡（`T` 是 `PGL` 的环面，不是 `GL` 的）。 -/
theorem sprDiagHom_const (u : Fˣ) :
    sprDiagHom F r n (fun _ => u) = AlgHom.id F (Spr F r n) := by
  refine MvPolynomial.algHom_ext (fun v => ?_)
  rcases v with i | ⟨i, j, k⟩
  · rw [sprDiagHom_X_inl]; rfl
  · rw [sprDiagHom_X_inr]
    have h : ((u : F) * ((u : F))⁻¹) = 1 := by field_simp
    rw [h, MvPolynomial.C_1, one_mul]
    rfl

#print axioms sprDiagHom_const

/-- ★★★ **环面特征标的提取**（`lem:14.25` 的 `T`-部分）：`f/g` 被整个 `T` 固定 ⟹
存在群同态 `lam : (Fin n → Fˣ) →* Fˣ` 使 `φ_b(g) = C(lam b)·g`。 -/
theorem sprDiag_exists_char {f g : Spr F r n} (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : ∀ b : Fin n → Fˣ, sprDiagFieldEquiv F r n b
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ lam : (Fin n → Fˣ) →* Fˣ,
      ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g := by
  classical
  have hex : ∀ b : Fin n → Fˣ, ∃ u : Fˣ,
      sprDiagHom F r n b g = MvPolynomial.C ((u : Fˣ) : F) * g := by
    intro b
    obtain ⟨c, hcunit, hc⟩ := sprDiag_exists_unit_mul_of_fixed F r n b hcop hg
      (hfix b) (hfix (fun i => (b i)⁻¹))
    obtain ⟨x, hxunit, hx⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hcunit
    obtain ⟨u, rfl⟩ := hxunit
    exact ⟨u, by rw [hc, hx]⟩
  choose lamFun hlam using hex
  refine ⟨{ toFun := lamFun, map_one' := ?_, map_mul' := ?_ }, fun b => hlam b⟩
  · have h1 : sprDiagHom F r n (fun _ => (1 : Fˣ)) g = g := by
      rw [sprDiagHom_one]; rfl
    have h := hlam (fun _ => 1)
    rw [h1] at h
    have hC : MvPolynomial.C ((lamFun (fun _ => 1) : Fˣ) : F) = 1 :=
      mul_right_cancel₀ hg (by rw [h.symm, one_mul])
    exact Units.ext ((MvPolynomial.C_injective (SprIdx r n) F) hC)
  · intro b b'
    have hAB : sprDiagHom F r n (b * b') g
        = MvPolynomial.C ((lamFun b' : Fˣ) : F)
          * MvPolynomial.C ((lamFun b : Fˣ) : F) * g := by
      rw [show sprDiagHom F r n (b * b')
          = (sprDiagHom F r n b).comp (sprDiagHom F r n b') from
        (sprDiagHom_mul F r n b b').symm]
      rw [AlgHom.comp_apply, hlam b', map_mul, hlam b, sprDiagHom_C]
      ring
    rw [hlam (b * b')] at hAB
    have hC : MvPolynomial.C ((lamFun (b * b') : Fˣ) : F)
        = MvPolynomial.C ((lamFun b' : Fˣ) : F) * MvPolynomial.C ((lamFun b : Fˣ) : F) :=
      mul_right_cancel₀ hg hAB
    rw [← map_mul] at hC
    have h' := (MvPolynomial.C_injective (SprIdx r n) F) hC
    refine Units.ext ?_
    rw [Units.val_mul]
    exact h'.trans (mul_comm _ _)

#print axioms sprDiag_exists_char




/-- `φ_σ` 固定常数。 -/
theorem sprPermAlgEquiv_C (σ : Equiv.Perm (Fin n)) (c : F) :
    sprPermAlgEquiv F r n σ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [sprPermAlgEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]

#print axioms sprPermAlgEquiv_C

/-- ★★★ **`S_n` 特征标的提取**（`lem:14.25` 的 `S_n` 部分）。 -/
theorem sprPerm_exists_char {f g : Spr F r n} (hcop : IsRelPrime f g) (hg : g ≠ 0)
    (hfix : ∀ σ : Equiv.Perm (Fin n), sprPermFieldEquiv F r n σ
      (algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g)
      = algebraMap (Spr F r n) (SprField F r n) f
        / algebraMap (Spr F r n) (SprField F r n) g) :
    ∃ lam : Equiv.Perm (Fin n) →* Fˣ,
      ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lam σ : Fˣ) : F) * g := by
  classical
  have hex : ∀ σ : Equiv.Perm (Fin n), ∃ u : Fˣ,
      sprPermAlgEquiv F r n σ g = MvPolynomial.C ((u : Fˣ) : F) * g := by
    intro σ
    obtain ⟨c, hcunit, hc⟩ := sprPerm_exists_unit_mul_of_fixed F r n σ hcop hg
      (hfix σ) (hfix σ⁻¹)
    obtain ⟨x, hxunit, hx⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hcunit
    obtain ⟨u, rfl⟩ := hxunit
    exact ⟨u, by rw [hc, hx]⟩
  choose lamFun hlam using hex
  refine ⟨{ toFun := lamFun, map_one' := ?_, map_mul' := ?_ }, fun σ => hlam σ⟩
  · have h1 : sprPermAlgEquiv F r n (1 : Equiv.Perm (Fin n)) g = g := by
      rw [show (1 : Equiv.Perm (Fin n)) = Equiv.refl (Fin n) from rfl, sprPermAlgEquiv_refl]
      rfl
    have h := hlam 1
    rw [h1] at h
    have hC : MvPolynomial.C ((lamFun 1 : Fˣ) : F) = 1 :=
      mul_right_cancel₀ hg (by rw [h.symm, one_mul])
    exact Units.ext ((MvPolynomial.C_injective (SprIdx r n) F) hC)
  · intro σ τ
    have hpt : sprPermAlgEquiv F r n (σ * τ) g
        = sprPermAlgEquiv F r n σ (sprPermAlgEquiv F r n τ g) := by
      rw [show (σ * τ : Equiv.Perm (Fin n)) = τ.trans σ from rfl]
      rw [← sprPermAlgEquiv_trans F r n τ σ, AlgEquiv.trans_apply]
    have hAB : sprPermAlgEquiv F r n (σ * τ) g
        = MvPolynomial.C ((lamFun τ : Fˣ) : F)
          * MvPolynomial.C ((lamFun σ : Fˣ) : F) * g := by
      rw [hpt, hlam τ, map_mul, hlam σ, sprPermAlgEquiv_C]
      ring
    rw [hlam (σ * τ)] at hAB
    have hC : MvPolynomial.C ((lamFun (σ * τ) : Fˣ) : F)
        = MvPolynomial.C ((lamFun τ : Fˣ) : F) * MvPolynomial.C ((lamFun σ : Fˣ) : F) :=
      mul_right_cancel₀ hg hAB
    rw [← map_mul] at hC
    have h' := (MvPolynomial.C_injective (SprIdx r n) F) hC
    refine Units.ext ?_
    rw [Units.val_mul]
    exact h'.trans (mul_comm _ _)

#print axioms sprPerm_exists_char

end SprChar

/-! ## §141 **系数比较** —— `lem:14.25` 的任务表第 4 项（杀特征标的前置）

[[proj-lem1425-plan-2026-10-19]] 的任务表第 4 项。§140 已把逐元单位打包成
`lam : N →* Fˣ`，使 `φ_b(g) = C(lam b)·g`（`g` 是分母）。本节把 `lam` **显式化**为
`g` 的某个**支撑单项式的权**：

```
∃ s, g.coeff s ≠ 0   ∧   lam b = ∏_v sprWt b v ^ (s v)   (∀ b)
```

**为何需要**：计划 §3 的"杀特征标"四步全靠这一显式形态——
① §96 `sprWtU_prod_exp` 把 `∏_v sprWt^s_v` 化成 `(∏_i b_i^{A_i})(∏_j b_j^{B_j})⁻¹`；
② §83 的半直积给出 `lam (σ·b) = lam b` ⟹ `A, B` 是**常向量**；
③ 常向量 ＋ `ΣA = ΣB` ⟹ `A = B` ⟹ `lam ≡ 1`。

**件**：
1. `sprDiagHom_monomial`：`φ_b(monomial s c) = C(c · ∏_v sprWt b v ^ s v) · monomial s 1`；
2. ★★★ **`sprDiagHom_coeff`**：`coeff s (φ_b g) = (∏_v sprWt b v ^ s v) · coeff s g`
   ——即 `φ_b` 在**单项式基**上是对角的，第 `s` 个系数乘上第 `s` 个权；
3. ★★★ **`sprDiag_support_weight`**：若 `φ_b g = C(lam)·g` 且 `g.coeff s ≠ 0`，
   则 `∏_v sprWt b v ^ s v = lam`——**系数比较的核心一步**。

**工艺（三处 `MvPolynomial` 形态，本批次实测）**：
* `coeff` **不是** `MvPolynomial` 命名空间里的函数：它是 `AddMonoidAlgebra.coeff` 的投影，
  写作 **`p.coeff s`**（点号形式）。写 `MvPolynomial.coeff s p` 会报 "unknown constant"
  （错误信息完全不指向根因——R171 家族）；
* `monomial s 1 = ∏ v ∈ s.support, X v ^ s v`：由 `MvPolynomial.monomial_eq` ＋
  `Finsupp.prod`（`Finsupp.prod = support.prod ∘ …`，故 `rw [Finsupp.prod]` 一步落地）；
* 系数比较的**线性**部分：`MvPolynomial.as_sum`（`g = ∑_{s ∈ supp} monomial s (coeff s g)`）
  ＋ `map_sum` ＋ `MvPolynomial.coeff_sum` ＋ `Finset.sum_ite_eq'`；`hterm` 里先
  `coeff_C_mul` 再 `coeff_monomial`（**不要**先 `C_mul_monomial`——那条会留下 `if` 的
  `split_ifs` 负担）。

**射程（勿夸大）**：本节只是**系数簿记**，不产生新数学。特征标**尚未杀死**
（`lam ≡ 1` 未证）；矩阵层归约未做。`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed`
—— **未做/未证**。**H2 仍不是定理。** -/

section SprCoeff

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- 单项式的权：`φ_b` 把 `monomial s c` 乘上权 `∏_v sprWt b v ^ s v`。 -/
theorem sprDiagHom_monomial (b : Fin n → Fˣ) (s : SprIdx r n →₀ ℕ) (c : F) :
    sprDiagHom F r n b (MvPolynomial.monomial s c)
      = MvPolynomial.C (c * (∏ v ∈ s.support, sprWt F r n b v ^ s v))
        * MvPolynomial.monomial s 1 := by
  have hwt := sprDiagHom_monomial_weight F r n b s.support (fun v => s v)
  have hmono : MvPolynomial.monomial s c = MvPolynomial.C c *
      (∏ v ∈ s.support, MvPolynomial.X v ^ s v) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod]
  have hmono1 : MvPolynomial.monomial s (1 : F) =
      ∏ v ∈ s.support, MvPolynomial.X v ^ s v := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod, map_one, one_mul]
  rw [hmono, map_mul, map_mul, sprDiagHom_C, hwt, hmono1]
  rw [← mul_assoc, ← map_mul]

#print axioms sprDiagHom_monomial

/-- ★★★ **系数比较**：`φ_b` 把单项式 `s` 的系数乘上它的权。 -/
theorem sprDiagHom_coeff (b : Fin n → Fˣ) (g : Spr F r n) (s : SprIdx r n →₀ ℕ) :
    (sprDiagHom F r n b g).coeff s
      = (∏ v ∈ s.support, sprWt F r n b v ^ s v) * g.coeff s := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum g]
  rw [map_sum, MvPolynomial.coeff_sum]
  have hterm : ∀ x ∈ g.support,
      (sprDiagHom F r n b (MvPolynomial.monomial x (g.coeff x))).coeff s
        = (∏ v ∈ s.support, sprWt F r n b v ^ s v) *
            (if x = s then g.coeff x else 0) := by
    intro x _
    rw [sprDiagHom_monomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    by_cases hxs : x = s
    · subst hxs
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg hxs, if_neg hxs, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_eq']
  by_cases h : s ∈ g.support
  · rw [if_pos h]
  · rw [if_neg h, MvPolynomial.notMem_support_iff.mp h]

#print axioms sprDiagHom_coeff

/-- ★★★ **支撑单项式的权 ＝ 特征标**（`lem:14.25` 的系数比较步）。 -/
theorem sprDiag_support_weight (b : Fin n → Fˣ) {g : Spr F r n}
    {u : Fˣ} (h : sprDiagHom F r n b g = MvPolynomial.C (u : F) * g)
    {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) :
    (∏ v ∈ s.support, sprWt F r n b v ^ s v) = (u : F) := by
  have hc := congrArg (fun p => p.coeff s) h
  simp only [sprDiagHom_coeff, MvPolynomial.coeff_C_mul] at hc
  exact mul_right_cancel₀ hs hc

#print axioms sprDiag_support_weight

end SprCoeff

/-! ## §142 **特征标的指数形态** —— `lem:14.25` 杀特征标的第一步

[[proj-lem1425-plan-2026-10-19]] §3 的第 1 步。§141 把特征标化成**某个支撑单项式的权**
`lam b = ∏_v sprWt b v ^ (s v)`。本节把该乘积写成**显式指数形态**

```
lam b = (∏_i b_i^{A_i}) · (∏_j b_j^{B_j})⁻¹ ,   A_i = Σ_{j,k} s(i,j,k),  B_j = Σ_{i,k} s(i,j,k)
```

**为何需要**：计划 §3 的第 2、3 步全靠这个形态——
* 半直积（§83）给 `lam (c ∘ σ⁻¹) = lam c`；代入指数形态后**比较指数**（§97 `coord_of_prod_eq`）
  得 `A`、`B` 都是**常向量**；
* 常向量 ＋ `Σ_i A_i = Σ_j B_j`（两边都等于 `s` 的 `y`-总次数）⟹ `A = B` ⟹ `lam ≡ 1`。

**件**：
1. `sprDiag_support_weightU`：`lam` 的 `Fˣ` 形态（`∏_{v ∈ supp} sprWtU b v ^ s v = lam b`；
   从 §141 的 `F`-形态经 `push_cast` ＋ `sprWt_eq_coe_sprWtU` 得到）；
2. `sprWtU_prod_support_eq_univ`：`∏_{v ∈ supp}` 与 `∏_{v}` 相同（支撑外指数为 `0`，
   `Finset.prod_subset` ＋ `Finsupp.notMem_support_iff`）；
3. ★★★★ **`sprDiag_char_exp`**：指数形态（直接消费 §96 的 `sprWtU_prod_exp`）。

**工艺（一处 coercion）**：`↑(∏ …) = ∏ ↑…` 用 **`push_cast`** 一次落地
（`map_prod`＋`Units.coe_pow` 两条手写不稳；`push_cast` 自动处理 `Units.val` 的乘积与幂）。

**射程（勿夸大）**：本节只给**形态**。特征标**尚未杀死**（`lam ≡ 1` 未证——还差
半直积的对称性一步与指数比较）；矩阵层归约未做。`prop:14.19` 装配、`V2'`／`V3'`、
`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprCharExp

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- 权在 `Fˣ` 里的形态：支撑单项式的权 ＝ 特征标。 -/
theorem sprDiag_support_weightU (b : Fin n → Fˣ) {g : Spr F r n}
    {u : Fˣ} (h : sprDiagHom F r n b g = MvPolynomial.C (u : F) * g)
    {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) :
    (∏ v ∈ s.support, sprWtU r n b v ^ s v) = u := by
  have hF := sprDiag_support_weight F r n b h hs
  refine Units.ext ?_
  rw [← hF]
  push_cast
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [sprWt_eq_coe_sprWtU]

#print axioms sprDiag_support_weightU

/-- 支撑的 `univ` 化：`∏_{v ∈ s.support}` 与 `∏_v` 相同（支撑外指数为 `0`）。 -/
theorem sprWtU_prod_support_eq_univ (b : Fin n → Fˣ) (s : SprIdx r n →₀ ℕ) :
    (∏ v ∈ s.support, sprWtU r n b v ^ s v)
      = ∏ v : SprIdx r n, sprWtU r n b v ^ s v := by
  rw [Finset.prod_subset (Finset.subset_univ _) (fun v _ hv => by
    rw [Finsupp.notMem_support_iff.mp hv, pow_zero])]

#print axioms sprWtU_prod_support_eq_univ




variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **特征标的指数形态**：`lam b = (∏_i b_i^{A_i})·(∏_i b_i^{B_i})⁻¹`。 -/
theorem sprDiag_char_exp (b : Fin n → Fˣ) {g : Spr F r n} {u : Fˣ}
    (h : sprDiagHom F r n b g = MvPolynomial.C (u : F) * g)
    {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) :
    u = (∏ i : Fin n, (b i) ^ (Finset.univ.sum
            (fun q : Fin n × {k : Fin r // k.val ≠ 0} => s (Sum.inr (i, q.1, q.2)))))
        * (∏ j : Fin n, (b j) ^ (Finset.univ.sum (fun i : Fin n => Finset.univ.sum
            (fun k : {k : Fin r // k.val ≠ 0} => s (Sum.inr (i, j, k))))))⁻¹ := by
  have hU := sprDiag_support_weightU F r n b h hs
  rw [sprWtU_prod_support_eq_univ, sprWtU_prod_exp] at hU
  exact hU.symm

#print axioms sprDiag_char_exp

end SprCharExp

/-! ## §143 **半直积给的特征标对称性** —— `lem:14.25` 杀特征标第二步

[[proj-lem1425-plan-2026-10-19]] §3 的第 2 步（前半）。§142 已把特征标写成指数形态
`lam b = (∏_i b_i^{A_i})(∏_j b_j^{B_j})⁻¹`。本节证明 `lam` 在**置换重标号**下不变：

```
lam (c ∘ σ⁻¹) = lam c      (∀ c, σ)
```

**机制（源文 `:361` 的 `N = T ⋊ S_n`，本仓 §83 已机检）**：
`sprPerm_sprDiagHom_comp σ c : φ_σ ∘ φ_c = φ_{c∘σ⁻¹} ∘ φ_σ`。两侧作用于分母 `g`
（由 §140 有 `φ_A g = C(lam A)·g`，`A` 跑遍 `T` 与 `S_n`）：

```
LHS = C(lam c) · φ_σ(g) = C(lam c · lamS σ) · g
RHS = C(lamS σ) · φ_{c∘σ⁻¹}(g) = C(lamS σ · lam (c∘σ⁻¹)) · g
```

比较并消去 `lamS σ`（单位故非零，`mul_left_cancel₀`）即得。

**下游（下一轮）**：把 §142 的指数形态代入本节的对称性，得
`∏_i c_i^{A_{σ i}} · (∏_i c_i^{B_{σ i}})⁻¹ = ∏_i c_i^{A_i} · (∏_i c_i^{B_i})⁻¹`
对**所有** `c` 成立 ⟹（§97 `coord_of_prod_eq`）`A`、`B` 是**常向量**；
再由 `Σ_i A_i = Σ_j B_j`（两边都等于 `s` 的 `y`-总次数）得 `A = B` ⟹ **`lam ≡ 1`**。

**工艺（`C` 的推动）**：`hpt` 的形状是 `C a * C s * g = C s * C b * g`，而
`mul_right_cancel₀` 要吃 `C (a*s) * g = C (s*b) * g`——先用 `MvPolynomial.C_mul`
把两侧写成 `C(乘积)` 再 `exact hpt`；消去后用 `MvPolynomial.C_injective` 落回 `F`。
两处 `ring` 处理 `C a * (C s * g)` 与 `C a * C s * g` 的结合律差异。

**射程（勿夸大）**：本节只给**对称性**。特征标**尚未杀死**（指数比较未做）；
矩阵层归约未做。`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。
**H2 仍不是定理。** -/

section SprCharSymm

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **半直积给的特征标对称性**：`lam (c ∘ σ⁻¹) = lam c`。

**机制**：§83 的 `sprPerm_sprDiagHom_comp σ c`：`φ_σ ∘ φ_c = φ_{c∘σ⁻¹} ∘ φ_σ`。
两侧作用于 `g`（`φ_A g = C(lam A)g`）得 `lam c · lamS σ = lamS σ · lam (c∘σ⁻¹)`，
消去 `lamS σ`（单位，非零）。 -/
theorem sprChar_symm {g : Spr F r n}
    (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamS : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (hg : g ≠ 0) (c : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    lam (fun i => c (σ⁻¹ i)) = lam c := by
  have hcomp := sprPerm_sprDiagHom_comp F r n σ c
  have hpt : sprPermAlgEquiv F r n σ (sprDiagHom F r n c g)
      = sprDiagHom F r n (fun i => c (σ⁻¹ i)) (sprPermAlgEquiv F r n σ g) := by
    have h := congrArg (fun (f : Spr F r n →ₐ[F] Spr F r n) => f g) hcomp
    simpa using h
  have hL : sprPermAlgEquiv F r n σ (sprDiagHom F r n c g)
      = MvPolynomial.C ((lam c : Fˣ) : F) * MvPolynomial.C ((lamS σ : Fˣ) : F) * g := by
    rw [hlam c, map_mul, sprPermAlgEquiv_C, hlamS σ]
    ring
  have hR : sprDiagHom F r n (fun i => c (σ⁻¹ i)) (sprPermAlgEquiv F r n σ g)
      = MvPolynomial.C ((lamS σ : Fˣ) : F)
        * MvPolynomial.C ((lam (fun i => c (σ⁻¹ i)) : Fˣ) : F) * g := by
    rw [hlamS σ, map_mul, sprDiagHom_C, hlam (fun i => c (σ⁻¹ i))]
    ring
  rw [hL, hR] at hpt
  have hpt2 : MvPolynomial.C (((lam c : Fˣ) : F) * ((lamS σ : Fˣ) : F)) * g
      = MvPolynomial.C (((lamS σ : Fˣ) : F)
        * ((lam (fun i => c (σ⁻¹ i)) : Fˣ) : F)) * g := by
    rw [MvPolynomial.C_mul, MvPolynomial.C_mul]
    exact hpt
  have hC : ((lam c : Fˣ) : F) * ((lamS σ : Fˣ) : F)
      = ((lamS σ : Fˣ) : F) * ((lam (fun i => c (σ⁻¹ i)) : Fˣ) : F) :=
    MvPolynomial.C_injective (SprIdx r n) F (mul_right_cancel₀ hg hpt2)
  have h1 : lam c * lamS σ = lamS σ * lam (fun i => c (σ⁻¹ i)) := by
    refine Units.ext ?_
    push_cast
    exact hC
  have h2 := congrArg (fun u : Fˣ => (u : F)) h1
  simp only [Units.val_mul] at h2
  rw [mul_comm ((lam c : Fˣ) : F) ((lamS σ : Fˣ) : F)] at h2
  have hunit : ((lamS σ : Fˣ) : F) ≠ 0 := (lamS σ).ne_zero
  refine Units.ext ?_
  exact (mul_left_cancel₀ hunit h2).symm

#print axioms sprChar_symm

end SprCharSymm

/-! ## §144 **指数簿记**：`A`／`B` 的行和与列和 ＋ 重标号 —— `lem:14.25` 第 5 项（3/4）

[[proj-lem1425-plan-2026-10-19]] §3 第 2 步的簿记部分。§142 把特征标写成
`lam b = (∏_i b_i^{A_i})(∏_j b_j^{B_j})⁻¹`，其中 `A`、`B` 是**支撑单项式** `s` 的行和／列和。
本节给这两个函数以**名字**，使下一步的指数比较可读：

```
A_i = Σ_{j,k} s(i,j,k)          （行和：第 i 行有多少个 y-因子）
B_j = Σ_{i,k} s(i,j,k)          （列和：第 j 列有多少个 y-因子）
```

**关键恒等式（记在心里）**：`Σ_i A_i = Σ_j B_j`（**两边都等于 `s` 的 `y`-总次数**）。
这一步是把 `∏_i b_i^{A_i}(∏b_i^{B_i})⁻¹` 化简为 `1` 的**唯一**依据：常向量 ＋ 该恒等式 ⟹ `A = B`。

**件**：
1. `sprA`／`sprB`：行和／列和；
2. `sprDiag_char_exp'`：§142 的指数形态（`sprA`／`sprB` 写法，逐字转写）；
3. `sprProd_perm`：**重标号** `∏_i c(σ⁻¹ i)^{f i} = ∏_i c i^{f (σ i)}`
   （`Equiv.prod_comp` 一次落地——**注意方向**：`prod_comp` 给的是 `∏ f(e i) = ∏ f i`，
   取 `e = σ⁻¹`、`f i = c i ^ f (σ i)` 即得）。

**下游（下一轮）**：把 §143 的 `sprChar_symm` 的 `lam` 用 2 展开、用 3 重标号，得
`(∏ c_i^{A_{σi}})(∏ c_i^{B_{σi}})⁻¹ = (∏ c_i^{A_i})(∏ c_i^{B_i})⁻¹` ∀c，
再整理成 `∏ c_i^{A_{σi}+B_i} = ∏ c_i^{A_i+B_{σi}}`，用 §97 `coord_of_prod_eq` 得
`A_{σi} + B_i = A_i + B_{σi}`；取 `σ` 为换位 ＋ `ΣA = ΣB` ⟹ `A = B` ⟹ **`lam ≡ 1`**。

**射程（勿夸大）**：本节只是**簿记**（定义 ＋ 重标号），**零数学**。
`lam ≡ 1` **未证**；矩阵层归约未做。`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed`
—— **未做/未证**。**H2 仍不是定理。** -/

section SprExpBookkeeping

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- 指数形态的**行和** `A_i = Σ_{j,k} s(i,j,k)`。 -/
noncomputable def sprA (s : SprIdx r n →₀ ℕ) : Fin n → ℕ :=
  fun i => Finset.univ.sum (fun q : Fin n × {k : Fin r // k.val ≠ 0} => s (Sum.inr (i, q.1, q.2)))

#print axioms sprA

/-- 指数形态的**列和** `B_j = Σ_{i,k} s(i,j,k)`。 -/
noncomputable def sprB (s : SprIdx r n →₀ ℕ) : Fin n → ℕ :=
  fun j => Finset.univ.sum (fun i : Fin n =>
    Finset.univ.sum (fun k : {k : Fin r // k.val ≠ 0} => s (Sum.inr (i, j, k))))

#print axioms sprB

/-- §142 的指数形态（`sprA`／`sprB` 写法）。 -/
theorem sprDiag_char_exp' (b : Fin n → Fˣ) {g : Spr F r n} {u : Fˣ}
    (h : sprDiagHom F r n b g = MvPolynomial.C (u : F) * g)
    {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) :
    u = (∏ i : Fin n, (b i) ^ (sprA r n s i))
        * (∏ j : Fin n, (b j) ^ (sprB r n s j))⁻¹ :=
  sprDiag_char_exp F r n b h hs

#print axioms sprDiag_char_exp'

/-- **重标号**：`∏_i c(σ⁻¹ i)^{f i} = ∏_i c i^{f (σ i)}`。 -/
theorem sprProd_perm (c : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) (f : Fin n → ℕ) :
    (∏ i : Fin n, (c (σ⁻¹ i)) ^ f i) = ∏ i : Fin n, (c i) ^ f (σ i) := by
  simpa using (Equiv.prod_comp (σ⁻¹) (fun i => (c i) ^ f (σ i)))

#print axioms sprProd_perm

end SprExpBookkeeping

/-! ## §145 **指数比较（半直积版）** —— `lem:14.25` 第 5 项收尾的核心一步

[[proj-lem1425-plan-2026-10-19]] §3 第 2 步。本节把 §143 的 `lam (c∘σ⁻¹) = lam c`
与 §142 的指数形态、§144 的重标号**合起来**，得到指数之间的**线性关系**：

```
sprA s (σ i) + sprB s i = sprA s i + sprB s (σ i)        (∀ σ, i)
```

**证明链（四段，全部落库）**：
1. `sprChar_symm`（§143）：`lam (c∘σ⁻¹) = lam c`；
2. `sprDiag_char_exp'`（§144）：把两侧的 `lam` 展开成 `(∏c_i^{A_i})(∏c_i^{B_i})⁻¹`；
3. `sprProd_perm`（§144）：重标号 `∏_i c(σ⁻¹ i)^{f i} = ∏_i c i^{f (σ i)}`；
4. 交叉相乘 ＋ `∏c^{A+B}` 合并 ＋ §97 `coord_of_prod_eq` ＋ §98 `pow_eq_of_forall_unit`
   （**需 `[Infinite F]`**——这是全库第一次在 `(B)` 层真正用到"域无限"）。

**★ 工艺（本轮最大教训：`group` 在大乘积原子上会失败）**：第 4 段的群论重排
`P1 * Q1⁻¹ = P2 * Q2⁻¹ ⟹ P1 * Q2 = P2 * Q1`（`P1..Q2` 是四个大 `Finset` 乘积）
**三次尝试全败**：`group` 报含 metavariable 的目标（把 `Finset` 索引也当变量重命名）；
显式 `rw` 链落点不匹配；`field_simp at h2` 报 "made no progress"。
**正解**：把恒等式抽成 **`mul_inv_eq_mul_inv_cross`**（**裸变量** `a b c d`）——
`calc` 两段 `group` 只需在裸变量上做，末段的 `rw` 链
`mul_assoc c d⁻¹ (b*d), ← mul_assoc d⁻¹ b d, mul_comm (d⁻¹) b, mul_assoc b d⁻¹ d,
inv_mul_cancel, mul_one` 一次落地。**判别动作（新工艺，记入 v14）**：
`group`／`ring` 失败时，先把恒等式**抽成裸变量引理**再实例化，别在大项上硬碰。

**下游（下一轮）**：取 `σ` 为换位 `(i j)` 得 `A_i + B_j = A_j + B_i`（∀i,j）；
再配合 `Σ_i A_i = Σ_j B_j`（`sprA`／`sprB` 的定义直接给）得 `A = B`；
代回 §142 得 **`lam ≡ 1`**（环面半边完成）。

**射程（勿夸大）**：本节只到**指数的线性关系**。`lam ≡ 1` **未证**；`S_n` 侧
`u^{n!}=1` 的收口、矩阵层、`prop:14.19`、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。
**H2 仍不是定理。** -/

section SprExponentCompare

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- **群论交叉恒等式**：`a * b⁻¹ = c * d⁻¹ ⟹ a * d = c * b`（交换群）。

**为何单列**：`group` 在"原子是大 `Finset` 乘积"时**会失败**（它把 `Finset` 索引也当变量
重命名，产生含 metavariable 的目标）；这里只用**裸变量**，把恒等式一次证死，下游全部消费它。 -/
theorem mul_inv_eq_mul_inv_cross {G : Type} [CommGroup G] {a b c d : G}
    (h : a * b⁻¹ = c * d⁻¹) : a * d = c * b := by
  calc a * d = (a * b⁻¹) * (b * d) := by group
    _ = (c * d⁻¹) * (b * d) := by rw [h]
    _ = c * b := by
      rw [mul_assoc c d⁻¹ (b * d), ← mul_assoc d⁻¹ b d, mul_comm (d⁻¹) b,
        mul_assoc b d⁻¹ d, inv_mul_cancel, mul_one]

#print axioms mul_inv_eq_mul_inv_cross

/-- ★★★★ **指数比较（半直积版）**：`A_{σ i} + B_i = A_i + B_{σ i}`。

**机制**：§143 的 `lam (c∘σ⁻¹) = lam c` ＋ §142 的指数形态 ＋ §144 的重标号
⟹ `(∏c_i^{A_{σi}})(∏c_i^{B_{σi}})⁻¹ = (∏c_i^{A_i})(∏c_i^{B_i})⁻¹` ∀c
⟹ 交叉相乘 ⟹ `∏c_i^{A_{σi}+B_i} = ∏c_i^{A_i+B_{σi}}` ⟹ §97 `coord_of_prod_eq`
＋ §98 `pow_eq_of_forall_unit`（需 `[Infinite F]`）。 -/
theorem sprA_add_sprB_perm [Infinite F] {g : Spr F r n}
    (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamS : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (hg : g ≠ 0) {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    sprA r n s (σ i) + sprB r n s i = sprA r n s i + sprB r n s (σ i) := by
  have hkey : ∀ c : Fin n → Fˣ,
      (∏ i : Fin n, (c i) ^ (sprA r n s (σ i) + sprB r n s i))
        = ∏ i : Fin n, (c i) ^ (sprA r n s i + sprB r n s (σ i)) := by
    intro c
    have hperm : lam (fun i => c (σ⁻¹ i)) = lam c :=
      sprChar_symm F r n lam hlam lamS hlamS hg c σ
    have e1 : lam (fun i => c (σ⁻¹ i))
        = (∏ i : Fin n, (c (σ⁻¹ i)) ^ (sprA r n s i))
          * (∏ j : Fin n, (c (σ⁻¹ j)) ^ (sprB r n s j))⁻¹ :=
      sprDiag_char_exp' F r n (fun i => c (σ⁻¹ i)) (hlam _) hs
    have e2 : lam c = (∏ i : Fin n, (c i) ^ (sprA r n s i))
          * (∏ j : Fin n, (c j) ^ (sprB r n s j))⁻¹ :=
      sprDiag_char_exp' F r n c (hlam c) hs
    rw [sprProd_perm F n c σ (sprA r n s),
      sprProd_perm F n c σ (sprB r n s)] at e1
    rw [e1, e2] at hperm
    set P1 : Fˣ := ∏ i : Fin n, (c i) ^ (sprA r n s (σ i)) with hP1
    set Q1 : Fˣ := ∏ i : Fin n, (c i) ^ (sprB r n s (σ i)) with hQ1
    set P2 : Fˣ := ∏ i : Fin n, (c i) ^ (sprA r n s i) with hP2
    set Q2 : Fˣ := ∏ i : Fin n, (c i) ^ (sprB r n s i) with hQ2
    have hcross : P1 * Q2 = P2 * Q1 := mul_inv_eq_mul_inv_cross hperm
    have hl : (∏ i : Fin n, (c i) ^ (sprA r n s (σ i) + sprB r n s i)) = P1 * Q2 := by
      rw [hP1, hQ2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => pow_add _ _ _)
    have hr : (∏ i : Fin n, (c i) ^ (sprA r n s i + sprB r n s (σ i))) = P2 * Q1 := by
      rw [hP2, hQ1, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => pow_add _ _ _)
    rw [hl, hr]
    exact hcross
  have h1 := coord_of_prod_eq (fun i : Fin n => sprA r n s (σ i) + sprB r n s i)
    (fun i : Fin n => sprA r n s i + sprB r n s (σ i)) hkey i
  exact pow_eq_of_forall_unit (fun t => by
    simpa using congrArg (fun u : Fˣ => (u : F)) (h1 t))

#print axioms sprA_add_sprB_perm

end SprExponentCompare

/-! ## §146 **换位对偶关系 ＋ `A`／`B` 的总次数相等** —— `lam ≡ 1` 的最后两块拼图

[[proj-lem1425-plan-2026-10-19]] §3 第 3 步。§145 给了 `A_{σi} + B_i = A_i + B_{σi}`；
本节补上把 `A`、`B` 逼成相等的**另两块拼图**：

1. **`sprA_add_sprB_swap`**：取 `σ = Equiv.swap i j`（换位）得
   `A_i + B_j = A_j + B_i`（∀i,j）——即 `A_i − B_i` 与 `i` **无关**；
2. **`sprA_sum_eq_sprB_sum`**：`Σ_i A_i = Σ_j B_j`——两边都等于 `s` 的 `y`-总次数
   （`simp` 展成 `Σ_{i,j,k}`，`Finset.sum_comm` 交换两层和）。

**⟹ 收口路径（下一轮，一步之遥）**：由 1 得 `∀j, A_i + B_j = A_j + B_i`，对 `j` 求和得
`n·A_i + ΣB = ΣA + n·B_i`；由 2 得 `n·A_i = n·B_i`；`n > 0`（`[Nonempty (Fin n)]`，
`Fintype.card_pos`）消去得 `A_i = B_i`，即 **`sprA s = sprB s`**。
代回 §142 的指数形态即得 **`lam b = (∏b_i^{A_i})(∏b_i^{A_i})⁻¹ = 1`**——`lem:14.25` 的
**环面半边完成**。

**⚠ 本轮的实际卡点（已登记，供下一轮直接命中）**：`sprA_eq_sprB` 的**最后一步**
`n * A = n * B → A = B`（`ℕ`）没找到可用的消去形式：`Nat.eq_of_mul_eq_mul_left hn hkey`、
`(Nat.mul_left_cancel hn).mp hkey` 均报 "Application type mismatch"（参数隐式性/顺序不符）。
**下一轮的判别动作**：先 `#check @Nat.mul_left_cancel`／`@Nat.eq_of_mul_eq_mul_left`
读准签名再写；或用 `Nat.mul_right_cancel` 换成 `A * n = B * n` 的形状
（把 `h1` 的 `Finset.sum_const` 结果写成 `A * n` 而非 `n * A`，即 `mul_comm` 一次）。
**不要**再试 `omega`——`n * A` 是**非线性**项，`omega` 原理上不处理。

**射程（勿夸大）**：本节只到 `A_i + B_j = A_j + B_i` 与 `ΣA = ΣB`。`sprA = sprB` 与
`lam ≡ 1` **未证**（差一步 `ℕ` 消去）；`lem:14.25` 矩阵层、`prop:14.19`、`V2'`／`V3'`、
`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprSwapAndSum

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

theorem sprA_sum_eq_sprB_sum (s : SprIdx r n →₀ ℕ) :
    (∑ i : Fin n, sprA r n s i) = ∑ j : Fin n, sprB r n s j := by
  simp only [sprA, sprB, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

#print axioms sprA_sum_eq_sprB_sum

theorem sprA_add_sprB_swap [Infinite F] {g : Spr F r n}
    (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamS : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (hg : g ≠ 0) {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) (i j : Fin n) :
    sprA r n s i + sprB r n s j = sprA r n s j + sprB r n s i := by
  have h := sprA_add_sprB_perm F r n lam hlam lamS hlamS hg hs (Equiv.swap i j) i
  simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using h.symm

#print axioms sprA_add_sprB_swap

end SprSwapAndSum

/-! ## §147 **`ℕ` 的正倍数消去（撞名免疫）** —— `A = B` 的最后一块工具

`§146` 已给 `A_i + B_j = A_j + B_i` 与 `ΣA = ΣB`，由此 `A = B` 只需 `n * A_i = n * B_i`
消去 `n > 0`。本轮把这一步所需的工具**独立成引理**，并解决一个**纯 elaboration 陷阱**。

**件**：`nat_mul_left_cancel_pos {c a b : ℕ} (hc : 0 < c) (h : c * a = c * b) : a = b`。

**为何单列（本轮四个实测发现，全部可复用）**：
1. **`sprA_sum_eq_sprB_sum` 的签名里没有 `F`**——该定理不涉及 `F`，Lean 把未用的
   `variable (F : Type)` **自动丢弃**。故 `sprA_sum_eq_sprB_sum F r n s` 报
   "argument `F` has type `Type` … expected `ℕ`"。**判别动作**：`#check @名字` 读准签名，
   别凭本文的 `variable` 行猜参数（**R163 家族第六次**）。
2. **`omega` 不处理非线性**：`n * sprA … = n * sprB …` 里的 `n * A` 是**乘积项**，
   `omega` 原理上不能证。**正解**：先用 `set` 把 `n * A`／`n * B`／`ΣB` 提成**不透明 ℕ 原子**
   （`X`、`Y`、`S`），则 `h1` 变成 `X + S = ΣA + Y`，用 `ΣA = ΣB = S` 化为 `X + S = S + Y`
   ——**线性**，`omega` 一次给出 `X = Y`。
3. **隐式参数撞名**：`Nat.mul_left_cancel`／`Nat.add_right_cancel` 的隐式参数名 `m`／`n`
   与本文 section 变量 `n` 撞名时，报错会指向**毫不相干的东西**（如 "argument `F`"）。
   正解：本条引理的形参取名 **`c a b`**（避开 `n`／`F`），并在调用处用**具名参数**
   `(c := n) (a := …) (b := …)`。
4. **本文 `F` 也不能省**：带 `sprDiagHom F r n` 的引理必须传 `F`；不带的**不能**传。

**射程（勿夸大）**：本节**只是一条 `ℕ` 工具**。`sprA = sprB` 与 `lam ≡ 1` **仍未证**
（差的正是用本节工具的那 3 行）；`lem:14.25` 矩阵层、`prop:14.19`、`V2'`／`V3'`、
`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprNatCancel

set_option linter.style.haveILetI false

/-- `ℕ` 的正倍数消去（形参名 `c a b` **避开**与 section 变量 `n`／`F` 撞名）。 -/
theorem nat_mul_left_cancel_pos {c a b : ℕ} (hc : 0 < c) (h : c * a = c * b) : a = b :=
  Nat.mul_left_cancel hc h

#print axioms nat_mul_left_cancel_pos

end SprNatCancel

/-! ## §148 ★★★★★ **`lam ≡ 1`**：环面特征标被 `N`-不变性杀死（`lem:14.25` 环面半边完成）

这是 [[proj-lem1425-plan-2026-10-19]] §3 的**收尾**，也是本战役第一次把源文
"`s` and `β'` are `T` invariant" 那句话变成机检定理。

**推理链（全链已落库，逐环可见）**：
`§138` 比值论证 ⟹ 对每个 `b` 有 `φ_b(g) = c_b·g`（`c_b` 单位）；
`§140` 打包成 `lam : (Fin n → Fˣ) →* Fˣ`；
`§141` 系数比较 ⟹ `lam b` ＝ 分母某个支撑单项式的权；
`§142` 该权写成 `(∏_i b_i^{A_i})(∏_j b_j^{B_j})⁻¹`；
`§143` 半直积 ⟹ `lam (c∘σ⁻¹) = lam c`；
`§145` ⟹ `A_{σi} + B_i = A_i + B_{σi}`；
`§146` ⟹ `A_i + B_j = A_j + B_i` 与 `ΣA = ΣB`；
**本节** ⟹ `A = B` ⟹ **`lam b = 1`**。

**件**：
1. `sum_add_const`／`sum_const_add`：**裸变量**的求和计算（`m f c`，无 `F`／无 `n`）；
2. ★★★★ **`sprA_eq_sprB`**：行和 ＝ 列和（对 `j` 求和 ＋ `ΣA = ΣB` ＋ `ℕ` 消去）；
3. ★★★★★ **`sprDiag_char_eq_one`**：`lam b = 1`（代回 §142 即 `(∏b^{A_i})(∏b^{A_i})⁻¹ = 1`）。

**★ 工艺（本轮突破的关键，一条）**：`∑ j, (c + f j)` 的裸变量计算里，
`nsmul_eq_mul` 产出的是 **`↑m * c`**（`ℕ` 的 `Nat.cast`），与目标 `m * c` **不同**；
`rw` 链会留下 `↑m * c + ∑x = m * c + ∑x` 的**看似恒真的残目标**。
**正解：把 `Nat.cast_id` 加进 `simp only` 集合**——一次即闭。
（这是"裸变量抽离"工艺的**第三次**兑现：R163／R321／本轮；载体 ＝ R171 家族。）

**射程（勿夸大）**：环面半边**已完成**；`S_n` 侧 `u^{n!}=1` 的收口（`sprPerm_exists_char`
＋ §139 已备）、`lem:14.25` 的矩阵层归约、`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed`
—— **未做/未证**。**H2 仍不是定理。** -/

section SprKillCharacter

set_option linter.style.haveILetI false
/-- 常数＋函数的和（**裸变量** `m f c`）。 -/
theorem sum_add_const {m : ℕ} (f : Fin m → ℕ) (c : ℕ) :
    (∑ j : Fin m, (c + f j)) = m * c + ∑ j : Fin m, f j := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]

#print axioms sum_add_const

/-- 函数＋常数的和（**裸变量**）。 -/
theorem sum_const_add {m : ℕ} (f : Fin m → ℕ) (c : ℕ) :
    (∑ j : Fin m, (f j + c)) = (∑ j : Fin m, f j) + m * c := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id]

#print axioms sum_const_add

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`A = B`**：行和 ＝ 列和（`lem:14.25` 环面半边的最后一环）。 -/
theorem sprA_eq_sprB [Nonempty (Fin n)] [Infinite F] {g : Spr F r n}
    (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamS : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (hg : g ≠ 0) {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) :
    sprA r n s = sprB r n s := by
  funext i₀
  have hpair : ∀ j : Fin n, sprA r n s i₀ + sprB r n s j
      = sprA r n s j + sprB r n s i₀ :=
    fun j => sprA_add_sprB_swap F r n lam hlam lamS hlamS hg hs i₀ j
  have hL : (∑ j : Fin n, (sprA r n s i₀ + sprB r n s j))
      = n * sprA r n s i₀ + ∑ j : Fin n, sprB r n s j :=
    sum_add_const (fun j : Fin n => sprB r n s j) (sprA r n s i₀)
  have hR : (∑ j : Fin n, (sprA r n s j + sprB r n s i₀))
      = (∑ j : Fin n, sprA r n s j) + n * sprB r n s i₀ :=
    sum_const_add (fun j : Fin n => sprA r n s j) (sprB r n s i₀)
  have h1 : (∑ j : Fin n, (sprA r n s i₀ + sprB r n s j))
      = ∑ j : Fin n, (sprA r n s j + sprB r n s i₀) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hpair j
  rw [hL, hR] at h1
  have hsum := sprA_sum_eq_sprB_sum r n s
  have h2 : n * sprA r n s i₀ + (∑ j : Fin n, sprB r n s j)
      = n * sprB r n s i₀ + (∑ j : Fin n, sprB r n s j) := by
    rw [h1, hsum, Nat.add_comm]
  exact nat_mul_left_cancel_pos (c := n) (a := sprA r n s i₀) (b := sprB r n s i₀)
    (by simpa using Fintype.card_pos (α := Fin n))
    (Nat.add_right_cancel (m := ∑ j : Fin n, sprB r n s j) h2)

#print axioms sprA_eq_sprB

/-- ★★★★★ **`lam ≡ 1`**：环面特征标被 `N`-不变性**杀死**。 -/
theorem sprDiag_char_eq_one [Nonempty (Fin n)] [Infinite F] {g : Spr F r n}
    (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamS : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (hg : g ≠ 0) {s : SprIdx r n →₀ ℕ} (hs : g.coeff s ≠ 0) (b : Fin n → Fˣ) :
    lam b = 1 := by
  have hAB : sprA r n s = sprB r n s := sprA_eq_sprB F r n lam hlam lamS hlamS hg hs
  have hexp : lam b = (∏ i : Fin n, (b i) ^ (sprA r n s i))
      * (∏ j : Fin n, (b j) ^ (sprB r n s j))⁻¹ :=
    sprDiag_char_exp' F r n b (hlam b) hs
  rw [hexp, ← hAB, mul_inv_cancel]

#print axioms sprDiag_char_eq_one

end SprKillCharacter

/-! ## §149 **特征标为 `1` 时的不变性 ＋ `S_n` 特征标的阶整除 `n!`** —— `lem:14.25` 收口（1/2）

§148 已证 **`lam ≡ 1`**（环面半边）。本节补 `S_n` 半边与两端合流所需的两条：

1. **`sprDiagHom_fixed_of_char`**：`lam ≡ 1` ⟹ `φ_b(g) = g`（∀b）
   ——源文 "`s` and `β'` are `T` invariant" 的**最终形态**（分母层面）；
2. **`sprPermHom_pow_card`**：`lamS σ ^ (n!) = 1`——`S_n` **有限**，故
   `lamS σ ^ Fintype.card (Equiv.Perm (Fin n)) = 1`（`pow_card_eq_one`），
   再用 `Fintype.card_perm` ＋ `Fintype.card_fin` 换成 `n!`；
3. **`sprDiagHom_pow_fixed`**：`lam ≡ 1` ⟹ `φ_b(g^{n!}) = g^{n!}`（取幂后仍被环面固定）。

**⟹ `lem:14.25` 标量层的收口（下一轮）**：取 §141 的互素 `f, g`（`α' = f/g`），令
`s := g^{n!}`、`β := f · g^{n!-1}`。由 1、3 得 `s` 的 `T`-不变性；由 2（`map_pow` ＋
`mul_pow` ＋ **`↑(u^k) = (↑u)^k` 的 units-val 转换**）得 `s` 的 `S_n`-不变性；
`β` 同法（`φ_A(f) = C(lam A)f`，同一特征标）。故 `s, β` 皆 `N`-不变且 `α' = β/s`。

**⚠ 本轮未过的一条（登记，供下一轮直接命中）**：`sprPermAlgEquiv_pow_fixed`
（`φ_σ(g^{n!}) = g^{n!}`）在最后一处 **`F`／`Fˣ` 转换**卡住：`mul_pow` 后目标里是
`(↑(lamS σ))^{n!}`（`F` 里），而 `sprPermHom_pow_card` 是 `Fˣ` 里的等式；`push_cast` 与
`← Units.val_pow_eq_pow_val` 两种尝试都未命中。**正解**：先单列
`((lamS σ : Fˣ) : F) ^ n! = 1` 的 **`F`-版引理**（`calc` 走
`(↑u)^k = ↑(u^k) = ↑1 = 1`，其中 `Units.val_pow_eq_pow_val : ↑(a^n) = (↑a)^n`，见
`Mathlib/Algebra/Group/Units/Defs.lean:270`），再在 `sprPermAlgEquiv_pow_fixed` 里用它。

**射程（勿夸大）**：本节只到"特征标为 `1` ⟹ 不变"，**尚未**组装 `lem:14.25`
（`s = g^{n!}`、`β = f g^{n!-1}`、两者的 `N`-不变性与 `α' = β/s` 未写）。
`prop:14.19`、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprNFixedPieces

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

variable (F : Type) [Field F] (r n : ℕ)

/-- 特征标为 `1` ⟹ 分母被环面固定。 -/
theorem sprDiagHom_fixed_of_char {g : Spr F r n} (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (hone : ∀ b, lam b = 1) (b : Fin n → Fˣ) :
    sprDiagHom F r n b g = g := by
  rw [hlam b, hone b]
  rw [show ((1 : Fˣ) : F) = 1 from rfl, MvPolynomial.C_1, one_mul]

#print axioms sprDiagHom_fixed_of_char

/-- `S_n` 侧特征标的阶整除 `n!`（有限群）。 -/
theorem sprPermHom_pow_card (lamS : Equiv.Perm (Fin n) →* Fˣ) (σ : Equiv.Perm (Fin n)) :
    lamS σ ^ Nat.factorial n = 1 := by
  rw [← map_pow]
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [← hcard, pow_card_eq_one, map_one]

#print axioms sprPermHom_pow_card

/-- 环面固定：特征标为 `1` 时分母的幂也被固定。 -/
theorem sprDiagHom_pow_fixed {g : Spr F r n} (lam : (Fin n → Fˣ) →* Fˣ)
    (hlam : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((lam b : Fˣ) : F) * g)
    (hb : ∀ b, lam b = 1) (b : Fin n → Fˣ) :
    sprDiagHom F r n b (g ^ Nat.factorial n) = g ^ Nat.factorial n := by
  rw [map_pow, sprDiagHom_fixed_of_char F r n lam hlam hb b]

#print axioms sprDiagHom_pow_fixed

end SprNFixedPieces

/-! ## §150 **`S_n` 侧的不变性**：`φ_σ(g^{n!}) = g^{n!}` —— `lem:14.25` 收口（2/2）

§149 已给 `lam ≡ 1`（环面）与 `lamS σ ^ (n!) = 1`（`Fˣ` 里）。本节补 `S_n` 半边在
**多项式环里**的形态——两处 `F`／`Fˣ` 与 `C` 的转换是本节的全部困难：

1. **`sprPermHom_pow_card_coe`**：`((lamS σ : Fˣ) : F) ^ (n!) = 1`（`F` 版）。
   **关键**：`Units.val_pow_eq_pow_val` 的**隐式参数 `a` 必须显式给出**
   （`(a := lamS σ) (n := …)`），否则整个项退化成"`a` 的函数"，`.symm` 报
   **"Invalid field `symm`: … `Function.symm`"**（错误信息完全不指向根因）。
2. **`sprPermAlgEquiv_pow_fixed`**：`φ_σ(g^{n!}) = g^{n!}`。
   **关键**：`mul_pow` 之后目标是 `(C ↑u)^{n!}`，而 §149 的引理是 `(↑u)^{n!} = 1`——
   中间必须**把 `C` 推到幂里去**：`← map_pow (MvPolynomial.C : F →+* Spr F r n) ↑u (n!)`
   （`C x ^ k = C (x^k)`）。缺这一步，`rw` 报"找不到落点"。

**⟹ `lem:14.25` 标量层**：`s := g^{n!}` 的 `N`-不变性已齐（`T` 由 §149
`sprDiagHom_pow_fixed`、`S_n` 由本节的 `sprPermAlgEquiv_pow_fixed`）。

**⚠ 本轮未过的第三条（登记，下一轮直接命中）**：`sprPermAlgEquiv_mul_pow_fixed`
（`β = f · g^{n!-1}` 的 `S_n`-不变性）。**根因已定位**：`β` 里 `g` 的指数是 `n!-1`，
而 `lamS σ^(n!-1)` **不是** `1`；必须先把两处 `C` **合成一个**：
`C u · C (u^{n!-1}) = C (u · u^{n!-1}) = C (u^{n!}) = C 1 = 1`
（即 `← map_mul` ＋ `← pow_succ`（`n!-1+1 = n!`，需 `n ≥ 1`）＋ 本节引理）。
**不得**指望逐项替换。

**射程（勿夸大）**：`s = g^{n!}` 的不变性**已齐**；`β` 的不变性与 `α' = β/s` 的组装
**未写**；`prop:14.19`、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。**H2 仍不是定理。** -/

section SprSPermFixed

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

variable (F : Type) [Field F] (r n : ℕ)

/-- `F` 版：`S_n` 特征标的 `n!` 次幂为 `1`。 -/
theorem sprPermHom_pow_card_coe (lamS : Equiv.Perm (Fin n) →* Fˣ) (σ : Equiv.Perm (Fin n)) :
    ((lamS σ : Fˣ) : F) ^ Nat.factorial n = 1 := by
  have h2 : ((lamS σ ^ Nat.factorial n : Fˣ) : F) = ((lamS σ : Fˣ) : F) ^ Nat.factorial n :=
    Units.val_pow_eq_pow_val (a := lamS σ) (n := Nat.factorial n)
  rw [← h2, sprPermHom_pow_card F n lamS σ]
  rfl

#print axioms sprPermHom_pow_card_coe

/-- ★★★ **`S_n` 侧不变性**：`φ_σ(g^{n!}) = g^{n!}`。 -/
theorem sprPermAlgEquiv_pow_fixed {g : Spr F r n} (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamS : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (σ : Equiv.Perm (Fin n)) :
    sprPermAlgEquiv F r n σ (g ^ Nat.factorial n) = g ^ Nat.factorial n := by
  rw [map_pow, hlamS σ, mul_pow,
    ← map_pow (MvPolynomial.C : F →+* Spr F r n) ((lamS σ : Fˣ) : F) (Nat.factorial n),
    sprPermHom_pow_card_coe F n lamS σ]
  simp

#print axioms sprPermAlgEquiv_pow_fixed

end SprSPermFixed

/-! ## §151 **`β = f·g^{n!-1}` 的 `S_n`-不变性** —— `lem:14.25` 标量层收口（3/3）

§150 给了 `s = g^{n!}` 的 `S_n`-不变性；`β` 里 `g` 的指数是 `n!-1`，而
`lamS σ ^ (n!-1)` **不是** `1`，故两处 `C` 系数**必须整体合成**：

```
C u · C (u^{n!-1}) = C (u · u^{n!-1}) = C (u^{n!-1+1}) = C (u^{n!}) = C 1 = 1
```

本节的第 1、2 条把 `u^{k-1}·u = u^k` 抽成**裸变量引理**（R173）——直接在大项上
`ring`／`rw` 都不可靠。

**射程（勿夸大）**：本节只给 `β` 的 `S_n` 侧；`lem:14.25` 的整体组装见 §152。
`prop:14.19`、`V2'`／`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/



section SprSPermMulFixed

set_option linter.style.haveILetI false

/-- `u^{k-1} * u = u^k`（`k ≥ 1`；裸变量引理，R173）。 -/
theorem pow_pred_mul {F : Type} [Field F] {u : F} {k : ℕ} (hk : 1 ≤ k) :
    u ^ (k - 1) * u = u ^ k := by
  rw [← pow_succ, Nat.sub_add_cancel hk]

#print axioms pow_pred_mul

/-- `u * u^{k-1} = u^k`（`k ≥ 1`；**交换**形态，`C` 的合成里要用）。 -/
theorem mul_pow_pred {F : Type} [Field F] {u : F} {k : ℕ} (hk : 1 ≤ k) :
    u * u ^ (k - 1) = u ^ k := by
  rw [mul_comm, pow_pred_mul (F := F) hk]

#print axioms mul_pow_pred

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`β = f · g^{n!-1}` 的 `S_n`-不变性**（`lem:14.25` 标量层收口的第一半）。

**路线（v14 §4.1 的正解）**：`φ_σ` 把 `β` 送成 `C u · f · (C u^{n!-1} · g^{n!-1})`；
两处 `C` 的**指数相加**才等于 `n!`，故必须先把它们**合成一个**——
`C u · C u^{n!-1} = C (u · u^{n!-1}) = C (u^{n!}) = C 1 = 1`。
**不得**逐项替换（`lamS σ ^ (n!-1) ≠ 1` 原理上）。 -/
theorem sprPermAlgEquiv_mul_pow_fixed {f g : Spr F r n} (lamS : Equiv.Perm (Fin n) →* Fˣ)
    (hlamf : ∀ σ, sprPermAlgEquiv F r n σ f = MvPolynomial.C ((lamS σ : Fˣ) : F) * f)
    (hlamg : ∀ σ, sprPermAlgEquiv F r n σ g = MvPolynomial.C ((lamS σ : Fˣ) : F) * g)
    (σ : Equiv.Perm (Fin n)) :
    sprPermAlgEquiv F r n σ (f * g ^ (Nat.factorial n - 1))
      = f * g ^ (Nat.factorial n - 1) := by
  have hk : 1 ≤ Nat.factorial n := Nat.factorial_pos n
  have hk1 : Nat.factorial n - 1 + 1 = Nat.factorial n := Nat.sub_add_cancel hk
  have hu : ((lamS σ : Fˣ) : F) ^ Nat.factorial n = 1 := sprPermHom_pow_card_coe F n lamS σ
  have hCc : (MvPolynomial.C ((lamS σ : Fˣ) : F) : Spr F r n)
      * (MvPolynomial.C ((lamS σ : Fˣ) : F) : Spr F r n) ^ (Nat.factorial n - 1) = 1 := by
    rw [← map_pow (MvPolynomial.C : F →+* Spr F r n) ((lamS σ : Fˣ) : F)
        (Nat.factorial n - 1),
      ← map_mul (MvPolynomial.C : F →+* Spr F r n) ((lamS σ : Fˣ) : F)
        (((lamS σ : Fˣ) : F) ^ (Nat.factorial n - 1)),
      mul_pow_pred (u := ((lamS σ : Fˣ) : F)) hk, hu, map_one]
  rw [map_mul, map_pow, hlamf σ, hlamg σ, mul_pow]
  calc (MvPolynomial.C ((lamS σ : Fˣ) : F) : Spr F r n) * f
        * ((MvPolynomial.C ((lamS σ : Fˣ) : F) : Spr F r n) ^ (Nat.factorial n - 1)
          * g ^ (Nat.factorial n - 1))
      = f * ((MvPolynomial.C ((lamS σ : Fˣ) : F) : Spr F r n)
          * (MvPolynomial.C ((lamS σ : Fˣ) : F) : Spr F r n) ^ (Nat.factorial n - 1))
        * g ^ (Nat.factorial n - 1) := by ring
    _ = f * g ^ (Nat.factorial n - 1) := by rw [hCc, mul_one]

#print axioms sprPermAlgEquiv_mul_pow_fixed

end SprSPermMulFixed

/-! ## §152 ★★★★★ **`lem:14.25` 的标量层**（`K'` 中的元素 = `S'` 两不变元之商）

源文 `:449`（陈述）、`:451–453`（证明）的 `n = 1` 情形——即 `α ∈ K'`（而非矩阵）：
`a` 被 `N = T ⋊ S_n` 固定 ⟹ 存在 `0 ≠ s, β ∈ S'`，皆 `N`-不变，且 `a = β/s`。

**路线**（与 `FixedRatio.lean` 的 `fixed_eq_ratio` 逐字同型）：

1. 取互素 `f0, g0`（`IsFractionRing.num`／`den` ＋ `num_den_reduced`），`a = f0/g0`；
2. `sprDiag_exists_char`／`sprPerm_exists_char`（§140）给两个特征标 `lam`、`lamS`；
3. **环面半边被杀死**：`sprDiag_char_eq_one`（§148，`lam ≡ 1`）⟹ `φ_b(g0) = g0`
   （§149）⟹ 用交叉关系 `sprDiag_mul_eq_of_fixed` 消去 `g0` 得 `φ_b(f0) = f0`；
4. **`S_n` 侧不死**（`lamS σ ^ (n!) = 1` 只是阶整除，不等于 `1`）：故取
   `s := g0^{n!}`（§150）与 `β := f0 · g0^{n!-1}`（§151）——**指数相加**才使系数消失；
5. `a = β/s`：`div_eq_div_iff` ＋ `pow_succ`。

**射程（勿夸大）**：本节 **只做标量层**。`lem:14.25` 的**矩阵层**
（`M_n(K')` 的 `N`-不变基 ＋ 有限个元素的公共分母）**未做**；
`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/

section SprLem1425Scalar

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `Spr` 层的 `N`-不变性（多项式层的 `K'^N ∩ S'`）：`T`-不变**且** `S_n`-不变。 -/
def sprNFixed (x : Spr F r n) : Prop :=
  (∀ b : Fin n → Fˣ, sprDiagHom F r n b x = x) ∧
    (∀ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ x = x)

#print axioms sprNFixed

/-- ★★★★ **`lem:14.25` 的标量层**（源文 `:449` 的 `n = 1` 情形，即 `K'` 里的元素）。

**陈述**：`a ∈ K'` 被 `N = T ⋊ S_n` 固定 ⟹ `a = β/s`，其中 `0 ≠ s, β ∈ S'` 且 `s, β`
皆 `N`-不变。

**路线**（与 `FixedRatio.lean` 的 `fixed_eq_ratio` 逐字同型，但 `S_n` 侧**有限群**故用
`n!` 次幂而非 `n` 次幂）：
1. 取互素的 `f0, g0`（`IsFractionRing.num_den_reduced`），`a = f0/g0`；
2. `sprDiag_exists_char`／`sprPerm_exists_char` 给两个特征标 `lam`、`lamS`；
3. `sprDiag_char_eq_one`（**环面半边被 `N`-不变性杀死**）⟹ `lam ≡ 1` ⟹
   `φ_b(g0) = g0` 且（经交叉关系 `sprDiag_mul_eq_of_fixed` 消去 `g0`）`φ_b(f0) = f0`；
4. `lamS σ ^ (n!) = 1`（§149 有限群），故 `s := g0^{n!}` 与 `β := f0·g0^{n!-1}`
   在 `S_n` 侧皆不变（§150 ＋ §4.1 的合成两点 `C`）；
5. `a = β/s` 由 `div_eq_div_iff` ＋ `pow_succ` 给出。 -/
theorem lem1425_scalar [Nonempty (Fin n)] [Infinite F] (a : SprField F r n)
    (ha : sprFieldNFixed F r n a) :
    ∃ s β : Spr F r n, s ≠ 0 ∧ sprNFixed F r n s ∧ sprNFixed F r n β ∧
      a = algebraMap (Spr F r n) (SprField F r n) β
        / algebraMap (Spr F r n) (SprField F r n) s := by
  classical
  obtain ⟨hT, hS⟩ := ha
  set f0 : Spr F r n := IsFractionRing.num (Spr F r n) a with hf0def
  set g0 : Spr F r n := (IsFractionRing.den (Spr F r n) a : Spr F r n) with hg0def
  have hmem : g0 ∈ nonZeroDivisors (Spr F r n) := (IsFractionRing.den (Spr F r n) a).2
  have hg0K : algebraMap (Spr F r n) (SprField F r n) g0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hmem
  have hg0 : g0 ≠ 0 := fun h => hg0K (by rw [h, map_zero])
  have hcop : IsRelPrime f0 g0 := IsFractionRing.num_den_reduced (Spr F r n) a
  have hratio : a = algebraMap (Spr F r n) (SprField F r n) f0
      / algebraMap (Spr F r n) (SprField F r n) g0 :=
    (IsFractionRing.mk'_num_den' (Spr F r n) a).symm
  have hT' : ∀ b : Fin n → Fˣ, sprDiagFieldEquiv F r n b
      (algebraMap (Spr F r n) (SprField F r n) f0
        / algebraMap (Spr F r n) (SprField F r n) g0)
      = algebraMap (Spr F r n) (SprField F r n) f0
        / algebraMap (Spr F r n) (SprField F r n) g0 := by
    intro b
    rw [← hratio]
    exact hT b
  have hS' : ∀ σ : Equiv.Perm (Fin n), sprPermFieldEquiv F r n σ
      (algebraMap (Spr F r n) (SprField F r n) f0
        / algebraMap (Spr F r n) (SprField F r n) g0)
      = algebraMap (Spr F r n) (SprField F r n) f0
        / algebraMap (Spr F r n) (SprField F r n) g0 := by
    intro σ
    rw [← hratio]
    exact hS σ
  obtain ⟨lam, hlam⟩ := sprDiag_exists_char F r n hcop hg0 hT'
  obtain ⟨lamS, hlamS⟩ := sprPerm_exists_char F r n hcop hg0 hS'
  have hs0 : ∃ t : SprIdx r n →₀ ℕ, g0.coeff t ≠ 0 := by
    obtain ⟨t, ht⟩ := MvPolynomial.support_nonempty.mpr hg0
    exact ⟨t, Finsupp.mem_support_iff.mp ht⟩
  obtain ⟨t0, ht0⟩ := hs0
  have hlam1 : ∀ b, lam b = 1 := fun b =>
    sprDiag_char_eq_one F r n lam hlam lamS hlamS hg0 ht0 b
  have hgf : ∀ b, sprDiagHom F r n b g0 = g0 := fun b =>
    sprDiagHom_fixed_of_char F r n lam hlam hlam1 b
  have hgf0 : ∀ b, sprDiagHom F r n b f0 = f0 := by
    intro b
    have hcross := sprDiag_mul_eq_of_fixed F r n b (f := f0) (g := g0) hg0 (hT' b)
    rw [hgf b] at hcross
    exact mul_right_cancel₀ hg0 hcross
  have hSf0 : ∀ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ f0
      = MvPolynomial.C ((lamS σ : Fˣ) : F) * f0 := by
    intro σ
    have hcross := sprPerm_mul_eq_of_fixed F r n σ (f := f0) (g := g0) hg0 (hS' σ)
    rw [hlamS σ] at hcross
    refine mul_right_cancel₀ hg0 ?_
    rw [hcross]
    ring
  refine ⟨g0 ^ Nat.factorial n, f0 * g0 ^ (Nat.factorial n - 1), pow_ne_zero _ hg0, ?_, ?_,
    ?_⟩
  · refine ⟨fun b => ?_, fun σ => ?_⟩
    · rw [map_pow, hgf b]
    · exact sprPermAlgEquiv_pow_fixed F r n lamS hlamS σ
  · refine ⟨fun b => ?_, fun σ => ?_⟩
    · rw [map_mul, map_pow, hgf0 b, hgf b]
    · exact sprPermAlgEquiv_mul_pow_fixed F r n lamS hSf0 hlamS σ
  · rw [hratio]
    simp only [map_mul, map_pow]
    have hk1 : Nat.factorial n - 1 + 1 = Nat.factorial n :=
      Nat.sub_add_cancel (Nat.factorial_pos n)
    have hpows : (algebraMap (Spr F r n) (SprField F r n) g0) ^ Nat.factorial n
        = (algebraMap (Spr F r n) (SprField F r n) g0) ^ (Nat.factorial n - 1)
          * (algebraMap (Spr F r n) (SprField F r n) g0) := by
      set x : SprField F r n := algebraMap (Spr F r n) (SprField F r n) g0
      calc x ^ Nat.factorial n = x ^ (Nat.factorial n - 1 + 1) :=
            congrArg (fun m => x ^ m) hk1.symm
        _ = x ^ (Nat.factorial n - 1) * x := pow_succ x (Nat.factorial n - 1)
    rw [div_eq_div_iff hg0K (pow_ne_zero _ hg0K), hpows]
    ring

#print axioms lem1425_scalar

end SprLem1425Scalar

/-! ## §153 **`N` 在 `M_n(K')` 上的作用** —— `lem:14.25` 矩阵层的**陈述前提**

源文 `:363–366` 把 `N` 的作用从 `S'`／`M_n(S')` "induced" 到 `K'` 与 `M_n(K')`：

```
ψ_A(α) = A · M_n(φ_A)(α) · A⁻¹        (A ∈ N')
```

v14 把 `lem:14.25` 的矩阵层列为"下一战场"，但**该层的陈述此前在本仓根本不存在**——
`Matrix (Fin n) (Fin n) (SprField F r n)` 在 22 个文件里出现 **0 次**。本节补这条前提：

| 件 | 内容 |
|---|---|
| `sprDiagMatK`／`sprPmatK` | `D_b`、`P_σ` 提升到 `K'` |
| `sprPsiDK`／`sprPsiSK` | `ψ_b`、`ψ_σ` 在 `M_n(K')` 上 |
| `sprMatNFixed` | `M_n(K')^N`（`lem:14.25` 的假设） |
| ★★ `sprPsiDK_smul` | **半线性** `ψ_b(s·α) = φ_b(s)·ψ_b(α)` |

**半线性为什么是关键**：矩阵层的证明要造 `N`-不变的公共分母 `s`。半线性给出
`ψ_b(sα) = φ_b(s)·α`（用 `ψ_b(α) = α`），故集合
`{ s ∈ S' : sα ∈ M_n(S') }` 在 `T`（以及 `S_n`）下**稳定**——这是
"用 `F` 无限 ＋ Van der Monde 投影把该集合里的元**对称化**"那条路线的入口
（见 [[proj-lem1425-plan-2026-10-19]] §6.2 的替代路线）。

**射程（勿夸大）**：本节**只定义作用并证半线性**；**没有**证明
`lem:14.25` 的矩阵层（"存在 `N`-不变公共分母"未写）。`ZEqNFixed` —— **未证**。
**H2 仍不是定理。** -/


section SprMatField

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `sprDiagMat` 的 `K'` 版本（对角矩阵 `D_b` 在 `SprField` 上）。 -/
noncomputable def sprDiagMatK (b : Fin n → Fˣ) :
    Matrix (Fin n) (Fin n) (SprField F r n) :=
  (sprDiagMat (F := F) (r := r) (n := n) b).map (algebraMap (Spr F r n) (SprField F r n))

#print axioms sprDiagMatK

/-- `sprPmat` 的 `K'` 版本。 -/
noncomputable def sprPmatK (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) (SprField F r n) :=
  sprPmat (SprField F r n) σ

#print axioms sprPmatK

/-- ★★★ **`T` 在 `M_n(K')` 上的作用**（源文 `:366` 的 `ψ_{D_b}(α) = D_{b^{-1}}·M_n(φ_b)(α)·D_b`，
提升到分式域）。 -/
noncomputable def sprPsiDK (b : Fin n → Fˣ)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    Matrix (Fin n) (Fin n) (SprField F r n) :=
  sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹)
    * α.map (sprDiagFieldEquiv F r n b).toRingHom
    * sprDiagMatK (F := F) (r := r) (n := n) b

#print axioms sprPsiDK

/-- ★★★ **`S_n` 在 `M_n(K')` 上的作用**。 -/
noncomputable def sprPsiSK (σ : Equiv.Perm (Fin n))
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    Matrix (Fin n) (Fin n) (SprField F r n) :=
  sprPmatK (F := F) (r := r) (n := n) σ * α.map (sprPermFieldEquiv F r n σ).toRingHom
    * (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹

#print axioms sprPsiSK

/-- ★★★★ **`M_n(K')^N`**（源文 `lem:14.25` 的假设：矩阵被 `N = T ⋊ S_n` 固定）。 -/
def sprMatNFixed (α : Matrix (Fin n) (Fin n) (SprField F r n)) : Prop :=
  (∀ b : Fin n → Fˣ, sprPsiDK F r n b α = α) ∧
    (∀ σ : Equiv.Perm (Fin n), sprPsiSK F r n σ α = α)

#print axioms sprMatNFixed

/-- `Matrix.map` 与标量乘法交换（`f` 为环同态）。 -/
theorem matrix_map_smul {m : Type} [Fintype m] {R S : Type} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (s : R) (M : Matrix m m R) :
    (s • M).map f = f s • M.map f := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

#print axioms matrix_map_smul

/-- ★★★★ **半线性**：`ψ_b(s·α) = φ_b(s)·ψ_b(α)`。

**为什么关键**：`lem:14.25` 的矩阵层要证"`α` `N`-不变 ⟹ 存在 `N`-不变的 `s` 使 `sα ∈ M_n(S')`"。
本式给 `ψ_b(s·α) = φ_b(s)·α`，故 **`{s : sα ∈ M_n(S')}` 是 `T`-稳定的**
（源文 `ψ_A(sα) = φ_A(s)ψ_A(α)` 的机检形态）。 -/
theorem sprPsiDK_smul (b : Fin n → Fˣ) (s : SprField F r n)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiDK F r n b (s • α) = sprDiagFieldEquiv F r n b s • sprPsiDK F r n b α := by
  rw [sprPsiDK, sprPsiDK, matrix_map_smul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

#print axioms sprPsiDK_smul

end SprMatField

/-! ## §154 **矩阵层的分母理想 `J`** —— `lem:14.25` 矩阵层（1/3）

源文 `lem:14.25` 的矩阵层只给一句："`M_n(K')` has a basis over `K'` that is `N` invariant.
Thus it suffices to show the following…"。第 329 轮末已判定**该句不是证明**（它依赖
`:270` 的 "`Ξ` 是 `K'`-基"，本仓没有那条输入），故改走**初等幂等路线**：

```
J := { s ∈ K' : sα ∈ M_n(S') }     (α 已 N-不变)
```

本节给 `J` 的三条结构性质：

| 件 | 内容 | 用途 |
|---|---|---|
| `sprHasDenom` | `J` 的定义（`∃ β, sα = β 的像`） | — |
| ★★ `sprPsiDK_algebraMap` | `ψ_b(β 的像) = (ψ_b β) 的像` | 把"`ψ_b` 保全 `M_n(S')`"搬到 `K'` |
| ★★★★ `sprHasDenom_diag` | **`J` 在 `T` 下稳定**：`sα ∈ M_n(S')` ⟹ `φ_b(s)α ∈ M_n(S')` | 投影的入口 |
| `sprHasDenom_add` | `J` 对加法封闭 | Van der Monde 线性组合 |
| ★ `sprHasDenom_algebraMap_mul` | **`J ∩ S'` 吸收乘法**：`s ∈ S'`、`t ∈ J` ⟹ `st ∈ J` | `S_n` 对称化的乘积 |

**本轮实测的易错点（登记）**：`J` 对**任意** `K'` 元的乘法**不**封闭
（`stα = s·(tα)`，`s ∈ K'` 未必把 `M_n(S')` 留在 `M_n(S')` 里）；
**闭的只是 `S'` 部分**。这正是"必须先在 `J ∩ S'` 里取半不变元"的原因——
`∏_σ φ_σ(s₂)` 的每个因子都在 `J ∩ S'` 里，故乘积仍在 `J` 里。

**射程（勿夸大）**：本节只给 `J` 的结构性质。**Van der Monde 投影（取半不变元）与
`S_n` 对称化未写**；`lem:14.25` 矩阵层**未证**；`ZEqNFixed` **未证**。**H2 仍不是定理。** -/


section SprMatDenom

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **`K'`-作用延拓 `S'`-作用**：`ψ_b(β 的像) = (ψ_b β) 的像`。

**用途**：`lem:14.25` 矩阵层的分母集合 `{s : sα ∈ M_n(S')}` 的 `N`-稳定性要用它把
"`ψ_b` 把 `M_n(S')` 送到 `M_n(S')`"这句从 `S'`-世界搬到 `K'`-世界。 -/
theorem sprPsiDK_algebraMap (b : Fin n → Fˣ) (β : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiDK F r n b (β.map (algebraMap (Spr F r n) (SprField F r n)))
      = (sprPsiD b β).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have hmap : (β.map (algebraMap (Spr F r n) (SprField F r n))).map
        (sprDiagFieldEquiv F r n b).toRingHom
      = (β.map (sprDiagHom F r n b)).map (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext x
    exact sprDiagFieldEquiv_algebraMap F r n b x
  rw [sprPsiDK, sprPsiD, hmap, Matrix.map_mul, Matrix.map_mul]
  rfl

#print axioms sprPsiDK_algebraMap

/-- **"`s` 是 `α` 的一个分母"**：`sα` 落在 `M_n(S')` 的像里。 -/
def sprHasDenom (α : Matrix (Fin n) (Fin n) (SprField F r n)) (s : SprField F r n) : Prop :=
  ∃ β : Matrix (Fin n) (Fin n) (Spr F r n),
    s • α = β.map (algebraMap (Spr F r n) (SprField F r n))

#print axioms sprHasDenom

/-- ★★★★ **分母集合在 `T` 下稳定**（半线性 ＋ `N`-不变性的直接后果）。

**这是矩阵层"造 `N`-不变公共分母"路线的入口**：`s ∈ J` ⟹ `φ_b(s) ∈ J`。
配合"`J` 对加法封闭"与"`F` 无限 ⇒ Van der Monde 投影"，可从任一 `g₀ ∈ J` 取出
**非零 `T`-半不变元**。 -/
theorem sprHasDenom_diag {α : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hα : sprMatNFixed F r n α) {s : SprField F r n} (hs : sprHasDenom F r n α s)
    (b : Fin n → Fˣ) : sprHasDenom F r n α (sprDiagFieldEquiv F r n b s) := by
  obtain ⟨β, hβ⟩ := hs
  refine ⟨sprPsiD b β, ?_⟩
  rw [← sprPsiDK_algebraMap, ← hα.1 b, ← sprPsiDK_smul, hβ]

#print axioms sprHasDenom_diag

/-- `J` 对加法封闭（`sα, tα ∈ M_n(S')` ⟹ `(s+t)α ∈ M_n(S')`）。 -/
theorem sprHasDenom_add {α : Matrix (Fin n) (Fin n) (SprField F r n)}
    {s t : SprField F r n} (hs : sprHasDenom F r n α s) (ht : sprHasDenom F r n α t) :
    sprHasDenom F r n α (s + t) := by
  obtain ⟨β, hβ⟩ := hs
  obtain ⟨γ, hγ⟩ := ht
  refine ⟨β + γ, ?_⟩
  rw [add_smul, hβ, hγ]
  ext i j
  simp [Matrix.map_apply]

#print axioms sprHasDenom_add

/-- ★★★ **`J` 的"理想"性**：`s ∈ S'`（多项式）时 `st ∈ J`（`t ∈ J`）。

**注意（易错，本轮实测）**：`J` 对**任意** `K'` 元的乘法**不**封闭
（`stα = s·(tα)`，而 `s ∈ K'` 不一定把 `M_n(S')` 留在 `M_n(S')` 里）。
**闭的只是 `S'` 部分**——这正是"`N`-不变分母"存在性论证里需要的那一半：
`∏_σ φ_σ(s₂)` 的每个因子都在 `J ∩ S'` 里，故乘积仍在 `J` 里。 -/
theorem sprHasDenom_algebraMap_mul {α : Matrix (Fin n) (Fin n) (SprField F r n)}
    (c : Spr F r n) {t : SprField F r n} (ht : sprHasDenom F r n α t) :
    sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) c * t) := by
  obtain ⟨γ, hγ⟩ := ht
  refine ⟨c • γ, ?_⟩
  rw [mul_smul, hγ, ← matrix_map_smul]

#print axioms sprHasDenom_algebraMap_mul

end SprMatDenom

/-! ## §155 **`J` 的 `S_n`-稳定性 ＋ 矩阵映射的四条通用件** —— `lem:14.25` 矩阵层（2/3）

§154 给了 `J` 的 `T`-稳定性。本节补 **`S_n` 半边**，于是 `J` **完整地 `N`-稳定**：

| 件 | 内容 |
|---|---|
| `matrix_map_mul`／`matrix_map_one` | `Matrix.map` 沿环同态保乘法／保单位（走 `RingHom.mapMatrix`，**不碰 `if` 改写**） |
| `sprPmatK_eq_map`／`sprPmat_inv`／`sprPmatK_inv` | `P_σ` 在 `K'` 上的形态与逆（`P_σ⁻¹ = P_{σ⁻¹}`） |
| `sprPsiSM` | `S_n` 侧 `ψ_σ` 的 `S'`-形态 |
| ★★ `sprPsiSK_algebraMap` | `ψ_σ(β 的像) = (ψ_σ β) 的像` |
| ★★ `sprPsiSK_smul` | **半线性（`S_n` 半边）** `ψ_σ(s·α) = φ_σ(s)·ψ_σ(α)` |
| ★★★★ `sprHasDenom_perm` | **`J` 在 `S_n` 下稳定** |

**⟹ 现在 `J` 同时 `T`-稳定（§154 `sprHasDenom_diag`）与 `S_n`-稳定（本节
`sprHasDenom_perm`），故 `J` **`N`-稳定**——这是"取 `N`-不变公共分母"路线的全部结构性前提。

**工艺（两条，实案）**：
* **R186**：矩阵的 `Inv` **不是** `DivisionMonoid` 的 `inv`——`inv_eq_of_mul_eq_one_right`
  对 `Matrix` **原理上不适用**（报"expected `@Inv.inv ?m.9 DivisionMonoid.toDivInvMonoid.toInv`"）。
  **正解**：用 `Matrix.inv_eq_right_inv`（`NonsingularInverse.lean:474`）。
* **R187**：`(RingHom.mapMatrix f).map_one` 在 `matrix_map_one` 里**卡 `DecidableEq` 元变量**
  （"typeclass instance problem is stuck `DecidableEq ?m.15`"）。
  **正解**：不借 `RingHom`，直接 `ext i j` ＋ `Matrix.one_apply` ＋ `split_ifs <;> simp`。

**射程（勿夸大）**：本节**仍不含** Van der Monde 投影（取 `T`-半不变元）与 `S_n` 对称化的
**组装**；`lem:14.25` 矩阵层**未证**；`ZEqNFixed` **未证**。**H2 仍不是定理。** -/


section SprMatDenomS

set_option linter.style.haveILetI false

/-- `Matrix.map` 沿环同态保乘法。 -/
theorem matrix_map_mul {m : Type} [Fintype m] [DecidableEq m] {R S : Type}
    [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) (A B : Matrix m m R) :
    A.map f * B.map f = (A * B).map f := by
  have h := (RingHom.mapMatrix f).map_mul A B
  simpa using h.symm

#print axioms matrix_map_mul

/-- `Matrix.map` 沿环同态保单矩阵。 -/
theorem matrix_map_one {m : Type} [Fintype m] [DecidableEq m] {R S : Type}
    [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) :
    (1 : Matrix m m R).map f = 1 := by
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

#print axioms matrix_map_one

variable (F : Type) [Field F] (r n : ℕ)

/-- `sprPmat` 的 `K'` 版就是 `S'` 版沿 `algebraMap` 的像（`0/1` 都在 `F` 里，故常值项不动）。 -/
theorem sprPmatK_eq_map (σ : Equiv.Perm (Fin n)) :
    sprPmatK (F := F) (r := r) (n := n) σ
      = (sprPmat (Spr F r n) σ).map (algebraMap (Spr F r n) (SprField F r n)) := by
  refine Matrix.ext fun i j => ?_
  show sprPmat (SprField F r n) σ i j
    = ((sprPmat (Spr F r n) σ).map (algebraMap (Spr F r n) (SprField F r n))) i j
  rw [Matrix.map_apply, sprPmat_apply, sprPmat_apply]
  split_ifs <;> simp

#print axioms sprPmatK_eq_map

/-- `sprPmat` 的逆就是 `σ⁻¹` 的 `sprPmat`（任意交换环）。 -/
theorem sprPmat_inv (R : Type) [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (sprPmat R σ)⁻¹ = sprPmat (n := n) R σ⁻¹ :=
  Matrix.inv_eq_right_inv (sprPmat_mul_symm R σ)

#print axioms sprPmat_inv

/-- `sprPmatK` 的逆的显式形态。 -/
theorem sprPmatK_inv (σ : Equiv.Perm (Fin n)) :
    (sprPmatK (F := F) (r := r) (n := n) σ)⁻¹
      = (sprPmat (Spr F r n) σ⁻¹).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have h1 : sprPmatK (F := F) (r := r) (n := n) σ
        * (sprPmat (Spr F r n) σ⁻¹).map (algebraMap (Spr F r n) (SprField F r n)) = 1 := by
    rw [sprPmatK_eq_map, matrix_map_mul, sprPmat_mul_symm, matrix_map_one]
  exact Matrix.inv_eq_right_inv h1

#print axioms sprPmatK_inv

/-- `S_n` 在 `M_n(S')` 上的作用（`S_n` 侧的 `ψ_σ`，逆写成 `σ⁻¹` 以免除逆元簿记）。 -/
noncomputable def sprPsiSM (σ : Equiv.Perm (Fin n))
    (β : Matrix (Fin n) (Fin n) (Spr F r n)) : Matrix (Fin n) (Fin n) (Spr F r n) :=
  sprPmat (Spr F r n) σ * β.map (sprPermAlgEquiv F r n σ) * sprPmat (Spr F r n) σ⁻¹

#print axioms sprPsiSM

/-- ★★★★ **`K'`-作用延拓 `S'`-作用**（`S_n` 半边）——`J` 的 `S_n`-稳定性的钥匙。 -/
theorem sprPsiSK_algebraMap (σ : Equiv.Perm (Fin n))
    (β : Matrix (Fin n) (Fin n) (Spr F r n)) :
    sprPsiSK F r n σ (β.map (algebraMap (Spr F r n) (SprField F r n)))
      = (sprPsiSM F r n σ β).map (algebraMap (Spr F r n) (SprField F r n)) := by
  have hmap : (β.map (algebraMap (Spr F r n) (SprField F r n))).map
        (sprPermFieldEquiv F r n σ).toRingHom
      = (β.map (sprPermAlgEquiv F r n σ)).map
          (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext x
    exact sprPermFieldEquiv_algebraMap F r n σ x
  rw [sprPsiSK, sprPsiSM, hmap, sprPmatK_inv, sprPmatK_eq_map, matrix_map_mul,
    matrix_map_mul]

#print axioms sprPsiSK_algebraMap

/-- ★★★ **半线性（`S_n` 半边）**：`ψ_σ(s·α) = φ_σ(s)·ψ_σ(α)`。 -/
theorem sprPsiSK_smul (σ : Equiv.Perm (Fin n)) (s : SprField F r n)
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    sprPsiSK F r n σ (s • α) = sprPermFieldEquiv F r n σ s • sprPsiSK F r n σ α := by
  rw [sprPsiSK, sprPsiSK, matrix_map_smul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

#print axioms sprPsiSK_smul

/-- ★★★★ **分母集合在 `S_n` 下稳定**（与 §154 的 `sprHasDenom_diag` 合起来即 `N`-稳定）。 -/
theorem sprHasDenom_perm {α : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hα : sprMatNFixed F r n α) {s : SprField F r n} (hs : sprHasDenom F r n α s)
    (σ : Equiv.Perm (Fin n)) : sprHasDenom F r n α (sprPermFieldEquiv F r n σ s) := by
  obtain ⟨β, hβ⟩ := hs
  refine ⟨sprPsiSM F r n σ β, ?_⟩
  rw [← sprPsiSK_algebraMap, ← hα.2 σ, ← sprPsiSK_smul, hβ]

#print axioms sprHasDenom_perm

end SprMatDenomS

/-! ## §156 **`J ∩ S'` 非空 ＋ 它是 `F`-子模** —— `lem:14.25` 矩阵层（3/3 的结构件）

§154／§155 给了 `J` 的 `T`／`S_n`-稳定性。本节补**非空性**与**`F`-子模结构**，
这是"Van der Monde 剥离算子"路线的载体：

| 件 | 内容 |
|---|---|
| ★★★ `sprHasDenom_exists` | **`J ∩ S' ≠ 0`**：每个 `M_n(K')` 矩阵都有非零多项式分母（`IsLocalization.surj` ＋ `Finset.mul_prod_erase` 剥出条目分母） |
| `sprHasDenom_smul` | `J_K'` 对 `F`-纯量封闭（走"`S'`-吸收乘法"，**避开标量塔簿记**） |
| ★★ `sprDenomSubmodule` | **`J ∩ S'` 作为 `F`-子模**（投影算子的载体） |

**⟹ `J` 的完整结构（矩阵层结构层收口）**：
`J` 是 `K'` 的非零子集，**`T`-稳定**（§154）、**`S_n`-稳定**（§155）；
`J ∩ S'` 是**非零 `F`-子模**并吸收 `S'`-乘法。**一条路线所需的全部前提已到手。**

**工艺新得（3 条，都有实案）**：
* **R188**：本 pin 的 `Matrix` 是 **`def` 而非透明缩写**——`fun i j => …` **不能**直接当
  `Matrix`（报 "expected `Matrix (Fin n) (Fin n) ℕ`"），且 `Matrix.map f M i j`
  在 `rw [Matrix.map_apply]` 下**匹配不到**。**正解**：用 `Matrix.of`，再 `Matrix.of_apply`。
* **R189**：`Finset.prod_erase` 在本 pin 是"`f a = 1` ⟹ 乘积不变"，**不是**剥出因子；
  剥出要用 **`Finset.mul_prod_erase`**（`f a * ∏ erase = ∏ s`，方向 `←`）。
* **R190**：`Submodule` 的 `zero_mem'`／`add_mem'`／`smul_mem'` 里，目标被
  `carrier := {c | …}` 包住 ⟹ 先 **`change`** 展开，再 `rw [map_zero/map_add/map_smul]`；
  且 `rw [map_smul]` 对 `algebraMap`（`RingHom` **不是** `MulActionHom`）**不过** ——
  改用 `Algebra.smul_def` ＋ `IsScalarTower.algebraMap_apply F (Spr) (SprField)`（带全参数）。

**射程（勿夸大）**：**Van der Monde 剥离算子（取非零半不变元）与 `S_n` 对称化的组装
未写**；`lem:14.25` 矩阵层**未证**；`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未做/未证**。
**H2 仍不是定理。** -/


section SprMatDenomEx

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **`J ∩ S' ≠ 0`**：每个 `M_n(K')` 的矩阵都有**非零多项式分母**。

**证明**：`K' = Frac(S')` 是 `nonZeroDivisors` 的局部化，故每个条目 `α i j` 有
`α i j * algebraMap (b p) = algebraMap (a p)`（`IsLocalization.surj`）。取
`c := ∏ p, b p`⋯，条目分母用 `Finset.prod_erase` 剥出，其余因子当作分子的一部分。

**意义**：这是矩阵层"造 `N`-不变公共分母"路线的**非空性起点**——`J` 里的非零元存在，
才有东西可投影。 -/
theorem sprHasDenom_exists (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    ∃ c : Spr F r n, c ≠ 0 ∧
      sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) c) := by
  classical
  have h : ∀ p : Fin n × Fin n, ∃ q : Spr F r n × nonZeroDivisors (Spr F r n),
      α p.1 p.2 * algebraMap (Spr F r n) (SprField F r n) (q.2 : Spr F r n)
        = algebraMap (Spr F r n) (SprField F r n) q.1 := fun p =>
    IsLocalization.surj (nonZeroDivisors (Spr F r n)) (α p.1 p.2)
  choose q hq using h
  refine ⟨∏ p : Fin n × Fin n, ((q p).2 : Spr F r n), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro p _
    exact mem_nonZeroDivisors_iff_ne_zero.mp (q p).2.2
  · refine ⟨Matrix.of (fun i j =>
        (∏ p ∈ Finset.univ.erase (i, j), ((q p).2 : Spr F r n)) * (q (i, j)).1), ?_⟩
    ext i j
    rw [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      ← Finset.mul_prod_erase Finset.univ (fun p : Fin n × Fin n => ((q p).2 : Spr F r n))
        (Finset.mem_univ (i, j)), map_mul, map_mul, ← hq (i, j)]
    ring

#print axioms sprHasDenom_exists

/-- `J_K'` 对 `F`-纯量封闭（用"`S'`-吸收乘法"实现，避开标量塔簿记）。 -/
theorem sprHasDenom_smul {α : Matrix (Fin n) (Fin n) (SprField F r n)}
    {t : SprField F r n} (ht : sprHasDenom F r n α t) (a : F) :
    sprHasDenom F r n α (a • t) := by
  have h : a • t = algebraMap (Spr F r n) (SprField F r n) (algebraMap F (Spr F r n) a) * t := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n)]
  rw [h]
  exact sprHasDenom_algebraMap_mul (F := F) (r := r) (n := n) _ ht

#print axioms sprHasDenom_smul

/-- ★★★ **`J ∩ S'` 作为 `F`-子模**——投影（Van der Monde 剥离算子）的载体。

`J ∩ S' = {c ∈ S' : cα ∈ M_n(S')}`；它是 **`T`-稳定**（§154）、**`S_n`-稳定**（§155）、
并对 `S'` 的吸收乘法封闭（`sprHasDenom_algebraMap_mul`）。 -/
noncomputable def sprDenomSubmodule (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    Submodule F (Spr F r n) where
  carrier := {c | sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) c)}
  zero_mem' := by
    change sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) (0 : Spr F r n))
    have h0 : algebraMap (Spr F r n) (SprField F r n) (0 : Spr F r n) = 0 := map_zero _
    rw [h0]
    exact ⟨0, by ext i j; simp⟩
  add_mem' := by
    intro a b ha hb
    change sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) (a + b))
    rw [map_add]
    exact sprHasDenom_add (F := F) (r := r) (n := n) ha hb
  smul_mem' := by
    intro a c hc
    change sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) (a • c))
    have hs : a • c = algebraMap F (Spr F r n) a * c := Algebra.smul_def a c
    rw [hs, map_mul, ← IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n),
      ← Algebra.smul_def]
    exact sprHasDenom_smul (F := F) (r := r) (n := n) hc a

#print axioms sprDenomSubmodule

end SprMatDenomEx

/-! ## §157 **剥离算子的两个核心事实：`φ_b` 保支撑 ＋ 真子集** —— `lem:14.25` 矩阵层（算子层 1/2）

§154–§156 把 `J` 的结构做完了。本节给**算子层**的两条：

| 件 | 内容 |
|---|---|
| `sprWt_ne_zero` | 每个变元的权 `sprWt b v` 非零（都是 `Fˣ` 的元素） |
| ★★★ `sprDiagHom_support_eq` | **`φ_b` 保持支撑**：`(φ_b g).support = g.support` |
| `sprDiagHom_C_mul` | `φ_b (C c · g) = C c · φ_b g` |
| ★★★★ `sprDiagHom_sub_C_mul_support_ssubset` | 若 `φ_b g` 不是 `g` 的纯量倍，则取 `c := (φ_b g).coeff s₀ / g.coeff s₀`，`φ_b g - C c · g` 的支撑是 **`g` 支撑的真子集** |

**★ 这两条合起来给出一个比"Van der Monde 投影"更省的论证（第 334 轮路线修正 4）**：
取 `J ∩ S'` 中**支撑最小**的非零元 `g`（`ℕ` 良序，`Nat.find`）。若某个 `b` 使
`φ_b g` 不是 `g` 的纯量倍，则由本节两条得 `φ_b g - C c g ∈ J ∩ S'` 非零而支撑**严格更小**
—— 与最小性矛盾。**故最小支撑元自动是 `T`-半不变元**。
* **不需要** 选分离特征标的 `b`（不用基-N 权、不用 `[Infinite F]` 的投影）；
* **不需要** `Polynomial`／`Module.End` 上的构造；
* 只需 `φ_b` 保支撑这一条（`sprDiagHom_coeff` ＋ 权非零）。

**工艺（2 条）**：
* **R191**：`MvPolynomial.support` 的成员判据是 **`MvPolynomial.mem_support_iff`**，
  `Finsupp.mem_support_iff` **匹配不到**（尽管底层是 `Finsupp`）。
* **R192**：`λ` 是 Lean 的**保留词**——`∀ λ : F, …` 与 `set λ : F := …` 都报
  "unexpected token 'λ'"。**正解**：改名 `mu`。

**射程（勿夸大）**：**最小支撑的装配（`Nat.find` ＋ 与 `J` 的交互）与 `S_n` 对称化未写**；
`lem:14.25` 矩阵层**未证**；`ZEqNFixed` **未证**。**H2 仍不是定理。** -/


section SprPeel

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- 单项式的权非零（每个变元的权都是 `Fˣ` 里的元素）。 -/
theorem sprWt_ne_zero (b : Fin n → Fˣ) (v : SprIdx r n) : sprWt F r n b v ≠ 0 := by
  rcases v with i | ⟨i, j, k⟩
  · rw [sprWt_inl]; exact one_ne_zero
  · rw [sprWt_inr]
    exact mul_ne_zero (Units.ne_zero (b i)) (inv_ne_zero (Units.ne_zero (b j)))

#print axioms sprWt_ne_zero

/-- ★★★ **`φ_b` 保持支撑**（每个单项式只被非零纯量乘）。

**用途**：`lem:14.25` 矩阵层的"最小支撑"论证里，`φ_b g` 与 `g` 支撑相同，
故 `φ_b g - C λ * g` 的支撑是 `g` 支撑的**子集**；取 `λ` 为一个条目的比值即可
使它**真包含**（去掉那个条目）。 -/
theorem sprDiagHom_support_eq (b : Fin n → Fˣ) (g : Spr F r n) :
    (sprDiagHom F r n b g).support = g.support := by
  classical
  ext s
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, sprDiagHom_coeff]
  constructor
  · intro h hc
    exact h (by rw [hc, mul_zero])
  · intro hc
    refine mul_ne_zero ?_ hc
    exact Finset.prod_ne_zero_iff.mpr
      (fun v _ => pow_ne_zero _ (sprWt_ne_zero F r n b v))

#print axioms sprDiagHom_support_eq

/-- `φ_b` 与常数乘法交换。 -/
theorem sprDiagHom_C_mul (b : Fin n → Fˣ) (c : F) (g : Spr F r n) :
    sprDiagHom F r n b (MvPolynomial.C c * g)
      = MvPolynomial.C c * sprDiagHom F r n b g := by
  rw [map_mul, sprDiagHom_C]

#print axioms sprDiagHom_C_mul

/-- ★★★ **支撑真的变小**：若 `φ_b g` 不是 `g` 的纯量倍，则取 `λ` 为任一非零条目的
比值，`φ_b g - C λ * g` 的支撑是 `g` 支撑的**真子集**。

（`s₀` 处系数为 `0`；又因 `φ_b g ≠ C λ * g` 故不全为 `0`。） -/
theorem sprDiagHom_sub_C_mul_support_ssubset (b : Fin n → Fˣ) {g : Spr F r n}
    {s₀ : SprIdx r n →₀ ℕ} (hs₀ : g.coeff s₀ ≠ 0)
    (hne : ∀ mu : F, sprDiagHom F r n b g ≠ MvPolynomial.C mu * g) :
    (sprDiagHom F r n b g
        - MvPolynomial.C ((sprDiagHom F r n b g).coeff s₀ / g.coeff s₀) * g).support
      ⊂ g.support := by
  classical
  set mu : F := (sprDiagHom F r n b g).coeff s₀ / g.coeff s₀ with hmu
  have hkill : (sprDiagHom F r n b g - MvPolynomial.C mu * g).coeff s₀ = 0 := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, hmu,
      div_mul_cancel₀ _ hs₀, sub_self]
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro s hs
    rw [MvPolynomial.mem_support_iff] at hs ⊢
    intro hc
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, sprDiagHom_coeff, hc] at hs
    simp at hs
  · intro h
    have hmem : s₀ ∈ (sprDiagHom F r n b g - MvPolynomial.C mu * g).support := by
      rw [h]
      exact MvPolynomial.mem_support_iff.mpr hs₀
    rw [MvPolynomial.mem_support_iff] at hmem
    exact hmem hkill

#print axioms sprDiagHom_sub_C_mul_support_ssubset

end SprPeel

/-! ## §158 ★★★★★ **最小支撑元是 `T`-半不变元** —— `lem:14.25` 矩阵层算子层收口

本节把 §154–§157 的零件装配成 `lem:14.25` 矩阵层的**关键一步**：

```
∃ g ∈ J ∩ S'（g ≠ 0）与 u : (Fin n → Fˣ) → Fˣ，使 ∀ b, φ_b g = C (u b) · g。
```

**论证（不需要选分离特征标的 `b`，不需要任何投影算子，也不需要 `[Infinite F]`）**：
取 `J ∩ S' = sprDenomSubmodule α` 中**支撑最小**的非零元 `g`（`Nat.find` 于 `support.card`）。
若某 `b` 使 `φ_b g` 不是 `g` 的纯量倍（`hcon`），取 `c := (φ_b g).coeff s₀ / g.coeff s₀`：

* `φ_b g ∈ J`（§154 的 `T`-稳定性，经 `sprDiagFieldEquiv_algebraMap` 改写）；
* `C c · g = c • g ∈ J`（§156 的 `F`-子模结构）；
* 故 `φ_b g − C c g ∈ J`，且由 `hcon` **非零**；
* §157 的 `sprDiagHom_sub_C_mul_support_ssubset` 说它支撑**真小** ⟹ 与 `g` 的最小性矛盾。

**⟹ `lem:14.25` 矩阵层的剩余 = 两步**：
① `s := ∏_{σ∈S_n} φ_σ(g)`（`S_n`-对称化）——它同时是 `S_n`-不变（§82）与 `T`-不变
  （由 `∏_σ χ(b_{σ⁻¹·}) = 1`，用 `sprA_sum_eq_sprB_sum`；**不需要逆单项式**）；
② `s ∈ J`（每个因子在 `J ∩ S'` 里，§154 的吸收乘法），故 `sα ∈ M_n(S')`。

**工艺（2 条）**：
* **R193**：`Nat.find_min'` 的第二参数是 `p m` 本身（`∃ g, …`），直接写
  `⟨g, hgJ, hgne, rfl⟩` 会**因 `∃ k, ∃ g, …` 的双层结构而对不上**——须先 `have`
  出 `∃ g, …` 的具名命题再传。
* **R194**：`sprHasDenom_diag` 的结论是 `sprHasDenom α (φ_b (algebraMap g))`，
  而 `J` 的成员形态是 `sprHasDenom α (algebraMap (φ_b g))`；两者差
  **`sprDiagFieldEquiv_algebraMap`**，须 `rw [← …]` 桥一次（否则报类型不符）。

**射程（勿夸大）**：`S_n`-对称化与 `lem:14.25` 矩阵层的**最终陈述未写**；
`lem:14.25` **未证**；`ZEqNFixed` **未证**。**H2 仍不是定理。** -/


section SprSemiInv

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **最小支撑元是 `T`-半不变元** —— `lem:14.25` 矩阵层算子层的收口。

**论证（路线修正 4，不需要选分离特征标的 `b`，也不需要任何投影算子）**：
取 `J ∩ S'`（`= sprDenomSubmodule α`）中**支撑最小**的非零元 `g`（`Nat.find`）。
若某 `b` 使 `φ_b g` 不是 `g` 的纯量倍，取 `c := (φ_b g).coeff s₀ / g.coeff s₀`
（`s₀ ∈ supp g`）。则

* `φ_b g ∈ J`（`J` 的 `T`-稳定性，§154）；
* `c • g ∈ J`（`J` 是 `F`-子模，§156），且 `C c * g = c • g`；
* 故 `φ_b g - C c g ∈ J`；又由 `hcon` 它 **非零**；
* 而 §157 的 `sprDiagHom_sub_C_mul_support_ssubset` 说它的支撑是 `g` 支撑的**真子集**
  ⟹ 基数严格更小 ⟹ 与 `g` 的最小性矛盾。

⟹ 存在函数 `u : (Fin n → Fˣ) → Fˣ` 使 `φ_b g = C (u b) * g`（`u b ≠ 0` 因 `φ_b g ≠ 0`）。 -/
theorem sprExists_semiInv (α : Matrix (Fin n) (Fin n) (SprField F r n))
    (hα : sprMatNFixed F r n α) :
    ∃ (g : Spr F r n) (u : (Fin n → Fˣ) → Fˣ),
      g ≠ 0 ∧ sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) g) ∧
        ∀ b : Fin n → Fˣ, sprDiagHom F r n b g = MvPolynomial.C ((u b : Fˣ) : F) * g := by
  classical
  have hex : ∃ k : ℕ, ∃ g : Spr F r n,
      g ∈ sprDenomSubmodule F r n α ∧ g ≠ 0 ∧ g.support.card = k := by
    obtain ⟨c, hc, hd⟩ := sprHasDenom_exists F r n α
    exact ⟨c.support.card, c, hd, hc, rfl⟩
  obtain ⟨g, hgJ, hgne, hgcard⟩ := Nat.find_spec hex
  have hmin : ∀ h : Spr F r n, h ∈ sprDenomSubmodule F r n α → h ≠ 0 →
      g.support.card ≤ h.support.card := by
    intro h hh hhne
    have h' : ∃ g : Spr F r n, g ∈ sprDenomSubmodule F r n α ∧ g ≠ 0
        ∧ g.support.card = h.support.card := ⟨h, hh, hhne, rfl⟩
    have hle := Nat.find_min' hex h'
    rw [← hgcard] at hle
    exact hle
  have hne0 : ∀ b : Fin n → Fˣ, sprDiagHom F r n b g ≠ 0 := by
    intro b h
    apply hgne
    have h1 : (sprDiagEquiv F r n b) g = 0 := by
      rw [sprDiagEquiv_apply]
      exact h
    exact (sprDiagEquiv F r n b).injective (by rw [h1, map_zero])
  have hsem : ∀ b : Fin n → Fˣ, ∃ mu : F,
      sprDiagHom F r n b g = MvPolynomial.C mu * g := by
    intro b
    by_contra hcon
    push_neg at hcon
    obtain ⟨s₀, hs₀⟩ := MvPolynomial.support_nonempty.mpr hgne
    have hs₀c : g.coeff s₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hs₀
    have hhJ : sprDiagHom F r n b g ∈ sprDenomSubmodule F r n α := by
      change sprHasDenom F r n α
        (algebraMap (Spr F r n) (SprField F r n) (sprDiagHom F r n b g))
      rw [← sprDiagFieldEquiv_algebraMap F r n b g]
      exact sprHasDenom_diag F r n hα hgJ b
    set mu : F := (sprDiagHom F r n b g).coeff s₀ / g.coeff s₀ with hmu
    have hcm : MvPolynomial.C mu * g = mu • g := (Algebra.smul_def mu g).symm
    have hg'J : sprDiagHom F r n b g - MvPolynomial.C mu * g
        ∈ sprDenomSubmodule F r n α := by
      rw [hcm]
      exact Submodule.sub_mem _ hhJ (Submodule.smul_mem _ mu hgJ)
    have hg'ne : sprDiagHom F r n b g - MvPolynomial.C mu * g ≠ 0 := by
      intro h
      exact hcon mu (sub_eq_zero.mp h)
    have hminle := hmin _ hg'J hg'ne
    have hss := sprDiagHom_sub_C_mul_support_ssubset F r n b hs₀c hcon
    have hlt := Finset.card_lt_card hss
    exact absurd hlt (Nat.not_lt.mpr hminle)
  have hsem2 : ∀ b : Fin n → Fˣ, ∃ u : Fˣ,
      sprDiagHom F r n b g = MvPolynomial.C ((u : Fˣ) : F) * g := by
    intro b
    obtain ⟨mu, hmu⟩ := hsem b
    have hne : mu ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.C_0, zero_mul] at hmu
      exact hne0 b hmu
    exact ⟨Units.mk0 mu hne, by rw [hmu]; rfl⟩
  choose u hu using hsem2
  exact ⟨g, u, hgne, hgJ, hu⟩

#print axioms sprExists_semiInv

end SprSemiInv

/-! ## §159 ★★★★ **组合件 3a**：`S_n`-对称化的 `T`-特征标相消 —— `lem:14.25` 矩阵层（组装 1/2）

§158 给出 `J ∩ S'` 中一个 `T`-半不变元 `g`（`φ_b g = C (u b) · g`）。
矩阵层的收口要取 `s := ∏_{σ∈S_n} φ_σ(g)`；由 §83 的交换律
（`φ_σ ∘ φ_b = φ_{b∘σ} ∘ φ_σ`，等价形态）得

```
φ_b(s) = (∏_{σ∈S_n} u (b∘σ)) · s
```

本节证明 **`∏_σ u (b∘σ) = 1`**（当 `u` 是指数形态 `(∏ b_i^{A_i})(∏ b_j^{B_j})⁻¹` 且
`ΣA = ΣB`，后者由 `sprA_sum_eq_sprB_sum` 给出）：

| 件 | 内容 |
|---|---|
| `sprPermTorus_prod_indep` | **`∏_σ b (σ i)` 与 `i` 无关**（把 `σ` 换成 `σ * π`，`π i = j`） |
| ★★★★ `sprProd_perm_char` | `∏_σ [(∏_i (b(σ i))^{A_i})·(∏_j (b(σ j))^{B_j})⁻¹] = 1`（`ΣA = ΣB`） |

**★ 证明的关键（省掉一条计数）**：令 `Q := ∏_σ b (σ i)`，由上面的无关性它与 `i` 无关。
交换两个乘积后用 `Finset.prod_pow` ＋ `Finset.prod_pow_eq_pow_sum`，两半分别是
`Q^{ΣA}` 与 `Q^{ΣB}`，由 `ΣA = ΣB` 相消。**`Q` 的具体值（本会是 `(∏b)^{(n-1)!}`）
从头到尾不出现** —— 故**不需要** `|{σ : σ i = j}| = (n-1)!` 那条计数。

**工艺（2 条，实案）**：
* **R195**：`Equiv.Perm` 的乘法序（R181）在这里的**具体用法**：`(σ * π) x = σ (π x)`
  （`rfl`），故"换指标"的等价取 **`Equiv.mulRight π`**（`σ ↦ σ * π`，得
  `(σ*π) i = σ j`）；取 `Equiv.mulLeft` 会得到 `(π*σ) i = π (σ i)`，**方向反**。
* **R196**：`Finset.prod_inv_distrib` 的可用方向是 **`∏ x, (f x)⁻¹ = (∏ x, f x)⁻¹`**；
  写 `← Finset.prod_inv_distrib` 会报"找不到落点"（目标里的形态正是左边）。

**射程（勿夸大）**：**组装（`s` 的 `N`-不变性与 `s ∈ J`）未写**；`lem:14.25` 矩阵层
**未证**；`ZEqNFixed` **未证**。**H2 仍不是定理。** -/


section SprProdPermChar

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- **`∏_σ b (σ i)` 与 `i` 无关**（把 `σ` 换成 `σ * π`，`π i = j`）。 -/
theorem sprPermTorus_prod_indep [Nonempty (Fin n)] (b : Fin n → Fˣ) (i j : Fin n) :
    (∏ σ : Equiv.Perm (Fin n), b (σ i)) = ∏ σ : Equiv.Perm (Fin n), b (σ j) := by
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin n), π i = j :=
    ⟨Equiv.swap i j, Equiv.swap_apply_left i j⟩
  have h := Equiv.prod_comp (Equiv.mulRight π)
    (fun τ : Equiv.Perm (Fin n) => b (τ i))
  simp only [Equiv.coe_mulRight] at h
  rw [← h]
  exact Finset.prod_congr rfl
    (fun σ _ => by rw [show (σ * π) i = σ (π i) from rfl, hπ])

#print axioms sprPermTorus_prod_indep

/-- ★★★★ **组合件 3a**：`∏_σ [(∏_i (b(σ i))^{A_i}) · (∏_j (b(σ j))^{B_j})⁻¹] = 1`
（当 `ΣA = ΣB`）。

**证明**：令 `Q := ∏_σ b (σ i)`（**与 `i` 无关**，见 `sprPermTorus_prod_indep`）。
交换两个乘积后用 `Finset.prod_pow` 与 `Finset.prod_pow_eq_pow_sum`，得两半分别是
`Q^{ΣA}` 与 `Q^{ΣB}`，由 `hAB` 相消。
**★ 关键**：`Q` 的**具体值从不出现**——所以不需要 `(n-1)!` 那条计数。 -/
theorem sprProd_perm_char [Nonempty (Fin n)] (b : Fin n → Fˣ) (A B : Fin n → ℕ)
    (hAB : ∑ i, A i = ∑ j, B j) :
    (∏ σ : Equiv.Perm (Fin n),
        (∏ i, (b (σ i)) ^ A i) * (∏ j, (b (σ j)) ^ B j)⁻¹) = 1 := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin n))
  set Q : Fˣ := ∏ σ : Equiv.Perm (Fin n), b (σ i₀) with hQ
  have hQi : ∀ i : Fin n, (∏ σ : Equiv.Perm (Fin n), b (σ i)) = Q := by
    intro i
    rw [hQ]
    exact sprPermTorus_prod_indep (F := F) (n := n) b i i₀
  have hA : (∏ σ : Equiv.Perm (Fin n), ∏ i : Fin n, (b (σ i)) ^ A i)
      = Q ^ (∑ i, A i) := by
    rw [Finset.prod_comm]
    have h1 : ∀ i : Fin n, (∏ σ : Equiv.Perm (Fin n), (b (σ i)) ^ A i)
        = Q ^ A i := by
      intro i
      rw [Finset.prod_pow, hQi i]
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_pow_eq_pow_sum]
  have hB : (∏ σ : Equiv.Perm (Fin n), ∏ j : Fin n, (b (σ j)) ^ B j)
      = Q ^ (∑ j, B j) := by
    rw [Finset.prod_comm]
    have h1 : ∀ j : Fin n, (∏ σ : Equiv.Perm (Fin n), (b (σ j)) ^ B j)
        = Q ^ B j := by
      intro j
      rw [Finset.prod_pow, hQi j]
    rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_mul_distrib, hA, Finset.prod_inv_distrib, hB, hAB, mul_inv_cancel]

#print axioms sprProd_perm_char

end SprProdPermChar

/-! ## §160 ★★★★★ **`lem:14.25` 的矩阵层收口** —— 源文 `:449`（陈述）、`:451–453`（证明）

**陈述（机检）**：`α ∈ M_n(K')` 被 `N = T ⋊ S_n` 固定 ⟹ 存在 `0 ≠ s ∈ S'`（`N`-不变）与
`β ∈ M_n(S')`，使 **`sα = β`**（即 `α = β/s`）。

**证明三步，全部零件已机检**：

| 步 | 内容 | 用到的件 |
|---|---|---|
| 1 | `J ∩ S'` 里的 **`T`-半不变元** `g`（`φ_b g = C (u b)·g`） | §158 `sprExists_semiInv` |
| 2 | 取 `s := ∏_{σ∈S_n} φ_σ(g)`，`s ≠ 0` | 域中非零因子之积 |
| 2a | `s` 是 **`S_n`-不变** | §82 `sprPerm_prod_fixed` |
| 2b | `s` 是 **`T`-不变** | §159 `sprProd_perm_char` ＋ 本节 `sprDiag_prod_sprPerm_fixed_of_semiInv` |
| 2c | `s ∈ J`（故 `sα ∈ M_n(S')`） | §155 ＋ 本节 `sprHasDenom_mul_algebraMap` ＋ `Finset` 归纳 |
| 3 | 由 `s ∈ J` 取出 `β` | `sprHasDenom` 的定义 |

**★ 路线史（四改，全部登记在 [[proj-lem1425-plan-2026-10-19]]）**：
① 源文一句 "`M_n(K')` has a basis over `K'` that is `N` invariant" **不是证明**
（要 `dim_F R(F,n,2) = n²`）⟹ 弃；② 分母理想 `J` 路线（§154–§156）；
③ Van der Monde 投影 ⟹ 被 ④ 取代；④ **最小支撑元自动半不变**（§158）⟹ 只余
`S_n` 对称化（§159 ＋ 本节）。

**工艺（3 条）**：
* **R197**：`Finset.prod_mul_distrib` 的**可用方向**是 `(∏f)*(∏g) = ∏(f*g)`；
  写 `←` 会报"找不到落点"（与 R196 同型，但**方向相反**——两条都要记）。
* **R198**：`sprHasDenom_perm`／`sprHasDenom_diag` 的结论里是 **`φ_σ (algebraMap g)`**，
  而调用点要的是 **`algebraMap (φ_σ g)`**；差 `sprPermFieldEquiv_algebraMap`
  （§155）／`sprDiagFieldEquiv_algebraMap`（§154 时已遇上，R194）。
  **凡用这两个稳定性引理，先 `rw [← …_algebraMap]`。**
* **R199**：`F`-纯量与 `S'`-纯量在 `M_n(K')` 上是**两个不同的 `•`**；
  桥接用 `smul_assoc` ＋ `Algebra.smul_def` ＋ `mul_one` 显式两段
  （`IsScalarTower.algebraMap_smul` 在本 pin 的隐式参数容易把中间环推成 `Spr` 自身）。

**射程（勿夸大）**：`lem:14.25` 的矩阵层**已成定理**；但**`β` 的 `N`-不变性尚未单列**
（它是 `ψ_b(β) = φ_b(s)α = β` 的一行推论，下一轮补）；
`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprAssembly

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `J ∩ S'` 对乘法封闭（两个都是 `algebraMap`-像时）。 -/
theorem sprHasDenom_mul_algebraMap {α : Matrix (Fin n) (Fin n) (SprField F r n)}
    {c c' : Spr F r n}
    (hc : sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) c))
    (hc' : sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) c')) :
    sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) (c * c')) := by
  rw [map_mul]
  exact sprHasDenom_algebraMap_mul (F := F) (r := r) (n := n) c hc'

#print axioms sprHasDenom_mul_algebraMap

/-- ★★★★ **半不变元的 `S_n`-对称化积是 `T`-不变的** —— `lem:14.25` 矩阵层组装（2/2）。

`g` 只被要求是 **`T`-半不变元**（`φ_b g = C (u b) · g`），不是 `T`-不变元。
**证明形状与 §84 的 `sprDiagHom_prod_sprPerm_fixed` 逐字同型**，只把那里用
`T`-固定性（`rw [hs]`）的那一步换成**特征标步**：

```
φ_b(φ_σ g) = φ_σ(φ_{b∘σ} g) = φ_σ(C (u (b∘σ)) · g) = C (u (b∘σ)) · φ_σ g
```

于是 `φ_b(∏_σ φ_σ g) = C (∏_σ u (b∘σ)) · ∏_σ φ_σ g`，而
**`∏_σ u (b∘σ) = 1`** 由 §159 的 `sprProd_perm_char`（指数形态取自 `sprDiag_char_exp'`，
`ΣA = ΣB` 取自 `sprA_sum_eq_sprB_sum`）。 -/
theorem sprDiag_prod_sprPerm_fixed_of_semiInv [Nonempty (Fin n)] {g : Spr F r n}
    (hgne : g ≠ 0) {u : (Fin n → Fˣ) → Fˣ}
    (hu : ∀ b, sprDiagHom F r n b g = MvPolynomial.C ((u b : Fˣ) : F) * g) :
    ∀ b : Fin n → Fˣ,
      sprDiagHom F r n b (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g)
        = ∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g := by
  classical
  obtain ⟨s₀, hs₀⟩ := MvPolynomial.support_nonempty.mpr hgne
  have hs₀c : g.coeff s₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hs₀
  have hchar : ∀ b : Fin n → Fˣ, u b
      = (∏ i, (b i) ^ sprA r n s₀ i) * (∏ j, (b j) ^ sprB r n s₀ j)⁻¹ :=
    fun b => sprDiag_char_exp' F r n b (hu b) hs₀c
  intro b
  have hstep : ∀ σ : Equiv.Perm (Fin n),
      sprDiagHom F r n b (sprPermAlgEquiv F r n σ g)
        = MvPolynomial.C ((u (fun i => b (σ i)) : Fˣ) : F)
          * sprPermAlgEquiv F r n σ g := by
    intro σ
    have h : sprPermAlgEquiv F r n σ (sprDiagHom F r n (fun j => b (σ j)) g)
        = sprDiagHom F r n (fun i => (fun j => b (σ j)) (σ⁻¹ i))
            (sprPermAlgEquiv F r n σ g) := by
      simpa using DFunLike.congr_fun
        (sprPerm_sprDiagHom_comp F r n σ (fun j => b (σ j))) g
    have hb : (fun i => (fun j => b (σ j)) (σ⁻¹ i)) = b := by
      funext i
      exact congrArg b (Equiv.apply_symm_apply σ i)
    rw [hb] at h
    rw [← h, hu (fun j => b (σ j)), map_mul, sprPermAlgEquiv_C]
  have hone : (∏ σ : Equiv.Perm (Fin n), u (fun i => b (σ i))) = 1 := by
    refine Eq.trans (Finset.prod_congr rfl (fun σ _ => hchar (fun i => b (σ i)))) ?_
    exact sprProd_perm_char (F := F) (n := n) b (sprA r n s₀) (sprB r n s₀)
      (sprA_sum_eq_sprB_sum r n s₀)
  rw [map_prod, Finset.prod_congr rfl (fun σ _ => hstep σ), Finset.prod_mul_distrib,
    ← map_prod, ← Units.coe_prod, hone, Units.val_one, map_one, one_mul]

#print axioms sprDiag_prod_sprPerm_fixed_of_semiInv

/-- ★★★★★ **`lem:14.25` 的矩阵层**（源文 `:449`／证明 `:451–453`）。

`α ∈ M_n(K')` 被 `N = T ⋊ S_n` 固定 ⟹ 存在 `0 ≠ s ∈ S'`（`N`-不变）与
`β ∈ M_n(S')`，使 `sα = β`（即 `α = β/s`）。

**证明（三步，全部零件已机检）**：
1. §158 给 `J ∩ S'` 中的 `T`-半不变元 `g`（`φ_b g = C (u b)·g`）；
2. 取 `s := ∏_{σ∈S_n} φ_σ(g)`：
   * `s ≠ 0`（域中非零因子之积）；
   * `S_n`-不变：§82 `sprPerm_prod_fixed`；
   * `T`-不变：§159 ＋ 本轮的 `sprDiag_prod_sprPerm_fixed_of_semiInv`；
   * `s ∈ J`：每个 `φ_σ(g) ∈ J`（§155），乘积用本轮的 `sprHasDenom_mul_algebraMap` 归纳；
3. 由 `s ∈ J` 的定义取出 `β`。 -/
theorem lem1425_matrix [Nonempty (Fin n)]
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) (hα : sprMatNFixed F r n α) :
    ∃ (s : Spr F r n) (β : Matrix (Fin n) (Fin n) (Spr F r n)),
      s ≠ 0 ∧ sprNFixed F r n s ∧
        s • α = β.map (algebraMap (Spr F r n) (SprField F r n)) := by
  classical
  obtain ⟨g, u, hgne, hgJ, hu⟩ := sprExists_semiInv F r n α hα
  have hσJ : ∀ σ : Equiv.Perm (Fin n),
      sprHasDenom F r n α
        (algebraMap (Spr F r n) (SprField F r n) (sprPermAlgEquiv F r n σ g)) :=
    fun σ => by
      rw [← sprPermFieldEquiv_algebraMap F r n σ g]
      exact sprHasDenom_perm F r n hα hgJ σ
  have hJmul : ∀ t : Finset (Equiv.Perm (Fin n)), ∀ c : Spr F r n,
      sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n) c) →
      sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n)
        (c * t.prod (fun σ => sprPermAlgEquiv F r n σ g))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro c hc; simpa using hc
    | insert σ t hσ ih =>
      intro c hc
      rw [Finset.prod_insert hσ, ← mul_assoc]
      exact ih (c * sprPermAlgEquiv F r n σ g)
        (sprHasDenom_mul_algebraMap F r n hc (hσJ σ))
  obtain ⟨σ₀⟩ := (inferInstance : Nonempty (Equiv.Perm (Fin n)))
  have hsJ : sprHasDenom F r n α (algebraMap (Spr F r n) (SprField F r n)
      (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g)) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun σ : Equiv.Perm (Fin n) => sprPermAlgEquiv F r n σ g) (Finset.mem_univ σ₀)]
    exact hJmul (Finset.univ.erase σ₀) (sprPermAlgEquiv F r n σ₀ g) (hσJ σ₀)
  obtain ⟨β, hβ⟩ := hsJ
  refine ⟨∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g, β, ?_, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro σ _
    exact (sprPermAlgEquiv F r n σ).injective.ne hgne
  · exact ⟨sprDiag_prod_sprPerm_fixed_of_semiInv F r n hgne hu,
      fun τ => sprPerm_prod_fixed F r n τ g⟩
  · have h1 : ((∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g) • (1 : SprField F r n)) • α
        = (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g) • α := by
      rw [smul_assoc, one_smul]
    have h2 : (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g) • (1 : SprField F r n)
        = algebraMap (Spr F r n) (SprField F r n)
            (∏ σ : Equiv.Perm (Fin n), sprPermAlgEquiv F r n σ g) := by
      rw [Algebra.smul_def, mul_one]
    rw [← h1, h2]
    exact hβ

#print axioms lem1425_matrix

end SprAssembly

/-! ## §161 ★★★★★ **`lem:14.25` 的完整形态（含 `β` 的 `N`-不变性）** —— 源文 `:449`

§160 给了 `∃ s β, sα = β` 与 `s` 的 `N`-不变性。本节补**最后一行**：
`β` 本身也被 `N` 固定。理由（一行）：

```
ψ_b(β) = ψ_b(s·α) = φ_b(s)·ψ_b(α) = s·α = β
```

这正是 `lem:14.24` 的**假设形态**（`α ∈ M_n(S')` 且 `N` 不变）——故 §137 的
`lem1424_general` 现在可以**直接消费**本节的输出。

| 件 | 内容 |
|---|---|
| `sprAlgebraMap_smul_eq` | `F`-纯量与 `S'`-纯量在 `M_n(K')` 上的桥（**R199 单列成引理**，供后续复用） |
| ★★★★★ `lem1425_matrix_fixed` | `∃ 0 ≠ s（N-不变）, β ∈ M_n(S')`，`β` 的像 **`N`-不变**，且 `sα = β` |

**⟹ `lem:14.25` 全部完成**（源文 `:449` 陈述、`:451–453` 证明）。
下一战场：`prop:14.19` 的装配（`S'' = S' ⊗_Z K'` ＋ `θ_i = η_i ⊗ ι`）。

**射程（勿夸大）**：`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` —— **未建/未证**。
**H2 仍不是定理。** -/


section SprLem1425Final

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `F`-纯量与 `S'`-纯量在 `M_n(K')` 上的桥（R199 单列）。 -/
theorem sprAlgebraMap_smul_eq {s : Spr F r n}
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) :
    algebraMap (Spr F r n) (SprField F r n) s • α = s • α := by
  have h1 : (s • (1 : SprField F r n)) • α = s • α := by
    rw [smul_assoc, one_smul]
  have h2 : s • (1 : SprField F r n) = algebraMap (Spr F r n) (SprField F r n) s := by
    rw [Algebra.smul_def, mul_one]
  rw [← h1, h2]

#print axioms sprAlgebraMap_smul_eq

/-- ★★★★★ **`lem:14.25` 的完整形态**（含 `β` 的 `N`-不变性）。

在 `lem1425_matrix` 之上补一行：`β = sα` 且 `s` 是 `N`-不变纯量、`α` 是 `N`-不变矩阵，
故 `ψ_b β = φ_b(s)·ψ_b(α) = sα = β`。这正是 `lem:14.24` 的假设形态
（`α ∈ M_n(S')` 且 `N` 不变）。 -/
theorem lem1425_matrix_fixed [Nonempty (Fin n)]
    (α : Matrix (Fin n) (Fin n) (SprField F r n)) (hα : sprMatNFixed F r n α) :
    ∃ (s : Spr F r n) (β : Matrix (Fin n) (Fin n) (Spr F r n)),
      s ≠ 0 ∧ sprNFixed F r n s ∧
        sprMatNFixed F r n (β.map (algebraMap (Spr F r n) (SprField F r n))) ∧
          s • α = β.map (algebraMap (Spr F r n) (SprField F r n)) := by
  obtain ⟨s, β, hsne, hsn, hβ⟩ := lem1425_matrix F r n α hα
  have hβ' : algebraMap (Spr F r n) (SprField F r n) s • α
      = β.map (algebraMap (Spr F r n) (SprField F r n)) := by
    rw [sprAlgebraMap_smul_eq]
    exact hβ
  refine ⟨s, β, hsne, hsn, ⟨fun b => ?_, fun σ => ?_⟩, hβ⟩
  · have h1 : sprPsiDK F r n b (β.map (algebraMap (Spr F r n) (SprField F r n)))
        = sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) s) • α := by
      rw [← hβ', sprPsiDK_smul, hα.1 b]
    have h2 : sprDiagFieldEquiv F r n b (algebraMap (Spr F r n) (SprField F r n) s) • α
        = β.map (algebraMap (Spr F r n) (SprField F r n)) := by
      rw [sprDiagFieldEquiv_algebraMap, hsn.1 b, sprAlgebraMap_smul_eq]
      exact hβ
    rw [h1, h2]
  · -- `S_n` 半边：同法
    have h1 : sprPsiSK F r n σ (β.map (algebraMap (Spr F r n) (SprField F r n)))
        = sprPermFieldEquiv F r n σ (algebraMap (Spr F r n) (SprField F r n) s) • α := by
      rw [← hβ', sprPsiSK_smul, hα.2 σ]
    have h2 : sprPermFieldEquiv F r n σ (algebraMap (Spr F r n) (SprField F r n) s) • α
        = β.map (algebraMap (Spr F r n) (SprField F r n)) := by
      rw [sprPermFieldEquiv_algebraMap, hsn.2 σ, sprAlgebraMap_smul_eq]
      exact hβ
    rw [h1, h2]

#print axioms lem1425_matrix_fixed

end SprLem1425Final

/-! ## §162 **`K'^T`／`K'^{S_n}`／`K'^N` 是子域** —— `prop:14.19` 装配的准备（1）

`Z = K'^N` 的论证要把 `K'^N` 当**域**用（`K'^N ⊆ Z` 与 `Z ⊆ K'^N` 两个方向都是域同态）。
本节把三个不动点集对 `+`／`*`／`⁻¹` 的封闭性机检（每条形如一行 `map_add`／`map_mul`／`map_inv₀`）。

| 件 | 内容 |
|---|---|
| `sprFieldTFixed_{add,mul,inv}` | `K'^T` 是子域 |
| `sprFieldSFixed_{add,mul,inv}` | `K'^{S_n}` 是子域 |
| ★ `sprFieldNFixed_{add,mul,inv}` | **`K'^N` 是子域** |

**⟹ 下一战场（`prop:14.19` 的左半装配）的**★ 架构问题**已在本轮定位**（见
[[proj-lem1425-plan-2026-10-19]] §7 的补注）：

源文 `:456` 写 `S'' = S' ⊗_Z K'`（`Z = Z(F,n,r)`）。这要求 `S'` 是 **`Z`-代数**，
即 **`Z ⊆ S'`**。但本仓的 `ZCanon = IntermediateField.adjoin F (range D.centK)` 住在
**`SField = Frac(S)`** 里，而 `S' = Spr` 的分式域是**另一个** `SprField = Frac(Spr)`
（两者只经 `V1` 的 `sprToS` 相联系，不是包含）。**故 `S'' = S' ⊗_Z K'` 不能照抄**。

**另据源文 `:442`**（`lem:14.24` 的证明内部）与 `thm:14.15` 的同款步骤，那里用的张量是
**`S^+ = S'' ⊗_F S'`**（**over `F`**，不是 over `Z`）—— 与本仓的 `F`-代数设置相容得多。
**下一轮的任务**：决定 `lem1424_general`（§137，已对 `T` 全一般）里的 `T` 与两条
`F`-代数同态 `θ_1, θ_2` 的具体取法，使"`θ_1 α = θ_2 α` ⟹ `α ∈ UD`"成立。

**射程（勿夸大）**：本节只给封闭性。`prop:14.19` 装配、`V2'`／`V3'`、`ZEqNFixed` ——
**未建/未证**。**H2 仍不是定理。** -/


section SprFixedField

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `K'^T` 是子域：对加法封闭。 -/
theorem sprFieldTFixed_add {x y : SprField F r n}
    (hx : sprFieldTFixed F r n x) (hy : sprFieldTFixed F r n y) :
    sprFieldTFixed F r n (x + y) := by
  intro b
  rw [map_add, hx b, hy b]

#print axioms sprFieldTFixed_add

/-- `K'^T` 对乘法封闭。 -/
theorem sprFieldTFixed_mul {x y : SprField F r n}
    (hx : sprFieldTFixed F r n x) (hy : sprFieldTFixed F r n y) :
    sprFieldTFixed F r n (x * y) := by
  intro b
  rw [map_mul, hx b, hy b]

#print axioms sprFieldTFixed_mul

/-- `K'^T` 对求逆封闭。 -/
theorem sprFieldTFixed_inv {x : SprField F r n} (hx : sprFieldTFixed F r n x) :
    sprFieldTFixed F r n x⁻¹ := by
  intro b
  rw [map_inv₀, hx b]

#print axioms sprFieldTFixed_inv

/-- `K'^{S_n}` 对加法封闭。 -/
theorem sprFieldSFixed_add {x y : SprField F r n}
    (hx : sprFieldSFixed F r n x) (hy : sprFieldSFixed F r n y) :
    sprFieldSFixed F r n (x + y) := by
  intro σ
  rw [map_add, hx σ, hy σ]

#print axioms sprFieldSFixed_add

/-- `K'^{S_n}` 对乘法封闭。 -/
theorem sprFieldSFixed_mul {x y : SprField F r n}
    (hx : sprFieldSFixed F r n x) (hy : sprFieldSFixed F r n y) :
    sprFieldSFixed F r n (x * y) := by
  intro σ
  rw [map_mul, hx σ, hy σ]

#print axioms sprFieldSFixed_mul

/-- `K'^{S_n}` 对求逆封闭。 -/
theorem sprFieldSFixed_inv {x : SprField F r n} (hx : sprFieldSFixed F r n x) :
    sprFieldSFixed F r n x⁻¹ := by
  intro σ
  rw [map_inv₀, hx σ]

#print axioms sprFieldSFixed_inv

/-- ★★★ **`K'^N` 是子域**：对加法封闭。 -/
theorem sprFieldNFixed_add {x y : SprField F r n}
    (hx : sprFieldNFixed F r n x) (hy : sprFieldNFixed F r n y) :
    sprFieldNFixed F r n (x + y) :=
  ⟨sprFieldTFixed_add F r n hx.1 hy.1, sprFieldSFixed_add F r n hx.2 hy.2⟩

#print axioms sprFieldNFixed_add

/-- ★★★ **`K'^N` 对乘法封闭**。 -/
theorem sprFieldNFixed_mul {x y : SprField F r n}
    (hx : sprFieldNFixed F r n x) (hy : sprFieldNFixed F r n y) :
    sprFieldNFixed F r n (x * y) :=
  ⟨sprFieldTFixed_mul F r n hx.1 hy.1, sprFieldSFixed_mul F r n hx.2 hy.2⟩

#print axioms sprFieldNFixed_mul

/-- ★★★ **`K'^N` 对求逆封闭**（故 `K'^N` 是一个子域——`Z = K'^N` 的证明要用）。 -/
theorem sprFieldNFixed_inv {x : SprField F r n} (hx : sprFieldNFixed F r n x) :
    sprFieldNFixed F r n x⁻¹ :=
  ⟨sprFieldTFixed_inv F r n hx.1, sprFieldSFixed_inv F r n hx.2⟩

#print axioms sprFieldNFixed_inv

end SprFixedField

/-! ## §163 ★★★★ **`S' ⊂ S` 的分式域版本：`K' ↪ SField`** —— 终局接口 `V2'` 的 (a)

源文 `:420` 的 `S' ⊂ S` 在第 302 轮已机检为 `sprToS : Spr →ₐ S`（`V1`，§128，
截面性 `evSpr_comp_sprToS`）。**但终局比较 `Z ⊆ K'` 是分式域层的事**——`ZCanon` 住在
`SField = Frac(S)` 里，`K' = Frac(S')`--- 故须把 `sprToS` **沿分式域延拓**：

| 件 | 内容 |
|---|---|
| `sprToS_injective` | `sprToS` 单射（`evSpr_comp_sprToS` 的即时推论） |
| ★★★★ `sprToSField` | **`K' = Frac(S') →ₐ[F] SField = Frac(S)`**（`IsFractionRing.liftAlgHom`） |
| `sprToSField_algebraMap` | 在 `S'` 的像上就是 `sprToS` |
| `sprToSField_injective` | **`K'` 真的落在 `SField` 里** |
| `algHom_injective_of_field` | 工具：域到域（非平凡）的 `F`-代数同态自动单射 |

**⟹ 意义**：`Z ⊆ K'`（终局输入 `ZInSpr`）现在有**精确的可陈述形态**：
`∀ c, D.centK c ∈ Set.range (sprToSField k₀ hk₀)`。「把 `ZCanon` 的生成元搬进 `K'`」
这句话从散文变成一条可核断言。

**工艺（2 条）**：
* **R200**：`IsFractionRing.liftAlgHom` 的 `lift_algebraMap` 里 `hg : Injective g`
  是**必须显式给**的（`exact IsFractionRing.lift_algebraMap (fun a b h => …) x`）；
  直接写 `rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]`
  会报 "don't know how to synthesize placeholder for argument `hg`"。
* **R201**：`lift` 的**单射性没有现成引理**（`lift_injective_of_injective` **不在本 pin**）。
  **正解**：域到域的同态自动单射（`ker` 是理想 ⟹ `⊥`），写成
  `algHom_injective_of_field`（5 行）一次复用。

**射程（勿夸大）**：本节只建**嵌入**。`Z ⊆ K'` 的**断言本身未证**（它需要
`ψ : R ↪ M_n(S')` 的分式域延拓 ＋ 交换图，即 `V2'` 的 (b)）；`V3'`、`prop:14.19` 装配、
`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprToSField

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `sprToS` 是单射（它是 `evSpr` 的截面，§128 的 `evSpr_comp_sprToS` 的即时推论）。 -/
theorem sprToS_injective (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (sprToS (F := F) (n := n) k₀) := by
  intro x y h
  have h1 : evSpr F r n k₀ hk₀ (sprToS (F := F) (n := n) k₀ x) = x := by
    have := DFunLike.congr_fun (evSpr_comp_sprToS (F := F) (r := r) (n := n) k₀ hk₀) x
    simpa using this
  have h2 : evSpr F r n k₀ hk₀ (sprToS (F := F) (n := n) k₀ y) = y := by
    have := DFunLike.congr_fun (evSpr_comp_sprToS (F := F) (r := r) (n := n) k₀ hk₀) y
    simpa using this
  rw [← h1, ← h2, h]

#print axioms sprToS_injective

/-- ★★★★ **`S' ⊂ S` 的分式域版本**：`K' = Frac(S') → SField = Frac(S)`（源文 `:415`／
`:420` 的 `S' ⊂ S` 在分式域层的形态）。这就是终局接口 `V2'` 的 **(a) 分式域延拓**一环。 -/
noncomputable def sprToSField (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    SprField F r n →ₐ[F] SField F r n :=
  IsFractionRing.liftAlgHom (K := SprField F r n)
    (g := (IsScalarTower.toAlgHom F (S F r n) (SField F r n)).comp
      (sprToS (F := F) (n := n) k₀))
    (fun x y h => sprToS_injective F r n k₀ hk₀
      (IsFractionRing.injective (S F r n) (SField F r n) h))

#print axioms sprToSField

/-- 域到域（非平凡）的 `F`-代数同态是单射（`ker` 是理想，不能是全环）。 -/
theorem algHom_injective_of_field {K L : Type} [Field K] [Field L]
    [Algebra F K] [Algebra F L] (f : K →ₐ[F] L) : Function.Injective f := by
  intro x y h
  have h1 : f (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hxy : x - y = 0 := by
    by_contra hne
    have h3 : f (x - y) * f ((x - y)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    rw [h1, zero_mul] at h3
    exact zero_ne_one h3
  exact sub_eq_zero.mp hxy

#print axioms algHom_injective_of_field

/-- `sprToSField` 在 `S'` 的像上就是 `sprToS`。 -/
theorem sprToSField_algebraMap (k₀ : Fin r) (hk₀ : k₀.val = 0) (x : Spr F r n) :
    sprToSField F r n k₀ hk₀ (algebraMap (Spr F r n) (SprField F r n) x)
      = algebraMap (S F r n) (SField F r n) (sprToS (F := F) (n := n) k₀ x) :=
  IsFractionRing.lift_algebraMap
    (fun a b h => sprToS_injective F r n k₀ hk₀
      (IsFractionRing.injective (S F r n) (SField F r n) h)) x

#print axioms sprToSField_algebraMap

/-- `sprToSField` 是**单射**（`K'` 真的落在 `SField` 里）——域到域的同态自动单射。 -/
theorem sprToSField_injective (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Function.Injective (sprToSField F r n k₀ hk₀) :=
  algHom_injective_of_field F (sprToSField F r n k₀ hk₀)

#print axioms sprToSField_injective

end SprToSField

/-! ## §164 ★★★★ **`M_n(K)` 的中心是纯量矩阵** —— 终局 `Z ↪ K'` 的那一步

`V2'` 的 (b) 要证"中心元在表示里是纯量"。其代数内核是一个与 `n` 无关的矩阵事实：

> 若 `z : M_n(K)` 与**所有**矩阵交换，则 `z` 是纯量矩阵。

本节机检之（`matrix_center_eq_scalar`）。**证明**用矩阵单位
`E_{ab} := Matrix.of (fun p q => if p = a ∧ q = b then 1 else 0)`：

* `i ≠ j`：`(z E_{ji})_{ii} = z_{ij}` 而 `(E_{ji} z)_{ii} = 0` ⟹ `z_{ij} = 0`（`z` 对角）；
* 任意 `i, i₀`：`(z E_{i₀i})_{i₀ i} = z_{i₀i₀}` 而 `(E_{i₀i} z)_{i₀ i} = z_{ii}`
  ⟹ 对角元全等。

⟹ `z = Matrix.scalar m (z i₀ i₀)`。**用途**：若 `Ψ : UD →ₐ[F] M_n(K')` 的像包含所有
矩阵单位（或像生成 `M_n(K')`），则 `Ψ(Z)` 是纯量矩阵，从而落在 `K'` 里 —— 这是
`Z ⊆ K'` 的代数内核。

**工艺（2 条）**：
* **R202**：本 pin **没有** `Matrix.stdBasisMatrix`，**也没有** `Matrix.single`
  （两者在检索中均 `unknownIdentifier`）。**正解**：用 `Matrix.of` 显式写
  `fun p q => if p = a ∧ q = b then 1 else 0`（配 `Matrix.of_apply`）。
* **R203**：本 pin 的 `Matrix` **不是 `DFunLike`** —— `DFunLike.congr_fun`／`congrFun`
  取矩阵条目会报 "failed to synthesize `DFunLike (Matrix m m K) m ?`"。
  **正解**：`congrArg (fun (M : Matrix m m K) => M i j)`。
* **R204**：`Finset.sum_eq_single` 的排除分支里，`if` 条件的**分量方向**要对上
  （`if c = j ∧ …` 的 `if_neg` 吃 `c = j`，别写 `.symm`）——写反会报
  "`Eq.symm hh.left` has type `j = c` but expected `c = j`"。

**射程（勿夸大）**：本节只给矩阵中心的代数事实。`Z ⊆ K'` 的**断言未证**（尚缺
`ψ` 的分式域延拓与其像生成 `M_n(K')`）；`V3'`、`prop:14.19` 装配、`ZEqNFixed` ——
**未建/未证**。**H2 仍不是定理。** -/


section MatrixCenter

/-- ★★★★ **`M_n(K)` 的中心是纯量矩阵**（`Z ↪ K'` 的那一步：中心元的矩阵像必是纯量）。

**证明**（矩阵单位 `E_{ji} = stdBasisMatrix j i 1`）：
* `i ≠ j` 时 `(z E_{ji})_{ii} = z_{ij}` 而 `(E_{ji} z)_{ii} = 0` ⟹ `z_{ij} = 0`（`z` 对角）；
* 任意 `i, i₀`：`(z E_{i₀ i})_{i₀ i} = z_{i₀ i₀}` 而 `(E_{i₀ i} z)_{i₀ i} = z_{ii}`
  ⟹ 对角元全等。
故 `z = scalar (z i₀ i₀)`。 -/
theorem matrix_center_eq_scalar {K : Type} [Field K] {m : Type} [Fintype m] [DecidableEq m]
    [Nonempty m] {z : Matrix m m K} (hz : ∀ M : Matrix m m K, z * M = M * z) :
    ∃ x : K, z = Matrix.scalar m x := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty m)
  refine ⟨z i₀ i₀, ?_⟩
  have hoff : ∀ i j : m, i ≠ j → z i j = 0 := by
    intro i j hij
    have hzE := hz (Matrix.of (fun p q : m => if p = j ∧ q = i then (1 : K) else 0))
    have hL : (z * Matrix.of (fun p q : m => if p = j ∧ q = i then (1 : K) else 0)) i i
        = z i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [Matrix.of_apply, if_pos ⟨rfl, rfl⟩, mul_one]
      · intro c _ hc
        rw [Matrix.of_apply, if_neg (fun hh => hc hh.1), mul_zero]
      · intro hc
        exact absurd (Finset.mem_univ j) hc
    have hR : (Matrix.of (fun p q : m => if p = j ∧ q = i then (1 : K) else 0) * z) i i
        = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero (fun c _ => by
        rw [Matrix.of_apply, if_neg (fun hh : i = j ∧ c = i => hij hh.1), zero_mul])
    have h := congrArg (fun (M : Matrix m m K) => M i i) hzE
    rw [hL, hR] at h
    exact h
  have hdiag : ∀ i : m, z i i = z i₀ i₀ := by
    intro i
    have hzE := hz (Matrix.of (fun p q : m => if p = i₀ ∧ q = i then (1 : K) else 0))
    have hL : (z * Matrix.of (fun p q : m => if p = i₀ ∧ q = i then (1 : K) else 0)) i₀ i
        = z i₀ i₀ := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
      · rw [Matrix.of_apply, if_pos ⟨rfl, rfl⟩, mul_one]
      · intro c _ hc
        rw [Matrix.of_apply, if_neg (fun hh => hc hh.1), mul_zero]
      · intro hc
        exact absurd (Finset.mem_univ i₀) hc
    have hR : (Matrix.of (fun p q : m => if p = i₀ ∧ q = i then (1 : K) else 0) * z) i₀ i
        = z i i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.of_apply, if_pos ⟨rfl, rfl⟩, one_mul]
      · intro c _ hc
        rw [Matrix.of_apply, if_neg (fun hh => hc hh.2), zero_mul]
      · intro hc
        exact absurd (Finset.mem_univ i) hc
    have h := congrArg (fun (M : Matrix m m K) => M i₀ i) hzE
    rw [hL, hR] at h
    exact h.symm
  refine Matrix.ext fun i j => ?_
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    exact hdiag i
  · rw [if_neg hij]
    exact hoff i j hij

#print axioms matrix_center_eq_scalar

end MatrixCenter

/-! ## §165 **`K'^N` 含 `F`** —— `K'^N` 作为 `F`-子域的最后一格

§162 给了 `K'^N` 对 `+`／`*`／`⁻¹` 封闭（故是子域）。要与 `ZCanon`（由
`IntermediateField.adjoin F (range D.centK)` 生成，**天然含 `F`**）比较，还须
`F ⊆ K'^N`：

| 件 | 内容 |
|---|---|
| `sprFieldTFixed_const` | `F` 的常数在 `K'^T` 里 |
| `sprFieldSFixed_const` | `F` 的常数在 `K'^{S_n}` 里 |
| ★ `sprFieldNFixed_const` | **`F` 的常数在 `K'^N` 里**（`K'^N` 是含 `F` 的子域） |
| `sprFieldNFixed_zero`／`_one` | `0, 1 ∈ K'^N` |

**工艺（2 条）**：
* **R205**：**名字撞车**——§138 已有 `sprFieldTFixed_algebraMap`（那是"**`Spr` 元**的
  `algebraMap` 像仍 `T`-固定"），与本节的"**`F` 的常数**"是**两条不同命题**。
  本节改名 `…_const`。**教训**：`…_algebraMap` 后缀在本库已被占用，新名用 `_const`。
* **R206**：`AlgHom.commutes` 作为 `rw` 规则**对 `sprPermAlgEquiv … (algebraMap F (Spr) a)`
  不落点**；须写成**具体项** `(sprPermAlgEquiv F r n σ).commutes a` ／
  `(sprDiagHom F r n b).commutes a`。

**射程（勿夸大）**：本节只补 `F ⊆ K'^N`。`Z ⊆ K'` 的**断言未证**；`V3'`、
`prop:14.19` 装配、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprFixedFieldF

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `K'^T` 含 `F` 的常数（`φ_b` 是 `F`-代数同态）。 -/
theorem sprFieldTFixed_const (a : F) :
    sprFieldTFixed F r n (algebraMap F (SprField F r n) a) := by
  intro b
  have h : algebraMap F (SprField F r n) a
      = algebraMap (Spr F r n) (SprField F r n) (algebraMap F (Spr F r n) a) :=
    IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a
  rw [h, sprDiagFieldEquiv_algebraMap, (sprDiagHom F r n b).commutes a,
    ← IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a]

#print axioms sprFieldTFixed_const

/-- `K'^{S_n}` 含 `F` 的常数。 -/
theorem sprFieldSFixed_const (a : F) :
    sprFieldSFixed F r n (algebraMap F (SprField F r n) a) := by
  intro σ
  have h : algebraMap F (SprField F r n) a
      = algebraMap (Spr F r n) (SprField F r n) (algebraMap F (Spr F r n) a) :=
    IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a
  rw [h, sprPermFieldEquiv_algebraMap, (sprPermAlgEquiv F r n σ).commutes a,
    ← IsScalarTower.algebraMap_apply F (Spr F r n) (SprField F r n) a]

#print axioms sprFieldSFixed_const

/-- ★★★ **`K'^N` 含 `F` 的常数**（`K'^N` 是含 `F` 的子域——与 `ZCanon` 比较时要用）。 -/
theorem sprFieldNFixed_const (a : F) :
    sprFieldNFixed F r n (algebraMap F (SprField F r n) a) :=
  ⟨sprFieldTFixed_const F r n a, sprFieldSFixed_const F r n a⟩

#print axioms sprFieldNFixed_const

/-- `0 ∈ K'^N`。 -/
theorem sprFieldNFixed_zero : sprFieldNFixed F r n (0 : SprField F r n) := by
  have h := sprFieldNFixed_const F r n (0 : F)
  simpa using h

#print axioms sprFieldNFixed_zero

/-- `1 ∈ K'^N`。 -/
theorem sprFieldNFixed_one : sprFieldNFixed F r n (1 : SprField F r n) := by
  have h := sprFieldNFixed_const F r n (1 : F)
  simpa using h

#print axioms sprFieldNFixed_one

end SprFixedFieldF

/-! ## §166 **`lem:14.7` 的 `S'`-世界形态（具名登记）** —— `V2'` 的基性输入

**本轮（第 343 轮）的检索结论（L46／L47 内容式检索）**：第 329 轮我判定 `V2'` 需要一条
"本仓没有的已发表输入"（"`Ξ` 是 `K'`-基"，当时写作 7b）。**该判定是错的**——

`GenericInv.lean:3798` 已有

```
XiBasisHyp (k₁ k₂ : Fin r) : Prop :=
  ∃ b : Basis (Fin n × Fin n) (SField F r n) (Matrix (Fin n) (Fin n) (SField F r n)),
    ∀ p, b p = (Xi F r n k₁ k₂ p.1 p.2).map (algebraMap (S F r n) (SField F r n))
```

其 docstring 逐字引源文 `:158–163`（"`Ξ = {X_1^iX_2^j | 0 ≤ i,j ≤ n−1}`；**Lemma 14.7.**
`Ξ` is a basis of `M_n(K)` over `K`"）。**`lem:14.7` 正是这条输入**，且**已在 `(A)` 层具名登记**。

⟹ **`(B)` 层不需要新的文献输入**，只需**同一条 `lem:14.7` 在 `S'`-世界的实例化**
（`lem:14.7` 对**通用矩阵**成立，与放进 `Frac(S)` 还是 `Frac(S')` 无关）。本节把这一实例化
具名登记，并按 `(A)` 层的成法补"基 ⟹ 张成"推论：

| 件 | 内容 |
|---|---|
| `sprXi` | `S'`-世界的 `Ξ` 元素 `xdiag^i · (ymat k)^j` |
| ★★★★★ `SprXiBasisHyp` | **`lem:14.7` 的 `S'`-世界形态**（具名，与 `XiBasisHyp` 同源） |
| `sprXiSpan_of_basis` | 基 ⟹ 张成（与 `xiSpanHyp_of_xiBasisHyp` 同型） |

**工艺（1 条）**：
* **R207**：**"库内没有"的判决必须先做内容式检索**（L46／L47）。本轮实测：`XiBasisHyp`
  一直在库（`GenericInv.lean:3798`），而我第 329 轮据"名字看起来对"的念头就判了它不存在，
  并在计划笔记 §6 把它列为需要新输入 ⟹ **一次假阻断**。教训与 L46 三次假阻断同根：
  **按内容搜（`Basis`／`Fin n × Fin n`／`lem:14.7` 的原文措辞），不按名字猜。**

**射程（勿夸大）**：本节只**登记实例化**并给张成推论。**`V2'` 仍未建**（尚缺 `ψ` 的分式域
延拓与"像生成 `M_n(K')`"的接线）；`prop:14.19` 装配、`V3'`、`ZEqNFixed` —— **未建/未证**。
**H2 仍不是定理。** -/


section SprXiBasis

open Module

variable (F : Type) [Field F] (r n : ℕ)

/-- `S'`-世界的 `Ξ` 元素：`xdiag^i · (ymat k)^j`。 -/
noncomputable def sprXi (k : {k : Fin r // k.val ≠ 0}) (i j : ℕ) :
    Matrix (Fin n) (Fin n) (Spr F r n) :=
  xdiag F r n ^ i * ymat F r n k ^ j

#print axioms sprXi

/-- ★★★★★ **`lem:14.7` 的 `S'`-世界形态（具名登记）**。

`(A)` 层已有 `XiBasisHyp`（`Frac(S)`-世界，源文 `:158–163` 逐字：
"`Ξ = {X_1^iX_2^j | 0 ≤ i,j ≤ n−1}`；**Lemma 14.7.** `Ξ` is a basis of `M_n(K)` over `K`"）。
`(B)` 层（`K' = Frac(Spr)`）需要的是**同一条已发表输入**在 `S'`-世界的形态——
`lem:14.7` 对**通用矩阵**成立，与把它放进哪个环无关。

**⟹ 本条不引入新的文献输入**：它与 `XiBasisHyp` 是 `lem:14.7` 的两次实例化
（`Frac(S)`-世界 vs `Frac(S')`-世界），差别只在"世界"。 -/
def SprXiBasisHyp (k : {k : Fin r // k.val ≠ 0}) : Prop :=
  ∃ b : Basis (Fin n × Fin n) (SprField F r n)
      (Matrix (Fin n) (Fin n) (SprField F r n)),
    ∀ p : Fin n × Fin n,
      b p = (sprXi F r n k p.1 p.2).map (algebraMap (Spr F r n) (SprField F r n))

#print axioms SprXiBasisHyp

/-- ★★★ **基性 ⟹ 张成性**（与 `xiSpanHyp_of_xiBasisHyp` 同型）。 -/
theorem sprXiSpan_of_basis (k : {k : Fin r // k.val ≠ 0})
    (h : SprXiBasisHyp F r n k) :
    Submodule.span (SprField F r n)
      (Set.range (fun p : Fin n × Fin n =>
        (sprXi F r n k p.1 p.2).map (algebraMap (Spr F r n) (SprField F r n))))
      = ⊤ := by
  obtain ⟨b, hb⟩ := h
  have hrange : Set.range (fun p : Fin n × Fin n =>
      (sprXi F r n k p.1 p.2).map (algebraMap (Spr F r n) (SprField F r n)))
      = Set.range b := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩; exact ⟨p, hb p⟩
    · rintro ⟨p, rfl⟩; exact ⟨p, (hb p).symm⟩
  rw [hrange]
  exact b.span_eq

#print axioms sprXiSpan_of_basis

end SprXiBasis

/-! ## §167 **`sprXi` 是 `ψ` 的像** —— `V2'`(b) 的接线格

§166 登记了基性输入 `SprXiBasisHyp`（`{xdiag^i·(ymat k)^j}` 是 `K'`-基）。
要把「`ψ` 的像的 `K'`-张成」接上「`M_n(K')`」，缺的正是：**基元素都是 `ψ` 的像**。

本节机检之：

```
sprXi k i j = xdiag^i · (ymat k)^j = ψ(g_{k₀}^i · g_k^j)
```

（`g_k := ⟨genericMatrix F r n k, _⟩`）。证明是 `map_mul`／`map_pow` ＋ 两条生成元等式
`psiSpr_genMat_self`（`ψ X_{k₀} = xdiag`）与 `psiSpr_genMat`（`ψ X_k = ymat k`，`k ≠ k₀`）。

**⟹ 与 §166 合起来的逻辑链**（下一轮完成）：
`⊤ = span{xdiag^i·ymat^j}`（`SprXiBasisHyp`）`⊆ span(range ψ) ⊆ ⊤`
⟹ **`ψ` 的像在 `K'`-上张成整个 `M_n(K')`** —— 这就是 `V2'`(b) 里
"像生成 `M_n(K')`"那一格。

**工艺（1 条）**：
* **R209**：把 `K`／`M` 放在 `{…}` 隐式位置写
  `(K : Type) [Field K] (M : Type) [AddCommMonoid M] [Module K M]` **仍会卡**
  "typeclass instance problem is stuck `Module ?m ?m`"；须把 `K`、`M` 都写成**显式参数**。
  （本轮该通用引理暂未入库，逻辑链下一轮直接内联。）

**射程（勿夸大）**：本节只给一格接线。**`V2'` 仍未建**；`prop:14.19` 装配、`V3'`、
`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprXiPsi

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★ **`sprXi` 是 `ψ` 的像**：`xdiag^i · (ymat k)^j = ψ(g_{k₀}^i · g_k^j)`。

这是把 §166 的基性输入接到 `ψ` 的像上的**唯一一格**：基元素都是 `ψ` 的像，
故 `ψ` 的像的 `K'`-张成就是整个 `M_n(K')`。 -/
theorem sprXi_eq_psiSpr (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (i j : ℕ) :
    sprXi F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩ i j
      = psiSpr F r n k₀ hk₀
          (⟨genericMatrix F r n k₀, genericMatrix_mem F r n k₀⟩ ^ i
            * ⟨genericMatrix F r n k, genericMatrix_mem F r n k⟩ ^ j) := by
  rw [sprXi, map_mul, map_pow, map_pow, psiSpr_genMat_self F r n k₀ hk₀,
    psiSpr_genMat F r n k₀ hk₀ hk]

#print axioms sprXi_eq_psiSpr

end SprXiPsi

/-! ## §168 ★★★★★ **`ψ` 的像在 `K'`-上张成 `M_n(K')`** —— `V2'`(b) 的最后一格

**链条（本节收口）**：

```
⊤ = span{xdiag^i · (ymat k)^j}   -- SprXiBasisHyp（lem:14.7 的 S'-世界形态，§166）
  ⊆ span(range ψ)                -- §167：基元素都是 ψ 的像
⟹ span(range ψ) = ⊤              -- top ≤ span 即得
```

**用途（`Z ⊆ K'` 的论证形状）**：设 `z` 是中心的、其矩阵像与 `ψ` 的像全部交换。
由本节的 `⊤ = span(range ψ)`，`z` 的像与 `M_n(K')` 的每个元素交换；再由 §164
`matrix_center_eq_scalar`，它是**纯量矩阵**，于是 `z` 落在 `K'` 里。

**工艺（1 条）**：
* **R210**：`Submodule.span_le.mpr` **只对 `≤` 目标**适用；目标若是**等式**
  `span s = ⊤`，`rw [← hbasis]` 之后仍是等式，写 `span_le` 会报
  "typeclass instance problem is stuck `Module ?m ?m`"（形似类型类问题，实为
  **目标形状不符**）。**正解**：先单列 `hle : span s ≤ span t` 用 `span_le`，
  再把 `hbasis` 重写进 `hle`，最后 `top_le_iff.mp`。

**射程（勿夸大）**：`V2'` 的**延拓本身**（`ψ` 到 `M_n(K')` 的 `K'`-代数同态）仍未建；
`prop:14.19` 装配、`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprPsiSpan

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`ψ` 的像在 `K'`-上张成整个 `M_n(K')`** —— `V2'`(b) 的最后一格。

**链条**：
```
⊤ = span{xdiag^i · (ymat k)^j}    -- SprXiBasisHyp (lem:14.7, S'-世界, §166)
  ⊆ span(range ψ)                 -- §167 sprXi_eq_psiSpr：基元素都是 ψ 的像
  ⊆ ⊤
```

**用途**：`Z ⊆ K'` 的论证里，中心元 `z` 的矩阵像与 `ψ` 的像**全部交换**，
故与 `M_n(K')` 全部交换（因像张成整个代数），故由 §164 `matrix_center_eq_scalar`
是纯量矩阵 —— 于是 `z` 落在 `K'` 里。 -/
theorem sprPsi_span_eq_top (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (h : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩) :
    Submodule.span (SprField F r n) (Set.range (fun x =>
      (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))) = ⊤ := by
  set k' : {k : Fin r // k.val ≠ 0} := ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩ with hk'
  have hb := sprXiSpan_of_basis F r n k' h
  have hle : Submodule.span (SprField F r n) (Set.range (fun p : Fin n × Fin n =>
        (sprXi F r n k' p.1 p.2).map (algebraMap (Spr F r n) (SprField F r n))))
      ≤ Submodule.span (SprField F r n) (Set.range (fun x =>
        (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact Submodule.subset_span
      ⟨_, congrArg (fun M => M.map (algebraMap (Spr F r n) (SprField F r n)))
        (sprXi_eq_psiSpr F r n k₀ hk₀ hk p.1 p.2).symm⟩
  rw [hb] at hle
  exact top_le_iff.mp hle

#print axioms sprPsi_span_eq_top

end SprPsiSpan

/-! ## §169 ★★★★★ **与 `ψ` 的像交换 ⟹ 纯量矩阵** —— `V2'`(b) 落地

**论证（两段）**：
1. 由 §168 的 `span(range ψ) = ⊤`，`z` 与 `range ψ` 交换 ⟹ `z` 与**整个 `M_n(K')`** 交换
   （沿 `Submodule.span_induction`）；
2. 由 §164 `matrix_center_eq_scalar`，`z` 是纯量矩阵。

**用途（`Z ⊆ K'` 的核心一步）**：中心元 `z` 的矩阵像是纯量 ⟹ `z` 落在 `K'`
（纯量矩阵的系数）里 —— 这正是终局输入 `ZInSpr` 的实体。

**工艺（1 条，含一条"错误信息误导"的实例）**：
* **R211**：本 pin 的 `Submodule.span_induction` 的谓词是**依赖型**
  `p : (x : M) → x ∈ span R s → Prop`，且参数序是 **(mem)(zero)(add)(smul)(hx)**
  —— 与教科书顺序 `(hx)(mem)(zero)(add)(smul)` **不同**。
  按教科书顺序写会报 **"`hM` expected `∀ x ∈ ?m, …`"**（形似谓词不符，实为**参数序**），
  而空着写 `?_` 会在 zero 分支报 **"unsolved goal `Type ?u.79`"**（形似类型缺失，
  实为**参数错位**）。**正解**：`refine Submodule.span_induction (p := fun m _ => …) ?_ ?_ ?_ ?_ hM`。

**射程（勿夸大）**：这是 `Z ⊆ K'` 的**代数内核**；把它接到 `D.centK`（`GenericDivisionData`
的字段）上还需要"`centK c` 就是那个纯量矩阵的系数"的交换图 —— **未建**。
`prop:14.19` 装配、`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprCenterScalar

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **与 `ψ` 的像交换 ⟹ 纯量矩阵** —— `V2'`(b) 的落地。

**论证**：由 §168 的 `span(range ψ) = ⊤`，`z` 与 `range ψ` 交换 ⟹ `z` 与**整个
`M_n(K')`** 交换（沿 `Submodule.span_induction`）；再由 §164 `matrix_center_eq_scalar`，
`z` 是纯量矩阵。

**用途**：中心元 `z` 的矩阵像是纯量 ⟹ `z` 落在 `K'`（纯量矩阵的系数）里 —— 这是
`Z ⊆ K'`（终局输入 `ZInSpr`）的核心一步。 -/
theorem matrix_eq_scalar_of_commute_psi [Nonempty (Fin n)] [DecidableEq (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩)
    {z : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hz : ∀ x, (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) * z
      = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))) :
    ∃ a : SprField F r n, z = Matrix.scalar (Fin n) a := by
  refine matrix_center_eq_scalar (fun M => ?_)
  have htop := sprPsi_span_eq_top F r n k₀ hk₀ hk hb
  have hM : M ∈ Submodule.span (SprField F r n) (Set.range (fun x =>
      (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun m _ => z * m = m * z) ?_ ?_ ?_ ?_ hM
  · rintro _ ⟨x, rfl⟩
    exact (hz x).symm
  · rw [Matrix.mul_zero, Matrix.zero_mul]
  · intro a b _ _ ha hb
    rw [Matrix.mul_add, Matrix.add_mul, ha, hb]
  · intro c a _ ha
    rw [Matrix.mul_smul, Matrix.smul_mul, ha]

#print axioms matrix_eq_scalar_of_commute_psi

end SprCenterScalar

/-! ## §170 **纯量矩阵的系数提取** —— `Z → K'` 映射的良定性准备

§169 给出"与 `ψ` 的像交换 ⟹ `∃ a, z = Matrix.scalar n a`"。要把它变成一条**映射**
（`centK c ↦ K'`，即终局输入 `ZInSpr` 的实体），须先固定系数的取法：

| 件 | 内容 |
|---|---|
| `sprScalarCoeff` | 纯量矩阵的**系数**（`Classical.choose`） |
| `sprScalarCoeff_spec` | `z = Matrix.scalar n (sprScalarCoeff …)` |

**工艺（1 条，含"错误信息误导"第二例）**：
* **R212**：`Matrix.scalar` 需要 **`[Semiring K]` ＋ `[DecidableEq m]`**（不是 `[Zero] [One]`）。
  但在证明"`Matrix.scalar` 单射"时，`simpa only [Matrix.scalar_apply, Matrix.diagonal_apply]`
  会**把目标化简成 `True`** 并报 "After simplification, term `hii` has type `True` but
  expected `a = b`" —— **形似证明失败，实为 `simp` 过度归约**。本轮因此**暂缓**该单射引理
  （下一轮改用显式 `rw` 链），先入库系数提取（它不依赖单射性）。

**射程（勿夸大）**：本节只给**取法**。系数的**唯一性**（`Matrix.scalar` 单射）未入库；
`Z ⊆ K'` 的映射、`prop:14.19` 装配、`V3'`、`ZEqNFixed` —— **未建/未证**。
**H2 仍不是定理。** -/


section SprScalarCoeff

set_option linter.style.haveILetI false


variable (F : Type) [Field F] (r n : ℕ)

/-- 纯量矩阵的**系数**（由 §169 的存在性 + `Matrix.scalar` 的单射性唯一确定）。

**用途**：`Z ⊆ K'`（`ZInSpr`）要定义一条映射 `centK c ↦ K'`，其**良定性**正是本定义。 -/
noncomputable def sprScalarCoeff [Nonempty (Fin n)]
    {z : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hz : ∃ a : SprField F r n, z = Matrix.scalar (Fin n) a) : SprField F r n :=
  Classical.choose hz

#print axioms sprScalarCoeff

/-- 系数确实实现 `z`。 -/
theorem sprScalarCoeff_spec [Nonempty (Fin n)]
    {z : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hz : ∃ a : SprField F r n, z = Matrix.scalar (Fin n) a) :
    z = Matrix.scalar (Fin n) (sprScalarCoeff F r n hz) :=
  Classical.choose_spec hz

#print axioms sprScalarCoeff_spec


end SprScalarCoeff

/-! ## §171 ★★★★★ **`Z → K'` 的映射实体** —— `V2'`(b) 的最后一件

§169 给"与 `ψ` 的像交换 ⟹ 纯量矩阵"，§170 给"系数取法"。本节把两者合成**一条映射**：
中心元 `z`（`z` 与 `ψ` 的像全部交换）↦ 它在 `K'` 里的**纯量系数**。

| 件 | 内容 |
|---|---|
| `sprScalarCoeff_unique` | 系数唯一（**用 Mathlib 的 `Matrix.scalar_inj`，无需自建单射引理**） |
| ★★★★★ `sprPsiCenterCoeff` | **`Z → K'` 的实体**（中心元 ↦ 纯量系数） |
| `sprPsiCenterCoeff_spec` | `z = Matrix.scalar n (sprPsiCenterCoeff …)` |

**★ 检索结论（L46／L47，本轮实测）**：第 347 轮准备自建 `Matrix.scalar` 的单射引理，
**其实 Mathlib 早有** `Matrix.scalar_inj [Nonempty n] {r s} : scalar n r = scalar n s ↔ r = s`
（`Mathlib/Data/Matrix/Basic.lean:200`）。⟹ 唯一性一行即得。
**这是本战役第二次"以为要自建、其实在库"**（前一次：第 343 轮的 `XiBasisHyp`）。

**工艺（2 条）**：
* **R213**：`sprScalarCoeff hz` 的 `hz` 是**依赖型**参数（其类型里含 `z`）；直接
  `rw [ha] at h1` 会报 **"motive is not type correct"**。**正解**：不要在含 `hz` 的项上重写，
  改成 `(…_spec hz).symm.trans ha : scalar coeff = scalar a`，再 `Matrix.scalar_inj.mp`。
* **R214**：`Matrix.scalar` 的 `DecidableEq (Fin n)` **实例不同会导致类型不匹配**
  （报 "`… with inst✝` vs `… with instDecidableEqFin n`"）。**正解**：在定义体里
  开头写 `classical`，让 `Matrix.scalar` 统一走 `Classical.decEq`。

**射程（勿夸大）**：本节给出**映射的实体**，但**尚未证它是 `F`-代数同态**
（加／乘／纯量的相容性），也**尚未把它接到 `D.centK`**。`prop:14.19` 装配、`V3'`、
`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprCenterCoeff

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- 系数唯一（`Matrix.scalar_inj` 直接给；**无需自建单射引理**）。 -/
theorem sprScalarCoeff_unique [Nonempty (Fin n)]
    {z : Matrix (Fin n) (Fin n) (SprField F r n)}
    {a : SprField F r n}
    (hz : ∃ b : SprField F r n, z = Matrix.scalar (Fin n) b)
    (ha : z = Matrix.scalar (Fin n) a) :
    sprScalarCoeff F r n hz = a := by
  have h1 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hz) = Matrix.scalar (Fin n) a :=
    (sprScalarCoeff_spec F r n hz).symm.trans ha
  exact Matrix.scalar_inj.mp h1

#print axioms sprScalarCoeff_unique

/-- ★★★★★ **`Z → K'` 的映射的实体**：把 `ψ` 的像的中心元送到它的纯量系数。

**输入**：`z` 与 `ψ` 的像全部交换（中心性）。
**输出**：`K'` 里的系数 —— 由 §169（存在性）＋ §170（取法）＋ `Matrix.scalar_inj`（唯一性）。 -/
noncomputable def sprPsiCenterCoeff [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩)
    (z : Matrix (Fin n) (Fin n) (SprField F r n))
    (hz : ∀ x, (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) * z
      = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))) :
    SprField F r n := by
  classical
  exact sprScalarCoeff F r n (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb hz)

#print axioms sprPsiCenterCoeff

/-- 该系数确实实现 `z`。 -/
theorem sprPsiCenterCoeff_spec [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩)
    (z : Matrix (Fin n) (Fin n) (SprField F r n))
    (hz : ∀ x, (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) * z
      = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))) :
    z = Matrix.scalar (Fin n) (sprPsiCenterCoeff F r n k₀ hk₀ hk hb z hz) := by
  classical
  exact sprScalarCoeff_spec F r n (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb hz)

#print axioms sprPsiCenterCoeff_spec

end SprCenterCoeff

/-! ## §172 **系数映射对 `+`／`*` 相容** —— `Z → K'` 成为环同态的两格

§171 定义了 `Z → K'` 的**映射实体**；要它成为 `F`-代数同态，须先对 `+`／`*` 相容。
本节机检这两格。

**关键（免费）**：`Matrix.scalar n` **本身就是 `RingHom`**（`diagonalRingHom.comp (Pi.constRingHom)`，
`Mathlib/Data/Matrix/Basic.lean:190`），故 `map_add`／`map_mul` 直接可用，**无需自建**。

| 件 | 内容 |
|---|---|
| ★★★ `sprScalarCoeff_add` | 系数对加法相容 |
| ★★★ `sprScalarCoeff_mul` | 系数对乘法相容 |

**工艺（1 条）**：
* **R215**：`Matrix.scalar_inj` 的 `n` 在"目标是 `SprField` 里的等式"时**推断不出来**
  （报 "typeclass instance problem is stuck `Nonempty ?m.47`"）。
  **正解**：显式给 `Matrix.scalar_inj (n := Fin n)`。

**射程（勿夸大）**：尚缺 `1`／`0`／`F`-纯量的相容格（本轮 `_one` 因
`sprScalarCoeff_spec` 的隐式参数不落点而**暂缓**）；且**尚未把它接到 `D.centK`**。
`prop:14.19` 装配、`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprScalarCoeffHom

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★ **系数对加法相容**（`Matrix.scalar` 是 `RingHom`，故 `map_add` 免费）。 -/
theorem sprScalarCoeff_add [Nonempty (Fin n)]
    {z w : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hz : ∃ a : SprField F r n, z = Matrix.scalar (Fin n) a)
    (hw : ∃ b : SprField F r n, w = Matrix.scalar (Fin n) b)
    (hzw : ∃ c : SprField F r n, z + w = Matrix.scalar (Fin n) c) :
    sprScalarCoeff F r n hzw = sprScalarCoeff F r n hz + sprScalarCoeff F r n hw := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  have e1 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hzw) = z + w :=
    (sprScalarCoeff_spec F r n hzw).symm
  have e2 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hz + sprScalarCoeff F r n hw)
      = Matrix.scalar (Fin n) (sprScalarCoeff F r n hz)
        + Matrix.scalar (Fin n) (sprScalarCoeff F r n hw) :=
    map_add (Matrix.scalar (Fin n)) _ _
  have e3 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hz) = z :=
    (sprScalarCoeff_spec F r n hz).symm
  have e4 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hw) = w :=
    (sprScalarCoeff_spec F r n hw).symm
  rw [e1, e2, e3, e4]

#print axioms sprScalarCoeff_add

/-- ★★★ **系数对乘法相容**。 -/
theorem sprScalarCoeff_mul [Nonempty (Fin n)]
    {z w : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hz : ∃ a : SprField F r n, z = Matrix.scalar (Fin n) a)
    (hw : ∃ b : SprField F r n, w = Matrix.scalar (Fin n) b)
    (hzw : ∃ c : SprField F r n, z * w = Matrix.scalar (Fin n) c) :
    sprScalarCoeff F r n hzw = sprScalarCoeff F r n hz * sprScalarCoeff F r n hw := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  have e1 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hzw) = z * w :=
    (sprScalarCoeff_spec F r n hzw).symm
  have e2 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hz * sprScalarCoeff F r n hw)
      = Matrix.scalar (Fin n) (sprScalarCoeff F r n hz)
        * Matrix.scalar (Fin n) (sprScalarCoeff F r n hw) :=
    map_mul (Matrix.scalar (Fin n)) _ _
  have e3 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hz) = z :=
    (sprScalarCoeff_spec F r n hz).symm
  have e4 : Matrix.scalar (Fin n) (sprScalarCoeff F r n hw) = w :=
    (sprScalarCoeff_spec F r n hw).symm
  rw [e1, e2, e3, e4]

#print axioms sprScalarCoeff_mul

end SprScalarCoeffHom

/-! ## §173 ★★★★★ **`ZInSpr` 具名登记** ＋ `Z ⊆ K'` 的域包含 —— 终局输入 (i)

**本轮的核心是一个判定，不是一个计算**：读清 `GenericDivisionData.centK_spec` 后确认，
`Z ⊆ K'` **不能**靠"两条嵌入一致"免费得到：

| 嵌入 | `X_{k₀}` 的像 |
|---|---|
| `M_n(S)` 那条（`centK_spec` 用的） | **完整**的 `X_{k₀}`（含非对角元） |
| `ψ` 再 `sprToSField`（`(B)` 层） | `xdiag`（**对角**） |

**两条在 `X_{k₀}` 的非对角元上真的不同** ⟹ `Z ⊆ K'` 需要 `prop:14.19` 的 `Z` 半，
故按 `(A)` 层 `XiBasisHyp` 的成法**具名登记**为 `ZInSpr`，
**不隐藏、也不把 `ZEqNFixed` 直接当假设**（这正是 v14 §6.2 的要求）。

| 件 | 内容 |
|---|---|
| ★★★★★ `ZInSpr` | **`∀ c, ∃ x ∈ K', D.centK c = sprToSField x`**（具名输入 (i)） |
| `sprToSFieldRange` | `K'` 在 `SField` 里的像，作为中间域 |
| ★★★ `ZCanon_le_sprToSFieldRange` | **`ZInSpr` ⟹ `ZCanon ≤ range (sprToSField)`** |

**射程（勿夸大）**：`ZInSpr` 是**具名输入**，**未证**。另一方向 `K'^N ⊆ Z`（输入 (ii)）
与 `V3'`（输入 (iii)）亦未建。`ZEqNFixed` —— **未证**。**H2 仍不是定理。** -/


section SprZInSpr

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`Z ⊆ K'`（沿 `sprToSField`）—— 终局输入 `ZInSpr`（**具名登记**）。

源文 `:415`："we may consider `UD(F,n,r)` a subalgebra of `M_n(K')`"。
本仓的 `ZCanon` 住在 `SField = Frac(S)`；`sprToSField`（§163）把 `K' = Frac(S')` 嵌进
`SField`。本谓词说的正是：**`Z` 的每个生成元都落在 `K'` 的像里**。

**⚠ 它为什么不能"结构性免费"（本轮实测）**：`D.centK_spec` 给的是
`c` 在 `M_n(SField)` 里的像是 `Matrix.scalar (centK c)`，其中 `c` 经
**`M_n(S)`** 那条嵌入；而 `(B)` 层的 `ψ : R ↪ M_n(S')` 经 `sprToSField` 后在
`ψ(X_{k₀}) = xdiag`（**对角**），而 `M_n(S)` 那条给的是**完整**的 `X_{k₀}`（含非对角）。
**两条嵌入在 `X_{k₀}` 的非对角元上真的不同** ⟹ 不能靠"两嵌入一致"得到本谓词。
它确实需要 `prop:14.19` 的 `Z` 半，故按 `(A)` 层 `XiBasisHyp` 的成法**具名登记**，
**不得**当成显然、也**不得**把 `ZEqNFixed` 直接当假设。 -/
def ZInSpr (D : GenericDivisionData F r n) (k₀ : Fin r) (hk₀ : k₀.val = 0) : Prop :=
  ∀ c : ↥(genericCenter F r n),
    ∃ x : SprField F r n, D.centK c = sprToSField F r n k₀ hk₀ x

#print axioms ZInSpr

/-- `K'` 在 `SField` 里的像，作为中间域。 -/
noncomputable def sprToSFieldRange (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    IntermediateField F (SField F r n) :=
  (sprToSField F r n k₀ hk₀).fieldRange

#print axioms sprToSFieldRange

/-- ★★★ **`ZInSpr` ⟹ `ZCanon ⊆ range (sprToSField)`**（即 `Z` 整个落进 `K'` 的像）。 -/
theorem ZCanon_le_sprToSFieldRange (D : GenericDivisionData F r n)
    {k₀ : Fin r} (hk₀ : k₀.val = 0) (h : ZInSpr F r n D k₀ hk₀) :
    ZCanon F r n D ≤ sprToSFieldRange F r n k₀ hk₀ := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨x, hx⟩ := h c
  exact ⟨x, hx.symm⟩

#print axioms ZCanon_le_sprToSFieldRange

end SprZInSpr

/-! ## §174 ★★★★★ **`K'^N` 作为 `F`-`Subalgebra`** —— `V3'` 的**左侧对象**

**本轮检索发现的形状对齐**：`SaltmanT.lean:2971` 的

```
NFixedAlg F : Subalgebra F (EM.latticeFunctionField F Mprime)
    carrier := {α | TFixed F α ∧ SFixed F α}
```

与 `(B)` 层的 `sprFieldNFixed`（载体 `sprFieldTFixed ∧ sprFieldSFixed`，`SprField` 上）
**完全同形**。且 `NFixedAlg` 的注释明写了**为何用 `Subalgebra` 而非 `Subfield`**：
"`≃ₐ[F]` 需要两侧都有 `Algebra F`，而本 pin 的 `Subfield` 没有 `Algebra F` 实例"。
⟹ `(B)` 层必须照办。

| 件 | 内容 |
|---|---|
| ★★★★★ `sprNFixedAlg` | **`K'^N` 作为 `Subalgebra F (SprField F r n)`** |
| `mem_sprNFixedAlg` | 成员刻画（`rfl`） |
| `sprNFixedAlg_typeLock` | 类型锁（载体一经改动立即编译失败） |
| `sprNFixedAlg_inv_mem` | 对求逆封闭（`K'^N` 其实是**子域**） |

**⟹ `V3'` 有了精确形状**：一条
`↥(sprNFixedAlg F 2 9) ≃ₐ[F] ↥(NFixedAlg F)`。
这是终局三输入里**唯一一个两侧对象都已就位**的（另两条输入 (i) `ZInSpr`／(ii) `K'^N ⊆ Z`
的对象也都已就位，但方向不同）。

**射程（勿夸大）**：本节只给**左侧对象**。`V3'` 的**同构本身未建**（需把
`SprField F 2 9` 与 `EM.latticeFunctionField F Mprime` 识别并使两边的 `T`／`S_n`
作用对应）。`ZEqNFixed` —— **未证**。**H2 仍不是定理。** -/


section SprNFixedAlg

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **`K'^N` 作为 `SprField` 的 `F`-`Subalgebra`** —— `V3'` 的**左侧对象**。

与 `SaltmanT.lean` 的 `NFixedAlg`（载体 `TFixed ∧ SFixed`，`latticeFunctionField` 上）
**同形**。**为何必须是 `Subalgebra` 而非 `Subfield`**（照 `NFixedAlg` 的既定理由）：
`≃ₐ[F]` 需要两侧都有 `Algebra F` 实例，而本 pin 的 `Subfield` 没有该实例。

**⟹ 于是 `V3'` 有了精确形状**：一条
`↥(sprNFixedAlg F 2 9) ≃ₐ[F] ↥(NFixedAlg F)`。 -/
noncomputable def sprNFixedAlg : Subalgebra F (SprField F r n) where
  carrier := {α | sprFieldNFixed F r n α}
  zero_mem' := sprFieldNFixed_zero F r n
  one_mem' := sprFieldNFixed_one F r n
  add_mem' := fun ha hb => sprFieldNFixed_add F r n ha hb
  mul_mem' := fun ha hb => sprFieldNFixed_mul F r n ha hb
  algebraMap_mem' := fun a => sprFieldNFixed_const F r n a

#print axioms sprNFixedAlg

/-- `sprNFixedAlg` 的成员刻画（`rfl`）。 -/
theorem mem_sprNFixedAlg {α : SprField F r n} :
    α ∈ sprNFixedAlg F r n ↔ sprFieldNFixed F r n α := Iff.rfl

#print axioms mem_sprNFixedAlg

/-- 类型锁：`sprNFixedAlg` 的载体（一旦改动立即编译失败）。 -/
theorem sprNFixedAlg_typeLock :
    (sprNFixedAlg F r n : Set (SprField F r n)) = {α | sprFieldNFixed F r n α} := rfl

#print axioms sprNFixedAlg_typeLock

/-- `sprNFixedAlg` 对求逆封闭（虽是 `Subalgebra`，`K'^N` 其实是**子域**）。 -/
theorem sprNFixedAlg_inv_mem {α : SprField F r n}
    (h : α ∈ sprNFixedAlg F r n) : α⁻¹ ∈ sprNFixedAlg F r n :=
  sprFieldNFixed_inv F r n h

#print axioms sprNFixedAlg_inv_mem

end SprNFixedAlg

/-! ## §175 ★★★★★ **系数计算的唯一入口**：`scalar a` 的系数就是 `a`

§170–§172 把 `Z → K'` 的映射分段建起来（存在性／取法／唯一性／`+`／`*`），
但每一步都带着一个 `∃ b, z = scalar b` 形式的**存在性假设**。本节给**唯一的计算入口**：

```
sprScalarCoeff (⟨a, rfl⟩) = a
```

**⟹ 意义**：在**已知是纯量**的矩阵上，"读出系数"就是 `a` 本身。于是
§172 的两条同态格都能从这个入口沿 `Matrix.scalar` 的 `map_add`／`map_mul` 重算，
**不必再携带存在性假设** —— 这是把 `Z → K'` 打包成 `AlgHom` 前的最后一块清障。

**射程（勿夸大）**：仍**未**把 `Z → K'` 打包成 `AlgHom`（需 `1`／`0`／`F`-纯量的相容格）；
`V3'`、`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprScalarCoeffCalc

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- ★★★★★ **系数计算的唯一入口**：`Matrix.scalar a` 的系数就是 `a`。

**为什么这是终局要的那一条**：`Z → K'` 的映射在**已知是纯量的**矩阵上就是"读出系数"。
有了本条，§172 的两条同态格（`_add`／`_mul`）都可从这个入口沿 `Matrix.scalar` 的
`map_add`／`map_mul` 重算 —— 且**不再需要用** `sprScalarCoeff_add`／`_mul` 的
`∃ ` 形式假设。 -/
theorem sprScalarCoeff_scalar [Nonempty (Fin n)] (a : SprField F r n) :
    sprScalarCoeff F r n
      (⟨a, rfl⟩ : ∃ b : SprField F r n,
        Matrix.scalar (Fin n) a = Matrix.scalar (Fin n) b) = a := by
  classical
  refine Matrix.scalar_inj (n := Fin n).mp ?_
  exact (sprScalarCoeff_spec F r n
    (⟨a, rfl⟩ : ∃ b : SprField F r n,
      Matrix.scalar (Fin n) a = Matrix.scalar (Fin n) b)).symm

#print axioms sprScalarCoeff_scalar

end SprScalarCoeffCalc

/-! ## §176 ★★★★★ **`Z → K'` 打包成 `F`-代数同态 ＋ `Z ≅ K'`** —— §6 清单第 1 项

§171–§175 把"中心元 ↦ 纯量系数"分段建起来（存在性／取法／唯一性／`+`／`*`／计算入口），
但**从未**给出一条 `AlgHom`：每一步都带着一个 `∃ b, z = scalar b` 形式的**存在性假设**。
本节把它收口：给出 `Z`（`ψ` 的像的中心化子）与 `K'` 的 **`F`-代数同构**。

| 件 | 内容 |
|---|---|
| `sprMatrixAlgebraMap_eq_scalar` | `algebraMap` 到矩阵环就是纯量矩阵（`F`-纯量格的桥） |
| ★★★★★ `sprPsiCentralizer` | **`Z` 的实体**：与 `ψ` 的像交换的矩阵，作为 `F`-`Subalgebra` |
| `mem_sprPsiCentralizer`／`sprPsiCentralizer_typeLock` | 成员刻画／类型锁 |
| ★★★★★ `sprPsiCenterCoeff_apply_scalar` | **唯一计算入口**（已知纯量 ⟹ 取系数就是它本身） |
| ★★★★★ `sprCenterCoeffHom` | **`Z → K'` 作为 `F`-代数同态**（本轮主件） |
| ★★★★★ `sprScalarToCentralizer` | **`K' → Z`** 反向（纯量矩阵嵌入） |
| `sprCenterCoeffHom_scalar`／`sprScalarToCentralizer_coeff` | 两个往返恒等 |
| ★★★★★★ `sprCenterCoeffEquiv` | **`Z ≅ K'`（`F`-代数同构）** |

**为什么 `sprCenterCoeffEquiv` 是"`Z ≅ K'`"**：`ψ` 的像在 `K'`-上张成 `M_n(K')`
（§168 `sprPsi_span_eq_top`），故与它交换的矩阵恰是**纯量矩阵**；而纯量矩阵的系数
就是 `K'` 的元。于是中心化子与 `K'` 同构。这是源文 `prop:14.19` 的 **`Z` 半**在
**规范化世界**（`M_n(K')`）里的形态。

**工艺（2 条，皆本轮实测）**：
* **R216 `∈` 与展开形态不是语法同一**：`z.2 : z ∈ sprPsiCentralizer …` 的类型是
  **隶属关系**，而引理要的是**展开的 `∀ x, …`**；直接传 `z.2` 报 "expected `∀ x, …`"。
  **正解**：`(mem_sprPsiCentralizer …).mp z.2`，或把引理的假设写成展开形态后显式
  `(z := …)` 指名。**形似类型不符，实为 `SetLike` 的 `∈` 未展开**。
* **R217 `sprPsiCenterCoeff` 按定义就是 `sprScalarCoeff`**：故 `+`／`*` 两格**不需要**
  重做系数计算，直接 `exact sprScalarCoeff_add …`；**但** `1`／`0`／`F`-纯量三格
  不能这样绕（`sprScalarCoeff` 没有 `_one`），必须走 `_apply_scalar` 入口。
  另：`Matrix` 上的 `Subtype.ext` 会被 `ext` 继续下钻到**条目层**，
  `AlgEquiv.ofAlgHom` 的往返证明要用 **`AlgHom.ext`（项而非 tactic）**。

**射程（勿夸大）**：本节的 `Z` 是 **`ψ`-中心化子**，**不是** `ZCanon = Frac(C(F,n,r))`
—— 两者的识别正是终局输入 (i) `ZInSpr`，**未证**。输入 (ii)／(iii)、`prop:14.19` 装配、
`ZEqNFixed` —— **未建/未证**。**H2 仍不是定理。** -/


section SprPsiCenterAlgHom

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- `algebraMap` 到矩阵环就是纯量矩阵（`Z → K'` 的 `F`-纯量格要用的桥）。 -/
theorem sprMatrixAlgebraMap_eq_scalar [Nonempty (Fin n)] (a : F) :
    algebraMap F (Matrix (Fin n) (Fin n) (SprField F r n)) a
      = Matrix.scalar (Fin n) (algebraMap F (SprField F r n) a) := by
  rw [Matrix.algebraMap_eq_diagonal]
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Pi.algebraMap_apply]
  by_cases h : i = j <;> simp [h]

#print axioms sprMatrixAlgebraMap_eq_scalar

/-- ★★★★★ **`Z` 的实体**：与 `ψ` 的像交换的矩阵，作为 `F`-`Subalgebra`。

源文 `prop:14.19` 的 `Z` 在规范化世界（`M_n(K')`）里的形态：`ψ` 的像的中心化子。 -/
noncomputable def sprPsiCentralizer [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    Subalgebra F (Matrix (Fin n) (Fin n) (SprField F r n)) where
  carrier := {z | ∀ x, (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) * z
      = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))}
  zero_mem' := by
    intro x
    rw [Matrix.mul_zero, Matrix.zero_mul]
  one_mem' := by
    intro x
    rw [Matrix.mul_one, Matrix.one_mul]
  add_mem' := by
    intro a b ha hb x
    rw [Matrix.mul_add, Matrix.add_mul, ha x, hb x]
  mul_mem' := by
    intro a b ha hb x
    have h1 : ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))) * (a * b)
        = (a * ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))) * b := by
      rw [← Matrix.mul_assoc, ha x]
    have h2 : (a * ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))) * b
        = a * (b * ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))) := by
      rw [Matrix.mul_assoc, hb x]
    have h3 : a * (b * ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))))
        = (a * b) * ((psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))) :=
      (Matrix.mul_assoc a b _).symm
    exact h1.trans (h2.trans h3)
  algebraMap_mem' := by
    intro a x
    exact (Algebra.commute_algebraMap_left a _).eq.symm

#print axioms sprPsiCentralizer

/-- `sprPsiCentralizer` 的成员刻画（`rfl`）。 -/
theorem mem_sprPsiCentralizer [Nonempty (Fin n)] {k₀ : Fin r} {hk₀ : k₀.val = 0}
    {z : Matrix (Fin n) (Fin n) (SprField F r n)} :
    z ∈ sprPsiCentralizer F r n k₀ hk₀ ↔
      ∀ x, (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) * z
        = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) :=
  Iff.rfl

#print axioms mem_sprPsiCentralizer

/-- 类型锁：`sprPsiCentralizer` 的载体（一旦改动立即编译失败）。 -/
theorem sprPsiCentralizer_typeLock [Nonempty (Fin n)] {k₀ : Fin r} {hk₀ : k₀.val = 0} :
    (sprPsiCentralizer F r n k₀ hk₀ : Set (Matrix (Fin n) (Fin n) (SprField F r n)))
      = {z | ∀ x, (psiSpr F r n k₀ hk₀ x).map
            (algebraMap (Spr F r n) (SprField F r n)) * z
          = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n))} :=
  rfl

#print axioms sprPsiCentralizer_typeLock

/-- ★★★★★ **唯一计算入口**：系数提取在"已知是纯量"的矩阵上就是取系数。

**为什么这是关键**：`sprPsiCenterCoeff` 按定义是 `sprScalarCoeff (matrix_eq_scalar …)`，
两条都带**存在性证明**作参数；一旦要证 `AlgHom` 的 `1`／`0`／`F`-纯量格，就必须
**绕过**那个不可控的 `Classical.choose` 见证——本条正是那个绕过点。 -/
theorem sprPsiCenterCoeff_apply_scalar [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩)
    {z : Matrix (Fin n) (Fin n) (SprField F r n)}
    (hz : ∀ x, (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)) * z
      = z * (psiSpr F r n k₀ hk₀ x).map (algebraMap (Spr F r n) (SprField F r n)))
    (a : SprField F r n) (ha : z = Matrix.scalar (Fin n) a) :
    sprPsiCenterCoeff F r n k₀ hk₀ hk hb z hz = a := by
  classical
  exact sprScalarCoeff_unique F r n
    (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb hz) ha

#print axioms sprPsiCenterCoeff_apply_scalar

/-- ★★★★★ **`Z → K'` 打包成 `F`-代数同态**（本轮主件）。

`toFun` ＝ 纯量系数（§171）。四条同态格：`+`／`*` 用 §172 的 `sprScalarCoeff_add`／`_mul`
（`sprPsiCenterCoeff` 按定义就是 `sprScalarCoeff`）；`1`／`0`／`F`-纯量用上一条的入口。 -/
noncomputable def sprCenterCoeffHom [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩) :
    ↥(sprPsiCentralizer F r n k₀ hk₀) →ₐ[F] SprField F r n where
  toFun z := sprPsiCenterCoeff F r n k₀ hk₀ hk hb z.1 z.2
  map_one' := by
    classical
    refine sprPsiCenterCoeff_apply_scalar F r n k₀ hk₀ hk hb
      (z := (1 : Matrix (Fin n) (Fin n) (SprField F r n)))
      (1 : ↥(sprPsiCentralizer F r n k₀ hk₀)).2 (1 : SprField F r n) ?_
    ext i j
    rw [Matrix.scalar_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  map_zero' := by
    classical
    refine sprPsiCenterCoeff_apply_scalar F r n k₀ hk₀ hk hb
      (z := (0 : Matrix (Fin n) (Fin n) (SprField F r n)))
      (0 : ↥(sprPsiCentralizer F r n k₀ hk₀)).2 (0 : SprField F r n) ?_
    ext i j
    rw [Matrix.scalar_apply]
    simp
  map_add' := by
    intro z w
    classical
    exact sprScalarCoeff_add F r n
      (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb z.2)
      (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb w.2)
      (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb (z + w).2)
  map_mul' := by
    intro z w
    classical
    exact sprScalarCoeff_mul F r n
      (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb z.2)
      (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb w.2)
      (matrix_eq_scalar_of_commute_psi F r n k₀ hk₀ hk hb (z * w).2)
  commutes' := by
    intro a
    classical
    refine sprPsiCenterCoeff_apply_scalar F r n k₀ hk₀ hk hb
      (z := algebraMap F (Matrix (Fin n) (Fin n) (SprField F r n)) a)
      (algebraMap F ↥(sprPsiCentralizer F r n k₀ hk₀) a).2
      (algebraMap F (SprField F r n) a)
      (sprMatrixAlgebraMap_eq_scalar F r n a)

#print axioms sprCenterCoeffHom

/-- ★★★★★ **`K' → Z`**：纯量矩阵嵌入。 -/
theorem sprScalar_mem_centralizer [Nonempty (Fin n)] (k₀ : Fin r) (hk₀ : k₀.val = 0)
    (a : SprField F r n) :
    Matrix.scalar (Fin n) a ∈ sprPsiCentralizer F r n k₀ hk₀ := by
  classical
  intro x
  exact (Matrix.scalar_comm (m := Fin n) (n := Fin n) a
    (fun r' => Commute.all a r') _).symm

#print axioms sprScalar_mem_centralizer

/-- ★★★★★ **`K' → Z`** 作为 `F`-代数同态。 -/
noncomputable def sprScalarToCentralizer [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) :
    SprField F r n →ₐ[F] ↥(sprPsiCentralizer F r n k₀ hk₀) where
  toFun a := ⟨Matrix.scalar (Fin n) a, sprScalar_mem_centralizer F r n k₀ hk₀ a⟩
  map_one' := by
    classical
    refine Subtype.ext ?_
    exact map_one (Matrix.scalar (Fin n))
  map_zero' := by
    classical
    refine Subtype.ext ?_
    exact map_zero (Matrix.scalar (Fin n))
  map_add' := by
    intro a b
    classical
    refine Subtype.ext ?_
    exact map_add (Matrix.scalar (Fin n)) a b
  map_mul' := by
    intro a b
    classical
    refine Subtype.ext ?_
    exact map_mul (Matrix.scalar (Fin n)) a b
  commutes' := by
    intro a
    classical
    refine Subtype.ext ?_
    exact (sprMatrixAlgebraMap_eq_scalar F r n a).symm

#print axioms sprScalarToCentralizer

/-- ★★★★★ `K' → Z → K'` 的恒等（`sprCenterCoeffHom` 在纯量矩阵上就是取系数）。 -/
theorem sprCenterCoeffHom_scalar [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩)
    (a : SprField F r n) :
    sprCenterCoeffHom F r n k₀ hk₀ hk hb (sprScalarToCentralizer F r n k₀ hk₀ a) = a := by
  classical
  exact sprPsiCenterCoeff_apply_scalar F r n k₀ hk₀ hk hb
    (z := Matrix.scalar (Fin n) a) (sprScalar_mem_centralizer F r n k₀ hk₀ a) a rfl

#print axioms sprCenterCoeffHom_scalar

/-- ★★★★★ `Z → K' → Z` 的恒等（`sprPsiCenterCoeff_spec` 直接给）。 -/
theorem sprScalarToCentralizer_coeff [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩)
    (z : ↥(sprPsiCentralizer F r n k₀ hk₀)) :
    sprScalarToCentralizer F r n k₀ hk₀
      (sprCenterCoeffHom F r n k₀ hk₀ hk hb z) = z := by
  classical
  refine Subtype.ext ?_
  exact (sprPsiCenterCoeff_spec F r n k₀ hk₀ hk hb z.1 z.2).symm

#print axioms sprScalarToCentralizer_coeff

/-- ★★★★★★ **`Z ≅ K'`（`F`-代数同构）** —— `prop:14.19` 的 **`Z` 半**在规范化世界
（`M_n(K')`）的形态：`ψ` 的像的中心化子与 `K'` 之间，由"取纯量系数"给出的同构。 -/
noncomputable def sprCenterCoeffEquiv [Nonempty (Fin n)]
    (k₀ : Fin r) (hk₀ : k₀.val = 0) {k : Fin r} (hk : k ≠ k₀)
    (hb : SprXiBasisHyp F r n ⟨k, fun h0 => hk (Fin.ext (by rw [h0, hk₀]))⟩) :
    ↥(sprPsiCentralizer F r n k₀ hk₀) ≃ₐ[F] SprField F r n :=
  AlgEquiv.ofAlgHom (sprCenterCoeffHom F r n k₀ hk₀ hk hb)
    (sprScalarToCentralizer F r n k₀ hk₀)
    (AlgHom.ext (fun a => sprCenterCoeffHom_scalar F r n k₀ hk₀ hk hb a))
    (AlgHom.ext (fun z => sprScalarToCentralizer_coeff F r n k₀ hk₀ hk hb z))

#print axioms sprCenterCoeffEquiv

end SprPsiCenterAlgHom

/-! ## §177 ★★★★★ **`N` 在纯量矩阵上就是 `φ`** —— 终局输入 (ii) 的接线格

终局输入 (ii)（`K'^N ⊆ Z`）的论证形状（v15 §4.2）是

```
c ∈ K'^N  ⟹  c·I ∈ M_n(K')^N  ⟹（若 UD = M_n(K')^N）  c·I ∈ UD  ⟹  c·I 中心于 M_n(K')  ⟹  c ∈ Z(UD) = Z
```

其中**第一步**正是本节：纯量矩阵在 `N = T ⋊ S_n` 下的作用恰是 `φ` 在系数上的作用。
一旦有了它，`c ∈ K'^N` 与 `c·I ∈ M_n(K')^N` **互为充要**（`sprMatNFixed_scalar_iff`）。

| 件 | 内容 |
|---|---|
| `sprScalar_mul_comm` | 纯量矩阵与任意矩阵交换（显式给矩阵参数以避开 η-展开失配） |
| `sprDiagMatK_inv_mul` | 对角矩阵互逆（`b⁻¹` 与 `b`） |
| ★★★★★ `sprPsiDK_scalar` | **`ψ_b(c·I) = φ_b(c)·I`** |
| ★★★★★ `sprPsiSK_scalar` | **`ψ_σ(c·I) = φ_σ(c)·I`** |
| ★★★★★ `sprMatNFixed_scalar_iff` | **`c·I ∈ M_n(K')^N ↔ c ∈ K'^N`** |

**工艺（1 条，本轮实测）**：
* **R218 `b⁻¹` 与 `fun i => (b i)⁻¹` 在 `rw` 下不等**：`Fin n → Fˣ` 的 `Inv` 是逐点定义的，
  `b⁻¹` 经 `Pi.inv` 展开成 lambda 后与**字面 lambda** 在 `rw` 的模式匹配中**不同一**
  （报 "Did not find an occurrence"，而两个表达式**显示上看起来一样**）。
  **正解**：在引理的**陈述**里就写 `fun i => (b i)⁻¹`（或全程用同一字面形式），
  不要一半用 `b⁻¹`、一半用 lambda。

**射程（勿夸大）**：本节只给**纯量层的对应**。`UD` 的对象本身在本仓**尚未定义**；
`UD = M_n(K')^N`（`prop:14.19` 左半）**未证**；`Z(UD) = Z` **未建**。
故输入 (ii) `K'^N ⊆ Z` **仍未证**。`ZEqNFixed` —— **未证**。**H2 仍不是定理。** -/


section SprScalarAction

set_option linter.style.haveILetI false

variable (F : Type) [Field F] (r n : ℕ)

/-- 纯量矩阵与任意矩阵交换（显式给矩阵参数，免得 `rw` 在 η-展开形态上失配）。 -/
theorem sprScalar_mul_comm [Nonempty (Fin n)] (c : SprField F r n)
    (M : Matrix (Fin n) (Fin n) (SprField F r n)) :
    Matrix.scalar (Fin n) c * M = M * Matrix.scalar (Fin n) c :=
  Matrix.scalar_comm c (fun r' => Commute.all c r') M

#print axioms sprScalar_mul_comm

/-- `sprDiagMatK b⁻¹ * sprDiagMatK b = 1`（两个对角矩阵互逆）。 -/
theorem sprDiagMatK_inv_mul [Nonempty (Fin n)] (b : Fin n → Fˣ) :
    sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹)
      * sprDiagMatK (F := F) (r := r) (n := n) b = 1 := by
  classical
  have h0 : sprDiagMat (r := r) b
      * sprDiagMat (r := r) (fun i => (b i)⁻¹) = 1 := sprDiagMat_mul_inv (r := r) b
  have hcomm : sprDiagMat (r := r) (fun i => (b i)⁻¹) * sprDiagMat (r := r) b
      = sprDiagMat (r := r) b * sprDiagMat (r := r) (fun i => (b i)⁻¹) := by
    rw [sprDiagMat, sprDiagMat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [sprDiagMatK, sprDiagMatK, ← Matrix.map_mul, hcomm, h0]
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j <;> simp [hij]

#print axioms sprDiagMatK_inv_mul

/-- ★★★★★ **`T` 在纯量矩阵上就是 `φ_b`**：`ψ_b(c·I) = φ_b(c)·I`。 -/
theorem sprPsiDK_scalar [Nonempty (Fin n)] (b : Fin n → Fˣ) (c : SprField F r n) :
    sprPsiDK F r n b (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) ((sprDiagFieldEquiv F r n b) c) := by
  classical
  rw [sprPsiDK]
  have hmap : (Matrix.scalar (Fin n) c).map (sprDiagFieldEquiv F r n b).toRingHom
      = Matrix.scalar (Fin n) ((sprDiagFieldEquiv F r n b) c) := by
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply]
    by_cases h : i = j <;> simp [h]
  rw [hmap]
  rw [← sprScalar_mul_comm F r n ((sprDiagFieldEquiv F r n b) c)
    (sprDiagMatK (F := F) (r := r) (n := n) (fun i => (b i)⁻¹))]
  rw [Matrix.mul_assoc, sprDiagMatK_inv_mul, Matrix.mul_one]

#print axioms sprPsiDK_scalar

/-- ★★★★★ **`S_n` 在纯量矩阵上就是 `φ_σ`**：`ψ_σ(c·I) = φ_σ(c)·I`。 -/
theorem sprPsiSK_scalar [Nonempty (Fin n)] (σ : Equiv.Perm (Fin n)) (c : SprField F r n) :
    sprPsiSK F r n σ (Matrix.scalar (Fin n) c)
      = Matrix.scalar (Fin n) ((sprPermFieldEquiv F r n σ) c) := by
  classical
  rw [sprPsiSK]
  have hmap : (Matrix.scalar (Fin n) c).map (sprPermFieldEquiv F r n σ).toRingHom
      = Matrix.scalar (Fin n) ((sprPermFieldEquiv F r n σ) c) := by
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply]
    by_cases h : i = j <;> simp [h]
  rw [hmap]
  rw [sprPmatK, sprPmat_inv]
  rw [← sprScalar_mul_comm F r n ((sprPermFieldEquiv F r n σ) c)
    (sprPmat (SprField F r n) σ)]
  rw [Matrix.mul_assoc, sprPmat_mul_symm, Matrix.mul_one]

#print axioms sprPsiSK_scalar

/-- ★★★★★ **`K'^N` ↔ 纯量矩阵层的 `M_n(K')^N`** —— 终局输入 (ii) 的接线格。

`c·I` 被 `N` 固定 **当且仅当** `c ∈ K'^N`。 -/
theorem sprMatNFixed_scalar_iff [Nonempty (Fin n)] (c : SprField F r n) :
    sprMatNFixed F r n (Matrix.scalar (Fin n) c) ↔ sprFieldNFixed F r n c := by
  classical
  constructor
  · rintro ⟨hT, hS⟩
    refine ⟨fun b => ?_, fun σ => ?_⟩
    · have h := hT b
      rw [sprPsiDK_scalar] at h
      exact Matrix.scalar_inj.mp h
    · have h := hS σ
      rw [sprPsiSK_scalar] at h
      exact Matrix.scalar_inj.mp h
  · rintro ⟨hT, hS⟩
    refine ⟨fun b => ?_, fun σ => ?_⟩
    · rw [sprPsiDK_scalar, hT b]
    · rw [sprPsiSK_scalar, hS σ]

#print axioms sprMatNFixed_scalar_iff

end SprScalarAction

end Procesi

