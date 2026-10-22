/-
  Procesi —— **AGPR2020 `lem:1.1.16` 的消费件**（**不**自建证明）

  命题：`S` 简单、中心 ＝ 基域 `F`（域）、`K/F` 域扩张 ⟹ `S ⊗_F K` 简单。

  **来源（用户令 2026-10-22：「已有 `lem:1.1.16` 的等价物就先用已有的」）**：
  `Procesi/External/TauCetiCentralSimpleTensorProduct.lean`（TauCeti
  `Algebra/CentralSimple/TensorProduct.lean` 的逐字移植）给出

  ```
  TauCeti.IsSimpleRing.tensorProduct               [IsSimpleRing A] [Algebra.IsCentral K A]
                                                   [IsSimpleRing B] : IsSimpleRing (A ⊗[K] B)
  TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right   （镜像方向；＝ 标量扩张形态）
  ```

  本件只做**两次搬运**：`Algebra.IsCentral F S`（由 `Subalgebra.center F S = ⊥`）＋
  `Algebra.TensorProduct.comm`（把 `K ⊗ S` 换成 `S ⊗ K`）。

  **历史（诚实登记）**：R732 曾在**未查 TauCeti**的情况下自建同一引理（265 行证明，
  用的是同一套"系数理想 ＋ 交换子支撑下降"技术）。R734 复查发现重复发明，
  按用户令**撤下自建证明**，改为消费 TauCeti 件；原自建件的四条辅助陈述
  （`tensorCoeffEquiv` 系列、`algebraMap_injective_of_field`、`..._aux`）一并删除。
  复盘见 [[proj-lean-external-recon-protocol]] §11.2。

  **射程**：本件是**一般代数**引理，不涉及 PI 理论。它把 PI 输入化为两半
  （`UDK'` 单 ＋ 中心 ＝ `Z`），本件本身不证那两半。
-/

import Procesi.External.TauCetiCentralSimpleTensorProduct

namespace Procesi

open TensorProduct
open scoped TensorProduct

variable {F S K : Type*} [Field F] [Ring S] [Algebra F S] [Field K] [Algebra F K]

/-- **AGPR2020 `lem:1.1.16`**（经 TauCeti `IsSimpleRing.tensorProduct`）：`S` 单环、
中心 ＝ 基域 `F`（域），`K/F` 域扩张 ⟹ `S ⊗_F K` 单。 -/
theorem isSimpleRing_tensorProduct_of_center_eq_bot [IsSimpleRing S]
    (hcenter : Subalgebra.center F S = ⊥) : IsSimpleRing (S ⊗[F] K) := by
  haveI hc : Algebra.IsCentral F S := ⟨hcenter.le⟩
  haveI : IsSimpleRing (K ⊗[F] S) :=
    TauCeti.IsSimpleRing.tensorProduct_of_isCentral_right (K := F) (A := K) (B := S)
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm F K S).toRingEquiv this

#print axioms isSimpleRing_tensorProduct_of_center_eq_bot

end Procesi
