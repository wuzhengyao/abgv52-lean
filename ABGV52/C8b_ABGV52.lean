/-
  ABGV-5.2 —— C 档 · **接线（C8 → B 档判据谓词）**

  目的：论文 `lem:H2-MH`（`coh²(H, M|_H) ≅ C_9`）在 Lean 里有**两种形态**，此前互不相识：

    * **B 档**（`Thm_ABGV52.lean`）把它当**显式假设** `h9 : Coh2IsoC9 M`（谓词见 `Hyp_ABGV52.lean`）；
    * **C 档**（`C8_ABGV52.lean`）把它**证明**了：`H2_MH_equiv_zmod9 : ↥(groupCohomology M_H_rep 2) ≃ₗ[ℤ] ZMod 9`。

  本件把两者接上：给出 **`Coh2IsoC9 M_H_rep` 的实例**，并给出**少一条假设**的论文推论版本。

  **口径后果（供论文 Code availability 参考）**：论文称「两处外部输入作显式假设」（`coh²` 读数 ＋
  EM 判据）。接线后，**第一处已由 Lean 开发本身证明**（`C8`），只剩 **EM 判据**一处仍是假设；
  **论文主文本的条件化地位不变**（那只由判据那条决定）。
-/
import ABGV52.C8_ABGV52
import ABGV52.Thm_ABGV52

namespace ABGV52

/-- **论文 `lem:H2-MH` 的实例**：`coh²(H, M|_H) ≅ C_9`（B 档谓词形态）。 -/
theorem coh2IsoC9_M_H_rep : Coh2IsoC9 M_H_rep :=
  ⟨H2_MH_equiv_zmod9⟩

/-- 连带：判别对（`C_9` **且** 指数不整除 3）在 `M|_H` 上就位。

`discriminant_pair`（`Thm_ABGV52.lean`）原以 `h9 : Coh2IsoC9 M` 为参数——此处由 C 档提供。 -/
theorem discriminant_pair_M_H_rep : Coh2IsoC9 M_H_rep ∧ ¬ Coh2ExpDvd3 M_H_rep :=
  discriminant_pair M_H_rep coh2IsoC9_M_H_rep

/-- **论文 `thm:not-stably-rational`（接线版；第四十二改修正判据）**：`coh²` 输入已由
C 档提供，余下**两条输入**为修正判据（序列形；⊕-形旧读法一般情形已证为假）与
`M|_H` 非 quasi-permutation（论文 `lem:not-quasi-perm`）。本件在 `EMQuasi` 层之下
（不能 import 它），故 `hnq` 此处仍为参数；其已证实例与全闭合消费见
`EMQuasi_ABGV52.lean`（`not_isQuasiPermutation_M_H_rep`）／`EM_ABGV52.lean`
（`not_stably_rational_EM`）。 -/
theorem not_stably_rational_wired (K : Type) (SRat : Type → Prop)
    (hEM : SRat K → IsQuasiPermutation M_H_rep)
    (hnq : ¬ IsQuasiPermutation M_H_rep) : ¬ SRat K :=
  not_stably_rational M_H_rep K SRat hEM hnq

/-! ## 公理闸门 -/

#print axioms coh2IsoC9_M_H_rep
#print axioms discriminant_pair_M_H_rep
#print axioms not_stably_rational_wired

end ABGV52
