# Lean 4 formalization: the Procesi lattice and stable rationality of Z_H(F, 9)

This repository contains a machine-checked Lean 4 development verifying the
logical chain of the arguments in the accompanying paper on the Procesi
lattice obstruction to stable rationality (Problem 5.2 of the
Auel--Brussel--Garibaldi--Vishne problem list), for the group
H = C_3 x C_3 and its generalizations H = C_p x C_p.

## Paper

The paper is included in this repository:

* `paper/ABGV-5.2-resolution.tex` — LaTeX source (version of 2026-10-01);
* `paper/ABGV-5.2-resolution.pdf` — a compiled PDF.

The PDF dates from 2026-09-30 and predates the current TeX source.

## Verification code

The two verification programs of the paper's Appendix A (Python and GAP
with HAP) and their recorded output are in `verification/`; see
`verification/README.md`.  They can be re-run with `verification/run.sh`.

## Verification status

* The development compiles with no `sorry`.
* Every declaration depends only on the three standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
* The Endo--Miyata--Voskresenskii criterion is used as an explicit named
  hypothesis, exactly as in the paper; it is not reproved.
* Saltman's Corollary 3.13 (retract rationality) is quoted as an explicit
  named hypothesis, not reproved.
* The geometric identification Z_H(F, p^2) ≅ F(M|_H)^H (Procesi, 1967)
  is used as a named hypothesis: the development formalizes the reduction
  to the regular restriction and the transport of invariants along that
  identification, but neither constructs the field Z_H(F, p^2) nor proves
  Procesi's theorem. The formalization of the stable-rationality chain is
  therefore conditional on these named inputs.

## Highlights

* The cohomological computation H^2(H, M|_H) ≅ C_9 is reproduced inside
  the development, together with the discriminant pair it yields.
* M|_H is not a stably permutation lattice: the relevant exponent bound
  on H^2 of permutation lattices is proved by combining Shapiro's lemma
  with the short exact sequence 0 -> Z -> Q -> Q/Z -> 0 of trivial
  modules over the corresponding subgroup.
* Z_H(F, 9) is not stably rational, with the Endo--Miyata--Voskresenskii
  criterion as the only hypothesis.
* Base change to the rationals: M|_H ⊗_Z Q ≅ 8 · Q[H] ⊕ Q as
  Q[H]-modules; both the linear isomorphism and its equivariance are
  formalized, together with the dimension count dim_Q = 73.
* The p-general statements for H = C_p x C_p (odd p) are formalized with
  p as a parameter; the case p = 3 is the corresponding instance.

## Layout

| Files | Content |
|:--|:--|
| `Hyp_*`, `C1`--`C8b` | shared setup (group, lattice, Procesi map) and the computation H^2(H, M\|_H) ≅ C_9 |
| `S1`--`S5` | exponent and stable-* statements, and the wiring of the criterion |
| `D1`--`D14` | criterion-facing definitions and interfaces |
| `P1`--`P6`, `PThm`, `PChallenge` | p-general lattice and theorem statements, with an independent restatement |
| `G1b`--`G4`, `GThm`, `GChallenge` | the geometric-identification reduction layer (named-hypothesis transport) |
| `MH`, `MQ`, `MI`, `BR` | the rational model of the Procesi kernel and the base-change bridge |
| `F1`, `R1`, `PC2` | faithfulness of the action, retract-rationality wiring, permutation-class lemma |
| `Thm_*`, `Challenge_*` | type-locked statements with independent restatements |
| `Probe*` | auxiliary probes retained for auditability |
| `paper/` | the paper: TeX source and compiled PDF |
| `verification/` | the Python and GAP verification programs of the paper's Appendix A, with recorded output |

## Build

The toolchain is `leanprover/lean4:v4.33.1` (see `lean-toolchain`) and the
development is pinned to mathlib4 commit
`db584cd6d46c92f209a44c0f1c829460d327499d` (see `lakefile.toml`).

    lake exe cache get
    lake build

`SHA256SUMS` records the SHA-256 of every Lean source file.

## License

The repository — the paper (`paper/`), the Lean development, and the
verification code — is released under the MIT license (see `LICENSE`).
The file `verification/LICENSE` carries the same license for the code
package.
