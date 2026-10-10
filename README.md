# Lean 4 formalization: the Procesi lattice and stable rationality of Z_H(F, 9)

This repository contains a machine-checked Lean 4 development verifying the
logical chain of the arguments in the accompanying paper on the Procesi
lattice obstruction to stable rationality (Problem 5.2 of the
Auel--Brussel--Garibaldi--Vishne problem list), for the group
H = C_3 x C_3 and its generalizations H = C_p x C_p.

## Paper

The paper is included in this repository:

* `paper/ABGV-5.2-resolution.tex` — LaTeX source (version of 2026-10-10);
* `paper/ABGV-5.2-resolution.pdf` — a compiled PDF.

The PDF was compiled from the current TeX source (2026-10-10).

## Verification code

The two verification programs of the paper's Appendix A (Python and GAP
with HAP) and their recorded output are in `verification/`; see
`verification/README.md`.  They can be re-run with `verification/run.sh`.

## Verification status

* The development compiles with no `sorry`.
* Every declaration depends only on the three standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
* The Endo--Miyata--Voskresenskii criterion is used as an explicit named
  hypothesis, exactly as in the paper; it is not reproved.  It is
  formalized as the type-locked interfaces `EMHyp` (H-level) and
  `EMHypP` (p-general), each with a definitional-shape lock, a wiring
  theorem, and a non-vacuity probe (`EM_ABGV52.lean`).
* Saltman's Corollary 3.13 (retract rationality) is quoted as an explicit
  named hypothesis, not reproved.  It is formalized as the type-locked
  interface `SaltmanHyp` with a wiring theorem that fills the
  faithfulness input from the elementary proof of faithfulness, and with
  a non-vacuity probe (`Saltman_ABGV52.lean`).
* As of the 2026-10-10 revision of the paper, the retract rationality
  of Z_H(F, 9) is left open in the paper (Remark 4.12), and the earlier
  comparison through the linear invariant field is recorded there as
  invalid.  The formalized retract-rationality wiring (`R1_ABGV52.lean`,
  `SaltT2_ABGV52.lean`, `Saltman_ABGV52.lean`, `ProcConsume_ABGV52.lean`)
  is retained as a record of the conditional assembly of that thread.
* In the same revision the quasi-permutation form of the criterion,
  together with a machine-checked counterexample to its original
  stably-permutation form, is formalized in `EMQuasi_ABGV52.lean` and
  `EMCounter_ABGV52.lean`.
* The geometric identification Z_H(F, p^2) ≅ F(M|_H)^H (Procesi, 1967)
  is used as a named hypothesis: the development formalizes the reduction
  to the regular restriction and the transport of invariants along that
  identification, but neither constructs the field Z_H(F, p^2) nor proves
  Procesi's theorem.  The interface `ProcesiHyp` carries a
  definitional-shape lock, and `Procesi_ABGV52.lean` supplies the
  named-hypothesis consumption theorem and a non-vacuity probe.  The
  formalization of the stable-rationality chain is therefore conditional
  on these named inputs.
* The development also formalizes proof layers behind the three named
  hypotheses, as described in the paper: for the converse direction of
  the criterion in the abelian case with roots of unity, the stable
  rationality of the invariant field is derived from the stably
  permutation condition together with faithfulness and a unique-product
  condition, with the rationality of the invariant field of an arbitrary
  permutation lattice, the identification of the two-step localization
  with the function field of the product lattice, and the comparison of
  the lattice bases all proved, not assumed.

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
| `F1`, `R1`, `PC2`, `FaithfulMH` | faithfulness of the action, retract-rationality wiring, permutation-class lemma, faithfulness obstruction |
| `EM_ABGV52`, `Saltman_ABGV52`, `Procesi_ABGV52` | the three named hypotheses (`EMHyp`/`EMHypP`, `SaltmanHyp`, `ProcesiHyp`) with definitional-shape locks, wiring theorems, and non-vacuity probes |
| `EMArtin`, `EMTrans`, `EMSpeiser`, `EMSemilinear`, `EMRational`, `EMFixed`, `EMDegree`, `EMIndep`, `EMRouteS`, `EMBridge`, `EMConsume` | the proof layers behind the criterion: Artin's fixed-field theorem, invariant transport, Speiser's theorem, the semilinear machinery, Lenstra's (1.4), the degree chain, algebraic independence, and the assembly of the converse |
| `EM1betaGen_*` | the permutation-lattice rationality engine (character-basis layer, monomial lattice, rationality closure, consumption) with a non-vacuity probe |
| `EMQuasi`, `EMCounter`, `ExtBridge`, `ExtLES`, `ExtMH`, `ExtMHUncond`, `ProbeLES1`, `ProbeLES2`, `S2b` | the criterion-clearing track: the corrected quasi-permutation form of the criterion with its cohomological refutation witness, the machine-checked counterexample to the original form, and the Ext^1 machinery with its unconditional closure |
| `SaltDef`, `SaltT2`, `SaltSwan`, `SaltCor`, `SaltCond`, `SaltGeneric`, `SaltRatOver` | the Saltman-track layers: the 1984 definitions, the rational-to-retract bridge, Swan's lemma, the corollary/reduction pair, the 2-power/cyclotomic condition layer, the named generic-object residual, and retract rationality along rational extensions |
| `ProcLat`, `ProcHyp`, `ProcStab`, `ProcStabLink`, `ProcConsume` | the Procesi-track layers: the lattice rank account, the corrected named interface, the stabilizer layer, its wiring, and the consumer assembly |
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
