# Rationality of the center of a generic division algebra with a group action
over a field of characteristic 0

Lean 4 companion to the paper with the same title.

Let $F$ be a field of characteristic $0$ and let $H = C_3 \times C_3$ act regularly as a
transitive subgroup of $S_9$. Let $Z_H(F,9)$ be the center of the generic division algebra of
degree $9$ with $H$-action. Problem 5.2 of the Auel--Brussel--Garibaldi--Vishne problem list
asks for its birational class. The answer proved in the paper is that $Z_H(F,9)$ is **not**
stably rational, **not** rational and **not** retract rational over $F$. Non-stable and
non-retract rationality both come from $H^2(H, M|_H) \cong C_9$ for the restricted Procesi
lattice: its exponent $9$ is incompatible with quasi-permutation and with every finite-index
permutation superlattice, while all permutation lattices have $H^2$-exponent dividing $3$. For
$H = C_p \times C_p \subset S_{p^2}$ with $p$ odd the same computation gives
$H^2(H, M|_H) \cong C_{p^2}$ against exponent $p$, so $Z_H(F,p^2)$ is not stably rational.

This repository contains the machine-checked Lean 4 development of that chain: the lattice
computations, the statement layers, and the wiring from the named inputs to the conclusions.
What is checked here, and which inputs are still named hypotheses, is listed under
*Verification status* below.

## Paper

The paper is included in this repository:

* `paper/ABGV-5.2-resolution.tex` — LaTeX source (version of 2026-10-23);
* `paper/ABGV-5.2-resolution.pdf` — the compiled PDF (21 pages).

The PDF was compiled from the TeX source of 2026-10-23. This revision updates the
paragraph recording the machine-checked status of the formalization and the disclosure of the
tools used; the mathematical results are unchanged.

## Verification code

The two verification programs (Python and GAP with HAP) and their recorded output are shipped
in `verification/` for reproducibility. They are **no longer part of the paper** (the appendix
that used to contain them has been removed). Re-run with `verification/run.sh`; details in
`verification/README.md`.

## Verification status

* The development compiles with **no `sorry`**, and every declaration depends only on the
three standard axioms `propext`, `Classical.choice`, `Quot.sound`.
* **Named hypotheses**, used as in the paper and *not* reproved: the
Endo--Miyata--Voskresenskii criterion (`EMHyp` for the H-level form, `EMHypP` for the
p-general form) and the retract-rationality criterion (`RetractCriterionHyp`,
`ABGV52/RetractCrit_ABGV52.lean`); each is a type-locked interface with a wiring theorem and a
non-vacuity probe. Saltman's Corollary 3.13 is quoted as a theorem in the paper and also appears
as a type-locked interface (`SaltmanHyp`).
* **The geometric identification** of `Z_H(F,9)` with the fixed field is *not* an input in the
degree-9 case: it is proved in this repository, in `Procesi/` (`Procesi.h2_unconditional`), for
every field of characteristic `0`, and the structure it names is constructed
(`Procesi.h2_unconditional_nonvacuous`), so the statement is not vacuous. The p-general form is
still consumed through `ProcesiHyp`.
* **Proof layers behind the named hypotheses** are formalized where the paper lists them: the
converse direction of the criterion in the abelian case with roots of unity, the
quasi-permutation form together with a machine-checked counterexample to its
stably-permutation form (`EMQuasi_ABGV52.lean`, `EMCounter_ABGV52.lean`), and the Saltman
condition layers.
* **Non-retract-rationality** (Theorem 4.13 of the paper) is formalized in
`ABGV52/NotRetract_ABGV52.lean`, with an independent restatement in
`ABGV52/NotRetractChallenge_ABGV52.lean`. The passage from the lattice to the field runs through
the flasque-resolution criterion of the paper, a named input (`RetractCriterionHyp`,
`ABGV52/RetractCrit_ABGV52.lean`), and through the geometric identification of `Z_H(F,9)` with
the invariant field.
* Consequently the stable-rationality chain verified here is **conditional on the named inputs
above**.

See `paper/` for the paper and `verification/` for the two verification programs; `## Layout`
says where each layer lives.

## Layout

The dependency graph of the H2 layer (the Procesi identification) is generated mechanically from
the Lean sources. Blue boxes are self-authored theorems; green dashed boxes are mathlib lemmas
used directly; an arrow points from a lemma to the statement that uses it.

* **[`index.html`](index.html)** — the clickable version: every blue box opens its declaration in
  the Lean sources on GitHub.
* **[`h2-dependency-graph.pdf`](h2-dependency-graph.pdf)** — the printable version (one A4
  landscape page).

The sources of the graph are in `dag-src/`; regenerate with `python3 dag-src/build_dag.py`.

| Files | Content |
|:--|:--|
| `Hyp_*`, `C1`--`C8b` | shared setup (group, lattice, Procesi map) and the computation H^2(H, M\|_H) ≅ C_9 |
| `S1`--`S5` | exponent and stable-* statements |
| `P1`--`P6` (with `P5a`, `P5b`), `PThm`, `PChallenge` | p-general lattice and theorem statements, with an independent restatement |
| `G1b`--`G4`, `GThm`, `GChallenge` | reduction to the geometric identification (named-hypothesis transport) |
| `ProcLat`, `ProcHyp`, `ProcStab`, `ProcStabLink`, `ProcConsume` | the Procesi track: lattice rank account, named interface, stabilizer layer, its wiring, consumption |
| `MH`, `MQ`, `MI`, `BR` | the rational model of the Procesi kernel and the base-change bridge |
| `NotRetract_ABGV52`, `NotRetractChallenge_ABGV52`, `RetractCrit_ABGV52`, `Superlattice_ABGV52`, `StableRationalBricks_ABGV52` | the non-retract-rationality chain (Theorem 4.13) and its independent restatement |
| `Procesi/` (83 files) | the H2 formalization: statement layer, the scalar-matrix bypass, non-vacuity |
| `Thm_*`, `Challenge_*`, `Probe*` | type-locked statements with independent restatements, and auxiliary probes |
| `dag-src/` | the script that regenerates the figure from the sources |
| `paper/` | the paper: TeX source and compiled PDF |
| `verification/` | the two verification programs and their recorded output |

## Build

The toolchain is `leanprover/lean4:v4.35.0` (see `lean-toolchain`) and the
development is pinned to mathlib4 commit
`aa35a481e5f0cdb3b04a899ead15d6ca7305a624` (see `lakefile.toml`) — an
upgrade of 2026-10-15 from `db584cd6d46c92f209a44c0f1c829460d327499d`
(2026-08-10) and Lean 4.33.

    lake build

(The prebuilt-object cache of the mathlib community was not usable at the
time of the upgrade; `lake build` compiles mathlib locally, which takes
roughly half an hour on a 20-core machine with sufficient memory.)

`SHA256SUMS` records the SHA-256 of every Lean source file.

## License

The repository — the paper (`paper/`), the Lean development, and the
verification code — is released under the MIT license (see `LICENSE`).
The file `verification/LICENSE` carries the same license for the code
package.
