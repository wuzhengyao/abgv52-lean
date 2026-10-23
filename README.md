# Rationality of the center of a generic division algebra with a group action over a field of characteristic 0

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
* `paper/ABGV-5.2-resolution.pdf` — the compiled PDF (22 pages).

The PDF was compiled from the TeX source of 2026-10-23. This revision adds the paragraph that
records the machine-checked status of the formalization (after Proposition 3.2) and updates the
disclosure of the tools used; the mathematical results are unchanged.

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
non-vacuity probe. Saltman's Corollary 3.13 is no longer quoted in the paper; the
type-locked interface `SaltmanHyp` is kept in the development for the Saltman track.

## Layout

The dependency graph of the H2 layer (the Procesi identification) is generated mechanically from
the Lean sources. Blue boxes are self-authored theorems; green dashed boxes are mathlib lemmas
used directly; an arrow points from a lemma to the statement that uses it.

* **[`index.html`](index.html)** — the clickable version: every blue box opens its declaration in
  the Lean sources on GitHub.
* **[`h2-dependency-graph.pdf`](h2-dependency-graph.pdf)** — the printable version (one A4
  landscape page).

The sources of the graph are in `dag-src/`; regenerate with `python3 dag-src/build_dag.py`.

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
