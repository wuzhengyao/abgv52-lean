# Verification code

Supplementary code for the paper

> Zhengyao Wu, *Rationality of the center of a generic division algebra with a
> group action over a field of characteristic \(0\)*

It reproduces, by explicit integer linear algebra, every numerical reading on
which the paper's main theorem rests.  Nothing in the output is a
pre-written conclusion: each number is computed from the input matrices by
integer Smith normal form.

## What is verified

Throughout, \(H = C_3 \times C_3 = \langle x, y\rangle\), \(M|_H\) is the
restriction of the Procesi lattice to \(H\) (the kernel of
\(\pi|_H \colon \mathbb{Z}[H]^9 \to I[H]\), see the paper), and
\(\coh^q(H, -)\) denotes integral group cohomology.

| # | Reading | Value |
|:-:|:--------|:------|
| R1 | \(\coh^1(H, I[H])\) | \(C_9\) |
| R2 | \(\coh^2(H, M\lvert_H)\) | \(C_9\) |
| R3 | \(\coh^2(H, \mathbb{Z})\) | \(C_3 \times C_3\) |
| R4 | \(\coh^2(H, \mathbb{Z}[H/K])\) for all six subgroups \(K \le H\) | \(0,\; C_3, C_3, C_3, C_3,\; C_3\times C_3\) (exponent divides \(3\) in every case) |
| R5 | \(\coh^2(H,\, 8\mathbb{Z}[H] \oplus \mathbb{Z})\) | \(C_3 \times C_3\) |
| R6 | \(\mathbb{Z}\)-rank of \(M\lvert_H\); rank of \(\pi\lvert_H\) | \(73\); \(8\) |

The pair R2 versus R5 is the discriminant used in the paper: the two modules
have the same rational character, yet their \(\coh^2\) differ
(\(C_9 \ne C_3\times C_3\)).

## Two independent implementations

| | `python/abgv52_certs.py` | `gap/abgv52_verify.g` |
|:--|:--|:--|
| Language | Python 3 (standard library only) | GAP |
| Resolution used | free resolution of \(\mathbb{Z}\) over \(\mathbb{Z}[H]\) built from the two periodic resolutions of \(C_3\) (Künneth) | inhomogeneous cochain complex, matrices built by hand |
| R2 computed | directly, on the rank-\(73\) module \(M\lvert_H\) | via the long exact sequence of the Procesi sequence |
| Extra | internal self-test, Smith certificates | summary of all readings |

The Python script also contains a **second, independent** pipeline (an
inhomogeneous cochain complex, i.e. the same construction as the GAP script,
written independently in Python); when the two are compared the script
asserts agreement.  The two languages use entirely separate Smith normal form
implementations.

R2 is the strongest cross-check: the GAP script *derives* it from
\(\coh^1(H,I[H])\) through the long exact sequence, whereas the Python script
computes it directly on \(M|_H\), whose \(\mathbb{Z}\)-rank is \(73\).

## Requirements

* Python 3.8 or later.  **No third-party packages** (only `argparse`,
  `itertools`, `math`, `sys`, `fractions`).
* GAP 4.11 or later **with the HAP package** (needed for
  `ResolutionFiniteGroup`, `HomToIntegers`, `Cohomology`), to run the GAP
  script.

## How to run

```
./run.sh
```

runs the Python script and the GAP script (for \(p=3\) and, by changing a
single line, for \(p=5\)), compares the output with the recorded output
in `expected/`, and exits non-zero on any mismatch.  The \(p=5\) run
reproduces the ranks quoted in the appendix of the paper
(24, 601 for \(\mathbb{Z}[H]\); 24, 576 for \(I[H]\); \(\coh^2(H,\mathbb{Z}) = [5,5]\)).  Individually:

```
python3 python/abgv52_certs.py --selftest           # self-test only
python3 python/abgv52_certs.py --out certs.json     # self-test + all readings + certificates
gap -q -b gap/abgv52_verify.g                        # GAP script
```

Total runtime is a few seconds on a laptop.

## Self-test

`python/abgv52_certs.py` refuses to report any reading unless its built-in
self-test passes; it exits with status 2 otherwise.  The self-test contains

* **positive controls** — values known independently:
  \(\coh^0(H,\mathbb{Z}) = \mathbb{Z}\),
  \(\coh^1(H,\mathbb{Z}) = 0\),
  \(\coh^2(H,\mathbb{Z}) = C_3\times C_3\), and
  \(\coh^q(H,\mathbb{Z}[H]) = 0\) for \(q = 1,2\);
* **agreement between the two internal pipelines** on three readings;
* **negative controls** — a deliberately corrupted differential must make the
  exactness check fail, and the invariant-theoretic pair R2/R5 must come out
  different (a permutation-type module must never yield \(C_9\)).

Note on the exactness check: it verifies **both** \(d_n d_{n+1} = 0\) and the
rank equality \(\operatorname{rank} d_n + \operatorname{rank} d_{n+1} =
\operatorname{rank} T_n\).  The rank equality alone does **not** imply that
the sequence is a complex, so both are checked.

## Certificates

For the integer matrix underlying each reading, the Python script emits
unimodular \(U, V\) and a diagonal \(D\) with \(UAV = D\), together with
\(\det U = \pm 1\) and \(\det V = \pm 1\).  This lets a reader check the
computation with any computer algebra system, or by hand for the smaller
matrices, without re-running the script.  For the largest matrices only the
diagonal and a SHA-256 digest of \((U,D,V)\) are printed; the full data is
reproducible by re-running the script.

## Lean development

The Lean development is in the repository root (`ABGV52/`), not in
this folder; see the main `README.md` of this repository for its
verification status, the list of named hypotheses, and build
instructions.

## Files

```
README.md                    this file
LICENSE                      MIT
CITATION.cff                 citation metadata
run.sh                       runs both scripts and diffs against expected/
MANIFEST.sha256              SHA-256 of every file in this folder
python/abgv52_certs.py       Python verification (two internal pipelines)
gap/abgv52_verify.g          GAP verification (HAP)
expected/python-certs.json   recorded output of the Python script
expected/gap-output.txt      recorded output of the GAP script, p = 3
expected/gap-output-p5.txt   recorded output of the GAP script, p = 5
```

## Citing

Please cite the accompanying paper when using this code, and give the
repository commit hash together with the SHA-256 manifest above, so that
the version you used is unambiguous.

## License

MIT; see `LICENSE`.
