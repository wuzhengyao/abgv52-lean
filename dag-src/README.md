# H2 dependency graph (English, single graph, clickable)

**Deliverables** (one A4 landscape page for print; an HTML page for GitHub):

| file | role |
|---|---|
| `index.html` | web page with the **clickable** graph — use this on GitHub Pages / in a browser |
| `procesi-h2-dag.svg` | the graph as standalone SVG; **each blue box is a hyperlink** to its Lean source |
| `procesi-h2-dag.pdf` | one-page A4 landscape, vector, with title and notes (link annotations kept) |
| `procesi-h2-dag.png` | raster preview (140 dpi) |
| `github-base.txt` | **one-line link config**: base URL (line 1) and in-repo path prefix (line 2) |

Purpose: draw the Lean 4 proof of the **Procesi identification (H2)** as a directed acyclic
graph of logical dependencies, with H2 itself as the terminal node.

## What the graph shows

* **Blue boxes** = self-authored theorems. Each box shows **only the Lean declaration name** and
  is a **clickable link** to that declaration in the Lean sources on GitHub
  (`https://github.com/wuzhengyao/abgv52-lean/blob/main/Procesi/<File>.lean#L<line>`).
* **Green dashed boxes** = mathlib lemmas that are *used directly* by the self-authored theorems.
* **Gold box** = the terminal statement `H2: Z_{S9}(F,9) ≅ F(M⊕U)^{S9}`.
* **Arrows** point from a lemma to the statement that uses it (logical order: the arrowhead is
  on the user, not on the used lemma).

Statistics: **31 nodes** (1 terminal + 24 self-authored theorems + 6 mathlib lemmas), **36 edges**.
Both branches are in the same graph and both attach to H2: the main chain through
`h2_unconditional`, and the non-vacuity branch through `nonempty_genericDivisionData_two_nine`.

## How the edges are obtained (mechanical, never hand-written)

`build_dag.py`:
1. splits each Lean source file into declaration blocks (`theorem|lemma|def|...` up to the next
   declaration) and **strips comments**;
2. for every self-authored node, searches its block for the **declaration names** of all other
   nodes (word-boundary match) — a hit is an edge;
3. merges pairs of external lemmas that always occur together, drops isolated nodes;
4. renders DOT → SVG / PDF / PNG, and writes `index.html`.

The same pass also **self-checks every hyperlink**: it re-reads the target line and verifies that
the declaration name actually occurs there (24/24 checked, 0 bad).

Rebuild: `python3 build_dag.py` (needs `dot` from graphviz and `pdflatex`).
If the repository layout changes, edit `github-base.txt` and rerun.

## Honest notes (also printed at the bottom of the PDF)

1. The edges are derived mechanically from the Lean sources (declaration blocks, comments
   stripped); none are hand-written, and every hyperlink is re-checked against the target line at
   build time.
2. Every theorem shown has `#print axioms` = `propext`, `Classical.choice`, `Quot.sound`
   (`sorryAx = 0`).

## Files

`graph_data.py` (node table: id / label / file / layer / kind / **declaration name** / merge table /
notes), `build_dag.py` (edge derivation + rendering + link self-check), `procesi-h2-dag.dot`
(generated source), `_raw.pdf` / `_page.tex` (intermediate LaTeX assembly).
