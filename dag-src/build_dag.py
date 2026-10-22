# -*- coding: utf-8 -*-
"""H2 dependency DAG (English, single merged graph).
Blue nodes carry ONLY the Lean declaration name and are hyperlinks to the
GitHub source file at the declaration line.  Edges are derived mechanically
from the Lean sources (declaration blocks, comments stripped) - never hand-written."""
import io, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import graph_data as g

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)?"
                     r"(?:theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z_][A-Za-z0-9_'!]*)")
def strip_comments(t):
    return re.sub(r"(?m)--.*$", "", re.sub(r"/-.*?-/", "", t, flags=re.S))
_b = {}
def blocks(rel):
    """decl name -> (comment-stripped block text, 1-based line of the declaration)"""
    if rel in _b: return _b[rel]
    path = os.path.join(ROOT, "Procesi", rel if rel.endswith(".lean") else rel + ".lean")
    t = io.open(path, encoding="utf-8").read().split("\n")
    starts = [(i, m.group(1)) for i, l in enumerate(t) if (m := DECL_RE.match(l))]
    out = {}
    for k, (i, name) in enumerate(starts):
        j = starts[k+1][0] if k+1 < len(starts) else len(t)
        out.setdefault(name, (strip_comments("\n".join(t[i:j])), i + 1))
    _b[rel] = out; return out

# ---- mechanically derived edges ----
CANDS = [(n[0], n[5]) for n in g.NODES if n[5]] + list(g.EXTRA_EXT.items())
edges, unmatched = set(), []
for nid, lab, f, _l, kind, decl in g.NODES:
    if kind != "self" or not decl: continue
    hit = blocks(f).get(decl)
    if hit is None: unmatched.append((f, decl)); continue
    blk = hit[0]
    for cid, lit in CANDS:
        if cid == nid or len(lit) < 4: continue
        if re.search(r"(?<![A-Za-z0-9_'])" + re.escape(lit) + r"(?![A-Za-z0-9_'])", blk):
            edges.add((nid, cid))
final = set()
for p, c in edges:
    c = g.MERGE.get(c, c)
    if c is not None and p != c: final.add((p, c))
if unmatched: print("!! missing decl blocks:", unmatched)

# ---- GitHub link base (one-line config) ----
cfg = [l.strip() for l in io.open(os.path.join(HERE, "github-base.txt"), encoding="utf-8")
       if l.strip() and not l.startswith("#")]
BASE = cfg[0].rstrip("/")
PREFIX = cfg[1].strip("/") + "/" if len(cfg) > 1 else ""
def gh_url(rel, line):
    return "%s/%s%s%s#L%d" % (BASE, PREFIX, rel, ".lean", line)

info = {n[0]: n for n in g.NODES}
used = {x for e in final for x in e}
ids = [n[0] for n in g.NODES if n[0] in used or n[4] == "root"]

def wrap(name, width=14):
    if " " in name or len(name) <= width: return name
    lines, cur = [], ""
    for tok in name.split("_"):
        piece = tok if not cur else "_" + tok
        if cur and len(cur) + len(piece) > width:
            lines.append(cur); cur = tok
        else:
            cur += piece
    if cur: lines.append(cur)
    return "\\n".join(lines)

STYLE = {
    "root":    'fillcolor="#fde68a", color="#92400e", penwidth=2.0, fontsize=9.5',
    "self":    'fillcolor="#dbeafe", color="#1e40af", penwidth=1.0, fontsize=7.8',
    "mathlib": 'fillcolor="#dcfce7", color="#166534", penwidth=0.9, fontsize=7.2, style="rounded,filled,dashed"',
}
MATHLIB_DOC = "https://leanprover-community.github.io/mathlib4_docs/find/?pattern=%s#doc"
LEGEND = ('<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="2" CELLPADDING="1">'
          '<TR><TD COLSPAN="2" ALIGN="LEFT"><B>Legend</B></TD></TR>'
          '<TR><TD BGCOLOR="#dbeafe" BORDER="1" COLOR="#1e40af" WIDTH="26" HEIGHT="12"> </TD>'
          '<TD ALIGN="LEFT">self-authored theorem;<BR/>click: its Lean source file (GitHub)</TD></TR>'
          '<TR><TD BGCOLOR="#dcfce7" BORDER="1" COLOR="#166534" STYLE="dashed" WIDTH="26" HEIGHT="12"> </TD>'
          '<TD ALIGN="LEFT">mathlib lemma,<BR/>used directly</TD></TR>'
          '<TR><TD ALIGN="CENTER">&#8593;</TD><TD ALIGN="LEFT">supports: points to the<BR/>statement that uses it</TD></TR>'
          '</TABLE>>')

L = ['digraph H2 {',
     '  graph [rankdir=TB, splines=spline, ordering=out, nodesep=0.10, ranksep=0.24, newrank=true,',
     '         fontname="DejaVu Sans", margin=0.05];',
     '  node [shape=box, style="rounded,filled", fontname="DejaVu Sans", margin="0.05,0.02"];',
     '  edge [color="#6b7280", arrowsize=0.5, penwidth=0.7, dir=back];']
for nid in ids:
    n = info[nid]
    kind = n[4]
    lab = wrap(n[1]).replace('"', '\\"')
    extra = ''
    if kind == "root":
        line = blocks("Statement")["ProcesiS9Hyp"][1]
        extra = ', URL="%s", target="_blank"' % gh_url("Statement", line)
    elif kind == "self" and n[5]:
        hit = blocks(n[2]).get(n[5])
        if hit: extra = ', URL="%s", target="_blank"' % gh_url(n[2], hit[1])
    elif kind == "mathlib" and "+" not in n[1] and "＋" not in n[1]:
        extra = ', URL="%s", target="_blank"' % (MATHLIB_DOC % n[1].replace("\\n", ""))
    L.append('  %s [label="%s", %s%s];' % (nid, lab, STYLE[kind], extra))
for p, c in sorted(final):
    st = ' [style=dashed, color="#166534"]' if info[c][4] == "mathlib" else ''
    L.append('  %s -> %s%s;' % (p, c, st))
L.append('  legend [label=%s, shape=plaintext, style="", fontsize=7.6];' % LEGEND)
L.append('  { rank=same; root; legend; }')
L.append('}')
out_dot = os.path.join(HERE, "procesi-h2-dag.dot")
io.open(out_dot, "w", encoding="utf-8").write("\n".join(L) + "\n")
nat = subprocess.run(["dot", "-Tplain", out_dot], capture_output=True, text=True).stdout.split("\n")[0]
print("natural:", nat, "| nodes", len(ids), "| edges", len(final))

# ---- link self-check (L43): each URL's (file, line) must hold the declaration ----
bad = []
for nid in ids:
    n = info[nid]
    if n[4] == "self" and n[5]:
        hit = blocks(n[2]).get(n[5])
        if hit is None: bad.append((nid, "no block")); continue
        path = os.path.join(ROOT, "Procesi", n[2] + ".lean")
        src_line = io.open(path, encoding="utf-8").read().split("\n")[hit[1] - 1]
        if n[5] not in src_line:
            bad.append((nid, "line %d does not hold %s" % (hit[1], n[5])))
print("link self-check: %d nodes checked, %d bad" % (sum(1 for i in ids if info[i][4] == "self" and info[i][5]), len(bad)))
for b in bad: print("  !!", b)

# ---- SVG (clickable) + PNG preview ----
svg = os.path.join(HERE, "procesi-h2-dag.svg")
subprocess.run(["dot", "-Tsvg", out_dot, "-o", svg], check=True)
subprocess.run(["dot", "-Tpng", "-Gdpi=140", out_dot, "-o", os.path.join(HERE, "procesi-h2-dag.png")], check=True)
print("links in svg:", io.open(svg, encoding="utf-8").read().count("<a xlink:href"))

# ---- PDF: graph + title + notes, one A4 landscape page ----
raw = os.path.join(HERE, "_raw.pdf")
subprocess.run(["dot", "-Tpdf", out_dot, "-o", raw], check=True)
def texesc(t):
    for a, b in (("\\", "\\textbackslash{}"), ("_", "\\_"), ("&", "\\&"),
                 ("%", "\\%"), ("#", "\\#"), ("^", "\\^{}")):
        t = t.replace(a, b)
    return t
notes_tex = "\\\\\n".join(texesc(n) for n in g.NOTES)
tex = os.path.join(HERE, "_page.tex")
io.open(tex, "w", encoding="utf-8").write(r"""\documentclass[11pt]{article}
\usepackage[paperwidth=297mm,paperheight=210mm,margin=9mm]{geometry}
\usepackage{graphicx}
\pagestyle{empty}
\begin{document}
\noindent{\Large\bfseries %s}\\[4pt]
\noindent\includegraphics[width=274mm]{%s}\\[2pt]
{\scriptsize
%s}
\end{document}
""" % (texesc(g.TITLE), raw, notes_tex))
r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-output-directory", HERE, tex],
                   capture_output=True, text=True)
print("pdflatex rc", r.returncode)
if r.returncode:
    print(r.stdout[-1200:]); sys.exit(1)
pdf = os.path.join(HERE, "procesi-h2-dag.pdf")
if os.path.exists(pdf): os.remove(pdf)
os.replace(os.path.join(HERE, "_page.pdf"), pdf)

# ---- HTML page (works on GitHub Pages / locally; keeps the links clickable) ----
svg_body = io.open(svg, encoding="utf-8").read()
svg_body = svg_body[svg_body.index("<svg"):]
html = """<!doctype html>
<meta charset="utf-8">
<title>%s</title>
<style>
 body{margin:18px;font:15px/1.45 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,Arial,sans-serif;color:#111}
 h1{font-size:19px;margin:0 0 10px}
 .wrap{overflow-x:auto}
 svg{max-width:100%%;height:auto}
 p.note{font-size:12.5px;color:#444;margin:6px 0 0}
 code{font-size:12.5px;background:#f3f4f6;padding:1px 4px;border-radius:3px}
</style>
<h1>%s</h1>
<p class="note">Blue boxes are self-authored theorems; each one links to its declaration in the Lean sources on GitHub.
Green dashed boxes are mathlib lemmas that are used directly. An arrow means &ldquo;uses&rdquo;.
Edges are derived mechanically from the Lean sources; the axiom profile is <code>propext</code>,
<code>Classical.choice</code>, <code>Quot.sound</code> (<code>sorryAx = 0</code>).</p>
<div class="wrap">%s</div>
""" % (g.TITLE, g.TITLE, svg_body)
io.open(os.path.join(HERE, "index.html"), "w", encoding="utf-8").write(html)
print("wrote svg / html / pdf")
