# 本目录 PDF 的构建说明（2026-10-11）

**tex**：`ABGV-5.2-resolution.tex` = 2026-10-11 版（与知识库 `wiki/ABGV-5.2-resolution.tex` 同步；
新增 `thm:retract-criterion`(4.12) 与 `thm:not-retract-rational`(4.13) 及其证明）。

**书目**：**本文的书目就嵌在 tex 里** —— `\begin{filecontents}{wu.bib}`（tex 第 2499 行）… `\end{filecontents}`（第 2878 行），
含 24 条 `@` 条目，**完整覆盖论文引用的全部 17 个键** ✓。**不需要外部 `wu.bib`** ✓（这是本目录 `wu.bib` 的来源：由 `pdflatex` 从 `filecontents` 自动生成）。

**构建（四步，缺一不可 —— `bibtex` 必须在首次 `pdflatex` 之后）**：
```
pdflatex -interaction=nonstopmode ABGV-5.2-resolution.tex   # 生成 .aux 与 wu.bib
bibtex   ABGV-5.2-resolution                                # 解析引文 -> .bbl
pdflatex -interaction=nonstopmode ABGV-5.2-resolution.tex
pdflatex -interaction=nonstopmode ABGV-5.2-resolution.tex
```
**判别式：末次日志的 `undefined` 计数必须为 0**：`grep -c undefined ABGV-5.2-resolution.log` ✓

**2026-10-11 构建读数**：`undefined = 0` ✓｜错误 0｜**22 页** ✓（含书目）。

**⚠ 更正（2026-10-11）**：本文件早前版本记有一条「书目缺失（`[?]`）」的缺陷 —— **该结论是错的** ✗。
真实原因是构建**步骤顺序**（在 `wu.bib` 尚未由 `filecontents` 生成／`.aux` 状态不对时就跑了 `bibtex`）。
`BIBLIOGRAPHY-GAP.md` 同属该错误结论的产物，已作废并改写为同目录的历史记录 ✓。
