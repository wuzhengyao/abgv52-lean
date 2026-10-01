#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ABGV-5.2-resolution 投稿稿 —— A 档「机器证书」（T0/T1）。

要证的读数（label 取自 raw/ABGV-5.2-resolution.tex）
  R1  h^1(H, I[H])          ≅ C_9          [lem:H1-IH]
  R2  h^2(H, M|_H)          ≅ C_9          [lem:H2-MH]
  R3  h^2(H, Z)             ≅ C_3 × C_3    [lem:H2-Z]
  R4  h^2(H, Z[H/K])  指数整除 3，K 遍历全部 6 个子群   [prop:perm-exponent 的内核]
  R5  h^2(H, 8Z[H] ⊕ Z)     ≅ C_3 × C_3    [prop:M_H-not-permutation 判别对]
  R6  Z-秩 M|_H = 73 且 0 → M|_H → Z[H]^9 → I[H] → 0 正合   [prop:procesi-H]

对象（逐字取自稿件，坐标约定见 prop:tensor-reg-ZH）
  H = C_3 × C_3 = <x> × <y>；R = Z[H]；I[H] = ker ε，基 e_g := g − 1（G ≠ 1，秩 8）。
  π|_H : Z[H]^9 → I[H]（坐标按 b ∈ H 分块）在「槽 b 中的 g」上取值 g − b，即 e_g − e_b。

管线
  A（Künneth/周期分辨）  Tot_n ≅ R^{n+1}
  B（非齐次上链复形）    C^k = Map(H^k, N)

用法（本目录为论文配套代码包）
  python3 python/abgv52_certs.py --selftest      # 只跑内置自检；不过退码 2
  python3 python/abgv52_certs.py --out CERT.json # 自检 + 全部读数 + 证书
"""
import argparse
import itertools
import math
import sys
from fractions import Fraction

P = 3
ELEMS = [(i, j) for i in range(P) for j in range(P)]
IDX = {g: k for k, g in enumerate(ELEMS)}
ID = (0, 0)
N_H = 9
X, Y = (1, 0), (0, 1)


def gmul(a, b):
    return ((a[0] + b[0]) % P, (a[1] + b[1]) % P)


# ======================================================== 1. 整数线性代数
def zmat(r, c):
    return [[0] * c for _ in range(r)]


def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def mmul(A, B):
    if not A or not B:
        return []
    n, k, p = len(A), len(B), len(B[0])
    C = zmat(n, p)
    for i in range(n):
        Ai, Ci = A[i], C[i]
        for t in range(k):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(p):
                    if Bt[j]:
                        Ci[j] += a * Bt[j]
    return C


def mrank(M):
    if not M or not M[0]:
        return 0
    A = [[Fraction(x) for x in row] for row in M]
    m, n, r = len(A), len(A[0]), 0
    for c in range(n):
        piv = next((i for i in range(r, m) if A[i][c]), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = A[r][c]
        for i in range(r + 1, m):
            if A[i][c]:
                f = A[i][c] / inv
                Ai, Ar = A[i], A[r]
                for j in range(c, n):
                    Ai[j] -= f * Ar[j]
        r += 1
        if r == m:
            break
    return r


def mdet(M):
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            if A[r][c]:
                f = A[r][c] / A[c][c]
                for j in range(c, n):
                    A[r][j] -= f * A[c][j]
    assert d.denominator == 1
    return int(d)


def snf(M):
    """U·M·V = D（Smith 对角形，非负、整除链）。"""
    A = [row[:] for row in M]
    m = len(A)
    n = len(A[0]) if m else 0
    U, V = eye(m), eye(n)

    def sw_r(i, j):
        A[i], A[j] = A[j], A[i]
        U[i], U[j] = U[j], U[i]

    def sw_c(i, j):
        for r in range(m):
            A[r][i], A[r][j] = A[r][j], A[r][i]
        for r in range(n):
            V[r][i], V[r][j] = V[r][j], V[r][i]

    def sub_r(i, j, q):
        if q:
            for c in range(n):
                A[i][c] -= q * A[j][c]
            for c in range(m):
                U[i][c] -= q * U[j][c]

    def sub_c(i, j, q):
        if q:
            for r in range(m):
                A[r][i] -= q * A[r][j]
            for r in range(n):
                V[r][i] -= q * V[r][j]

    t = 0
    while t < min(m, n):
        piv = None
        for i in range(t, m):
            for j in range(t, n):
                if A[i][j]:
                    piv = (i, j)
                    break
            if piv:
                break
        if piv is None:
            break
        if piv[0] != t:
            sw_r(piv[0], t)
        if piv[1] != t:
            sw_c(piv[1], t)
        while True:
            done = True
            for i in range(t + 1, m):
                if A[i][t]:
                    sub_r(i, t, A[i][t] // A[t][t])
                    if A[i][t]:
                        sw_r(i, t)
                        done = False
            for j in range(t + 1, n):
                if A[t][j]:
                    sub_c(j, t, A[t][j] // A[t][t])
                    if A[t][j]:
                        sw_c(j, t)
                        done = False
            if not done:
                continue
            for i in range(t + 1, m):
                if A[i][t] % A[t][t]:
                    sub_r(i, t, A[i][t] // A[t][t])
                    sw_r(i, t)
                    done = False
                    break
            if not done:
                continue
            for j in range(t + 1, n):
                if A[t][j] % A[t][t]:
                    sub_c(j, t, A[t][j] // A[t][t])
                    sw_c(j, t)
                    done = False
                    break
            if done:
                break
        if A[t][t] < 0:
            for c in range(n):
                A[t][c] = -A[t][c]
            for c in range(m):
                U[t][c] = -U[t][c]
        t += 1
    # 内建断言：U·M·V = D 且 D 为对角（**不**在此改对角元去凑整除链——
    # 直接改 D 而不配套行列变换会破坏恒等式，使证书失效；不变因子表作为
    # 多重集读取即可，群结构不依赖顺序）。
    assert mmul(mmul(U, M), V) == A, "snf: U·M·V ≠ D"
    for i in range(m):
        for j in range(n):
            if i != j and A[i][j]:
                raise AssertionError("snf: D 非对角")
    return U, A, V


def snf_check(M, U, D, V):
    """证书自检：U·M·V = D 且 |det U| = |det V| = 1（U、V 为方阵时）。"""
    ok1 = mmul(mmul(U, M), V) == D
    ok2 = (len(U) == len(U[0]) and abs(mdet(U)) == 1) if U and U[0] else True
    ok3 = (len(V) == len(V[0]) and abs(mdet(V)) == 1) if V and V[0] else True
    return ok1, ok2, ok3


def ker_basis(M, ncols=None):
    m = len(M)
    n = len(M[0]) if m else (ncols or 0)
    if m == 0:
        return eye(n)
    if n == 0:
        return zmat(0, 0)
    U, D, V = snf(M)
    r = min(m, n)
    cols = [j for j in range(n) if j >= r or D[j][j] == 0]
    if not cols:
        return zmat(n, 0)
    return [[V[i][j] for j in cols] for i in range(n)]   # 形状 n×k，列为基向量


def im_basis(M):
    """M 的像的一组基（列为基向量）。

    用 M·V = U^{-1}·D 的前 r 列（**不是** U 的列——U 的列张成的不是像）。
    """
    if not M or not M[0]:
        return zmat(len(M), 0)
    U, D, V = snf(M)
    r = sum(1 for i in range(min(len(D), len(D[0]))) if D[i][i])
    if r == 0:
        return zmat(len(M), 0)
    MV = mmul(M, V)
    return [[MV[i][j] for j in range(r)] for i in range(len(MV))]


def in_col_span(B, Y, check=True):
    """解 X 使 B·X = Y（**Y 的每一列**是一个待解向量；B 的每一列是基向量）。

    约定：X 的行数 = B 的列数，列数 = Y 的列数。返回前做 round-trip 断言 B·X = Y。
    """
    if not Y or not Y[0]:
        return zmat(len(B[0]), 0)
    U, D, V = snf(B)
    d = [D[i][i] for i in range(len(B[0]))]
    cols = []
    for jc in range(len(Y[0])):
        col = [Y[i][jc] for i in range(len(Y))]
        u = [sum(U[i][j] * col[j] for j in range(len(col))) for i in range(len(U))]
        Vx = [0] * len(B[0])
        for i, di in enumerate(d):
            if di == 0:
                if u[i]:
                    raise ValueError("向量不在像中")
            else:
                if u[i] % di:
                    raise ValueError("向量不在像中")
                Vx[i] = u[i] // di
        for i in range(len(d), len(u)):
            if u[i]:
                raise ValueError("向量不在像中")
        cols.append([sum(V[i][j] * Vx[j] for j in range(len(Vx))) for i in range(len(V))])
    X = [[cols[j][i] for j in range(len(cols))] for i in range(len(B[0]))]
    if check:
        assert mmul(B, X) == Y, "in_col_span: round-trip 失败"
    return X


def quotient_invariants(K, I):
    """span(K)/span(I) 的不变因子（K、I 的列为基）。

    返回**完整**对角表（含 0 与 1）：0 = 一个自由 ℤ 因子，1 = 一个 ℤ/1 = 0 因子，
    d > 1 = 一个 C_d 因子。渲染交给 fmt_group。
    """
    n = len(K[0]) if K else 0
    if n == 0:
        return []
    if I and I[0]:
        C = in_col_span(K, I)
        _, D, _ = snf(C)
        return [abs(D[i][i]) for i in range(min(len(D), len(D[0])))]
    return [0] * n          # 像为空 ⟹ 商 = ℤ^n


def fmt_group(inv):
    """不变因子表 → 可读形式：0 → ℤ^m，1 → 略去（ℤ/1 = 0），d > 1 → C_d。"""
    if inv is None:
        return "?"
    free = sum(1 for x in inv if x == 0)
    tors = sorted(x for x in inv if x > 1)
    parts = []
    if free:
        parts.append("ℤ" if free == 1 else "ℤ^%d" % free)
    parts += ["C_%d" % x for x in tors]
    return " × ".join(parts) if parts else "0"


# ======================================================== 2. Z[H]-模
class Mod:
    def __init__(self, rank, act):
        assert set(act) == set(ELEMS)
        self.rank = rank
        self.act = act

    def act_coeff(self, coeff):
        r = self.rank
        A = zmat(r, r)
        for g, c in coeff.items():
            if c:
                Ag = self.act[g]
                for i in range(r):
                    for j in range(r):
                        if Ag[i][j]:
                            A[i][j] += c * Ag[i][j]
        return A


def mod_trivial():
    return Mod(1, {g: [[1]] for g in ELEMS})


def mod_regular():
    act = {}
    for g in ELEMS:
        A = zmat(N_H, N_H)
        for k, h in enumerate(ELEMS):
            A[IDX[gmul(g, h)]][k] = 1
        act[g] = A
    return Mod(N_H, act)


def subgroup(gens):
    S, fr = {ID}, [ID]
    while fr:
        h = fr.pop()
        for g in gens:
            t = gmul(h, g)
            if t not in S:
                S.add(t)
                fr.append(t)
    return sorted(S)


def mod_perm(K):
    """Z[H/K]；K 为子群（元素列表）。"""
    cosets, seen = [], set()
    for g in ELEMS:
        if g not in seen:
            c = sorted({gmul(g, k) for k in K})
            cosets.append(c)
            seen |= set(c)
    idx = {g: i for i, c in enumerate(cosets) for g in c}
    act = {}
    for g in ELEMS:
        A = zmat(len(cosets), len(cosets))
        for i, c in enumerate(cosets):
            A[idx[gmul(g, c[0])]][i] = 1
        act[g] = A
    return Mod(len(cosets), act)


def mod_dsum(Ms):
    rank = sum(M.rank for M in Ms)
    offs, o = [], 0
    for M in Ms:
        offs.append(o)
        o += M.rank
    act = {}
    for g in ELEMS:
        A = zmat(rank, rank)
        for M, off in zip(Ms, offs):
            AM = M.act[g]
            for i in range(M.rank):
                for j in range(M.rank):
                    if AM[i][j]:
                        A[off + i][off + j] = AM[i][j]
        act[g] = A
    return Mod(rank, act)


def mod_on_submodule(ambient, basis):
    rank = len(basis[0])
    act = {}
    for g in ELEMS:
        AB = mmul(ambient.act[g], basis)
        act[g] = in_col_span(basis, AB)
    return Mod(rank, act)


ALL_SUBGROUPS = []
_seen = set()
for _a in ELEMS:
    for _b in ELEMS:
        K = tuple(subgroup([_a, _b]))
        if K not in _seen:
            _seen.add(K)
            ALL_SUBGROUPS.append(K)


# ======================================================== 3. π|_H 与 M|_H
def pi_H_matrix():
    """π|_H : Z[H]^9 → I[H]（基 e_g = g − 1, g ≠ 1）。槽 b 中的 g ↦ g − b = e_g − e_b。"""
    basis_IH = [g for g in ELEMS if g != ID]
    pos = {g: i for i, g in enumerate(basis_IH)}
    M = zmat(len(basis_IH), N_H * N_H)
    for bi, b in enumerate(ELEMS):
        for gi, g in enumerate(ELEMS):
            col = bi * N_H + gi
            if g != ID:
                M[pos[g]][col] += 1
            if b != ID:
                M[pos[b]][col] -= 1
    return M


def mod_IH():
    """增广理想 I[H] ⊂ Z[H]，基 e_g := g − 1（g ≠ 1）。

    作用：h·(g − 1) = hg − h = e_{hg} − e_h（e_1 := 0）。
    注意**不是** h·e_g = e_{hg}——漏掉 −e_h 项会使 π|_H 不等变、上同调静默算错。
    """
    basis = [g for g in ELEMS if g != ID]
    pos = {g: i for i, g in enumerate(basis)}
    act = {}
    for h in ELEMS:
        A = zmat(len(basis), len(basis))
        for j, g in enumerate(basis):
            hg = gmul(h, g)
            if hg != ID:
                A[pos[hg]][j] += 1
            if h != ID:
                A[pos[h]][j] -= 1
        act[h] = A
    return Mod(len(basis), act)


def ginv(a):
    return ((-a[0]) % P, (-a[1]) % P)


def mod_diag_tensor():
    """Z[H] ⊗_Z Z[H]（对角作用 h·(x⊗y) = hx⊗hy），坐标按第二因子。
    坐标约定（与 prop:tensor-reg-ZH 的坐标式一致）：x⊗g ↦ 向量（槽 g 中放 x）。
    故 h 把「槽 b 中的 z_b」送到「槽 hb 中的 h·z_b」。"""
    act = {}
    for h in ELEMS:
        A = zmat(N_H * N_H, N_H * N_H)
        for bi, b in enumerate(ELEMS):
            hb = IDX[gmul(h, b)]
            for gi, g in enumerate(ELEMS):
                A[hb * N_H + IDX[gmul(h, g)]][bi * N_H + gi] += 1
        act[h] = A
    return Mod(N_H * N_H, act)


def build_MH():
    pi = pi_H_matrix()
    K = ker_basis(pi)
    MH = mod_on_submodule(mod_diag_tensor(), K)
    return MH, K, pi


# ======================================================== 4. 管线 A：Künneth
def tot_rank(n):
    return n + 1


def tot_diff(n):
    srcs = [(i, n - i) for i in range(n + 1)]
    tgts = [(i, n - 1 - i) for i in range(n)]
    tp = {t: k for k, t in enumerate(tgts)}
    out = {}
    for si, (i, j) in enumerate(srcs):
        terms = []
        if i >= 1:
            t = (i - 1, j)
            terms.append((tp[t], {X: 1, ID: -1} if i % 2 == 1 else {(k, 0): 1 for k in range(P)}))
        if j >= 1:
            t = (i, j - 1)
            s = (-1) ** i
            terms.append((tp[t], {Y: s, ID: -s} if j % 2 == 1 else {(0, k): s for k in range(P)}))
        out[si] = terms
    if STATE["corrupt"] and n == 2:
        # 判别力自证的负例：把 d_2 的首个生成元改成映到单位元（**真的**破坏复形：
        # d_1·d_2 ≠ 0）。仅变号是无害自同构，不能作负例。
        ti = out[0][0][0]
        out[0] = [(ti, {ID: 1})]
    return out


STATE = {"corrupt": False}


def tot_diff_matrix(n):
    r = mod_regular()
    A = zmat(tot_rank(n - 1) * N_H, tot_rank(n) * N_H)
    for si, terms in tot_diff(n).items():
        for ti, coeff in terms:
            M = r.act_coeff(coeff)
            for i in range(N_H):
                for j in range(N_H):
                    if M[i][j]:
                        A[ti * N_H + i][si * N_H + j] += M[i][j]
    return A


def hom_matrix(N, n):
    """Hom(Tot_{n−1}, N) → Hom(Tot_n, N) 的矩阵（列向量约定）。

    行按 Tot_n 的生成元 s 索引，列按 Tot_{n−1} 的生成元 t 索引：
        ψ_s = φ(d_n(s)) = Σ_t (coeff_{t,s})·φ(t)。
    （写成转置会使 δ∘δ ≠ 0，上同调静默算错。）
    """
    A = zmat(tot_rank(n) * N.rank, tot_rank(n - 1) * N.rank)
    for si, terms in tot_diff(n).items():
        for ti, coeff in terms:
            M = N.act_coeff(coeff)
            for i in range(N.rank):
                for j in range(N.rank):
                    if M[i][j]:
                        A[si * N.rank + i][ti * N.rank + j] += M[i][j]
    return A


def cohomology_A(N, q):
    """h^q(H, N) 的不变因子（管线 A）。"""
    K = ker_basis(hom_matrix(N, q + 1))
    I = zmat(N.rank, 0) if q == 0 else im_basis(hom_matrix(N, q))
    return quotient_invariants(K, I)


def resolution_exactness(maxdeg=4):
    """逐度校验 Tot 复形正合。**两条都要**（秩和相等**不蕴含**复形）：

    ① 复形条件 d_n · d_{n+1} = 0；
    ② 秩和条件 rank d_n + rank d_{n+1} = rank Tot_n（⟹ im = ker）。
    """
    dm = {n: tot_diff_matrix(n) for n in range(1, maxdeg + 1)}
    rk = {n: mrank(dm[n]) for n in range(1, maxdeg + 1)}
    out = []
    for n in range(1, maxdeg):
        z = mmul(dm[n], dm[n + 1])
        zero_ok = all(x == 0 for row in z for x in row)
        rank_ok = (rk[n] + rk[n + 1] == tot_rank(n) * N_H)
        out.append((n, zero_ok and rank_ok, rk[n], rk[n + 1], tot_rank(n) * N_H))
    return out


# ======================================================== 5. 管线 B：非齐次上链复形
def tuples_of(k):
    if k == 0:
        return [()]
    return list(itertools.product(ELEMS, repeat=k))


def act_vec(N, g, v):
    A = N.act[g]
    return [sum(A[i][j] * v[j] for j in range(N.rank)) for i in range(N.rank)]


def cochain_diff(k, u, v, N):
    """d^k 作用在「k-元组 u 处取值 v、别处为 0」的基向量 f 上。

    穷举全部输出 (k+1)-元组 g，按公式求值：
      d^k f(g_0..g_k) = g_0·f(g_1..g_k) + Σ_{i=1..k}(−1)^i f(..,g_{i−1}g_i,..)
                        + (−1)^{k+1} f(g_0..g_{k−1})
    返回 {输出元组: 值向量}（只留非零）。
    """
    r = len(v)
    out = {}
    for g in tuples_of(k + 1):
        val = None

        def add(w):
            nonlocal val
            val = w if val is None else [val[j] + w[j] for j in range(r)]

        if g[1:] == u:                                  # 第 1 项
            add(act_vec(N, g[0], v))
        for i in range(1, k + 1):                       # 第 i 项（i = 1..k）
            arg = g[:i - 1] + (gmul(g[i - 1], g[i]),) + g[i + 1:]
            if arg == u:
                s = (-1) ** i
                add([s * x for x in v])
        if g[:-1] == u:                                 # 末项
            s = (-1) ** (k + 1)
            add([s * x for x in v])
        if val and any(val):
            out[g] = val
    return out


def cochain_matrix_B(N, k):
    """d^k: C^k → C^{k+1} 的整数矩阵（C^k 的基 = 元组 × N 的基）。"""
    r = N.rank
    S, T = tuples_of(k), tuples_of(k + 1)
    row = {t: i for i, t in enumerate(T)}
    col = {t: i for i, t in enumerate(S)}
    A = zmat(len(T) * r, len(S) * r)
    for t in S:
        for vi in range(r):
            e = [0] * r
            e[vi] = 1
            for tgt, vec in cochain_diff(k, t, e, N).items():
                for j in range(r):
                    if vec[j]:
                        A[row[tgt] * r + j][col[t] * r + vi] += vec[j]
    return A


def cohomology_B(N, q):
    """h^q(H, N)（管线 B，与 A 无共享构造）。q ≤ 2 且 N 的秩不宜过大
    （C^3 的规模 = 729·rank(N)，本函数只对 rank(N) ≤ 9 实用）。"""
    K = ker_basis(cochain_matrix_B(N, q))
    I = zmat(N.rank, 0) if q == 0 else im_basis(cochain_matrix_B(N, q - 1))
    return quotient_invariants(K, I)


# ======================================================== 6. 读数
def reading_R1():
    return cohomology_A(mod_IH(), 1)


def reading_R2():
    MH, _, _ = build_MH()
    return cohomology_A(MH, 2)


def reading_R3():
    return cohomology_A(mod_trivial(), 2)


def reading_R4():
    return [(K, cohomology_A(mod_perm(K), 2)) for K in ALL_SUBGROUPS]


def reading_R5():
    return cohomology_A(mod_dsum([mod_dsum([mod_regular()] * 8), mod_trivial()]), 2)


def reading_R6():
    MH, K, pi = build_MH()
    return {"pi_rank": mrank(pi), "ker_rank": len(K[0]) if K else 0, "MH_rank": MH.rank}


# ======================================================== 7. 判别力自证（L43）
def selftest(verbose=True):
    res = []

    def chk(name, got, want):
        ok = (got == want)
        res.append((name, ok, got, want))
        if verbose:
            print("  %s %-46s 得 %-14s 期望 %s" % ("✓" if ok else "✗", name, got, want))
        return ok

    print("[自证 P] 正例：经典已知值（管线 A）")
    chk("h^0(H,ℤ) = ℤ", fmt_group(cohomology_A(mod_trivial(), 0)), "ℤ")
    chk("h^1(H,ℤ) = 0", fmt_group(cohomology_A(mod_trivial(), 1)), "0")
    chk("h^2(H,ℤ) = C_3 × C_3", fmt_group(cohomology_A(mod_trivial(), 2)), "C_3 × C_3")
    chk("h^1(H,ℤ[H]) = 0（Shapiro）", fmt_group(cohomology_A(mod_regular(), 1)), "0")
    chk("h^2(H,ℤ[H]) = 0（Shapiro）", fmt_group(cohomology_A(mod_regular(), 2)), "0")

    print("[自证 Q] 正例：管线 B 与 A 在此三处应一致（互不共享构造）")
    chk("B: h^1(H,ℤ) = 0", fmt_group(cohomology_B(mod_trivial(), 1)), "0")
    chk("B: h^2(H,ℤ) = C_3 × C_3", fmt_group(cohomology_B(mod_trivial(), 2)), "C_3 × C_3")
    chk("B: h^1(H,I[H]) = C_9", fmt_group(cohomology_B(mod_IH(), 1)), "C_9")

    print("[自证 N1] 负例：腐蚀 Tot 的 d_2 ⟹ 正合性检查必须判不过")
    STATE["corrupt"] = True
    bad = resolution_exactness(3)
    STATE["corrupt"] = False
    chk("腐蚀后正合性检查判不过", all(ok for (_, ok, _, _, _) in bad), False)
    chk("未腐蚀时正合性检查判过", all(ok for (_, ok, _, _, _) in resolution_exactness(3)), True)

    print("[自证 N2] 负例：判别对必须分开（置换型模不得给出 C_9）")
    chk("h^2(H,ℤ[H]) ≠ C_9（置换型）", fmt_group(cohomology_A(mod_regular(), 2)) == "C_9", False)
    chk("h^2(H,8ℤ[H]⊕ℤ) = C_3 × C_3 ≠ C_9", fmt_group(reading_R5()), "C_3 × C_3")

    nfail = sum(1 for (_, ok, _, _) in res if not ok)
    if verbose:
        print("  —— 自证：%d/%d 通过%s" % (len(res) - nfail, len(res),
                                      "" if nfail == 0 else "  ⟹ 读数不得取用（L19/L43）"))
    return nfail == 0, res


# ======================================================== 8. 证书输出
def cert_entry(name, M, note="", full_limit=4000):
    """给一个整数矩阵出具 Smith 证书：U·M·V = D，|det U| = |det V| = 1。"""
    U, D, V = snf(M)
    ok_uvd, ok_u, ok_v = snf_check(M, U, D, V)
    diag = [D[i][i] for i in range(min(len(D), len(D[0])))]
    entry = {
        "name": name,
        "note": note,
        "shape": [len(M), len(M[0]) if M else 0],
        "U·M·V=D 成立": bool(ok_uvd),
        "det U = ±1": bool(ok_u),
        "det V = ±1": bool(ok_v),
        "D 对角": diag,
    }
    if len(M) * len(M[0]) <= full_limit:
        entry["U"] = U
        entry["V"] = V
    else:
        import hashlib
        import json as _json
        h = hashlib.sha256(_json.dumps([M, U, D, V]).encode()).hexdigest()
        entry["(U,V) 规模过大，仅给摘要"] = h[:32]
    return entry


def run_all(emit_cert=True, out_path=None):
    """跑全部读数；返回 (结果字典, 证书字典)。"""
    certs = {}
    out = {}

    exact = resolution_exactness(3)
    out["Tot 正合性（3 度）"] = "全部度通过" if all(ok for (_, ok, _, _, _) in exact) else "有度失败"

    r6 = reading_R6()
    out["R6 π 秩 / ker 秩 / M|_H 秩"] = "%d / %d / %d" % (r6["pi_rank"], r6["ker_rank"], r6["MH_rank"])
    if emit_cert:
        certs["pi|_H"] = cert_entry("π|_H : ℤ[H]^9 → I[H]（prop:procesi-H）", pi_H_matrix(),
                                    "秩 8 ⟹ 满射；其核即 M|_H")

    out["R1 h^1(H, I[H])"] = fmt_group(reading_R1())
    if emit_cert:
        certs["R1"] = cert_entry("d^2 : Hom(Tot_1)→Hom(Tot_2)（h^1 的分母）", hom_matrix(mod_IH(), 2),
                                 "ker/im = C_9")
    out["R2 h^2(H, M|_H)"] = fmt_group(reading_R2())
    out["R3 h^2(H, ℤ)"] = fmt_group(reading_R3())
    if emit_cert:
        certs["R3"] = cert_entry("d^3 : Hom(Tot_2)→Hom(Tot_3)（h^2 的分子）", hom_matrix(mod_trivial(), 3),
                                 "ker/im = C_3 × C_3")
    out["R4 h^2(H, ℤ[H/K])，K 遍历子群"] = "; ".join(
        "|K|=%d: %s" % (len(K), fmt_group(v)) for K, v in reading_R4())
    out["R5 h^2(H, 8ℤ[H] ⊕ ℤ)"] = fmt_group(reading_R5())
    if emit_cert:
        certs["R5"] = cert_entry("d^2 : Hom(Tot_1)→Hom(Tot_2)（8ℤ[H]⊕ℤ）",
                                 hom_matrix(mod_dsum([mod_dsum([mod_regular()] * 8), mod_trivial()]), 2),
                                 "ker/im = C_3 × C_3")

    # 交叉：管线 B 在可行处独立复核
    out["B 交叉 h^1(H, ℤ)"] = fmt_group(cohomology_B(mod_trivial(), 1))
    out["B 交叉 h^2(H, ℤ)"] = fmt_group(cohomology_B(mod_trivial(), 2))
    out["B 交叉 h^1(H, I[H])"] = fmt_group(cohomology_B(mod_IH(), 1))

    if out_path:
        import json
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump({"读数": out, "证书": certs}, f, ensure_ascii=False, indent=1)
        print("\n证书已写入 %s" % out_path)
    return out, certs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true", help="只跑判别力自证")
    ap.add_argument("--out", help="写证书文件（JSON）")
    a = ap.parse_args()

    print("== ABGV-5.2 A 档机器证书（T0/T1；双管线 ╱ 判别力自证 L43）==")
    print("\n[1] 判别力自证")
    ok, _ = selftest()
    if not ok:
        print("自证不过 ⟹ 退码 2，读数不得取用")
        return 2
    if a.selftest:
        return 0

    print("\n[2] 全部读数")
    out, _ = run_all(emit_cert=True, out_path=a.out)
    for k, v in out.items():
        print("  %-32s %s" % (k, v))

    print("\n[3] 与稿件的对照")
    exp = [("R1 h^1(H, I[H])", "C_9"), ("R2 h^2(H, M|_H)", "C_9"),
           ("R3 h^2(H, ℤ)", "C_3 × C_3"), ("R5 h^2(H, 8ℤ[H] ⊕ ℤ)", "C_3 × C_3")]
    allok = True
    for k, want in exp:
        got = out[k]
        okk = (got == want)
        allok = allok and okk
        print("  %s %-26s 得 %-14s 稿件 %s" % ("✓" if okk else "✗", k, got, want))
    print("  %s R6 秩三元组" % ("✓" if out["R6 π 秩 / ker 秩 / M|_H 秩"] == "8 / 73 / 73" else "✗"))
    print("  %s R4 指数整除 3（逐子群）" % ("✓" if all(
        set(v) <= {0, 1, 3} for _, v in reading_R4()) else "✗"))
    print("\n全部对照：%s" % ("通过" if allok else "有失败"))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
