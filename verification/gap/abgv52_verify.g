# GAP 4.11.1 with HAP 1.30
LoadPackage("HAP");;

p := 3;;  # change to 5 for p=5 verification
H := DirectProduct(CyclicGroup(p), CyclicGroup(p));;
elts := ShallowCopy(Elements(H));;
n := Size(H);;
one := Identity(H);;
idx := NewDictionary(one, true);;
for i in [1..n] do AddDictionary(idx, elts[i], i); od;;
pos := h -> LookupDictionary(idx, h);;

BuildCochains := function(A_elts, r)
    local n_, d0, d1, gi, hi, g, h, gh, r0, ch, cgh, cg, j, k;
    n_ := Length(A_elts);
    d0 := NullMat(r * n_, r, Integers);;
    for gi in [1..n_] do
        for j in [1..r] do
            d0[(gi-1)*r + j] := A_elts[gi][j] - IdentityMat(r, Integers)[j];;
        od;
    od;
    d1 := NullMat(r * n_ * n_, r * n_, Integers);;
    for gi in [1..n_] do
        for hi in [1..n_] do
            g := elts[gi]; h := elts[hi]; gh := g * h;;
            r0 := ((gi-1)*n_ + (hi-1)) * r + 1;;
            ch := (hi-1)*r + 1;;
            cgh := (pos(gh)-1)*r + 1;;
            cg := (gi-1)*r + 1;;
            for j in [1..r] do for k in [1..r] do
                if A_elts[gi][j][k] <> 0 then
                    d1[r0+j-1][ch+k-1] := d1[r0+j-1][ch+k-1]
                        + A_elts[gi][j][k];;
                fi;
            od; od;
            for j in [1..r] do
                d1[r0+j-1][cgh+j-1] := d1[r0+j-1][cgh+j-1] - 1;;
                d1[r0+j-1][cg+j-1]  := d1[r0+j-1][cg+j-1] + 1;;
            od;
        od;
    od;
    return rec(d0 := d0, d1 := d1);
end;;

RankIntMat := function(M)
    local s, d, i;
    s := SmithNormalFormIntegerMat(M);;
    d := Minimum(DimensionsMat(s));;
    i := 0; while i < d and s[i+1][i+1] <> 0 do i := i + 1; od;
    return i;
end;;

Print("|H| = ", n, "\n\n");

A_ZH := [];;
for g in elts do
    mat := NullMat(n, n, Integers);;
    for i in [1..n] do mat[pos(g * elts[i])][i] := 1; od;
    Add(A_ZH, mat);;
od;
CC_ZH := BuildCochains(A_ZH, n);;
rk_d0_ZH := RankIntMat(CC_ZH.d0);;
rk_d1_ZH := RankIntMat(CC_ZH.d1);;
dimC1_ZH := n * n;;
dimKer_d1_ZH := dimC1_ZH - rk_d1_ZH;;
h1_ZH_free := dimKer_d1_ZH - rk_d0_ZH;;

Print("Z[H]  (Z-rank ", n, "):\n");
Print("  d^0: ", DimensionsMat(CC_ZH.d0)[1], " x ", DimensionsMat(CC_ZH.d0)[2],
      "  rank = ", rk_d0_ZH, "\n");
Print("  d^1: ", DimensionsMat(CC_ZH.d1)[1], " x ", DimensionsMat(CC_ZH.d1)[2],
      "  rank = ", rk_d1_ZH, "\n");
Print("  dim(C^1) = ", dimC1_ZH, ",  dim(ker d^1) = ", dimKer_d1_ZH, "\n");
Print("  H^1 free rank = dim(ker d^1) - rank(d^0) = ", h1_ZH_free, "\n");
if h1_ZH_free <> 0 then Print("  *** UNEXPECTED ***\n"); fi;
Print("\n");

nonid := Filtered(elts, h -> h <> one);;
r_IH := Length(nonid);;
A_IH := [];;
for g in elts do
    mat := NullMat(r_IH, r_IH, Integers);;
    for j in [1..r_IH] do
        if g * nonid[j] <> one then
            mat[pos(g*nonid[j])-1][j] := mat[pos(g*nonid[j])-1][j] + 1;
        fi;
        if g <> one then
            mat[pos(g)-1][j] := mat[pos(g)-1][j] - 1;
        fi;
    od;
    Add(A_IH, mat);;
od;
CC_IH := BuildCochains(A_IH, r_IH);;
rk_d0_IH := RankIntMat(CC_IH.d0);;
rk_d1_IH := RankIntMat(CC_IH.d1);;
dimC1_IH := r_IH * n;;
dimKer_d1_IH := dimC1_IH - rk_d1_IH;;
h1_IH_free := dimKer_d1_IH - rk_d0_IH;;

Print("I[H]  (Z-rank ", r_IH, "):\n");
Print("  d^0: ", DimensionsMat(CC_IH.d0)[1], " x ", DimensionsMat(CC_IH.d0)[2],
      "  rank = ", rk_d0_IH, "\n");
Print("  d^1: ", DimensionsMat(CC_IH.d1)[1], " x ", DimensionsMat(CC_IH.d1)[2],
      "  rank = ", rk_d1_IH, "\n");
Print("  dim(C^1) = ", dimC1_IH, ",  dim(ker d^1) = ", dimKer_d1_IH, "\n");
Print("  H^1 free rank = dim(ker d^1) - rank(d^0) = ", h1_IH_free, "\n");
if h1_IH_free <> 0 then Print("  *** UNEXPECTED ***\n"); fi;
Print("  augmentation coker = Z / ", n, "Z\n\n");

R := ResolutionFiniteGroup(H, 3);;
C := HomToIntegers(R);;
h2_Z := Cohomology(C, 2);;
Print("H^2(H, Z_triv) = ", h2_Z, "\n");
if h2_Z <> [p, p] then Print("*** UNEXPECTED: ", h2_Z, " ***\n"); fi;
Print("\n");

Print("Summary of computed results:\n");
Print("  H^1(H, Z[H])      free rank = ", h1_ZH_free, "\n");
Print("  H^2(H, Z[H])      = 0  (Shapiro: Ind_1^H Z)\n");
Print("  H^1(H, I[H])      free rank = ", h1_IH_free,
      ",  torsion ~= Z/", n, "Z\n");
Print("  H^2(H, Z_triv)    = ", h2_Z, "\n");
Print("  H^1(H, Z[H]^9)    = 0  (additivity)\n");
Print("  H^2(H, Z[H]^9)    = 0  (additivity)\n\n");

Print("Procesi LES:  0 -> H^1(I[H]) -> H^2(M|_H) -> 0\n");
Print("  =>  H^2(H, M|_H) ~= H^1(H, I[H]) ~= Z/", n, "Z\n");
Print("  =>  exp H^2(M|_H) = ", n, "\n");
QUIT;

# non-interactive use
QUIT;
