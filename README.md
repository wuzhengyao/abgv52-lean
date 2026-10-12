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
| `P1`--`P6` (with `P5a`, `P5b`), `PThm`, `PChallenge` | p-general lattice and theorem statements, with an independent restatement |
| `G1b`--`G4`, `GThm`, `GChallenge` | the geometric-identification reduction layer (named-hypothesis transport) |
| `MH`, `MQ`, `MI`, `BR` | the rational model of the Procesi kernel and the base-change bridge |
| `F1`, `R1`, `PC2`, `FaithfulMH` | faithfulness of the action, retract-rationality wiring, permutation-class lemma, faithfulness obstruction |
| `EM_ABGV52`, `Saltman_ABGV52`, `Procesi_ABGV52` | the three named hypotheses (`EMHyp`/`EMHypP`, `SaltmanHyp`, `ProcesiHyp`) with definitional-shape locks, wiring theorems, and non-vacuity probes |
| `EMArtin`, `EMTrans`, `EMSpeiser`, `EMSemilinear`, `EMRational`, `EMFixed`, `EMDegree`, `EMIndep`, `EMRouteS`, `EMBridge`, `EMConsume` | the proof layers behind the criterion: Artin's fixed-field theorem, invariant transport, Speiser's theorem, the semilinear machinery, Lenstra's (1.4), the degree chain, algebraic independence, and the assembly of the converse |
| `EM1betaGen_*` | the permutation-lattice rationality engine (character-basis layer, monomial lattice, rationality closure, consumption) with a non-vacuity probe |
| `EMQuasi`, `EMCounter`, `ExtBridge`, `ExtLES`, `ExtMH`, `ExtMHUncond`, `ProbeLES1`, `ProbeLES2`, `S2b` | the criterion-clearing track: the corrected quasi-permutation form of the criterion with its cohomological refutation witness, the machine-checked counterexample to the original form, and the Ext^1 machinery with its unconditional closure |
| `SaltDef`, `SaltT2`, `SaltSwan`, `SaltCor`, `SaltCond`, `SaltGeneric`, `SaltRatOver` | the Saltman-track layers: the 1984 definitions, the rational-to-retract bridge, Swan's lemma, the corollary/reduction pair, the 2-power/cyclotomic condition layer, the named generic-object residual (which now also carries the source's two existence theorems -- theorem 2.1 of the 1982 paper, and its theorem 5.1 via Noether's construction, with rationality over the base field defined and the fixed field of a group action used for its hypothesis -- as named statements, with the witness of existence packaged, the pages of the 1982 paper actually cited by the 1984 text census-completed, rationality over the base field given a non-vacuity probe, and the source's Noether action built on the polynomial ring and carried to its fraction field with source-faithful locks and a faithfulness probe), the opening of the 1982 paper's lemma 5.2 (the product of the conjugates of a polynomial is invariant, its evaluation lands in the fixed points, the evaluation itself being equivariant so that the statement carries no extra hypothesis, the nonvanishing of that product transfers to the polynomial itself, which is the source's unit clause, and the determinant of the coordinate matrix of the conjugates is characterised as the criterion for those conjugates to be independent in the field itself, the transport from coordinates to vectors being carried by the definition of linear independence as injectivity of the finitely supported linear combination, the determinant then exhibited as an honest polynomial in the coordinates, the infinite-field step that two nonzero polynomials share a nonvanishing point, through the bridge that reads the group action as algebra automorphisms, the abstract normal basis theorem together with the nonvanishing of that polynomial, the carrier of the companion polynomial for the conjugates together with the identity identifying its values with the evaluation of the source polynomial at the conjugates, and the derivation of finite-dimensionality from the basis, and closing the paper's determinant argument end to end, the last hypothesis then removed by two further steps: first, that a polynomial over the field which vanishes at every point with coordinates in the base field is zero, which frees the avoidance step from having to be run on base-field coefficients, and second, the algebraic independence of the conjugates, in the form that the linear substitution attached to them is injective, proved from Dedekind's independence of the algebra homomorphisms through the invertibility of the matrix of the conjugates of a basis and the inverse substitution that matrix supplies) with that lemma's nonvanishing recorded as a theorem rather than as a hypothesis, the first step of the source's proof of theorem 5.1 formalized as well -- from rationality of a field over the ground field one extracts a transcendence basis, as an algebraically independent family generating the field, the generating half proved for the fraction field directly and then transported along the isomorphism, which keeps the algebraicity transfer across an algebra equivalence out of the proof, the interface between that extraction and the descent proposition then supplied by the fraction form of the generated subalgebra -- every element of the field being a quotient of two elements of it, proved by structural induction on the field adjunction and recorded also in the multiplication form needed to clear denominators, with the bridge to the library's transcendence basis predicate registered together with the inference failure that blocks it, the clearing of denominators then carried out for a finite family -- the single multiplier being the product of the denominators, its nonvanishing coming from the no-zero-divisor instance on a subalgebra of a field, and the finite form specialized to the generated-field setting so that it consumes the fraction form directly, and the same clearing for a finitely generated algebra, where the single multiplier is the product of the denominators of a finite generating set and the powers are tracked through the generators, the ground field, sums and products, with the generated-field specialization of that form supplied as well, and the cleared elements then placed inside the localization at that single element, taken as the subalgebra generated by the inverse of the multiplier, so that the image of the finitely generated algebra lands where the source requires it, and the transcendence basis predicate of the library reached as well, by proving that the generated subalgebra is algebraic over the field, which together with algebraic independence yields that predicate, so that the extraction of rationality now produces the library's own notion, and the localization at a single element made an explicit carrier inside the field, containing the ground ring and finitely generated over it, into which the finitely generated algebra's structure map factors, the subalgebra generated by an algebraically independent family then identified with a polynomial ring and shown finitely generated over the ground field, with a map from the abstract localization back into the field supplied by its universal property, and the elements of that localization written with a common denominator as powers of the multiplier, the powers of the multiplier shown to lie in the nonzero divisors so that the library's localization subalgebra applies, and that subalgebra identified with the one generated by the inverse of the multiplier, which is thereby a localization and isomorphic to the abstract one, localizations being transported along an isomorphism of the base rings, and the resulting identification of the localized subalgebra with a localized polynomial ring assembled -- and retract rationality along rational extensions |
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

## Coverage update (2026-10-12, appended)

The table above reflects the state of 2026-10-10.  The development has since grown to **122 Lean
files**, with the mirror, `SHA256SUMS` (122 lines) and the crosscheck gate (122-item table) all in
sync.  The items added since then are:

- `BaseChangeProj_ABGV52.lean`: the base-change statement `hBC` (the source's `proposition-0-2(d)`)
  in the orientation the use site needs, `S' = T ⊗_R S`.  It proves the crossed-product base change
  `SkewMonoidAlgebra S G ⊗[R] T ≃ₗ SkewMonoidAlgebra (T ⊗_R S) G` with its generator formula, the
  endomorphism base change `(S →ₗ[R] S) ⊗[R] T ≃ₗ (T ⊗_R S →ₗ[T] T ⊗_R S)` (using finite
  projectivity through `rTensorHomEquivHomRTensor`, `LinearMap.ringLmapEquivSelf` and
  `AlgebraTensorModule.lift.equiv`), the target-orientation action layer, the fixed-subring clause in
  that orientation, the linearity of the crossed-product map, the commutativity of that map with the
  two base-change isomorphisms, and the resulting bijectivity: the third clause of the base-change
  statement.  Two registrations are recorded in the file: the source's `GaloisBaseChangeHyp` is false
  as stated for degenerate coefficient rings (a counterexample with `Z[i]/Z` and `G = C2`), and the
  hypothesis slot that quantifies over *every* action satisfying `hR'G` is not inhabitable (the
  trivial action satisfies `hR'G` but fails faithfulness), so the usable form pins the action by the
  canonicality equation `g • (1 ⊗ x) = 1 ⊗ (g • x)`.
- `GenericExtension_ABGV52.lean`: definition 1.1, the `E(G)`-slice language (realization property,
  representing and generic objects, the lifting property).  The file carries two transcriptions of
  definition 1.1 -- the three clauses listed flat, and the `E(G)`-slice reading as a representing
  object whose ring is a localized polynomial ring -- and a lock records that the two are the same
  predicate up to the order of the conjunction.  The printed page of the source is PDF page plus
  249, re-verified here against the printed 254 on PDF 5; the Lifting property for generic objects
  (Saltman's Proposition 1.1(a), whose source proof is omitted) and its `_strong`, `_stronger` and
  `_strongest` variants.  `_strongest` proves the statement with *no* base-change hypothesis at all:
  the step that consumed it now constructs the Galois structure on `T ⊗_R S` directly.  The earlier
  variants keep their original statements but have an uninhabited base-change hypothesis, so
  downstream steps must be wired to `_strongest`.
- `GaloisAlgebra_ABGV52.lean`: besides the Galois-algebra criterion, the file registers the source's
  `proposition-0-2(a)` as a named external input (`GaloisProjectiveHyp`: a `G`-Galois `S/R` has `S`
  finitely generated and projective over `R`), the use-site form of the source's `[CHR68] p. 13`
  projectivity statement (`GaloisProjectiveSectionHyp`: a `G`-equivariant `R`-linear surjection onto
  a `G`-Galois `S'` has a `G`-equivariant section), and the missing half of the fixed-subring clause
  (`GaloisFixedSubringHyp`: `S^G ⊆ R`), each with a type lock, a data-level non-vacuity probe and a
  gap registration, following the precedent of the Fischer interface.  The use sites
  `exists_galoisProjectiveSection` and `exists_algebraMap_of_invariant` extract the section and the
  fixed-subring clause from those inputs.  The same file now also registers the source's
  `proposition-0-2(b)` (`Prop02bStatement`: the vanishing of the first cohomology of the units, encoded as crossed homomorphisms being principal, with the zero-Picard hypothesis abstract, that encoding shown coherent by deriving the crossed relation from principality, and the conclusion instantiated for the trivial group over the rationals) and `proposition-0-2(c)` (`GaloisDescentHyp`): for a `G`-Galois `S/R` and an `F`-subalgebra `R' ⊆ R`
  there are `F`-algebras `R''` finitely generated over `R'`, with `R' → R'' → R` a tower, and a
  `G`-Galois `R''`-algebra `S''` with `S` isomorphic to `S'' ⊗_{R''} R`; the encoding is single-universe
  throughout, the source is quoted rather than proved (it is one of the four results the source cites
  from the literature), the type lock, data-level non-vacuity probe and gap registration follow the
  same pattern, and `exists_galoisDescent` is the use-site form wanted by the proof of theorem 5.1.
  Three of the four parts of `proposition-0-2` are now in the library; part (b), on the vanishing of
  `H^1(G, S^*)`, is not.
- `SaltLem12_ABGV52.lean`: the `F₊[V]` layer for the blueprint's `lem1.2` — the action of `g` on `V`
  as an `F`-linear equivalence, the induced `F`-algebra automorphism of the symmetric algebra with
  its generator compatibility `ι v ↦ ι (g • v)`, the assembled `MulSemiringAction` on `F₊[V]`, the
  invariant subalgebra `F₊[V]^G` (built by hand because mathlib has no `FixedPoints`), the lifting
  core (an `F`-linear section of a map `S → S'` lifts every algebra map `F₊[V] → S'`), and the
  equivariance of that lift: when the section and the algebra map are `G`-equivariant and the action
  on `S` commutes with the `F`-scalars, the lifted map is `G`-equivariant as well, proved on
  generators from generator compatibility and closed by `SymmetricAlgebra.algHom_ext`.  The
  object-level statement `IsProjectiveObjectSymmetric` (single-universe, with a type lock) is then
  *proved*, not merely stated, by `isProjectiveObjectSymmetric_of_galoisHyps` from the two named
  inputs above: the lifting theorem plus equivariance, and the fixed-subring clause — the blueprint's
  step 9 `lem1.2`, modulo those two registered inputs.
- `SaltLocalProj_ABGV52.lean`: the *local* layer for the blueprint's step 10, Saltman's
  `thm1.3(a)(c)`.  The source's notion of a *local* morphism (`φ⁻¹(S*) = R*`, the preimage of every
  unit is a unit) is mathlib's `IsLocalHom`, so no new term is introduced; a discriminating witness
  shows the condition is genuine: localizing `ℚ[X]` at `X` turns the non-unit `X` into a unit, so the
  canonical map `ℚ[X] → ℚ[X](1/X)` is *not* `IsLocalHom` — exactly the gap between "surjective" and
  "local surjective" that step 10 turns on.  On top of that the file gives the local-projective
  object statement `IsLocalProjectiveSymmetric` (same shape as the step-9 statement, with the map
  required to be a local surjection), proves that projectivity implies local projectivity, feeds it
  the two named inputs of step 9, and proves the kernel of the source's step (a): the lift of a map
  whose value at the localizing element `s` is a unit again sends `s` to a unit, because the
  surjection is local.  The file also proves the sentence that opens the source's proof of (a) —
  that a map out of `M ⊗_R R(1/s)` exists exactly when it inverts `s` — in the abstract commutative
  case: `isUnit_algebraMap_tensor_away` (the scalar `s` is a unit in `M ⊗_R R(1/s)`),
  `exists_tensor_away_lift` (a map inverting `s` factors through the localization, by
  `IsLocalization.liftAlgHom` and `Algebra.TensorProduct.productMap`) and the resulting equivalence
  `exists_tensor_away_lift_iff`.  Uniqueness of that factorization is not claimed, since the source's
  argument uses only existence.  The file then carries out the descent of the `G`-action to the
  localization, so that the source object of step 10(c) becomes an object of the slice: for a
  `G`-invariant `s`, `Localization.Away s` carries a `MulSemiringAction` (`locMulSemiringAction`,
  with the use point `symLocMulSemiringAction` for `S = F₊[V](1/s)`).  The action is defined through
  the universal property (`locActBase`, `locActAlgHom`) and its laws are proved by `algHom_ext`
  rather than by comparing localization equivalences.  Finally the file assembles step 10(c)
  (`exists_localized_lift_of_isLocalProjectiveSymmetricLocalized`): given the de-localized form of
  local projectivity, a local surjection and a `G`-equivariant map out of `F₊[V](1/s)` can be lifted
  along it, with the base invariants `F₊[V]^G` mapped into `R`; the compatibility of the localization
  map with the action (`symLocMulSemiringAction_algebraMap`) is what links the two sides.  One
  difference from the source is registered: the invariant clause is asserted only for the image of
  `F₊[V]^G`, not for every `G`-invariant of `F₊[V](1/s)`.  The identification of those invariants is
  also proved (`exists_symInvariants_fraction_of_fixed`): for a `G`-invariant `s`, every `G`-invariant
  element of `F₊[V](1/s)` is a fraction whose numerator *and denominator* lie in `F₊[V]^G`, with the
  use point `exists_symInvariants_fraction_of_fixed_away` for the action of the previous paragraph.
  The finiteness of `G` enters here, through a maximum over the group; the argument needs no Galois
  hypothesis.  The conclusion is deliberately stated as a fraction rather than as membership in the
  image of `F₊[V]^G`, which would be false in general.
- The same file closes step 10(c) in the form the source uses
  (`exists_localized_lift_equivariant_of_galoisHyps`): from the two named inputs, a local surjection
  and a `G`-equivariant map out of `F₊[V](1/s)` have a lift that is again `G`-equivariant, and the
  invariant clause then covers *every* `G`-invariant element, not only the image of `F₊[V]^G`.  The
  proof differs from the earlier, weaker assembly in one place: it uses the equivariant lifting core
  `symLift_core_equivariant` of the step-9 file instead of an existential de-localized hypothesis, so
  the equivariance survives to the localization.  The `G`-action on the localization is carried as an
  instance parameter with its compatibility with the localization map; the `G`-invariance of `s`
  itself is needed only to *construct* that action and does not appear among the hypotheses.  The use
  point `exists_localized_lift_equivariant_of_galoisHyps_away` instantiates it for that action.
- The Saltman-track layers `SaltDef`, `SaltT2`, `SaltSwan`, `SaltCor`, `SaltCond`, `SaltGeneric`,
  `SaltRatOver`, `SaltLocalProj`, `SaltLocalLift`, `SaltThm38`, `SaltClass` carry the 1984
  definitions, the
  rational-to-retract bridge, Swan's lemma, the corollary/reduction pair, the 2-power condition
  layer, the named generic-object residual, retract rationality along rational extensions, the
  local-projective layer of step 10, and the local-lifting layer of §3.  The last of these states
  the lifting property of `thm3.9(ii)` (a local `F`-algebra is an `IsLocalRing`, the residue field
  is its `IsLocalRing.ResidueField` and the canonical map is `IsLocalRing.residue`), proves the unit
  criterion of a local ring that the source's argument needs, and proves the easy direction of
  `thm3.9` — rationally factoring maps lift along residue maps — by the source's own construction.
  The file also supplies the affineness layer that the converse needs (a finitely generated algebra
  is a quotient of a polynomial ring, with prime kernel and the quotient identified), and it registers
  a statement-completeness finding checked against the printed paper: the statement of `thm3.9` omits
  the affineness of `S` and of `R(1/r)` although its proof uses both, while `thm3.8` on the same page
  does say "affine".  Two further pieces of the converse are in place: the field case (over a field the
  residue map is injective, so the lifting property gives an honest lift of every map out of `R(1/r)`
  into a field), and the two identifications the printed proof names — `F[x]_P` is
  `Localization.AtPrime` and its residue field is the fraction field of `F[x]/P`, which is how the
  proof reads off `T/M = K`.  The setup half of the converse is also there: localizing a domain at a
  non-zero element stays a domain, the residue map `R(1/r) → T/𝔪` of the proof is built from the
  quotient isomorphism and the fraction-ring structure, and applying the lifting property at
  `T = F[x]_P` produces the map `ψ : S → T` the proof needs.  The algebraic kernel of the refinement
  "`ψ(S) ⊆ F[x](1/w)` for some `w ∉ P`" is in place too: finitely many elements of a localization
  share a common denominator, and consequently a finitely generated subalgebra of a localization lies
  in a one-element localization, in the prime form `w ∉ P`.  The containment of the refinement is
  also cashed out as an interface: an algebra map whose image lies in the range of an injective
  one-element localization factors through it.  Alongside it sits the canonical map `A[1/w] -> A_P`
  (as the inclusion `F[x](1/w) inside F[x]_P` the proof uses) together with injectivity of the
  structure map into the localization at a prime over a domain, and also injectivity of that
  canonical map itself (for a domain `A`, a prime `P` and `w ∉ P`), which is what the refinement
  interface needs in order to be applied at `F[x]_P`.  The converse of `thm3.9` is now assembled:
  from the lifting property, an affine surjection onto `R(1/r)`, its prime kernel `P` and the map
  `ψ : S -> F[x]_P`, the finitely many images of a generating set of `S` share a denominator
  `w ∉ P`, the refinement interface produces `ψ' : S -> F[x](1/w)`, and the rational factorization
  is closed by mapping both sides into the residue field of `F[x]_P` — the localization
  `R(1/r₀) -> R(1/(r₀ c))` and the localization of `η₀` at `w` are constructed for that purpose.
  The finding above was likewise refined: affineness of `R` does *not* give affineness of `R(1/r)`,
  so the target must carry that hypothesis separately.  The equivalence of `thm3.8` is proved both in
  the relative form used by the source's own proof and in the quantified form of its statement: for a
  given affine subalgebra `S` with `K` its fraction field, `K/F` is retract rational exactly when `S`
  has the lifting property and its one-element localizations are affine; the subalgebra demanded by
  the quantified form is extracted from the retract-rationality witness itself, as its image in `K`.
- The section-1 language of the source is opened by `SaltClass_ABGV52.lean`: the structure
  `LinearStructure` of a tuple `<R, M, f_1, ..., f_r>`, whose `i`-th entry is an `R`-linear map
  `M^(s_i) -> M^(t_i)` between tensor powers of `M`, together with its *type*, the sequence of index
  pairs `(s_1, t_1), ..., (s_r, t_r)`.  Two definitional-shape locks pin the constructor and the
  type, and two probes exhibit the structure at `r = 0` and at `r = 1`, so the parameter domain is
  not empty at either end.  Two sentences were corrected against the printed page: page 169 reads
  `f_i : M^(s_i) -> M^(t_i)` and `g_i . psi^(s_i) = psi^(t_i) . f_i`, while the local TeX
  transcription drops the subscript `i` (leaving `M^(i) -> M^(i)` in the definition and
  `psi^(s) = psi^(s)` in the morphism condition, so that the right-hand superscript `t` is lost as
  well).  A reader of the TeX alone would therefore find the type of `f_i` contradicting the type
  sequence printed in the same sentence; the file follows the printed version.  The source's
  `M^(0) = R` is recorded as an
  isomorphism rather than a definitional equality, because mathlib's `TensorPower R 0 M` is the
  tensor product over the empty index type.  The same file now carries the morphisms of the source:
  the induced map `psi^(n) : M^(n) -> N^(n)` of a semilinear `psi`, with its value on generators, its
  identity case and its functoriality (the composition case has to be stated with the middle ring
  homomorphism of mathlib's `RingHomCompTriple` supplied explicitly, since only the identity cases of
  that class are registered); the homomorphism structure `Hom` of a pair `(phi, psi)` with `phi` a
  ring homomorphism, `psi` semilinear over it, and the preservation condition
  `g_i . psi^(s_i) = psi^(t_i) . f_i` of the printed page, together with its identity, its
  composition and the three composition laws, so that the structures of a fixed type do form a
  category; and the isomorphism structure `IsIso`, in which the base ring is common, `phi` is the
  identity and `psi` is a linear equivalence, with the forgetful map to `Hom`, the identity
  isomorphism, and the inverse isomorphism: an isomorphism is invertible in the category, because
  the inverse of a linear equivalence again satisfies the preservation condition.  That last step is
  proved pointwise, from the identity and functoriality cases of the induced map: if `P` and `Q` are
  the induced maps at `s_i` and at `t_i`, and `P'` and `Q'` their inverses, then
  `Q' (B y) = Q' (B (P (P' y))) = Q' (Q (A (P' y))) = A (P' y)`, where `A` and `B` are the two
  structure maps and `B . P = Q . A` is the preservation condition.  The same file carries the
  source's notion of an *`F` structure*, a linear structure over a ring containing `F`; because the
  closure properties of a class change the base ring, that notion is bundled, with the ring, the
  module and the structure travelling together, and it comes with two definitional-shape locks and
  three non-vacuity probes, one of them at an arbitrary base ring.  The base change
  `M (x)_phi S` of the source is also there: mathlib provides the `S`-module structure on the
  tensor product only with the algebra in the first factor, so the structure is transported along
  `TensorProduct.comm`, which keeps the factor order of the source; the induced map `f (x) 1` is
  then obtained by conjugating mathlib's `AlgebraTensorModule.map` with that isomorphism, its
  `S`-linearity coming from `AddEquiv.linearEquiv`, together with the pointwise description
  `(f (x) 1)(x (x) s) = f x (x) s`.  The identification `(M (x) S)^(n) = M^(n) (x) S` that the
  source states on page 170 is there as well, as a three-part composite that keeps the factor order
  of the source: a `comm` in each tensor slot, a recursion in the number of slots (base case through
  `isEmptyEquiv` and `rid`, step through `mulEquiv`, `cancelBaseChange` and `assoc`), and a final
  `comm`.  The base change of a linear structure along an `R`-algebra uses that isomorphism to
  sandwich `f (x) 1` between the two tensor-power models, and the base change of an `F` structure
  along an `F`-map is built on top of it (`IsScalarTower F R S` is the library form of the map being
  an `F`-map).  What is not yet computed is the value of the isomorphism on generators: that needs a
  generator lemma for `TensorPower.mulEquiv.symm` which mathlib does not provide, so the isomorphism
  and the base changes built on it are to be treated as unchecked downstream until such a probe is
  written.  On top of that language sits the source's notion of an F class, a predicate on F
  structures closed under isomorphisms, under base change, and satisfying the descent condition that
  a subring can be enlarged to a finitely generated one over which the structure descends.  The
  descent data is packaged in a structure of its own, since an existential cannot bind instances;
  modules are taken in the same universe as the ground ring so that base change is universe-stable
  and the class can be a single predicate.  That the shape is satisfiable is recorded; that a
  non-empty class satisfies it, as the source asserts for Azumaya algebras and Galois extensions, is
  not.  The lifting property is a predicate on classes: a local F algebra with a structure over its
  residue field in the class lifts to a structure over the algebra itself, whose base change back
  agrees.  Representing objects, the specializations they induce, and generic objects -- those whose
  ring is a localized polynomial ring -- are there as well, with the existential over the map of
  rings packaged as data, since an existential cannot bind instances, and with the source's affine
  hypothesis read as finite generation.  A densely representing object is one that is representing,
  whose ring is a domain, and such that every localization of the ring still carries a representing
  object.  The morphism vocabulary of the section is there too: F-linearity, surjectivity in the
  source's sense of both components being onto, and locality in the sense that the preimage of a unit
  is a unit.  On that vocabulary sit projective objects for a class -- where the source is explicit
  that the object need not lie in the class -- projective objects in a class, and local projectives,
  which do lie in the class and lift against local surjections.  Specializations are named as the
  source names them, and a representing object induces one for every object over a field in the
  class.  Theorem 1.3(a) is recorded as a statement only: its proof turns on identifying a
  Hom-set, and the three remaining parts of that theorem need the Azumaya and Galois classes, which
  are outside this file.  The relative form of the lifting property is there, along with the field
  theory the corollary is stated in: retract rationality, which asks for a domain with a quotient
  field and a retraction through a localized polynomial ring, and rational factoring of a map of
  domains.  Corollary 3.10 itself, both parts, is recorded as a statement only, since its proof
  rests on the bridge between those two notions that is not built here.  Proposition 1.1 closes the
  section's vocabulary: a class with a generic object has the lifting property, and a class with a
  densely representing object and the lifting property has a generic object, both recorded as
  statements.  The source omits the proof of the first, calling it a trivial generalization.
  Where the source's sentences say that a class *has* an object, membership is written out at the
  statement level rather than folded into the property predicates; the one place it is folded in is
  local projectivity, whose statement names an object of the class.  Not yet formalized are
  the classes and their closure properties, the lifting property,
  representing and densely representing objects, projective and local projective objects, and
  specializations.

- The files added after the snapshot that neither the table above nor the bullets above name.  This
  bullet completes the list: it was obtained by diffing the gate's 122-item `FILES` table against the
  file names occurring in this README, so it is exhaustive rather than illustrative.  They are
  `Flasque_ABGV52.lean` (the flasque class: the flasque and coflasque predicates, the similarity
  relation with its laws, invertibility, flasque resolutions with the named subgroup-permutation
  input, the coflasque consequences of invertibility, and the birational-invariance residual read off
  printed page 189 of the 1984 paper, together with the encoding bridge that carries the source's
  literal similar-to-zero form to the invertibility form this development uses), `HypRefute_ABGV52.lean` (the machine-checked refutations of the
  two flasque hypotheses as originally stated), `LatticeHyp_ABGV52.lean`, `TateLayer_ABGV52.lean`,
  `TateTrivial_ABGV52.lean`, `SubgroupPerm_ABGV52.lean`, `NotRetract_ABGV52.lean`,
  `NotRetractChallenge_ABGV52.lean` (the 4.13 non-retract-rationality chain and its independent
  restatement), `RetractCrit_ABGV52.lean`, `StableRationalBricks_ABGV52.lean`,
  `Superlattice_ABGV52.lean`, `SuperlatticeClass_ABGV52.lean`, and `FischerRegular_ABGV52.lean`.

The authoritative per-hypothesis status (the five-piece coverage for the thirteen named hypotheses)
is maintained on the knowledge-base side, in `wiki/proj-ABGV52-named-hypotheses-status.md`.

- `SaltGeneric_ABGV52.lean` (2026-10-12, latest): the named hypothesis that the conjugate evaluation is
  given by a nonzero polynomial with base-field coefficients is no longer on the critical path.  Two
  declarations close the determinant argument unconditionally: a density lemma, that a polynomial over
  the field which vanishes at all base-field points is zero, taken from the library's function
  extensionality for multivariate polynomials over an infinite integral domain along a box with
  infinite sides; and the nonvanishing lemma for the companion polynomial of the product of the
  conjugates, which is the source's appeal to the algebraic independence of the conjugates.  The
  latter is proved by reading the group action as algebra homomorphisms and applying Dedekind's
  independence to the matrix whose entries are the conjugates of a basis: its rows are linearly
  independent, the matrix is therefore a unit, and the inverse matrix supplies a substitution that is
  a left inverse of the original one.  The unconditional end-to-end form is
  `exists_linearIndependent_smul_aeval_ne_zero_of_ne_zero`.  The same round records a defect in the
  neighbouring named statement: `Lemma52Statement` quantifies over every polynomial, so at the zero
  polynomial its conclusion is unsatisfiable and the statement is refutable; the machine-checked
  refutation `Lemma52Statement.false_at_zero` is included, its only consumer is the shape lock, and
  the source's `t` is a nonzero polynomial, so the statement needs that hypothesis.  The corrected
  statement is then proved: with that hypothesis the source's lemma 5.2 holds as a theorem, the
  spanning half of "generates a normal basis" coming from the library's construction of a basis out
  of a linearly independent family of the right cardinality, and the base change of the evaluation
  along the two structure maps carrying the conclusion back to the polynomial ring over the ground
  field.

*Note (2026-10-12): this file was accidentally truncated while being edited and has been restored
from the submodule commit `bd659a8` plus the update above; the prose of the intermediate revision
(2026-10-11, 29 rows) is not recoverable from the working tree and is registered as lost in
`wiki/log.md`.*
