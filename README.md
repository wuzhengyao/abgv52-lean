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
| `SaltDef`, `SaltT2`, `SaltSwan`, `SaltCor`, `SaltCond`, `SaltGeneric`, `SaltRatOver` | the Saltman-track layers: the 1984 definitions, the rational-to-retract bridge, Swan's lemma, the corollary/reduction pair, the 2-power/cyclotomic condition layer, the named generic-object residual (which now also carries the source's two existence theorems -- theorem 2.1 of the 1982 paper, and its theorem 5.1 via Noether's construction, with rationality over the base field defined and the fixed field of a group action used for its hypothesis -- as named statements, with the witness of existence packaged, the pages of the 1982 paper actually cited by the 1984 text census-completed, rationality over the base field given a non-vacuity probe, and the source's Noether action built on the polynomial ring and carried to its fraction field with source-faithful locks and a faithfulness probe), the opening of the 1982 paper's lemma 5.2 (the product of the conjugates of a polynomial is invariant, its evaluation lands in the fixed points, the evaluation itself being equivariant so that the statement carries no extra hypothesis, the nonvanishing of that product transfers to the polynomial itself, which is the source's unit clause, and the determinant of the coordinate matrix of the conjugates is characterised as the criterion for those conjugates to be independent in the field itself, the transport from coordinates to vectors being carried by the definition of linear independence as injectivity of the finitely supported linear combination, the determinant then exhibited as an honest polynomial in the coordinates, the infinite-field step that two nonzero polynomials share a nonvanishing point, through the bridge that reads the group action as algebra automorphisms, the abstract normal basis theorem together with the nonvanishing of that polynomial, the carrier of the companion polynomial for the conjugates together with the identity identifying its values with the evaluation of the source polynomial at the conjugates, and the derivation of finite-dimensionality from the basis, and closing the paper's determinant argument end to end, the last hypothesis then removed by two further steps: first, that a polynomial over the field which vanishes at every point with coordinates in the base field is zero, which frees the avoidance step from having to be run on base-field coefficients, and second, the algebraic independence of the conjugates, in the form that the linear substitution attached to them is injective, proved from Dedekind's independence of the algebra homomorphisms through the invertibility of the matrix of the conjugates of a basis and the inverse substitution that matrix supplies) with that lemma's nonvanishing recorded as a theorem rather than as a hypothesis, the first step of the source's proof of theorem 5.1 formalized as well -- from rationality of a field over the ground field one extracts a transcendence basis, as an algebraically independent family generating the field, the generating half proved for the fraction field directly and then transported along the isomorphism, which keeps the algebraicity transfer across an algebra equivalence out of the proof, the interface between that extraction and the descent proposition then supplied by the fraction form of the generated subalgebra -- every element of the field being a quotient of two elements of it, proved by structural induction on the field adjunction and recorded also in the multiplication form needed to clear denominators, with the bridge to the library's transcendence basis predicate registered together with the inference failure that blocks it, the clearing of denominators then carried out for a finite family -- the single multiplier being the product of the denominators, its nonvanishing coming from the no-zero-divisor instance on a subalgebra of a field, and the finite form specialized to the generated-field setting so that it consumes the fraction form directly, and the same clearing for a finitely generated algebra, where the single multiplier is the product of the denominators of a finite generating set and the powers are tracked through the generators, the ground field, sums and products, with the generated-field specialization of that form supplied as well, and the cleared elements then placed inside the localization at that single element, taken as the subalgebra generated by the inverse of the multiplier, so that the image of the finitely generated algebra lands where the source requires it, and the transcendence basis predicate of the library reached as well, by proving that the generated subalgebra is algebraic over the field, which together with algebraic independence yields that predicate, so that the extraction of rationality now produces the library's own notion, and the localization at a single element made an explicit carrier inside the field, containing the ground ring and finitely generated over it, into which the finitely generated algebra's structure map factors, the subalgebra generated by an algebraically independent family then identified with a polynomial ring and shown finitely generated over the ground field, with a map from the abstract localization back into the field supplied by its universal property, and the elements of that localization written with a common denominator as powers of the multiplier, the powers of the multiplier shown to lie in the nonzero divisors so that the library's localization subalgebra applies, and that subalgebra identified with the one generated by the inverse of the multiplier, which is thereby a localization and isomorphic to the abstract one, localizations being transported along an isomorphism of the base rings, and the resulting identification of the localized subalgebra with a localized polynomial ring assembled, the fraction-ring structure of the generated subalgebra supplied on the way, then the realization argument's evaluation map, taken as a named algebra homomorphism together with its value on the variables, extended to the localization at the polynomial once that value is a unit, the resulting package of a basis and a map on the localized polynomial ring that the source's lemma 5.2 supplies, the spanning half of that basis clause, and finally the descent of a group-equivariant map out of a Galois algebra to the fixed field, which is where the map on the base ring comes from, with the fixed-field identification and the embedding of the descended algebra into the Noether field registered as the remaining inputs, then the half of that bridge coming from the denominators of the transcendence basis: every finite family of the Noether field lands in a single localization of the polynomial ring, in the subalgebra form the source's ring generated by a transcendence basis takes, and with the inverse of a nonzero element included, which is the source's localized polynomial ring; two field identities and the multiplicative form of an element of a fraction ring are factored out first so that the heavy fraction-ring term occurs only at the application site, then the second mechanism: the localization at one element is contained in the localization at a multiple of it, two such localizations join into one, and consequently the denominators of the transcendence basis and those of any further family of elements are absorbed by a single multiplier, which is the product the source takes, and the wiring that puts the two together: the image of a
finitely generated algebra over the base lands in a single localization once the base's own image
does, the multiplier being exhibited explicitly, and a Galois algebra embeds into the big ring
along the descent isomorphism, so that the embedding half of the source's containment is a
theorem, together with the first block of the map on the base field: a nonzero polynomial is
replaced by an invariant multiple, the localization at an invariant element carries an action of
the group, and the lift of an equivariant map to that localization is equivariant again, by
uniqueness of the lift; the boundary map into a subalgebra is recorded as well, and the fixed-field step in the form where
the subring is pointwise fixed rather than the base of a Galois pair, together with the
compatibility of the action on the localization with the canonical map into the field, which is
what makes the preimages of the base elements fixed.  The two are then put together: the
canonical map out of the localization is injective, so the base can be transported into the
localization and its preimages are fixed there, and the fixed-field step produces the map of the
base into the fixed field, so the whole chain from the base to the fixed field is a theorem -- supplied
from the source side with the missing input of that chain: the localization at a nonzero polynomial
sits inside the range of the canonical map into the field, the inverse of the polynomial being reached
through the ring inverse rather than through a field inverse, since a localization is only a
commutative ring, so that the image of a base ring presented by a family together with the inverse of
one element lies in that range once the multiplier is replaced by an invariant multiple; the result is
an end-to-end theorem that, from that presentation, an equivariant evaluation map, and the fixed-field
step, produces the map of the base into the fixed field of a Galois extension together with its
compatibility equations, and a strengthened form in which a further finitely generated algebra over
the base is placed inside one and the same invariant localization, so that the base and the descended
algebra share a single multiplier -- and the tensor side of that realization is reduced to one input: the
base change of the equivariant evaluation along the algebra adjunction is a map from the tensor product
of the fixed field with the localization onto the field, surjective because the conjugates of the
distinguished element span the field and are the evaluations of the variables, and an equality of
dimensions upgrades that surjection to an isomorphism, so that only the rank of the localization over
the base remains, the source's own criterion being that a group-equivariant map whose image together
with the field generates the extension realizes it.  That tensor side is now complete as well: the
map produced there is equivariant whenever the evaluation is, the group acting on the second tensor
factor and commuting with the scalars of the fixed field, and the dimension of the base change,
which had been the only remaining input, is supplied by the rank of a Galois algebra over a field,
so that a surjection of equal dimensions becomes an isomorphism preserving the group actions, as the
source's definition of realization requires -- and now packaged end to end: the
Galois structure of the base change, the action on the tensor product with its formula on pure
tensors, and the finiteness of that tensor product are all supplied inside one statement, so that a
caller brings the Galois structure of the localization, the projectivity input, and a linear
equivariant evaluation, and receives the isomorphism preserving the group actions.  The packaging
cannot be pushed further, and the reason is recorded in the file: the tensor product and the facts
assumed of it mention the algebra structure on the fixed field, which the assembly point produces,
so an identity between that structure and the produced map is the price of stating the result, and
it is registered rather than claimed away -- and the realization is now assembled: from the Galois
data of the target extension and the transport of the base ring, a single theorem produces both the
map of the base ring into the fixed field and an isomorphism from the extension to the tensor
product of the fixed field with the localization which preserves the group actions, the evaluation,
its equivariance and the rank all being supplied inside.  Two inputs remain explicit and are
recorded: the action on the localization must agree with the canonical one on the polynomial ring,
and its algebra structure must be the embedding into the Noether field.  The lift of an equivariant
evaluation is also recorded in the generality that an arbitrary action requires, since that is what
the assembly point has -- and the base ring may be taken to be the
subalgebra generated by the fixed elements, and then the transport of that ring into the Noether
field, its containment in the localization, and its invariance under the group are theorems of the
construction rather than inputs, a fixed subalgebra being recognised by induction on its
generators, leaving the identification of the algebra structure, the two structures asked by
condition (b), and the fixed-field hypothesis as the recorded inputs -- and that subalgebra is itself a localization of a polynomial ring, as
condition (a) asks, provided the generators are algebraically independent, they generate the
field, and the distinguished element is a polynomial in them, the comparison of the carrier with
the adjunction over the polynomial subalgebra being the library's own decomposition of an
adjunction -- and retract rationality
along rational extensions, and the reading of the realization clause of the generic-extension
definition settled from the source's own emphasis that the algebra realising an extension need not
be a field -- so that the library's ring-level form is the faithful one and the field-level form is
a weaker specialisation, whose witness is constructed from the assembly's data while the
source-level witness is registered as still open, and the bridge between the Galois-algebra
predicate and the automorphism group is closed in the field case -- the action map bijective, a
group-indexed normal basis on which the action multiplies indices, the spanning element the
source's lemma produces, and the fixed points identified with the base field -- so that the three
clauses the assembly had assumed are supplied rather than hypothesized, the field-level
restriction and the finite-dimensionality input being registered alongside, and the source's
lemma on the normal basis closed on top of that bridge: its two data hypotheses, a basis and the
identification, are supplied rather than assumed, in the form the source writes, with the unit
clause stated literally and the finiteness input registered, and the realization clause restated
with finite-dimensionality inside its quantifier and proved outright in that form, without the
data hypothesis the assembly had carried -- a separate name from the faithful clause, since the
source's clause does not carry finiteness, with a definitional lock whose discriminating power is
checked against a mutant that drops that binder, the faithful clause implying the restated one and
the converse registered as the finiteness gap, the page citations of the 1982 source audited and
corrected, and the source-side data wired to the witness in one theorem, with the carrier
concretized, the two compatibility hypotheses discharged and the two named inputs left
explicit; the witness at that level is reached as before.
clauses there are packaged into a witness of their own, and from the source-side data alone -- with
no data hypothesis, the realization clause being supplied on the spot -- such a witness is obtained,
the first witness in the library that needs nothing beyond that data, with the three levels of
witness recorded side by side |
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
  canonicality equation `g • (1 ⊗ x) = 1 ⊗ (g • x)`.  The base-change step of the source's theorem
  5.1 is then packaged for the assembly: the two instance hypotheses (finite generation and
  projectivity) are replaced by the single registered external input, so that the hypothesis list of
  that step matches the rest of the development; the non-triviality the statement needs is supplied
  by a general lemma pulling it back along a ring homomorphism, which is how the descent isomorphism
  provides it; and the case of a trivial group is recorded separately, since its faithfulness clause
  is free there.  An application lock pins the hypothesis list, and the remaining input is
  registered as the source's cited projectivity result.  The first mechanism of
  the other half of that bridge is added as well: a flat module tensored with an
  injective map of scalars stays injective, so a Galois algebra embeds into its
  tensor product with the big ring once the registered projectivity input is
  available, with a data-level non-vacuity probe and an application lock, and now also the composite with a
descent isomorphism, which is the embedding of the descended algebra into the field, with its own
data-level non-vacuity probe.  The base change of a Galois algebra to a tensor factor is also
packaged with its three lines of wiring internal, so that a caller supplies the Galois structure
and the single named input, and nothing else: the nontriviality the statement asks for is
produced inside, from the algebra map into the field through the base-change adjunction, which is
the same route the descent isomorphism takes and needs only a map rather than an isomorphism.  The
source writes the base change
with the base ring on the right, while the packaging above produces the other orientation; the two
are now compared by the library's own commutativity isomorphism, an algebra equivalence over the
common factor, with the group action and the algebra structure on that side built here, and a
Galois structure is transported across that isomorphism, so the statement in the source's
orientation follows from the same three inputs.
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
  `H^1(G, S^*)`, is not.  The criterion also yields the rank of a Galois algebra over a field, with no
  external input: the third clause makes the skew monoid algebra isomorphic to the endomorphism ring,
  that isomorphism is linear over the field, and comparing dimensions on the two sides -- the free
  module of rank the order of the group against the endomorphism ring of a space of dimension `n` --
  gives `n` equal to that order, nontriviality of the algebra supplying the positivity.
  The same file also transports a Galois structure along an equivariant algebra isomorphism:
  faithfulness of the action, fixedness of scalars, and bijectivity of the skew-algebra map all move
  across, the last through a pointwise conjugation identity for that map, with the conjugated
  endomorphism taken from the library's own composition rather than built by hand.
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
  field.  The realization step is also recorded in the orientation the source writes, with the
  tensor factor on the left, by composing the packaged isomorphism with the library's commutativity
  equivalence, whose equivariance is what carries the group actions across; the remaining
  quantifier shape of that clause is registered as an open gap rather than claimed closed.
  The infinitude the realization argument needs on the target side is not an extra hypothesis: the
  source's theorem asks the ground field to be infinite and the argument invokes that the extension
  field is, which is derived here.  That ground-field hypothesis now stands in the library's
  statement of the theorem as the source writes it, with a definitional lock that fails if it is
  dropped.  The three clauses of the generic-extension definition are also packaged into the
  existence witness, which had no construction in the library before, and the realization clause
  is now available in the field form the source's argument uses, supplied by the assembly from the
  normal-basis and fixed-field data, with the ring form of that clause registered as still open.

The reading of the realization clause of the generic-extension definition is now settled from the
source itself, at page level: where the paper turns to the case that the base ring is a field, it
says that the algebra being realised is not necessarily a field, "here and in the rest of the
paper".  The library's clause, which quantifies over commutative rings, is therefore the faithful
transcription and is not weakened; the field-level variant that the assembly can supply is a
weaker specialisation, and that direction is now a theorem -- the ring-level clause implies
the field-level one, the converse left open, so no strictness is claimed.  Packaged with that
variant are the field-level
twin of the generic-extension predicate, its definitional shape lock, whose discriminating power is
checked against two mutants that make the lock fail, the witness structure of the weaker predicate,
and -- from the same source-side data as the assembled clauses -- the existence of a witness for it,
which is the first witness reached from that data at either level.  The source-level witness is
registered as still open, and the registration now names the three inputs it waits on: a
group-indexed normal basis, the identification of the group with the automorphism group, and the
fixed-point condition.  All three are bridges inside the library rather than material the source
withholds, since the source's own proposition supplies the normal basis for general, possibly
non-field algebras; an earlier registration, which recorded that normal basis as quoted but
unproved, is corrected accordingly.

The bridge between the library's Galois-algebra predicate and the group of automorphisms is now
closed in the field case.  From that predicate together with finite-dimensionality one gets, for a
field extension: that the action map from the group to the algebra automorphisms is bijective, so
that the abstract group is the Galois group; a group-indexed normal basis, with the group acting on
it by multiplication on the indices; an element whose conjugates are independent and span, which is
the element the source's lemma 5.2 produces; and that the fixed points of the action are exactly
the base field, by comparing the two degrees and applying the degree-one criterion.  The three
clauses the earlier assembly had taken as a hypothesis are therefore no longer an independent
input: they are supplied on the spot, and a pointwise realization is derived from the source-side
data together with the Galois-algebra predicate and finite-dimensionality alone.  Two limits are
registered: the bridge is field-level, because the fixed-point and automorphism-count tools are,
while the source states its proposition for general algebras; and the one remaining input is
finite-dimensionality, which the source obtains from the cited projectivity of a Galois extension
over its base.  Removing that input at the level of the predicate is registered as the next step,
since it requires the finiteness to enter the quantifier.

The source's lemma on the normal basis now stands without its two data hypotheses.  It had been a
theorem already, but one that assumed a basis of the extension over the base field and the
identification of the abstract group with the automorphism group; both are exactly what the bridge
supplies, so they are now derived rather than assumed, and the lemma holds from the Galois-algebra
predicate together with finite-dimensionality.  It is recorded in the form the source's own
theorem assumes, with the ground field infinite and the infinitude of the extension derived, and
in the source's literal wording, where the evaluation of the polynomial at the conjugates is a
unit, alongside the nonvanishing form that had been used.  The statement the library had registered
as a named residual is thereby accounted for in corrected form, its uncorrected version being
false as it stands and kept only as a record, and the finiteness input is registered as the one
remaining hypothesis of the lemma.

The realization clause is now available at a level where finite-dimensionality need not be assumed
as a hypothesis of the statement.  The field-level clause has been restated with that finiteness
inside its quantifier, and in that form it is proved outright from the source-side data alone: the
data hypothesis the assembly had carried is discharged by the bridge, so the clause follows without
it.  The restatement is a separate name rather than an edit of the faithful clause, because the
source's clause does not carry finiteness -- it is a consequence of the cited projectivity of a
Galois extension over its base -- and writing that assumption into the faithful statement would be a
deviation from it.  A definitional shape lock keeps the two apart, and its discriminating power is
checked against a mutant with the finiteness binder removed; the faithful clause implies the
restated one, while the converse is exactly the finiteness gap, which is registered rather than
claimed.  The witness at that level, and the conjunction of the three clauses there, are now in
place: the three clauses are packaged into a witness of their own, and from the source-side data
alone -- no data hypothesis being needed, since the realization clause is supplied on the spot --
such a witness is obtained.  It is the first witness in the library that asks for nothing beyond
that data, and it is a witness of the finite-level, field-level form rather than of the source's
clause, so the three levels of witness now stand side by side, each with its own hypothesis table,
and the source-level one is registered as still open.

The end-to-end form of the source's theorem 5.1 -- rationality of the fixed field implying a
witness, with no data supplied by hand -- has now been audited for reachability before being
attempted, and the audit's answer is that it is out of reach here: exactly two structural inputs
remain outside the development.  One is the Galois property of the algebra the source constructs,
which the paper quotes from its own earlier work, and the other is the finite projectivity of a
Galois extension over its base, quoted from the literature on Galois theory of rings; neither
reference is in the library.  Every other input is available here, including the fixed-point
condition that an earlier round supplied.  The target is therefore restated as the end-to-end form
modulo those two named inputs, the statement of that form is fixed with a definitional lock whose
discriminating power is checked against a mutant that swaps the witness level, the source-level
statement is shown to imply it, and the two inputs are recorded as being of the same kind as the
other named residuals.

The page citations of the 1982 source have been audited.  Every reference to its printed pages was
counted, the load-bearing three were read again on the rendered pages and match what the library
quotes of them verbatim, and the single wrong page has been corrected: the basis line of the
cross-vocabulary lock had given the page that carries the proposition and the emphasis sentence of
section 0 rather than the page that carries the definition, and the two are now distinguished, with
the pages not read one by one recorded as a residual.  A registration in the other file back-links a
residual that an earlier round superseded.

The wiring the audited target called for is now in place.  The source-side construction data,
together with the two named inputs, yield the finite-level witness in a single theorem, and the two
compatibility hypotheses the earlier assembly carried are discharged by concretizing the carrier to
the invariant subalgebra of the Noether field.  A duplicate instance binder had to be dropped for
the identification of the algebra structure to line up, which is recorded.  The hypothesis table of
the result is exactly the source-side data plus the two named inputs, and the construction of that
data from the rationality hypothesis is recorded as the remaining step.

The first two links of that remaining chain are now in place.  With the carrier taken to be the
subalgebra generated by a transcendence basis together with an element and its inverse, the clause
asking that carrier to be a localization of a polynomial ring is derived from the rationality data,
and so is the statement that the carrier is pointwise fixed, from the invariance of the generators.
The hypothesis table of the resulting end-to-end statement therefore asks only for the source-side
data, the invariant multiplier, the containment, the instances and the two named inputs.  What
remains of the chain is recorded: the construction of the invariant multiplier from the clearing of
denominators, which is available in principle, and the algebra structure carrying the subalgebra
into the localization, which is the input registered earlier.

*Note (2026-10-12): this file was accidentally truncated while being edited and has been restored
from the submodule commit `bd659a8` plus the update above; the prose of the intermediate revision
(2026-10-11, 29 rows) is not recoverable from the working tree and is registered as lost in
`wiki/log.md`.*

The two inputs that the audit had placed outside the development are not outside it after all.
The 1978 paper that the 1982 source quotes for the descent construction, long recorded as
absent, is now in the library together with its published text, and the page that carries the
quoted theorem and the sentence the projectivity clause needs has been read on the rendered
page and matches what is quoted of it.  The printed page is the third page of the file, an
offset of its own: the three sources this development reads at page level each need a
different shift.  Both inputs are therefore reclassified as available within the library and
merely unformalized, and every registration that said otherwise has been rewritten, the
superseded wording being kept in place as a note rather than deleted.  The amount of work is
unchanged: what is now available is the source's own proof, not a formalization of it, and
neither endpoint has a proof here.

The progenerator sentence that supplies the finite projectivity clause has a different source than
the one recorded for it.  The sentence cites, in the 1978 paper's own numbering, the monograph on
separable algebras, not the memoir on Galois theory of rings that the 1982 paper cites for the same
clause; the two are different works, and a search of the paper confirms it never cites the memoir at
all.  Both inputs are accordingly given named endpoints in the declarations, one for the descent
statement and one for the progenerator statement, each with a definitional shape lock and a
non-emptiness probe for its conclusion data, and each registered as having no proof here.  The
progenerator statement is the stronger of the two and is shown to imply the projectivity clause's
named form, so the source's sentence suffices for that clause once it is formalized; a definitional
lock on the descent statement records that it is stated for the source's own existential form rather
than the earlier assembly's fixed subalgebra form, so the two cannot be used interchangeably.  The
discriminating power of both locks is checked against mutants, one swapping the faithful-flatness
clause for freeness and one dropping the tensor product from the descent conclusion, and both
mutants fail the lock as intended.

The construction data of the end-to-end statement is now produced rather than assumed.  A single
existential produces the invariant multiplier together with its nonvanishing, its invariance and
the containment, and the three instances that statement had carried as parameters are produced as
well: the algebra structure on the localization from the carrier step, its scalar tower from
instance resolution, and the group action from the general construction in the local-projective
file.  Two of the statement's hypotheses disappear in the same step.  The compatibility of the
localization map with the group action is the member form of the compatibility lemma that file
already carried for its algebra homomorphism, recorded there now at the general carrier level, of
which the symmetric-algebra instance was a special case; and the identification of the algebra
structure with the carrier map is the conclusion of the carrier step read at the algebra structure
that map induces, so it is supplied rather than assumed.  What remains in the hypothesis table is
the commutativity of the group action with the scalars, the Galois clause and the projectivity
clause, all stated inside the binders of the existential, since each of them mentions the
multiplier or one of the instances.  The local instances are introduced with the plain `let` and
`have` forms, which register local instances in Lean 4, rather than with the `letI` and `haveI`
forms, whose only further effect is inlining, so the round adds no warning to the build.

The commutativity of the group action with the scalars is produced rather than assumed as well, so
the closed form of the wiring asks only for the Galois clause and the projectivity clause.  The
derivation reads that commutativity as the statement that the image of the carrier map is
pointwise fixed, and obtains the latter from the injectivity of the map into the Noether field, the
equivariance of that map with respect to the two actions, and the fixedness of the generators of
the subalgebra.  All three were already in the library, and the same three are used, in the same
order, by the earlier equivariant assembly in the generic file, so this step is retrieval rather
than construction.  The closed form takes the group action that the generic file itself constructs
on the localization, rather than the general-carrier construction of the local-projective file
that the preceding round used, because the equivariance lemma is stated for the former.  A
registration of the preceding round recorded the last of the three instances as blocked by file
order and placeable only after both source files.  That is true of the general-carrier
construction, but the generic file's own construction was available at the target all along: the
block was one of instance synthesis, not of availability.

The Galois clause of the wiring has been reduced to its crossed-product content.  Of the three
clauses the Galois predicate carries, the second -- that the base ring's image is pointwise fixed
-- is automatic from the commutativity hypothesis alone, by applying that hypothesis to the unit;
this is recorded as a general fact next to the predicate, and it makes that clause redundant.  The
first clause, faithfulness of the group action on the localization, is proved from the
compatibility of the action with the localization map, the injectivity of that map into the
Noether field, and faithfulness of the action on the polynomial ring, all of them already in the
library.  The closed form of the wiring therefore assembles the Galois clause from its third
clause, bijectivity of the crossed-product map, which is the Galois content itself, and takes that
bijectivity together with the projectivity clause as the two remaining inputs.  Neither is proved
here, and neither is the source's theorem.

One of the endpoints the chain had carried is not merely unproved but refutable as stated.  The
endpoint asked that a Galois extension make the base ring act faithfully, and the earlier rounds
had recorded that its entity was unproved, with a linear-independence route named as the next
attempt.  The stated form is false: taking the base ring to be a product of two copies of the
rational field, mapping it onto the rational field by the first projection, and letting the group
be trivial, the three clauses of the Galois predicate all hold -- faithfulness of the trivial
group, fixedness of scalars, and bijectivity of the crossed-product map, the last because the
one-point group makes the skew algebra one-dimensional and every linear endomorphism of the
rational field is multiplication by its value at one -- while the base ring acts unfaithfully,
the second factor being nonzero and acting as zero.  The counterexample is machine-checked and
uses only the standard axioms.  The correction recorded with it is that the endpoint is not a
separate assumption in the intended use, where the base ring and the extension are subrings of a
common field and the structure map is an inclusion; the stated form is kept in place as a trace
rather than deleted, and the linear-independence route is withdrawn, the target being false rather
than the route blocked.

A second endpoint fails in the same way, and the defect is now recorded as systematic rather than
accidental: both endpoints of the Galois criterion were stated for an arbitrary algebra map, while
the intended use has the base ring included in the extension.  Taking the base ring to be the
integers, the extension the rational field and the group trivial, the three clauses again hold --
the crossed-product map being bijective because every linear endomorphism of the rational field is
multiplication by its value at one, this time via the library's fact that an additive map of the
rational field is rational-linear -- while the fixed element one half is not in the image of the
integers.  The two endpoints are therefore recorded as refuted in their stated form and as
available in the intended one: the first directly, the second only through the progenerator
statement, whose entity is still unproved.  The projectivity endpoint is flagged as a candidate of
the same kind, its refutation awaiting the fact that the rational field is not a finitely generated
module over the integers, a fact the library does not supply; the candidate is registered as such
and not claimed.

That missing fact is now supplied, and with it the third endpoint joins the two refuted ones.  The
rational field is not a finitely generated module over the integers: a finite generating set would
give a common denominator, the submodule of rationals with that denominator is closed under
addition and integer scaling and contains the generators, and one over twice the denominator is not
of that form.  With the same counterexample as before -- integers, rational field, trivial group,
whose antecedent was already machine-checked -- the projectivity endpoint is therefore refuted as
well, since its conclusion would give finiteness of the rational field over the integers.  All
three endpoints of the Galois criterion are thus recorded as refuted in their stated form, the
defect being that each was stated for an arbitrary algebra map while the intended use has an
inclusion; and since the projectivity endpoint is the one the wiring carries as a hypothesis, that
hypothesis must likewise be read in the intended setting, its satisfiability there being registered
as unverified rather than assumed.

A fourth endpoint closes the census of the family, and it is the one that mattered most: the
progenerator statement whose entity the project had planned to carry over from the source.  The
same counterexample refutes it, since its conclusion would give finiteness of the rational field
over the integers; and the implication from it to the projectivity endpoint, already in the
library, is consistent with both being false.  The census is now complete over the family: the four
endpoints stated for an arbitrary algebra map are all refuted, while the two stated over algebras
over the base field are not reached by the counterexample and their truth is left undetermined.  The
defect is thus confined to the arbitrary-map group, and the consequence recorded for the plan is
that the source's assertion is proved there for an inclusion, so the endpoint must be rebuilt in
the intended setting rather than carried over as stated.  The trace-and-corestriction route
recorded earlier keeps its value for that rebuilding, since the faithfulness clause it stumbled on
is not an obstacle when the structure map is an inclusion.

Non-vacuity is now established for the family, and it is the complement the refutations needed.
The earlier probes had only shown that the data appearing in the conclusions can be instantiated,
and one of them claimed that this made the hypothesis class non-empty, which it does not; the
Galois predicate itself was never exhibited.  It is now: over the rational field with the base ring
equal to the extension and the group trivial, the predicate holds -- the third clause because the
one-point group makes the skew algebra one-dimensional and a rational-linear endomorphism of the
rational field is multiplication by its value at one -- and all four refuted endpoints hold at that
same instance.  The refutations are therefore about the stated forms being too wide, not about
empty classes; the claim that the data layer implied non-emptiness of the hypothesis class is
withdrawn and the probe is marked as showing only the data layer.  The instance is not, however,
the pair the wiring uses, so the satisfiability of the wiring's own hypothesis table remains
unverified, with a candidate instance recorded for it.

The source side of that table is now exhibited, over the rational field with the trivial group: a
transcendence basis of the Noether field, an element generating it, the two invariance conditions,
the infinite base field, and a multiplier with its nonvanishing, its invariance and the containment.
The algebraic independence is the library's for the polynomial variables, transported into the
fraction field and reindexed; the generation clause reduces to the fact that every element of the
field is a quotient of polynomial values; and the invariance conditions hold because the group is a
singleton, independently of the shape of the action.  The wiring's hypothesis table is therefore not
empty on the source side.  What remains outside this witness is the three instances with the
commutativity clause and the two inputs; their sufficient condition is that the localization at the
multiplier be isomorphic to the algebra itself, which holds in the exhibited instance and is
registered as the next step.

The crux for that isomorphism is now in place: in the exhibited instance the algebra generated
by the inverse of the multiplier and the algebra generated by the transcendence basis together
with the element and its inverse are the same subalgebra.  One inclusion follows by induction on
the generators of the first, with the coefficient case handled by pulling back along the structure
map rather than by unfolding the evaluation of constants, whose instance elaboration is ambiguous;
the other follows because the element itself is a value of the structure map and the inverse is a
generator.  With the localization isomorphism already available, the two inputs that remained --
finiteness with projectivity, and bijectivity of the crossed-product map -- are now within reach by
rank-one considerations.


The upper half of the range identification is now in place as well: in the exhibited instance the
subalgebra generated by the data lies inside the range of the canonical map from the localization.
Only the two generators need checking, the element following from the compatibility of that map
with the structure map and the inverse from the library's containment of the algebra generated by
the inverted multiplier.  With the equality of the preceding round this identifies the range with
the subalgebra generated by the data, so the isomorphism between the localization and that
subalgebra is a matter of recording it through the injectivity of the canonical map.  One technical
point is recorded: the algebra-homomorphism form of that map is not definitionally the ring
homomorphism it extends, so the goal has to be changed before the compatibility lemma applies.


A correction is recorded for the preceding round.  The statement landed there and the library's
containment of the algebra generated by the inverted multiplier point the same way, and the
equality of the round before already yields the same statement, so that statement is not the
second half of the range identification as reported; the claim that both halves were in place is
withdrawn.  What is actually missing is the reverse containment, that the range of the canonical map
lies in the subalgebra generated by the data.  A route for it is recorded: an element of the range
is the image of a localization element, which is a fraction with denominator a power of the
multiplier, so the element satisfies a multiplicative relation that can be solved without dividing
inside the subalgebra, since the subalgebra is not automatically a field; both factors are members,
one being a value of the structure map and the other a power of the inverse of the multiplier.  The
statement of the preceding round is kept as an independent cross-check, its other route avoiding the
equality.


The missing direction is now in place: in the exhibited instance the range of the canonical map
lies inside the subalgebra generated by the data.  An element of the range is the image of a
localization element, which the localization's surjectivity condition presents as a fraction whose
denominator is a power of the multiplier; rewriting that power before applying the compatibility of
the canonical map with the structure map -- the order matters, since otherwise the multiplier enters
the map's own argument and the rewrite is blocked by a dependent motive -- gives a multiplicative
relation, from which the element is read off as a product without dividing inside the subalgebra,
which is not automatically a field.  Both factors are members, one being a value of the structure
map by the same pullback used earlier and the other a power of the inverse of the multiplier, which
is a generator.  With the containment of the preceding round this identifies the range with the
subalgebra generated by the data, so the isomorphism between the localization at the multiplier and
that subalgebra is now a matter of recording it through injectivity.


The range identification is now recorded as an equality: the range of the canonical map is exactly
the subalgebra generated by the data, by the two containments established in the two preceding
rounds.  All the substance of the isomorphism between the localization at the multiplier and that
subalgebra is therefore in place, and what remains is bookkeeping: transporting the isomorphism onto
the range through injectivity of the canonical map, along the equality of subalgebras.  The gap
registered two rounds ago, namely the missing containment, is closed by this.


The bookkeeping is done: in the exhibited instance the localization at the multiplier is isomorphic,
as an algebra over the rational field, to the subalgebra generated by the data.  The isomorphism is
assembled by restricting the canonical map to that subalgebra, which the equality of the preceding
round permits, and then invoking bijectivity: injectivity is the library's, and surjectivity follows
from the same equality.  Assembling the pieces before invoking the constructor was what made this
step go through, after an earlier attempt had failed by interleaving the constructor's placeholders
with tactic bullets.

What now remains for non-emptiness of the wiring's hypothesis table is to derive finiteness with
projectivity and bijectivity of the crossed-product map from this isomorphism, both being rank-one
considerations, and then to record the hypothesis table itself.


The first of the two remaining corollaries is now available in general form: if an algebra is
isomorphic to its base ring as an algebra over it, then it is a finitely generated projective
module, by transporting finiteness and projectivity along the isomorphism, the base ring being free
of rank one over itself.  A corollary records what this gives for the wiring: the projectivity
endpoint holds whenever the extension is isomorphic to the base ring, for any group and any
compatibility clause.  Since that endpoint is refutable as stated, this is the satisfiable
sufficient condition its role in the hypothesis table needs; what remains for the wiring is to raise
the isomorphism of the preceding round from algebras over the rational field to algebras over the
subalgebra, which is where finiteness and projectivity are asked for.


The tool needed to raise the isomorphism to the level at which finiteness and projectivity are
asked for is now available: if an algebra is isomorphic to its base ring as a ring, then with the
algebra structure that the isomorphism itself induces, the algebra is a finitely generated
projective module.  The linear equivalence is the isomorphism itself, its compatibility with the
scalars following from multiplicativity and the inverse law, and finiteness with projectivity are
transported along it as before.  The instance is registered by a plain local definition rather than
an instance binding, since the latter trips a style linter that is a false positive for instance
registration but still counts as a warning.

What remains is to apply this to the wiring's pair, using the isomorphism of two rounds ago, and to
derive bijectivity of the crossed-product map there.


The first corollary is now instantiated on the wiring's pair.  The isomorphism of three rounds ago
is first given a name, its proof being unchanged apart from dropping the existential wrapper so that
downstream steps can use the multiplier explicitly; one technical point is recorded, that the type
must pin the coefficient ring of the polynomial ring, since otherwise instance resolution stalls.
Feeding that isomorphism to the upgrade lemma then yields, for the algebra structure it induces,
finiteness and projectivity of the localization over the subalgebra generated by the data, for any
group and any compatibility clause.  This is exactly the two clauses the projectivity endpoint asks
for on the wiring's pair.

What remains for non-emptiness of the wiring's hypothesis table is bijectivity of the
crossed-product map, and then the recording of the table itself.


The sufficient condition for the last input is now available in general form: if the structure map
from the base ring to the algebra is surjective, then for a one-point group the Galois predicate
holds, for any compatibility clause.  The faithfulness clause is automatic for a one-point group, as
is the invariance of the base ring; the crossed-product map is bijective because on the one hand the
skew algebra is one-dimensional over the algebra, and on the other every linear endomorphism is
multiplication by its value at one, since each element is a scalar multiple of the identity by
surjectivity of the structure map.  The statement is phrased for a generic one-point group rather
than the one-point type, since that type carries a global scalar-action instance whose resolution
clashes with the one the Galois predicate expects.

Applied to the wiring's pair this gives the crossed-product input, the structure map onto the
localization being surjective because the localization is isomorphic to the subalgebra.


A registration closes this round.  The instantiation of the crossed-product input on the wiring's
pair was assembled and its proof body is valid: with the trivial action declared locally, the
algebra structure over the subalgebra bound in the conclusion, surjectivity of the structure map
read off from the isomorphism, and the general lemma of the preceding round, the first version
compiles; the only diagnostic is a style linter that is a false positive for instance registration.
Packaging the same proof without that diagnostic did not go through in this round: replacing the
instance binding in the proof by a plain local definition changes the goal into a function type, so
the introduction binds the instance instead of the compatibility clause, and moving the structure to
a section-level local instance meets the noncomputability of the localization's ring structure,
which a noncomputable marker should address but which was not pursued further.  The route for the
next round is recorded in the statement itself.


The last input is now instantiated on the wiring's pair.  The route registered in the preceding
round works as recorded: both the trivial action and the algebra structure induced by the
isomorphism are declared as local instances at section level, marked noncomputable because the
localization's ring structure is, and the conclusion mentions no instance binding; the predicate
then follows from the general lemma together with surjectivity of the isomorphism, and the
compatibility clause is taken as a parameter so that no instance has to be bound in the statement.

With the two clauses of finiteness and projectivity from three rounds ago, the three pieces needed
for non-emptiness of the wiring's hypothesis table are not only in place but assembled.  On the pair
the wiring is run on, the compatibility clause is witnessed, the crossed-product map is bijective,
and the projectivity predicate holds, so the table is non-empty; feeding those three entries into
the wiring's existential form then yields the witness field data, so the wiring fires on this
instance rather than being non-vacuous on paper only.

One process reading is worth recording.  The compatibility clause between the source action and the
action on the localization cannot be written with `one_smul` under the trivial action: the trivial
instance of the one-point group and the action induced from the Noether action are different
instances, so the rewrite matches no occurrence, and registering the induced action locally does not
repair the mismatch either.  The clause is obtained instead by evaluating the Noether ring
homomorphism at the group's single element, where it is the identity, and transporting the resulting
equality along `congrArg`.


The fifth criterion of the family has now been decided, and it is false even in the F-algebra tier.
The counterexample takes the base field to be the rationals, the group to be the one-point type, the
algebra to be the polynomial ring in one variable with the structure map sending the variable to
zero, and the module to be the polynomial ring itself with the structure map as the surjection.  The
Galois predicate holds on this data by the general lemma of two rounds ago, since the structure map
is surjective and the group is a one-point type; the equivariant section, however, does not exist.
A section would send one to a polynomial mapping to one, and the variable times that polynomial
would be the image of the variable times one, which is zero; the polynomial ring being a domain,
that polynomial would be zero, and one would be zero.

One process reading: this is the first refutation that needs section-level local instances.  Neither
the algebra structure of the rationals over the polynomial ring nor the trivial action of the
one-point group is a global instance, and the counterexample's compatibility clause mentions the
scalar action, so the statement itself cannot be written without them.  The refutation lives in the
file that carries the general lemma rather than in the file that carries the rest of the family,
because the family's file precedes the lemma's file in the compilation order and therefore cannot
see it; the family's file is imported, in the legal direction, to make the criterion visible.

The descent endpoint has been reduced to a single explicit step.  The counterexample instance is the
polynomial ring in countably many variables mapping onto the rationals at the point where every
coordinate is one, with the one-point group acting trivially; the Galois predicate holds on it by the
general lemma of three rounds ago, because the structure map is surjective and the group is a
one-point type.  The point is chosen with infinitely many nonzero coordinates, so that the kernel of
the structure map, a maximal ideal, is not finitely generated.  What is now available is the bridge:
any finitely generated algebra mapping into that polynomial ring has its image inside the subalgebra
generated by finitely many variables.  The proof takes finitely many generators of the algebra,
bounds the variables occurring in each image by a supremum of supports, and expands each image along
its support.

What remains for the refutation is the tensor step, and its exact shape is recorded in the file: with
the image contained in the subalgebra on the first n variables, associativity of the tensor product
rewrites the tensor as a polynomial extension of the base change along that subalgebra, and a
polynomial extension in nonempty many variables keeps its variables free; the tensor is therefore
either zero or of dimension at least two over the rationals, and in neither case is it isomorphic to
the rationals.  The refutation is accordingly not complete, and the endpoint is not yet decided.

The fifth step of the descent refutation is now available.  A polynomial ring in a nonempty set of
variables over a nontrivial algebra over the rationals is never isomorphic to the rationals as an
algebra: an isomorphism would send the variable to some rational, and comparing coefficients of the
corresponding monomial turns the transported equality into one between zero and one; the
alternative, that the variable is sent to zero, is excluded by injectivity.

What remains is the tensor half of the reduction.  The associativity isomorphism for algebra tensor
products and the base change isomorphism identifying a tensor with a polynomial extension are both
in the library; the remaining work is transporting the algebra structure along the index splitting
of the variable set, after which the step above applies verbatim to the tensor described as a
polynomial extension over a nonempty set of variables.


One endpoint remains: the other descent statement carries an extra tensor factor in its conclusion,
so the same instance and skeleton apply only after that factor is accounted for, and nothing about
it is claimed here.  Neither is anything claimed about the source's descent statement; only the
project's named endpoint is refuted.

The second of the two descent endpoints is now refuted.  The counterexample is the same instance as
before: the polynomial ring in countably many variables mapping onto the rationals at the all-ones
point, with the one-point group acting trivially.  Assuming the endpoint gives finitely generated
data together with an isomorphism from the rationals to the tensor of the two algebras; finite
generation forces the image of the small algebra into the subalgebra on finitely many variables, so
the tensor factors through that subalgebra.  Two structural inputs finish the argument: the
polynomial ring is isomorphic over that subalgebra to a polynomial ring in the remaining variables,
proved by transporting along the index splitting with an explicit retraction, and the associativity
of the tensor product combined with the base change isomorphism turns the tensor into a polynomial
extension in the remaining variables over the base-changed factor.  That set of variables is
nonempty, so the extension is never the rationals: if the base-changed factor is nontrivial the
dimension step from the preceding round applies, and if it is trivial the extension is trivial and
the rationals are not.

One endpoint remains: the other descent statement carries an extra tensor factor in its conclusion,
so the same instance and skeleton apply only after that factor is accounted for, and nothing about
it is claimed here.  Neither is anything claimed about the source's descent statement; only the
project's named endpoint is refuted.

The first descent endpoint is now refuted as well, so both named endpoints of that criterion are
decided.  Its conclusion differs from the second endpoint only in that the small algebra is required
to be finitely generated over a subalgebra of the big one rather than over the base field, and in
that the structure map into the second algebra is required to be injective; the tensor tail has the
same shape.  Refuting it therefore amounts to choosing the bottom subalgebra and transporting finite
generation across the identification of that subalgebra with the base field, which is done by
surjectivity of the structure map of the bottom subalgebra together with transitivity of finite
generation along the scalar tower.  With that instance in hand the preceding round's proof applies
verbatim, including the injectivity hypothesis, which is simply unused.

The refuted section criterion has been rebuilt on its expected use case.  The unrestricted form was
false because a Galois structure alone says nothing about the module structure, and the counterexample
satisfies every hypothesis of the rebuilt statement except projectivity.  The rebuilt form therefore
adds exactly two inputs: that the target algebra is projective over the base ring, and that the order
of the group is invertible there.  Under them a section exists: projectivity splits the equivariant
surjection linearly, and averaging the resulting linear section over the group produces a section that
is again equivariant, the inverse of the group order supplying the normalisation.  A companion
statement keeps the Galois hypothesis for signature compatibility, documenting it as redundant, and a
characteristic-zero corollary dispenses with the invertibility input, which holds automatically there.
Neither the refuted unrestricted form nor the source's projectivity statement is claimed.

The blueprint's step that consumed the section criterion has been rewired onto the rebuilt form.
Since the old criterion is false, the two theorems that took it as an input now come in twins whose
hypothesis is the pair of provable inputs instead: projectivity of the target algebra over the base
ring, and invertibility of the group order there.  Their conclusions are verbatim those of the
originals, and the section is supplied by the rebuilt statement of the preceding round.  One twin
needs the projectivity input in a quantified form, because its conclusion is itself a statement about
every pair at once; a second twin is stated over the rationals, where the invertibility input is
automatic and hence dropped.  The originals are left in place, documented as resting on a refuted
hypothesis and not to be used as before.

The progenerator endpoint has been rebuilt on its expected use case, and the full triple goes
through: finite generation, projectivity and faithful flatness over the base ring.  The inputs are
those the source's argument uses: the algebra is a finitely generated projective module over the
group ring, which has to be an explicit input because mathlib has no automatic module structure of
the algebra over its group ring, together with the accompanying scalar tower and injectivity of the
structure map.  Projectivity descends by change of rings, using that the group ring is finite free
over the base; faithful flatness needs Nakayama driven by finite generation, because flatness plus
injectivity alone is not enough, as localising the integers at two shows.  A companion theorem checks
that the counterexample refuting the unrestricted form is excluded by the new inputs, and a
non-emptiness probe witnesses the hypothesis class.


The injectivity input of the rebuilt progenerator endpoint has been shown to be necessary rather
than an artifact.  The Galois predicate alone does not give injectivity of the structure map, and the
project already carries a machine-checked witness for that in the smallest tier: the product of the
rationals with itself mapping onto the rationals.  What was missing for the point to be sharp is that
in that same instance the third clause of the rebuilt conclusion genuinely fails, and that is now
proved: faithful flatness implies injectivity of the structure map, so it cannot hold there.  The
witness is the same Galois datum as before, taken unchanged.  Accordingly the rebuilt endpoint cannot
drop the input, and the source's use case is not affected, because there injectivity is structural:
the base ring sits inside the algebra.

The two source statements have been reduced to named residuals, and one of them turned out to rest on
a route that is empty.  For the second source statement the library now has: the shared ring-tier
residual of the realisation clause, a reduction from that residual together with the source's
construction side to the statement, and a proof that the statement's conclusion does not mention the
ambient field, so the field quantifier and the rationality hypothesis are idle at this step.  For the
first source statement, the ten wiring rows that had been blocked at file level are now produced
mechanically, but a machine-checked judgement shows that the encoding used since an earlier round is
unsatisfiable when the group is nontrivial: the hypothesis table of that route is empty, so no amount
of wiring along it can reach the statement.  The repair is recorded and landed: the data should be
read as a fixed transcendence basis of the invariant field, which the rationality hypothesis supplies
directly, rather than as an adelic basis of the ambient field.

The data chain of the first source statement has been rerouted to the invariant-field reading, and the
rerouting is not vacuous.  The residual hypothesis table is now read on the fixed field: the
transcendence basis lives there, so the demand for invariance is automatic rather than contradictory,
which is exactly what made the previous encoding empty for nontrivial groups.  Along the way two
library lemmas were strengthened: the identification of a localisation with a subalgebra no longer
needs the fraction-ring hypothesis, and clause (a) of the source's construction no longer needs the
generating hypothesis.  A non-emptiness probe supplies the whole data table and machinery from the
rationality hypothesis, leaving only the two named Galois endpoints as unproved rows; an unconditional
probe at the one-point group over the rationals is also landed.  The old route is left in place,
documented as vacuous, and the ring-tier residual is still shared with the second source statement.

The coherence lemma behind the rerouted residual is now proved, and it came with a strategic
finding: the residual's data rows are equivalent to the source's rationality hypothesis, which is the
Noether problem itself for the invariant field.  So the generating row is load-bearing rather than a
bookkeeping row, and the residual must not be pursued unconditionally — for groups where the Noether
problem fails it is false.  What landed: the sharp form identifying the invariant field with a
rational function field on the same number of generators, its existential form, the two-sided
equivalence, a strengthened reduction whose second conjunct consumes the generating row, a
discrimination witness for the empty family, and two non-emptiness probes including an unconditional
one at the one-point group over the rationals.  The old reduction is untouched, because its proof
route genuinely does not need the generating row.

The shared ring-tier residual has been diagnosed rather than discharged, and both source statements
have been re-reduced without it.  The diagnosis is machine-checked: the library's Galois predicate
accepts the zero ring when the group is a one-point type, while on the source's side a Galois
extension is a finitely generated projective module of rank the group order, so the zero ring lies in
the library's quantifier range but not in the source's.  Since the zero ring is not a field, the
finite-field tier cannot see such targets, which is why the implication from that tier to the ring
tier cannot be expected to hold as stated.  The corrected residual adds non-triviality and finite
generation over the base, matching the source's own finiteness consequence, and that corrected form is
proved unconditionally for one-point groups.  Finally the two source statements now reduce without the
ring-tier bridge at all: the ring-tier clause is absorbed into a carrier-shaped residual, and the
conditions under which the bridge was previously assumed are recorded.

The ring-tier bridge has been refuted rather than proved, and the encoding obstacle that blocked the
refutation last round is gone.  The witness: take the base ring and the algebra both equal to the base
field, the intermediate field equal to the base field, and the target the zero ring.  The finite-field
tier hypothesis holds there, while the ring-tier conclusion fails, because the library's Galois
predicate accepts the zero ring for a one-point group whereas the tensor of the field with itself over
itself is nontrivial.  To make that argument typecheck the realisation property was re-encoded with
its algebra structures as explicit data instead of instance bindings, and the two encodings are proved
equivalent in both directions, so the refutation transfers back to the original form.  Consequently
the bridge is dead for one-point groups, and the corrected finite-tier-to-ring-tier statement, which
adds non-triviality and finite generation, is exactly the form that survives.  The remaining case is
non-singleton groups, where the zero ring is excluded by faithfulness and another degenerate target is
needed.

The library now has its first non-trivial Galois instance: for the algebra of functions from a finite
group to a field, with the group acting by permuting the coordinates, the Galois predicate holds.  The
proof is a faithfulness check, a bijectivity argument for the structure map by extracting
coefficients, and a two-sided dimension count.  With that instance in hand the ring-tier question for
non-singleton groups is no longer vague: the split algebra is not isomorphic to the field once the
group has at least two elements, by counting idempotents, so the ring tier fails there outright, while
the finite-field tier is false at the same carrier once any non-trivial Galois field extension exists.
The remaining obstruction is therefore pinned to a single point: refuting the bridge for non-singleton
groups is exactly the problem of making the finite-field tier true at some carrier, and the only
available carriers are the source-side generic objects, whose field tier is the project's open
main-line obligation.  The instance-ambiguity trap of the previous round is broken by fixing the
tensor's instances once and naming the algebra homomorphism's compatibility slots explicitly.

The field tier of the realisation property is now instantiated at a non-degenerate carrier on the
source side, and the two source statements have been shown to share a single input.  On the carrier
given by the fixed-field construction, with the base field the rationals and the one-point group, the
tier holds unconditionally: every row of the source-data table is instantiated, so the predicate now
has a non-degenerate example rather than only the degenerate one.  A sharper reduction replaces the
former eighteen-row table by two rows plus one datum, and it feeds both source statements at once: from
the same data one gets the second source statement's clause residual and the first's wiring residual,
which makes explicit that the surjectivity of the structure map and the projectivity of the carrier are
exactly the common input.  A mutant probe where each of five rows is replaced by a trivial statement
fails inside the proofs, so the rows are load-bearing rather than decorative.  The ring-tier bridge
remains open, and the degenerate carrier for it is now provably dead, so a refutation there needs a
non-degenerate carrier instead.

The two rows shared by the source statements have been reduced further.  Injectivity of the structure
map now follows from a general criterion requiring only that the algebra have no zero divisors and
that the group act faithfully, with both inputs supplied by construction on the source side, so that
row is settled up to surjectivity.  The projectivity row has been replaced by two module-theoretic
rows over the group ring, whose module structure is itself constructed here because the library had
none: an action of the group algebra is built from the multiplicative action, its single-element
formula is proved, and the scalar tower is verified, after which the earlier change-of-rings and
Nakayama argument supplies the projectivity conclusion.  Non-emptiness is witnessed on the split
Galois algebra for a non-trivial group, where both old rows hold, and a mutant probe in which each new
row is replaced by a trivial statement fails inside the proof bodies.  What remains shared is
surjectivity of the structure map together with finiteness and projectivity over the group ring, and
the ring-tier bridge for the source-form witness.

Surjectivity of the structure map is now settled in the field tier, and the naive way of porting it
to the ring tier is refuted.  In the field tier the argument needs only a cardinality equation, the
dimension over the base field being the order of the group, and injectivity from the previous round;
for a finite Galois extension that cardinatity is supplied by the standard degree count, so the
statement becomes unconditional there, and an explicit non-degenerate example over a finite field
witnesses it.  The ring tier is different: the obvious hypotheses, a domain with a faithful finite
group action, the fixed ring equal to the base, finite freeness of rank the group order, and
injectivity of the structure map, are all satisfied by the Gaussian integers over the integers with
conjugation, where the structure map is nevertheless not surjective, as the trace form shows.  So the
ring-tier row must be tied to the module-theoretic rows rather than deduced from injectivity and rank.
The imports needed for the field-tier argument were added; nothing existing was changed.

The correct module-theoretic input for the ring tier has been found and pinned exactly.  On the
quadratic carrier, where the group of order two acts by conjugation, surjectivity of the structure map
is equivalent to unimodularity of the trace form, that is, to the discriminant being a unit; one
direction gives an explicit preimage from the unit formed by twice the generator minus the trace, the
other reads the discriminant off the preimage of the coefficient projection, and no injectivity
hypothesis is needed.  The Gaussian integers are the failing case and are identified with the previous
round's carrier by an explicit ring isomorphism compatible with conjugation, while the same quadratic
data over the rationals, and the split case over the integers, satisfy the hypothesis and the
conclusion.  Three weaker candidate inputs are refuted by explicit witnesses: surjectivity of the
trace, invertibility of the group order, and freeness of rank one over the group ring.  Invertibility
of the group order and unimodularity are incomparable.  The general case for an arbitrary finite group
is registered as a shape-locked obligation, and the module-theoretic rows over the group ring are
untouched.

The general shape registered last round for the ring tier is false, and this round settles the wiring
pair as well.  The registered shape asked for a group-invariant trace functional whose pairing is
unimodular; on the quadratic carrier with the group of order two that hypothesis holds while the
conclusion fails, and the diagnosis is visible in the same witness: the invariant pairing is
unimodular whereas the multiplication trace has determinant four.  So the correct input is
unimodularity of the multiplication trace, which is what last round's equivalence actually used.  On
the wiring model the discriminant is not a unit, and it stays a non-unit in every subring containing
it, so surjectivity fails for the plain choice of the localising element; the repair is to multiply
the discriminant into that element, and the mechanism is proved in general, with an explicit instance
where the strengthened element makes the discriminant a unit and surjectivity follows.  What remains is
the classical statement that unimodularity of the multiplication trace plus the rank condition gives
surjectivity, which is registered and open.

The discriminant repair is now complete for an arbitrary finite group and the ring-tier surjectivity
question is reduced to a single precisely located gap.  The discriminant element, the product over
ordered pairs of distinct coordinates of their differences, is nonzero and invariant under the group
for every finite group; on the two-element group it reproduces the previous round's discriminant up to
a unit, so the general statement genuinely generalises the model.  Multiplying it into the localising
element makes the discriminant a unit in the localisation, and the whole wiring package is rebuilt at
that element, with all downstream rows supplied by construction as before.  For surjectivity itself, a
trace formula together with unimodularity of the trace form implies surjectivity for an arbitrary
finite group, arbitrary rank and arbitrary commutative base ring, the preimage being written down
explicitly from trace-dual elements; neither the rank hypothesis nor injectivity is needed.  The one
remaining obligation is whether the registered hypotheses imply that trace formula, and the split
carrier witnesses the new hypotheses over an arbitrary commutative ring.

The twelve modules that the file manifest above lists by name only are now under version control.
They were already compiled as part of the development and already covered by `SHA256SUMS` and by the
gate's 122-item table, but they existed only in the working tree, so no commit recorded them and no
diff could show a change to them; the modules are `TateTrivial_ABGV52.lean`,
`TateLayer_ABGV52.lean`, `Superlattice_ABGV52.lean`, `SuperlatticeClass_ABGV52.lean`,
`SubgroupPerm_ABGV52.lean`, `StableRationalBricks_ABGV52.lean`, `RetractCrit_ABGV52.lean`,
`NotRetract_ABGV52.lean`, `NotRetractChallenge_ABGV52.lean`, `LatticeHyp_ABGV52.lean`,
`HypRefute_ABGV52.lean` and `FischerRegular_ABGV52.lean`.  Four of them carry the flasque layer, the
permutation-lattice-to-flasque gap, the trivial-group and trivial-module flasque instances and the
refutations of the two flasque hypotheses as first stated; two carry the multiplicity arithmetic of
the superlattice classification and its orbit-multiplicity interface; the non-retract-rationality
chain of 4.13 and its independent restatement are two more; the remaining four are the named
hypothesis interface of 4.12, the stable-rationality closure bricks, the lattice form of the flasque
resolution hypothesis, and the regular-invariant Fischer hypothesis.  With this addition the file
count, the mirror, `SHA256SUMS` and the gate table all agree at 122, and every module the gate
compiles is tracked.

Round 283 completes the five-step plan registered for the ring-tier trace formula and lands the load-bearing half
of it.  The apply lemma for `LinearMap.mul` was measured rather than guessed: it is `LinearMap.mul_apply'` with a
prime, while the unprimed `LinearMap.mul_apply` does not exist; the trace hooks `LinearMap.trace_conj'` and
`LinearMap.trace_eq_matrix_trace` were not previously imported, so `Mathlib.LinearAlgebra.Trace` is now imported.
The pointwise shape recorded in the plan omitted the outer group action on the right-hand side and is false as
written; the corrected pointwise identity carries a `g •`, and the measured counterexample lives on the split
carrier for the three-element group.  From the corrected pointwise form the conjugation identity
`m_{g•x} = c_g ∘ m_x ∘ c_g⁻¹` is proved with the linear equivalence `c_g : y ↦ g • y`, and the basis-change
bridge identifies the multiplicative trace `r270MulTrace` with the trace of multiplication as a linear map,
yielding group invariance `Tr_b (g • x) = Tr_b x` as a direct instance of `LinearMap.trace_conj'`.  The
rank-three probe on the split carrier for the three-element group instantiates the registered hypotheses
(injectivity of the structure map over the rationals, unimodularity of the trace form, the trace formula itself)
and verifies the criterion directly by reindexing: the group-average vanishes on the trace-zero submodule, so
this carrier supplies no counterexample.  The main implication, that the registered hypotheses force the trace
formula, remains open, and the trace formula itself is not claimed.

Round 284 machine-checks the criterion to which the trace-formula gap reduces.  The multiplicative trace is
shown to be linear in its second variable, the group average is shown to be fixed by the action, and the trace of
that average is shown to be the group order times the trace.  From these, and assuming only that the basis rank
equals the group order and that this order is cancellable, the trace formula is proved equivalent to the
vanishing of the group average on the trace-zero submodule.  This shrinks the open implication to a single
statement; the criterion is verified on the split carrier but is not yet forced by the registered hypotheses.
The next round follows the published route: Saltman's normal-basis proposition for the field case and the trace
identity for Galois field extensions already available in mathlib are to be used where they apply.

Round 285 opens the published-source route for the trace-formula obligation.  The multiplicative trace is
identified with mathlib's `Algebra.trace` for an arbitrary commutative coefficient ring and basis, and the two
field-tier facts that Saltman's Theorem 5.1 proof invokes are landed as direct bridges from mathlib: existence
of a normal basis for a finite Galois field extension (`IsGalois.normalBasis`) and the trace identity expressing
the field trace as the sum over the Galois group (`trace_eq_sum_automorphisms`).  The ring-tier registered
implication remains open and is carried as a parallel registration; the source route now has its field-tier
inputs machine-checked in the project.


Round 286 opens and closes the module-theoretic pair of rows by the published route.  Saltman's normal-basis
proposition states that the extension possesses a normal basis, that is, that it is isomorphic to the group
algebra as a module over that group algebra, and that is exactly the mechanism the two rows need.  What is
landed here is the resulting conditional implication at ring tier: given a normal basis, the map sending a
group-algebra element to its action on the basis element is a bijection of group-algebra modules, because the
coordinates of that action in the normal basis are precisely the coefficients of the element.  Injectivity and
surjectivity therefore come from one computation rather than two, and the two rows, finiteness and projectivity
over the group algebra, are then transferred along the resulting linear equivalence from the group algebra
itself, so no module theory is reproved.  The transport is wired into the existing reduction, so the projectivity
hypothesis is now supplied by a normal basis.  The existence of that basis is the source-side input and is not
claimed at ring tier; the field-tier instance was machine-checked in the previous round.  With this, the
trace-formulation obligation of the earlier rounds is bypassed for the main chain, and the bypass criterion is
registered explicitly: the normal basis, not the trace formula.  A probe that appeared to refute the trace
formulation through the split carrier was itself refuted by the project's existing machine-checked lemmas, which
show that carrier to satisfy both the trace formula and the conclusion; that line is closed as a positive
instance rather than a counterexample.

Round 287 settles the field tier of the surjectivity question by dimension counting.  Over a field, if the rank of
the algebra equals the order of the group, then injectivity of the crossed-product map implies its surjectivity,
because the two sides are vector spaces of the same dimension: the group order times the rank on one side, the
square of the rank on the other, equal precisely under the rank hypothesis.  The dimension of the skew monoid
algebra is computed through its coefficient linear equivalence and the standard formula for finitely supported
functions, and the dimension of the endomorphism ring through the standard formula for linear maps, so the whole
argument is a transport of existing results.  Neither the trace form nor the trace formula is used, which locates
the weight of the earlier trace rounds precisely: they matter only over a general ring, where equal ranks no longer
suffice.  The field tier of the outstanding surjectivity obligation therefore reduces to injectivity alone.  Nothing
about the ring tier is claimed; the registered shape remains open there.

Round 288 makes the first incision into the source's Section 1 carrier for the Artin-Schreier case.  The carrier is
the algebra obtained by adjoining a root of the polynomial X^p - X - a in characteristic p, and the group action
the source uses sends that root to the root shifted by one.  What is landed here is the relation-preserving core of
that action: in characteristic p with p prime, if an element satisfies the Artin-Schreier relation, then so does its
shift by any scalar fixed by the p-th power map, in particular by one.  The computation is a single application of
the Frobenius identity in characteristic p together with ring arithmetic, and it covers the whole orbit at once
rather than the generator alone, because the shift parameter is arbitrary among the p-th-power-fixed scalars.  The
statement is deliberately stated for an arbitrary commutative ring of characteristic p rather than for one
particular model of the carrier, so that any later construction of the carrier can consume it directly.  The
carrier itself, the resulting action of the cyclic group, and the Galois clauses are not claimed here; this round
lands the relation-preserving core only.

Round 290 lands the source's Section 1 carrier for the Artin-Schreier case together with the shift endomorphism
that generates its cyclic action.  The carrier is the algebra obtained by adjoining a root of X^p - X - a in
characteristic p, and the shift sends that root to the root plus a scalar that is fixed by the p-th power map.  Two
computations support it: substituting X + k into the defining polynomial changes it by the constant k^p - k, and
that constant vanishes precisely for the p-th-power-fixed scalars, so the substitution descends to the carrier and
yields an endomorphism.  Characteristic p is not installed on the carrier: the substitution is computed inside the
polynomial ring, whose characteristic is inherited along the injective constant map, and the result is then pushed
through the quotient map, which avoids the quotient-characteristic transfer entirely.  What is not claimed is that
the shift is bijective, that the cyclic group acts, or any of the Galois clauses; the endomorphism alone is landed.

Round 291 supplies the missing prerequisite for turning the Artin-Schreier shift into an automorphism: the set of
scalars fixed by the p-th power map is closed under negation.  The argument splits on the parity of the prime.  For
p equal to two the square of the negative equals the square of the original, which the defining relation turns back
into the original, while characteristic two identifies the negative with the original; for odd p the sign simply
factors out of the p-th power and the defining relation collapses the rest.  The negation closure is exactly what
lets the shift by the negative serve as the inverse shift, and it is therefore recorded as the standing prerequisite
for the automorphism that the next round is to assemble.  Nothing about bijectivity, the cyclic group action, or the
Galois clauses is claimed here.

Round 292 removes the obstruction recorded in the previous round to computing with the Artin-Schreier shift.  The
obligation that the shifted root satisfies the defining relation was previously written as an anonymous proof term
inside the definition of the shift, which made the two standard evaluation lemmas fail to match it syntactically.
That obligation is now a named theorem, and the shift is restated in terms of it, so the two computations that the
automorphism argument needs, namely that the shift fixes the coefficients and that it sends the root to the root
plus one, become direct instances of the evaluation lemmas for adjoining a root.  The restated shift has the same
value as the version landed earlier, which is kept for the record.  Bijectivity itself, the group action and the
Galois clauses are not claimed here; what is landed is the pair of computations the bijectivity argument consumes.

Round 293 completes the automorphism: the Artin-Schreier shift is now proved bijective, and with the ring hom
structure landed earlier it is therefore a ring automorphism of the carrier.  The proof composes the shift by the
scalar and the shift by its negative in both orders and shows each composite is the identity.  Extensionality is
taken in two steps, first along the quotient presentation of the carrier and then along the polynomial presentation
of the ring being quotiented, so that it suffices to check the coefficients and the root; the coefficient case is the
statement that the shift fixes the base, and the root case reduces to the trivial cancellation of the two shifts.
Two practical points are recorded: the two composites are written out separately rather than obtained from one
another by substituting the negative scalar, because that substitution would move a proof term into a dependent
position and block rewriting, and the associativity of the sum is normalized before the cancellation is applied.
The group action and the Galois clauses are not claimed here.

Round 294 assembles everything the cyclic action on the Artin-Schreier carrier needs.  The set of scalars fixed by
the p-th power map is shown to be closed under addition, and the elements of the prime field inside the coefficient
ring are shown to lie in that set, so a supply of group-like parameters is available without installing an algebra
structure on the coefficient ring.  The shifts are then shown to compose: the shift by one parameter followed by the
shift by another is the shift by their sum, proved by the same two-step extensionality as before, where the
coefficient case is that both sides fix the base and the root case reduces to associativity of the sum.  Finally the
bijectivity of the previous round is packaged as a ring equivalence, so each shift is available as an automorphism
rather than merely as a bijective homomorphism.  The action itself and the Galois clauses are not claimed here.

Round 295 lands the cyclic action on the Artin-Schreier carrier.  Each element of the prime field acts by the shift
by that element, the supply of shift parameters being the image of the cyclic group in the coefficient ring, whose
elements satisfy the fixed-point equation by Fermat's theorem for the prime field.  The action axioms reduce to
facts already established: the identity acts trivially, composition of shifts is the shift by the sum, and the
remaining axioms are the ring-equivalence properties of the shift.  Two practical points are recorded.  Rewriting a
parameter is blocked when it occurs inside a term whose proof argument depends on it, so parameter conversions are
performed in non-dependent positions, or by simplification, which does handle such dependent positions, or at the
level of functions; and the composition law as stated is oriented from the composite to the single shift, so the
multiplication axiom consumes it with the opposite orientation.  The Galois clauses are not claimed here.

Round 296 lands two of the three Galois clauses for the Artin-Schreier carrier.  The clause that the base is fixed is
immediate from the computation that the shift fixes the coefficients, and is landed unconditionally.  The
faithfulness clause is landed as a reduction: it suffices that the canonical map from the coefficient ring into the
carrier is injective and that the prime field maps injectively into the coefficient ring, and the argument then reads
the action off at the root, where the shift moves the root by the image of the group element, so triviality of the
action forces that image to vanish.  Both remaining injectivity hypotheses are expected to be available in the
intended applications, one from the carrier's presentation over a domain and one from the characteristic, and
removing them is recorded as the next step.  The crossed-product clause and the Galois predicate as a whole are not
claimed here.

Round 298 removes one of the two hypotheses that the faithfulness clause of the previous round was stated under.
The map from the prime field into the coefficient ring is injective whenever the coefficient ring has characteristic
the prime in question: the prime field is a field, so a ring homomorphism out of it is injective as soon as the
target is nontrivial, and nontriviality follows because otherwise one would be zero and hence divisible by the prime.
The faithfulness clause is then restated with the injectivity of the canonical map into the carrier as its only
hypothesis, the prime-field injection being supplied by the new lemma.  Two practical notes are recorded: the
nontriviality of a ring in prime characteristic must be extracted from the element one rather than from the
characteristic element, since in the zero ring every natural number vanishes; and the instance of nontriviality has
to be registered as a local instance for the field argument to apply.  The remaining hypothesis, the injectivity of
the canonical map into the carrier, is not addressed here.

Round 299 makes the faithfulness clause for the Artin-Schreier carrier unconditional.  The remaining hypothesis was the
injectivity of the canonical map from the coefficient ring into the carrier, which holds as soon as the defining
polynomial has nonzero degree.  That degree is computed here by squeezing: the coefficient of the top power is one,
which bounds the degree from below, while the degree of a difference and of a sum is bounded by the maximum of the
degrees of the terms, which bounds it from above.  Nonvanishing of the degree then follows, and the injectivity of
the canonical map is available over a domain, which is exactly the source's setting.  With the fixed-base clause
landed earlier, two of the three Galois clauses are therefore in place; the crossed-product clause is not addressed
here, and the Galois predicate is not claimed as a whole.  Two practical points are recorded about the degree
computation, concerning the top-degree term of the upper bound and the coercion of the natural number degree into the
type with an adjoined bottom element.

Round 300 establishes that the conjugates of the root of the Artin-Schreier polynomial are pairwise distinct, which
is the injective half of the crossed-product clause.  The shift by a group element sends the root to the root plus
the image of that element, so equality of two conjugates forces the two images to be equal; injectivity of the
canonical map from the coefficient ring into the carrier turns that into equality of the two images in the
coefficient ring, and injectivity of the prime-field map turns that into equality of the group elements.  All three
ingredients were landed in previous rounds, so the argument is a direct composition of them.  One practical point is
recorded: a hypothesis stated for a function is not beta-reduced, so rewriting with the evaluation lemmas requires
restating it first in applied form.  The independence of the conjugates, the crossed-product clause itself, and the
Galois predicate as a whole are not claimed here.

Round 301 supplies the compatibility hypothesis of the Galois criterion for the Artin-Schreier action and assembles
the criterion from its parts.  The action is given by algebra automorphisms, so it commutes with the scalars of the
base ring, which is exactly the hypothesis that the criterion takes as an explicit parameter; the proof reduces that
commutation to multiplicativity of the shift together with the earlier computation that the shift fixes the
coefficients.  With the fixed-base clause and the unconditional faithfulness clause already in place, the criterion
for the carrier therefore follows as soon as the crossed-product clause is available, and that assembly is recorded
as a theorem whose only hypothesis is precisely that remaining clause.  Two practical points are recorded: the
scalar action must be unfolded by rewriting with the algebra scalar law rather than by definitional unfolding, and the
criterion lives in a nested namespace, so it must be referenced by its qualified name.

Round 302 computes the crossed-product map on the two families of generators that determine it.  On an element of the
form one tensor a group element the map is the action of that group element, and on an element of the form a carrier
element tensor the identity it is left multiplication by that carrier element; both computations are immediate from
the description of the map on single terms that was already available.  Specializing the first of them to the
Artin-Schreier carrier identifies the value of the crossed-product map on the group part with the shift automorphism,
so the formalization now records that the crossed-product map and the action studied in the previous rounds agree on
the group part.  Two practical points are recorded, one about which of these constructions require the group to be
finite and one about the placement of generic lemmas inside the carrier-specific file.  Bijectivity of the
crossed-product map is not claimed here.

Round 303 records that the Artin-Schreier carrier is free of rank p over its coefficient ring, together with the
explicit power basis given by the powers of the root.  The defining polynomial is first shown to be monic by
combining the computation of its top coefficient with the degree computation of an earlier round, and the power basis
is then obtained from the standard basis of a quotient by a monic polynomial, relabelled along the equality between
the degree and the prime.  The rank statement is a direct consequence.  This is the common floor for the two bases
that the explicit inverse of the crossed-product map will be written in, and it also feeds the module-theoretic rows
of the paper in the cyclic case.  Two practical points are recorded: the relabelling of a basis requires the index
equivalence in the direction the library expects, and an attempt to substitute the degree for the prime must be
avoided because it rewrites the prime inside the defining polynomial as well.

Round 304 rules out the naive candidate for a normal basis of the Artin-Schreier carrier.  The conjugates of the root
are pairwise distinct, which was established two rounds earlier, but they all lie in the two-dimensional span of the
unit and the root, because the shift moves the root by a scalar.  As the carrier is free of rank p, they therefore
cannot form a basis as soon as the prime exceeds two, and a normal basis element has to be sought among elements of
higher weight; the top power of the root is the natural candidate.  The round thus converts a plausible but wrong
guess into a machine-checked statement, so that no later round can quietly rely on it, and it records a repetition of
a practical point about beta-reduction that was met once before.

Round 305 supplies the two rank computations that the dimension count for the crossed-product map needs: the
crossed product has rank the order of the group times the rank of the algebra, and the endomorphism ring has rank the
square of that rank.  The first is obtained by transporting along the linear equivalence between the crossed product
and finitely supported functions, the second is the standard rank of a module of linear maps.  The round also records
a change of ground: on the carrier over a polynomial ring the explicit inverse would amount to a matrix computation of
size the square of the prime, whereas the two statements of the source live over a field, so the remainder of this
line goes through the field case, where the normal basis theorem is available in the library and was already used in
an earlier round.  Three practical points are recorded about the transport, the direction of the rank lemma, and the
instances the rank lemmas require.

Round 306 computes the value of the crossed-product map on a single generator term, namely the coefficient times the
group element applied to the argument.  This is the atomic case of the expansion of the map on a general element as a
sum over the support of its coefficients, which is the first step of the injectivity argument for the crossed-product
map in the field case: one evaluates at the translate of a normal basis element and concludes that all coefficients
vanish by linear independence of the conjugates.  The expansion itself is not completed here; the round records that
the intended decomposition of an element into single terms is blocked, together with the route that the next round
should take, namely to prove it by injectivity of the coefficient map and then reduce to a statement about finitely
supported functions.  Two rank computations for the dimension count were landed in the previous round.

Round 307 records the linear-independence interface that the injectivity argument for the crossed-product map consumes:
given a basis indexed by the group and a family of scalars whose combination against that basis vanishes, every scalar
vanishes.  The statement is a direct consequence of the library's criterion for linear independence of a finite
family, and it is stated with the scalars appearing only through the basis, so that callers who know their combination
in the shape of the conjugates of a normal basis element can pass it after rewriting.  Two practical points are
recorded.  The library's criterion lives along a different instance path than the linear independence attached to a
basis, so the statement is phrased with an additive group to bring the two into the same path; and the elaboration of
such a combination over an abstract semiring is expensive enough to require a raised heartbeat budget, which does not
add warnings.  The coefficient expansion of the crossed-product map and injectivity itself are not claimed here.

Round 308 discharges the decomposition of an element of the crossed product into its single terms, which had been
recorded as blocked two rounds earlier.  The identity is proved by injectivity of the coefficient map, which reduces
it to a statement about finitely supported functions; the coefficients of a sum are moved inside the sum along the
linear equivalence between the crossed product and finitely supported functions, and the resulting pointwise identity
is settled by splitting on whether the index lies in the support.  With this decomposition available, the expansion of
the crossed-product map as a sum over the support is one step away, and that expansion is the first half of the
injectivity argument in the field case.  Three practical points are recorded, concerning the transport of
coefficients through a sum, the direction expected by a lemma about single functions, and the correct name for the
support membership criterion.

Round 309 completes the expansion of the crossed-product map as a sum over the support of the coefficients, which is
the first half of the injectivity argument in the field case.  The expansion follows from the decomposition of an
element into its single terms, from the compatibility of the map with finite sums, and from the value of the map on a
single term computed three rounds earlier.  Four practical points are recorded: an auxiliary statement whose base ring
does not occur in its main argument must have that ring supplied explicitly; a rewrite that is meant to affect only
one side of an equation must be restricted to that side, otherwise the same symbol is rewritten inside the terms of
the other side as well; the evaluation of a sum of endomorphisms must be moved inside the sum by the linear-map
version of the lemma, the set version not applying; and the earlier failure of this step was due to an anonymous
conversion rather than to a named lemma.  Injectivity itself is not claimed here.

Round 310 records a correction and lands the bridge that the corrected route needs.  A previously planned step argued
that evaluating the crossed-product map at a normal basis element forces all coefficients to vanish by linear
independence of the conjugates; that step is invalid, because the relation obtained there has coefficients in the
extension rather than in the base, and relations with coefficients in the extension always exist since the extension
is one-dimensional over itself.  The valid route goes through the independence of distinct field automorphisms, which
the library provides in the strong form, linear independence over the extension itself.  The bridge landed here turns
the group action into algebra automorphisms of the extension, using that the action fixes the base; it is the first
input of that route.  Three practical points are recorded, about beta-reduction in the structure fields of an algebra
equivalence, about the asymmetric naming of the compatibility lemmas for addition and multiplication, and about the
field over which independence is asserted.

Round 311 lands the independence engine for the injectivity argument on the corrected route.  Distinct field
automorphisms of an extension are linearly independent over the extension itself, which the library provides for the
family of all algebra homomorphisms; restricting that family along an injective indexing map gives the version needed
here, namely that the automorphisms arising from a faithful action are linearly independent over the extension.  Two
practical points are recorded, both consequences of how the library elaborates these statements: statements that are
composed with the bridge landed in the previous round must declare the base ring in the same way that the bridge does,
and the elaboration of the independence statement is expensive enough that the heartbeat budget has to be raised
substantially, which does not add warnings.  Injectivity of the crossed-product map and the Galois clause itself are
not claimed here.

Round 312 states the vanishing of the crossed-product map in coefficient form: the map sends an element to zero exactly
when, for every argument, the sum of its coefficients against the translates of that argument vanishes.  The forward
direction evaluates the endomorphism at an argument, and the backward direction rebuilds the endomorphism from its
values.  This is the entry point of the independence argument, after which only relations among coefficients remain to
be handled: if a coefficient were nonzero, dividing by it would exhibit one group element as a linear combination of
the others over the extension, contradicting the independence engine landed in the previous round.  Two practical
points are recorded about evaluating and rebuilding linear endomorphisms.

Round 313 extends the coefficient relation from the support of an element to the whole group, which is the form the
independence engine consumes.  Terms outside the support vanish, so adjoining them does not change the sum; the only
practical point is that the library's lemma for shrinking a sum infers its two index sets from the goal, so the
equality has to be stated in the direction the library expects before it can be used.  With this bridge the injectivity
argument has all its pieces: the coefficient form of vanishing, the extension to the whole group, the bridge from the
action to algebra automorphisms, and the independence of a faithful family of automorphisms.

Round 314 generalizes the support-to-group sum comparison of the previous round to an arbitrary summand vanishing
outside the support, and specializes it to the shape the independence argument needs, where the second factor varies
with the group element.  The general form also shows why the earlier statement was not sufficient: it had a constant
second factor, whereas the application needs one that changes with the group element.  The round records the
obstruction met while attempting the final assembly, namely that the library's lemmas for splitting a sum at a point
are stated for sums displayed with an explicit index set, so the bound-variable notation must be converted before they
apply; that conversion is the next step.  The Galois clause itself is not claimed here.

Round 315 discharges the obstruction recorded in the previous round: the splitting of a sum over the whole group at a
single point.  The statement is the expected one, that the total equals the value at the chosen point plus the sum over
the remaining points, and the practical point is that the library's lemma has to be applied with its three arguments
given explicitly; with the arguments elided it failed to match inside a longer proof, which is what produced the
recorded obstruction.  Together with the previous rounds this completes the toolkit for the injectivity argument: the
coefficient form of vanishing, the comparison between the support and the whole group, the splitting, the bridge from
the action to algebra automorphisms, and the independence of a faithful family of automorphisms.
