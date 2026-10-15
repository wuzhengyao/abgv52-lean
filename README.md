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

Round 316 completes the injectivity half of the crossed-product clause over a field, assembling the seven tools landed
in the preceding rounds.  Assuming the map vanishes on an element and that some coefficient is nonzero, one divides by
that coefficient, splits the resulting relation at the corresponding group element, and reads off a linear dependence
of that element on the others with coefficients in the extension; independence of a faithful family of automorphisms
then forces the coefficient to be both one and zero.  Since the rank of the crossed product and of the endomorphism
ring agree, bijectivity of the map is now one dimension count away.  Three practical points are recorded about moving a
factor across a sum, about pointwise congruence of sums, and about deriving injectivity of a map into algebra
homomorphisms from injectivity of the underlying algebra equivalences.

Round 317 lands the third and last clause of the Galois criterion in the field case: the map from the crossed product to
the endomorphism ring is bijective.  Injectivity was established in the previous round, and surjectivity follows from
the equality of the two ranks, which is obtained from the dimension count of an earlier round together with the
hypothesis that the degree of the extension equals the order of the group; the criterion for linear maps over a field
then converts injectivity into bijectivity.  The map is transported to the linear-map form used by the criterion along
the linearization of the same underlying function, and the finiteness needed there is supplied by transporting along
the linear equivalence between the crossed product and finitely supported functions.  Four practical points are
recorded, about the common universe the rank lemmas require, about supplying the finiteness instance, about the style
of local instances, and about naming the linear map explicitly when applying the rank criterion.

Round 318 assembles the Galois criterion in the field case.  The criterion has three clauses: faithfulness of the
action, the base being fixed, and bijectivity of the crossed-product map; the first and second are hypotheses here and
the third was proved in the previous round, so the criterion follows in three lines.  One bridge is needed, from
faithfulness to injectivity of the family of automorphisms that the bijectivity argument consumes: if two automorphisms
of that family agree, then the two group elements act identically, so their quotient is the identity.  A single
practical point is recorded about the group cancellation used in that bridge.  With this, the criterion of the source
is complete over fields, and the carrier-specific results of the preceding rounds appear as its special case.

Round 319 adds three interface lemmas for the Galois criterion: the rank hypothesis of the field case implies
finiteness, so that callers need not supply it; the criterion is stated as the conjunction of its three clauses, which
makes it available for unpacking; and conversely the three clauses assemble into the criterion, which gives one
uniform way to package a Galois algebra from its parts, whether they come from the field case or from a future ring
case.  One practical point is recorded about the name of the library lemma that turns a positive rank into finiteness.
The existing field-case results are not rewritten in terms of the simplified interface here.

Round 320 strengthens the field-case criterion: the finiteness of the extension is no longer requested, because it
follows from the hypothesis that the degree equals the order of the group.  The helper that performs that step was
landed in the previous round and is moved ahead of its uses here, since a declaration must precede its use within a
file.  Existing callers are unaffected, as supplying an instance that is no longer required is harmless, and new
instantiations of the criterion are spared one step.  One practical point is recorded about the ordering of
declarations when strengthening a statement, and the round is a hardening round: it adds no new mathematics.

Round 321 completes the faithfulness interface of the field criterion by proving the converse of the bridge landed three
rounds earlier: if the family of automorphisms attached to the action is injective, then the action is faithful.  The
two forms are therefore equivalent, and a caller may supply either the faithfulness assumption or the injectivity of
that family.  The proof reduces faithfulness to the statement that an element acting trivially is the identity, and
concludes by injectivity.  No new mathematics is added beyond this interface, and the ring case of the criterion
remains open.

Round 322 records the interfaces for the generic extension of the source.  The definition has three clauses, that the
base is a localization of a polynomial ring, that the extension is Galois with the given group, and that the
realization property holds; the round states the definition as that conjunction, provides the converse assembly, and
packages the three clauses together with the carrier data into the witness whose existence the source's existence
theorem asserts.  This splits the remaining gap for that theorem into three named subgoals, of which the Galois clause
is already available in the field case and the other two remain open.  One practical point is recorded about the
namespace in which these predicates live.

Round 323 adds the faithfulness form of the injectivity and bijectivity results for the crossed-product map.  The
criterion is stated in terms of faithfulness while two of its ingredients were stated in terms of injectivity of the
family of automorphisms attached to the action; the equivalence of the two forms was established two rounds ago, and
these wrappers apply it once so that a caller holding either form has a matching statement, which spares a conversion
when instantiating the criterion.  No new mathematics is added.

Round 325 supplies the canonical case of the first clause of the generic extension definition: any localization of a
polynomial ring at a nonzero element satisfies that clause by taking itself, with the identity equivalence.  This makes
the first clause free for the family of carriers that future constructions of generic extensions naturally produce, so
that only the Galois clause and the realization clause remain as real work.  The case of the polynomial ring itself is
not completed here: it requires transporting along the identification of multivariable polynomials in one variable with
univariate polynomials, composed with the fact that localizing at one changes nothing, and the library places the latter
instance at the monoid generated by one rather than at its closure, which is the obstacle recorded for the next step.

Round 328 completes the first clause of the generic extension definition for the base ring that the source actually uses,
namely the polynomial ring in one variable.  The polynomial ring is identified with multivariable polynomials in one
variable, localizing at the element one leaves a ring unchanged, and the library supplies the missing instance that a
ring is a localization of itself away from a unit; composing these gives the required equivalence.  Two practical points
are recorded: the library lemma that provides that instance has to be imported and must be referenced with its
namespace, and the algebra equivalence obtained from the general localization comparison is over the polynomial ring as
base and has to be restricted to scalars over the original field.

Round 329 lands the base change of adjoining a root: tensoring `R[y]/(f)` with a commutative `R`-algebra `K` over
`R` yields `K[y]/(f.map)`, as a `K`-algebra, where the polynomial is mapped along the structure map of `K`.  The
forward map comes from the universal property of the base change of algebras applied to the map that adjoins a root,
and the backward map from the universal property of adjoining a root of the mapped polynomial, whose obligation
reduces to the defining relation of the original root through the compatibility of evaluation with polynomial
mapping and of the two structure maps of the tensor product.  The two composites are identities because they agree on
the root, respectively on the image of the root in the tensor product, and the latter generates the tensor product as
an algebra over the new base by the base change of the generation statement for the root.  The specialization to the
Artin--Schreier carrier records the shape of a specialization as it occurs in the source, namely the tensor product
of the carrier with the target field; the existence of a root of the mapped polynomial in a Galois extension of the
target field is not addressed here.  Two practical points are recorded: the tensor notation has to be opened inside
this section, and the polynomial operations have to be referred to with their namespace because the file has the
multivariable polynomial namespace open.

Round 330 lands the generation half of the structure theorem for cyclic extensions of degree a prime in
characteristic that prime.  If an automorphism of a domain over a field sends an element to its successor, then
the conjugates of that element under the powers of the automorphism are as many distinct elements as the
characteristic, so a polynomial over the base vanishing at the element either is zero or has degree at least that
prime; consequently a monic polynomial of that degree vanishing at the element divides every polynomial vanishing
there.  Combining this divisibility with the dimension count for the Artin--Schreier carrier yields an isomorphism
between the carrier and any finite-dimensional domain carrying an element that satisfies the Artin--Schreier
relation, provided the dimension over the base equals the prime.  Three practical points are recorded: a statement
that does not mention the base field loses the section instances, so the characteristic has to be requested in the
statement itself; injectivity is not proved by introducing one element and a vanishing hypothesis, because the
definition of injectivity takes two elements and an equality; and instances are registered with an anonymous local
binding rather than with a local instance command.  The existence of such an element, which is the other half of
the structure theorem quoted by the source, is not addressed here.

Round 331 determines the fixed points of a nontrivial automorphism of a domain over a field when the degree of
the extension is a prime.  Since a domain finite dimensional over a field is a field, the intermediate fields are
available, and the degree over the base of the field generated by a fixed element divides the degree of the whole
extension, hence is either one or the prime; in the second case that intermediate field is everything, so the
automorphism fixes the whole extension and is trivial, contrary to the hypothesis.  Therefore the fixed element
lies in the base.  This is the half of the cyclic structure theorem that supplies the Artin--Schreier relation
with a coefficient in the base, and that identifies the kernel of the difference of the automorphism and the
identity with the base.  Three practical points are recorded: a proof that a commutative ring is a field does not
provide the field instance that the theory of intermediate fields requires, so the instance has to be built from
it; the two lemmas about the degree of the top intermediate field have the same name modulo a prime and opposite
meanings, the one without the prime being the degree over the top field; and the lemma stating that a set is
contained in the field it generates takes the set and the membership as separate arguments.  The existence of an
element moved to its successor by the automorphism, which is the other half, is not addressed here.

Round 332 produces an element moved to its successor by a nontrivial automorphism of a domain over a field of
prime characteristic when the degree of the extension is that prime.  The difference of the automorphism and the
identity is nilpotent with exponent the prime, its kernel is the base by the previous round, and if the unit of
the ring were not in its range then the base and the range would be complementary, so the range would be stable
under the difference and hence, being killed after as many steps as the prime, would be zero, making the
automorphism trivial.  Therefore the unit lies in the range, which is the required element.  This route replaces
the classical one through the nonvanishing of the trace, which would require the normal basis theorem.  Three
practical points are recorded: the Frobenius identity for a difference requires the primality of the exponent as
an instance, which has to be registered from the hypothesis; the lemmas identifying multiplication of
endomorphisms with composition and the recursion of powers live in the endomorphism namespace rather than the
linear map one; and there is no lemma stating that the image of the kernel is the bottom submodule, so that
identity is proved directly.  The realization property itself, which assembles these ingredients, is not
addressed here.

Round 333 assembles the three preceding rounds into the structure theorem for cyclic extensions of prime degree
in prime characteristic: a Galois extension of a field by a cyclic group of prime order, in characteristic that
prime, is obtained by adjoining a root of a polynomial of the form the prime-th power minus the element minus a
constant of the base.  An element moved to its successor by a generating automorphism exists by the previous
round, the difference of its prime-th power and itself is fixed by the automorphism and hence lies in the base by
the round before, and the isomorphism between the extension and the carrier is the one of the round before that.
One practical point is recorded: the Frobenius identity for a sum also requires the primality of the exponent as
an instance, which again has to be registered from the hypothesis.  The realization property, which additionally
requires producing the specialization and treating the case of a split algebra, is not addressed here.

Round 334 extracts, from the hypothesis that a Galois algebra over a field carries an action of the cyclic group
of prime order, the explicit data consumed by the structure theorem of the preceding rounds.  The generator of the
group yields an algebra automorphism whose prime-th power is the identity, since the powers of the generator
correspond to the multiples of the unit of the residue ring, and the automorphism is nontrivial because the action
is faithful and the generator is not the identity.  The degree of the extension over the base equals the prime
because the degree equals the order of the group and the order of the residue ring is the prime.  Three practical
points are recorded: the round is carried out at the lowest universe, because the degree computation available
requires the base, the algebra and the group to live in the same universe while the residue ring does not; the
lemmas relating powers of the additive-to-multiplicative tag to multiples live in the root namespace rather than
under the tag; and the fact that the unit of the residue ring is nonzero is best obtained from the characteristic
rather than from the general lemma about units of nontrivial rings.  The assembly of the specialization and the
tensor product, and the case of a split algebra, are not addressed here.

Round 335 closes the domain case of the realization property for cyclic groups of prime order in characteristic
that prime.  The generator of the group supplies a nontrivial automorphism of prime order by the previous round,
the structure theorem of the round before that produces a coefficient in the base together with an isomorphism
from the extension to the Artin--Schreier carrier, the coefficient defines the specialization of the polynomial
ring by evaluation, and the base change of the carrier along that specialization, established five rounds
earlier, provides the remaining isomorphism.  What results is a specialization and an algebra structure on the
target field, compatible with it, such that the extension is isomorphic to the tensor product of the carrier with
the field.  Three practical points are recorded: the structure theorem needs the characteristic of the target
field, which has to be registered from the characteristic of the base together with injectivity of the structure
map; the algebra structure on the target is registered with an anonymous local binding rather than with a local
instance command; and the identification of the value of the structure map on the variable with the coefficient
has to be performed on the isomorphism before it is used, since the goal already displays the coefficient.  The
realization property itself, whose quantifier also ranges over algebras that are not domains, and the case of a
split algebra, are not addressed here.

Round 336 begins the split case of the realization property for cyclic groups of prime order.  The case is split
further: first the carrier at the zero coefficient has to be identified with a product of copies of the base, and
second the algebra under consideration has to be identified with such a product.  This round records the first
half of the first step, namely that the residue classes of the integers modulo the prime are roots of the
polynomial defining the carrier at the zero coefficient, so that there are as many distinct roots as the degree;
this is Fermat's congruence read through the characteristic.  Two practical points are recorded: the algebra
structure of the residue ring on the field is available as a definition rather than as an instance, so the
structure map has to be named explicitly in statements; and naming a lemma for evaluation that does not exist
silently leaves a proof hole, which the axiom check exposes, so the evaluation form of the root statement is
deferred until the correct lemma has been located.  The identification of the carrier with the product, and the
identification of the algebra with the product, are not addressed here.

Round 337 identifies the carrier at the zero coefficient with a product of copies of the base, completing the
first step of the split case of the realization property for cyclic groups of prime order.  The identification
goes through the evaluation of polynomials at the residue classes of the integers modulo the prime, which are
roots of the defining polynomial as recorded in the previous round; the resulting map out of the carrier is
injective because a polynomial vanishing at all those points reduces modulo the defining polynomial to one of
smaller degree that still vanishes there, and therefore is divisible by the defining polynomial; equality of the
two dimensions then upgrades injectivity to bijectivity.  Two practical points are recorded: the passage between
evaluation of a polynomial in the algebra and evaluation in the base, which the library does not provide
directly, has to be bridged by a small lemma of its own, and the intermediate values are best kept in the
algebra-valued form with a single conversion at the end; and a local definition introduced by a let-binding
cannot be substituted away, so the case of a degenerate coefficient has to be handled by rewriting instead.
The identification of the algebra under consideration with such a product, and hence the split case itself, are
not addressed here.

Round 339 supplies the prerequisite of finiteness for the ring case of the Galois criterion: the Artin--Schreier
carrier is a finite module over an arbitrary nontrivial commutative ring, not merely over a field.  The carrier
carries a power basis by an earlier round, whence it is free, and finiteness follows from the positivity of its
rank, which that earlier round computes as the prime.  One practical point is recorded: the criterion converting a
positive rank into finiteness requires freeness, which a basis does not register as an instance by itself, so the
freeness instance has to be introduced explicitly from the basis.  The bijectivity of the crossed-product map
over a ring, and the projectivity of the carrier, are not addressed here.

Round 340 continues the prerequisites of the ring case of the Galois criterion by recording that the
Artin--Schreier carrier is projective over an arbitrary nontrivial commutative ring, which is the second half of
the conclusion that the source derives from the normal basis.  Freeness follows from the power basis of an earlier
round, and projectivity from freeness.  The route through the structure of etale algebras is examined and set
aside: the library's statement that an etale algebra is a finite product of separable field extensions is a
statement over a field, so it does not apply to the ring case and cannot serve as the wheel for the ring case of
the criterion.  The bijectivity of the crossed-product map over a ring is not addressed here.

Round 341 takes the first step of the explicit-inverse route to the ring case of the Galois criterion, by
computing the orbit of the candidate normal basis element.  That element is the power of the root one below the
prime; a power of a ring homomorphism applied to a power of the root is the power of the image of the root, and
the previous rounds have recorded that the image of the root is the root shifted by the coefficient, so the orbit
is given by the corresponding shifted powers.  One practical point is recorded: rewriting a power of the root
under a ring homomorphism uses the direction of the power rule that produces a power of the image, not the
direction that collects one.  That the orbit forms a basis, and hence the bijectivity of the crossed-product map
over a ring, are not addressed here.

Round 342 records the determinant half of the route to the ring case of the Galois criterion, after a probe shows
that the route through the endomorphism ring as a module over the algebra cannot be taken: the library's algebra
structure on the endomorphism ring of a module requires the scalars to act on the ring of endomorphisms, which the
structure map of an algebra does not provide.  The record instead goes through the moment map on the space of
coefficient vectors, whose matrix has as its entries the powers of the shifted roots.  Its determinant is the
Vandermonde determinant of the shifted roots, and the difference of two shifted roots is the structure map applied
to the difference of the corresponding residue classes.  Distinct residue classes have a nonzero difference in the
residue ring, which is a field, so that difference is a unit there and its image under the structure map is a unit
in the base; a product of units is a unit, so the determinant is a unit.  Eight declarations are recorded: that
distinct residue classes have unit difference in the base, that the difference of two shifted roots is the
structure map applied to the difference of the classes, that such a difference is a unit, that pairwise unit
differences make a Vandermonde determinant a unit in general, the family of shifted roots itself, the injectivity
of the numbering of the residue classes by the initial segment, the unitness of the Vandermonde determinant of the
shifted roots, and the transposed form of that matrix, which is the one the next round consumes.  Four practical
points are recorded: an additive identity involving the structure map is not closed by the ring tactic but by its
normalizing variant; the injectivity of the numbering is best obtained from the congruence criterion for casts of
natural numbers rather than from the value of a residue class; the transpose notation is unavailable in this file,
so the matrix transpose has to be named; and the lemmas about units of finite products live in the namespace of the
unit predicate rather than in that of finite sums.  The invertibility of the moment map itself, and hence the
bijectivity of the crossed-product map over a ring, are not addressed here.

Round 343 wires the moment map to the crossed-product map for the ring case of the Galois criterion.  The action
of a group element on a power of the root is the corresponding power of the shifted root, and the numbering of the
residue classes by the initial segment is an equivalence whose values are definitionally the tagged residue
classes, so that a sum over the group can be reindexed to a sum over the initial segment.  Reading the
crossed-product map at a power of the root then gives the moments of the coefficient vector of the element, that
is, the product of the moment matrix with that vector.  The moment map so defined is invertible because the
determinant of the moment matrix is a unit by the previous round, and the passage from an invertible determinant
to an invertible linear map is supplied by the library's construction of a linear equivalence on a function space,
which needs no choice of basis.  Injectivity of the crossed-product map follows: if the map vanishes on an element,
then all moments of its coefficient vector vanish, so that vector is zero, and since every group element is a
tagged residue class the element itself vanishes.  This replaces the argument of the field case, which divides by
a nonzero coefficient and therefore needs the algebra to be a field; over a ring the moment map supplies the same
conclusion.  Five declarations are recorded: the action on a power of the root, the numbering equivalence, the
moment form of the crossed-product map, the moment matrix together with the moment map, its invertibility and its
evaluation formula, and injectivity.  Three practical points are recorded: the scalar action does not expose the
shift map syntactically, so the goal has to be restated by definitional equality before the power and root rules
apply; an invertible determinant is turned into an invertible linear map by the library's construction on function
spaces, which avoids naming a basis; and reindexing a sum over the group is done along an equivalence built from a
bijectivity proof, whose point values are definitional, with the surjectivity of the numbering obtained from the
value of a residue class.  Surjectivity of the crossed-product map, and hence its bijectivity and the Galois
criterion for the ring case, are not addressed here.

Round 344 completes the ring case of the Galois criterion for the Artin-Schreier carrier by proving the
crossed-product map surjective, hence bijective, and assembling the criterion.  The values of the carrier's power
basis are identified with the powers of the root, so that a linear map can be checked on those powers.  An element
with prescribed coefficients is produced by the construction of a skew monoid algebra element from a finitely
supported function, so that no coefficient of a finite sum of basis vectors has to be computed; with the moment
solution of the previous round, the crossed-product map at a power of the root is then the corresponding moment of
that element, and agreement with the given linear map on the power basis finishes the proof.  Bijectivity follows,
and the criterion is assembled from faithfulness, the fixed base and bijectivity, so that the Artin-Schreier
carrier is Galois with the cyclic group of prime order over any domain of characteristic that prime, which is the
statement the source derives from its structure results.  Four declarations are recorded: the values of the power
basis, surjectivity of the crossed-product map, its bijectivity, and the Galois criterion for the carrier.  Four
practical points are recorded: the equation expressing a power basis vector as a power of the generator is a field
of the power basis structure rather than a lemma, so the index has to be supplied explicitly, and the
identification of the generator with the root together with the equality of the exponents is best recorded
separately; the evaluation of a finitely supported function built from a function is definitional, whereas a lemma
naming it does not exist; an element with prescribed coefficients is best produced by the constructor from a
finitely supported function, which avoids computing coefficients of finite sums; and two linear maps are proved
equal from their agreement on a basis by the named extensionality lemma of the basis.  The case of a base ring that
is not a domain, the remaining clauses of the source's structure result, and the realization property, are not
addressed here.

Round 345 removes the hypothesis that the base ring is a domain from the ring case of the Galois criterion for the
Artin-Schreier carrier, so that the criterion holds over any commutative ring of the given prime characteristic.
The hypothesis entered only through the injectivity of the structure map of the adjoining construction, which the
library states for domains; over an arbitrary commutative ring the same conclusion follows from the fact that the
defining polynomial is monic of positive degree, since a constant lying in the principal ideal it generates
reduces to itself modulo that polynomial and also to zero.  With injectivity available, the faithfulness of the
action, the compatibility of the action with scalars and the bijectivity of the crossed-product map are combined to
give the criterion, all three without further hypothesis on the base beyond its characteristic.  Six declarations
are recorded: that the characteristic and the primality force the base to be nontrivial, that a constant killed by
the structure map is zero, that the structure map is injective, the faithfulness of the action, the compatibility
of the action with scalars, and the Galois criterion for the carrier over an arbitrary commutative ring of that
characteristic.  Three practical points are recorded: the degree computations for the defining polynomial require
the base to be nontrivial, which the characteristic and the primality supply; the criterion for a polynomial to be
its own remainder modulo a monic divisor is available as an equivalence rather than as a degree comparison, and the
comparison of degrees is made through the transitivity of the order rather than by rewriting; and the general
assembly lemma for the criterion requires the base, the algebra and the group to live in the same universe, which
the group of residue classes does not, so the three clauses are filled in directly instead.  The remaining clauses
of the source's structure result and the realization property are not addressed here.

Round 346 treats the split branch of the realization property for the cyclic group of prime order.  If the algebra
to be realized is isomorphic, as an algebra over the field, to the product of the prime many copies of that field,
then the specialization sending the variable to zero realizes it: the base change of the carrier along that
specialization is the carrier at the zero coefficient, and that carrier is isomorphic to the product of the copies,
so composing the two isomorphisms with the given one yields the required isomorphism.  This branch does not use the
hypothesis that the algebra is Galois, only the isomorphism with the product.  With the branch in place, the
realization property for the carrier over the polynomial ring follows from a single dichotomy, namely that a Galois
algebra with the cyclic group of prime order over a field is either a finite domain or a product of copies of the
field; the two branches of the dichotomy are supplied by the domain case of an earlier round and by the split
branch proved here.  Two declarations are recorded: the split branch of the realization, and the reduction of the
realization property to the dichotomy.  One practical point is recorded: the base change isomorphism is stated with
the tensor product on the left, so its direction has to be reversed once before it is composed, and reversing it
twice gives the wrong composite.  The dichotomy itself is not proved here, and neither is the realization
property, the generic extension, nor the source's theorems.

Round 347 assembles the whole of the source's theorem on the generic extension for the cyclic group of prime order,
conditionally on the dichotomy of the previous round.  The first clause, that the ring is a localization of a
polynomial ring, holds for the polynomial ring itself; the second, that the carrier is Galois, holds over any
commutative ring of the prime characteristic; and the third, the realization property, is obtained from the
reduction of the previous round together with the equivalence between its explicit and its plain form.  The
resulting statement is the source's theorem for the cyclic group of prime order, and the witness form of the
generic extension follows from the same three clauses.  Two declarations are recorded: the generic extension for
the carrier over the polynomial ring, and the nonemptiness of the witness, both under the dichotomy.  Two practical
points are recorded: the action on the carrier has to be registered as a local instance whenever a scalar action
appears in a statement, and the hypotheses of the criterion for this carrier are best given as a type class rather
than as an explicit proof, since the action on the carrier enters the elaboration of the statement itself.  The
dichotomy is not proved here, and hence neither is the source's theorem unconditionally.

Round 348 begins the multiplicative counterpart of the carrier chain, for the clause of the source's structure
result that concerns the cyclic group of order coprime to the characteristic.  The carrier is the adjoining of a
root of the polynomial that is the variable raised to that order minus the coefficient, its power basis and its
rank are computed as in the additive case, and the substitution sending the variable to the coefficient times the
variable is shown to fix the defining polynomial, which yields a ring homomorphism of the carrier sending the root
to the coefficient times the root.  The contrast with the additive case is recorded: there the substitution shifts
the defining polynomial by a constant, and it is the difference of two shifted roots rather than the polynomial
itself that becomes the unit whose existence drives the criterion; here the polynomial is fixed, and the nodes of
the corresponding matrix are the root times the powers of the coefficient, whose pairwise differences are products
of the root with a unit of the base field.  Seven declarations are recorded: the carrier, the monicity and the
degree of the defining polynomial, the power basis, the rank, the substitution identity, the evaluation obligation
and the shift homomorphism together with its two computation rules.  Three practical points are recorded: the
monicity lemma for this polynomial asks for a nonzero exponent rather than a positive one; the degree lemma asks
for no exponent hypothesis but for the base to be nontrivial, and an unused explicit hypothesis has to be marked;
and the evaluation rule for constants produces the structure map rather than the constant polynomial, so the
identification of the two has to be inserted.  The Galois criterion for this carrier, the group action, the
realization property and the source's theorem for this case are not addressed here.

Round 349 records the group structure of the shift of the Kummer carrier.  Two shifts compose to the shift by the
product of their coefficients, the shift by one is the identity, and a shift by a unit is an automorphism, its
inverse being the shift by the inverse of that unit.  The composition law is proved on the two generators of the
carrier, the coefficients and the root; the automorphism is proved by showing that the two composites with the
inverse shift act as the identity, which is done inside the carrier, since rewriting the product of a unit with its
inverse inside the argument of the shift would change the type of the proof that the coefficient is a root of
unity.  Three declarations are recorded: the composition law, the identity of the shift by one, and the
bijectivity of a shift by a unit.  Two practical points are recorded: a rewrite inside the argument of the shift is
to be avoided because the proof that the coefficient is a root of unity depends on it, and instead the product is
computed inside the carrier; and a large simplification with restricted lemmas easily fails to terminate and, when
it does not, is reported as containing unused arguments, so the steps are given individually.  The action of the
cyclic group on the carrier, the Galois criterion for it, the realization property in this case and the source's
theorem for it are not addressed here.

Round 350 records two prerequisites of the group action and of the criterion for the Kummer carrier.  First, the
root is a unit as soon as the coefficient is one, since the product of the root with its power one below the order
is the image of that coefficient.  Second, the powers of the shift act on the root by multiplying it by the
corresponding power of the coefficient, and they still fix the coefficients; both are proved by induction, the
induction step for the root using the composition law of the previous round.  Three declarations are recorded: the
unitness of the root, the invariance of the coefficients under powers of the shift, and the action of powers of the
shift on the root.  Two practical points are recorded: multiplying two ring homomorphisms is composition only up to
definitional equality, so the value of a product at an argument has to be restated explicitly rather than obtained
from a lemma; and the two recursion equations for powers produce the new factor on different sides, so the step
that collects a power of the coefficient has to use one of them and the step that collects a power of the
coefficient in the target the other.  The group action on the carrier, the Galois criterion for it, the realization
property in this case and the source's theorem for it are not addressed here.

Round 351 constructs the action of the cyclic group on the Kummer carrier.  The group element acts by the shift
whose coefficient is the corresponding power of the distinguished unit, taken at the canonical representative of
the residue class, and the action axioms reduce to the composition law of the previous rounds together with the
compatibility of that canonical representative with addition and the reduction of powers modulo the order.  Two
auxiliary lemmas are recorded: powers of the distinguished unit have the required order, and the shift depends only
on the value of its coefficient, so that two shifts with the same coefficient but different proofs of that order
agree; the latter is what allows the group law to be proved without rewriting inside the argument of a shift.  Four
declarations are recorded: the order of the powers of the unit, the independence of the shift from the proof, its
value form, and the action itself.  Three practical points are recorded: the proof that the coefficient has the
required order must be a named lemma, since an inlined proof cannot be matched syntactically and rewriting it
fails with a motive error; an equality of coefficients is transported to an equality of shifts through the
independence lemma rather than by rewriting, for the same reason; and the composition law has to be applied with all
of its arguments, including the three proofs of the order condition, since they cannot be inferred.  Faithfulness of
the action, the Galois criterion for the carrier, the realization property in this case and the source's theorem
for it are not addressed here.

Round 352 records the injectivity of the structure map of the Kummer carrier and the faithfulness of the action.  The
injectivity is proved as in the additive case, by reducing a constant modulo the defining polynomial, which is
monic of positive degree.  Faithfulness is proved by evaluating at the root: if a group element acts trivially, then
the structure map applied to one less than the corresponding power of the distinguished unit annihilates the root,
and since the root is a unit the structure map is injective, so that power is one; primitivity of the unit then
forces the exponent to be divisible by the order, whence the canonical representative of the residue class is zero.
The conclusion is stated as the triviality of the kernel rather than as the type class of faithfulness, because the
action carries the distinguished unit and its order as explicit arguments which do not occur in its result type, so
that it cannot be registered for type class synthesis; this is recorded as a difference from the additive case,
where the coefficient does occur in the result type.  Three declarations are recorded: the vanishing criterion for
the structure map, its injectivity, and the triviality of the kernel of the action.  Three practical points are
recorded: cancelling a unit is done by extracting the unit first, since rewriting with its specification otherwise
fails with a motive error; collecting a power under the structure map uses the direction of the power rule that
collects rather than the one that distributes; and after cancelling a unit the zero may stand on the left, which
requires the corresponding lemma for multiplication by zero on the left.  The fixed base, the Galois criterion for
this carrier, the realization property in this case and the source's theorem for it are not addressed here.

Round 353 records the invariance of the coefficients under the action and the determinant half of the criterion for
the Kummer carrier.  The action sends a scalar multiple of an element to the same scalar multiple of its image,
which follows from the shift being a ring homomorphism that fixes coefficients; the statement is given with the
shift displayed explicitly, since the action cannot be registered for type class synthesis.  For the determinant,
the nodes are the products of the root with the powers of the unit, and their differences are the structure map
applied to the differences of those powers times the root; each such difference is a unit, being the product of the
image of a nonzero element of the base field with the root, which is itself a unit.  The determinant of the
Vandermonde matrix of the nodes is therefore a unit, and so is that of its transpose, which is the matrix whose
entries are the powers of the nodes.  The nonvanishing of the differences of powers of a primitive root is proved
directly from the injectivity of the power map below the order, which is shorter than the corresponding step in the
additive case, where a factorization of the difference of the shifted powers is needed.  Eight declarations are
recorded: the invariance of coefficients, the nodes, their differences, the unitness of those differences, the two
determinants, the nonvanishing of the differences of powers, and their unitness.  Four practical points are
recorded: the structure map and the algebra structure on the carrier are equal only up to definitional equality, so
the identification has to be restated; factoring a common factor out of a difference uses the reverse of the lemma
that distributes it; the order of the carrier has to be given explicitly in statements where the node family occurs
only under a matrix construction; and a unit of the base ring is transported to the carrier by the map on units.
The moment map, the bijectivity of the crossed-product map, the realization property in this case and the source's
theorem for it are not addressed here.

Round 354 records the moment form of the crossed-product map for the Kummer carrier and the injectivity of that map.
The shift is given in a form indexed by the group, agreeing with the action, and the action on powers of the root is
computed; the group is identified with the residue classes through a bijection that sends a residue to its canonical
representative, which allows the sum over the group to be reindexed along the nodes.  The moment matrix has the
powers of the nodes as its entries, its determinant is a unit by the previous round, so the associated linear map is
invertible, and from the moment form of the crossed-product map and the vanishing of that map on an element one
deduces that all coefficients of the element vanish.  Nine declarations are recorded: the indexed shift with its two
computation rules, the action on powers of the root, the bijection between the indices and the group, the moment
form, the matrix, the map, its invertibility, its values, and the injectivity.  The statements take the action as a
hypothesis together with the assumption that it agrees with the shift, because the action cannot be registered for
type class synthesis, and they take the invariance of coefficients as a further hypothesis, exactly as in the
additive case.  Two practical points are recorded: the computation rules for the indexed shift require all their
arguments to be named, since placeholders leave the ring undetermined, and the coefficient is the second explicit
argument rather than the unit; and aligning the exponents of the nodes requires reducing the canonical
representative of a residue class modulo the order, so the final step is not definitional.  Surjectivity of the
crossed-product map, the Galois criterion for this carrier, the realization property in this case and the source's
theorem for it are not addressed here.

Round 355 completes the criterion for the Kummer carrier by proving surjectivity and hence bijectivity of the
crossed-product map.  The values of the power basis are computed as in the additive case, and a given endomorphism
is matched by the moment map applied to its values on the powers of the root; the preimage is assembled from the
resulting coefficient family through the identification of the group with the indices, and the two maps agree on
the basis, hence everywhere.  With the injectivity of the previous round this gives bijectivity, so that the
criterion holds for this carrier in the same form as in the additive case, under the same formulation with the
action, its invariance of coefficients and its agreement with the displayed shift taken as hypotheses.  The three
clauses of the source's result for this carrier are therefore all present, but the packaged form of the criterion,
in which the action is an instance, is not available for this carrier, since the distinguished unit and its
primitivity cannot be recovered from the type; introducing a type class carrying that data is recorded as the next
step.  Three declarations are recorded: the values of the power basis, the surjectivity, and the bijectivity.  No new
practical difficulty arose in this round.  The packaged criterion, the realization property in this case and the
source's theorem for it are not addressed here.

Round 356 packages the criterion for the Kummer carrier, removing the need to carry the action as a hypothesis.  The
distinguished unit and the statement that its order is exactly the order of the group are collected in a type class
whose parameters are the base ring, the order and the coefficient, so that they all occur in the type of the
carrier; from this data the action of the group on the carrier is produced as an instance, the agreement of that
action with the displayed shift becomes definitional, and the invariance of coefficients and the criterion follow
from the previous rounds.  The three clauses of the criterion are then assembled into the packaged form, which is
the source's statement for this carrier.  A first attempt to register the action directly failed because the unit
and its order do not occur in the type of the carrier, so that they cannot be recovered during instance synthesis;
expressing the order as an equivalence between the vanishing of a power and divisibility by the order keeps the data
inside the base ring and suffices for the faithfulness argument.  Seven declarations are recorded: the data class,
the action instance, the agreement with the shift, the invariance of the scalars, the invariance of coefficients,
the faithfulness and the packaged criterion.  Two practical points are recorded: an omission command has to be
placed before the documentation comment rather than between it and the declaration, so unused instance assumptions
are instead given as explicit binders of the affected theorems; and the projections of the data class have to be
applied with all their arguments named.  The realization property in this case, the corresponding statement for
orders coprime to the characteristic and the source's remaining theorems are not addressed here.

Round 357 identifies the split Kummer carrier with a power of the base field.  The carrier with coefficient one is
the quotient by the polynomial that is the variable raised to the order minus one, and its points are the powers of
the distinguished unit; these satisfy the defining relation, since the order of the unit divides the order of the
group.  They are pairwise distinct, and here the multiplicative case differs from the additive one: in the additive
case distinctness comes from the injectivity of the structure map of the residue classes, which fails here, as for
instance the class of five in the integers modulo six maps to zero in a field of five elements; instead
distinctness follows from the order of the unit being exactly the order of the group.  The evaluation channel at
these points is injective by the interpolation criterion for a polynomial of degree below the order, and the two
sides have the same rank, so the channel is an isomorphism.  Three declarations are recorded: the defining relation
at the points, their distinctness, and the isomorphism.  Three practical points are recorded: the equation obtained
from an injective function has to be restated in the unfolded form before it can be used for rewriting; the two
branches of the dichotomy on the canonical representatives have to be matched with the correct formula; and the
arithmetic decision procedure does not know about divisibility, so the vanishing of the difference has to be
extracted first.  The model side of the split case, the Kummer realization for fields, the corresponding statement
for orders coprime to the characteristic and the source's remaining theorems are not addressed here.

Round 358 records the injectivity of the structure map of the base field into the coefficient ring, which is
load-bearing for supplying the data class of the previous round from the hypotheses of the source, and records an
obstruction met in that attempt.  The injectivity holds because in a field a nonzero difference is invertible, so
its image would be both invertible and zero, which is impossible in a nontrivial ring.  The attempt to build the
data class from a primitive root of the base field, and to supply the unitness of the differences of its powers,
did not succeed in this round: the coercion of the unit group map and the application of the ring homomorphism are
not syntactically the same, and the rewriting, reflexivity and restricted simplification tactics all fail to bridge
them.  Two candidate repairs are recorded: to carry out the power computations inside the unit group, where the map
on powers applies directly and equality of units is decided by their values, or to take the unit itself rather than
the element of the field as the field of the data class.  This is a probe-level reading and no negative claim is
made.  The data class built from a primitive root, the unitness of the differences of its powers, the source-side
usability of the criterion, and the source's remaining theorems are not addressed here.

Round 359 supplies the data class of the previous rounds from a primitive root in the base field, in the case where
the coefficient ring is that field, and sharpens the obstruction met in the general case to a single transport step.
In the case of the field itself the unit and the two required properties are exactly the primitivity hypothesis, so
no coercion occurs at all.  In the general case the power computations can now be carried out inside the unit
group, since composition of powers and equality of units by their values are available there; what remains is that
the statements of primitivity are about the element coerced into the field rather than about the power of the unit,
so that the identification of the value of a power of a unit with the power of its value has to be inserted
explicitly, and likewise the coercion of the unit group map has to be replaced by the application of the ring
homomorphism.  Two exact repairs are recorded: to prove the vanishing of the power as an equality of units and then
transport it along the value map, so that the ring homomorphism is never applied in the statement, or to state the
order condition of the class directly for the coerced unit.  One declaration is recorded, namely the data class in
the case of the base field.  The data class over a general algebra, the source-side usability of the criterion, and
the source's remaining theorems are not addressed here.

Round 360 supplies the data class of the previous two rounds over an arbitrary algebra from a primitive root of the
base field, supplies the unitness of the differences of the distinct powers of that root, and thereby closes the
source-side hypothesis chain of the criterion for orders coprime to the characteristic.  The obstruction recorded
in the two previous rounds was that the coercion of the unit group map and the application of the ring
homomorphism are not syntactically the same, so that neither rewriting nor reflexivity nor restricted
simplification could bridge them.  The repair is to carry out all power computations inside the unit group and to
cross into the ring exactly once, through a bridge stating that the value of a power of the image of a unit equals
the monoid homomorphism applied to the power of that unit; the bridge is proved from the value lemma of the unit
group map and the composition rule for powers, and it mentions the homomorphism as a free variable, so no coercion
occurs.  The order condition of the data class is then the bridge combined with the equivalence between the
vanishing of a power of a primitive root and divisibility by its order, together with the injectivity of the
structure map of the field recorded in the previous round; the vanishing of the power itself is the bridge applied
to the primitivity statement.  The powers of a primitive root indexed by the canonical representatives below the
order are pairwise distinct, which is the finite-set counterpart of the distinctness of the split points of an
earlier round and is proved by the same divisibility argument; consequently the differences of two distinct powers
are nonzero in the field, hence units, and units are carried to units by the structure map.  Supplying the instance
and that difference hypothesis to the packaged criterion of the criterion round gives the unconditional form of the
source's statement over an arbitrary algebra, whose hypotheses are exactly the unitness of the coefficient and the
membership of the root in the base field as printed in the source.  Seven declarations are recorded: the general
bridge, its specialization to the structure map, the equivalence of the vanishing of a power with the vanishing of
the corresponding power in the field, the data class over an arbitrary algebra, the distinctness of the powers, the
unitness of their differences, and the unconditional criterion.  Two practical points are recorded: rewriting does
not close a goal by reflexivity when the two sides differ only by the coercion of the ring homomorphism to a monoid
homomorphism, so an explicit reflexivity step has to be added; and the value lemmas of the unit group carry
different names in this version of the library than the ones anticipated in the previous round, so the proof was
arranged so that none of them is needed.  The tensor product statement, the dichotomy for the group of prime order,
the realization statements and the source's remaining theorems are not addressed here.

Round 361 proves the fixed point theorem for the criterion without any finiteness assumption, which is strictly
stronger than the version already in the library.  The existing version derives the fixed points from the theorem of
Artin on the cardinality of a group of automorphisms together with the degree of the extension, and therefore
carries finite dimensionality as a hypothesis; the new proof reads the fixed points off the third clause of the
criterion instead, which is the bijectivity of the trivial crossed product onto the endomorphism ring.  The image
of that map consists of endomorphisms that are linear over the fixed subring, because every group element fixes
that subring, and by the third clause this image is the whole endomorphism ring; hence linearity over the base field
and linearity over the fixed subring are the same notion.  If an element were fixed by the group but outside the
image of the field, a linear functional taking the value one at the unit would produce an endomorphism that
vanishes at the unit and does not vanish at that element, so that it would be linear over the base field without
being linear over the fixed subring, a contradiction.  One declaration is recorded.  Two practical points are
recorded: a conversion command for a local definition has to carry the type ascription, since otherwise the term is
not yet known to be a function and cannot be applied; and rewriting an equation whose left hand side occurs inside
the very term one wants to rewrite rewrites those inner occurrences as well, so the transport has to be composed
explicitly instead.  Finiteness over the base field, the identification of the degree with the order of the group,
the dichotomy and the source's remaining theorems are not addressed here.

## Toolchain upgrade (2026-10-15, appended)

The development was moved from mathlib `db584cd6` (2026-08-10) / Lean 4.33 to
mathlib `aa35a481e5` (2026-10-15) / Lean 4.35.0.  Twelve files needed
adaptation; all changes are local and preserve the statements:

| file(s) | adaptation |
|---|---|
| `P5b`, `S3`, `SubgroupPerm`, `ExtMHUncond` | `Finsupp.mapDomain_apply hf` became `Finsupp.mapDomain_apply_of_injective hf` |
| `EMFixed`, `SaltGeneric`, `SaltThm38` | the motive argument of `adjoin_induction` is named `motive`, not `p` |
| `EMIndep`, `SaltThm38` | `MvPolynomial.coeff v p` is now the projection `p.coeff v` |
| `SaltGeneric` | `TensorProduct.induction_on` lost its zero case and is now `TensorProduct.inductionOn` with the two cases `tmul` and `add` |
| `TateLayer`, `TateTrivial` | `End X` is a structure: `M.norm.asHom.toModuleCatHom`, `M.norm = 1` rather than `= 𝟙 M` |
| `PC` | `Equiv.setCongr` changed meaning; use `Equiv.subtypeEquivRight` |
| `EMDegree` | a set literal in named-argument position needs `Set.singleton` |
| `SaltThm38` | on `NoetherField F G = FractionRing (MvPolynomial G F)` two `F`-algebra instances are synthesizable and only propositionally equal; the intended one is pinned by a `local instance` together with a file-level `attribute [-instance] DivisionRing.toRatAlgebra` |

After the upgrade the development again compiles with no `sorry`
(`lake build`, 9176 jobs, zero errors), every declaration still depends only
on `propext`, `Classical.choice` and `Quot.sound`, and `SaltThm38_ABGV52.lean`
still declares 368 declarations.  The warning count of a full build is 924
lines (918 distinct), of which 218 are deprecations of names renamed in
mathlib; these are recorded, not yet rewritten.

## Round 362 (2026-10-15, appended)

`GaloisAlgebra_ABGV52.lean` gains the entry point of the finiteness step: from
the bijectivity of `deltaToEndRingHom` one extracts an element `x` of the skew
monoid algebra with `deltaToEndRingHom x = 1`, read pointwise as

    sum over g of (coeff g x) * (g • t) = t    for every t

together with the normalisation `sum over g of (coeff g x) = 1` obtained at
`t = 1`.  This is the skew-algebra counterpart of the dual element in the
classical proof that a Galois extension of rings is a finitely generated
projective module.  The finiteness statement itself is *not* proved in this
round: what is still missing is the step that turns the coefficients into
elements of the fixed ring.

## Round 363 (2026-10-15, appended)

`ABGV52/TauCetiCHR_ABGV52.lean` (new, 388 lines) is a verbatim port of the
Chase--Harrison--Rosenberg Theorem 1.3 from the TauCeti project
(https://github.com/TauCetiProject/TauCeti, Apache-2.0), namely
`TauCeti/RingTheory/Invariant/Free.lean` together with `TauCeti.smul_sum_smul`
from `TauCeti/RingTheory/Invariant/Basic.lean`.  The port holds the original
Apache-2.0 header; the file is otherwise unchanged.

It provides `tensorToPi` (the map `A ⊗[R] A → (G → A)` of the theorem), the
criterion `tensorToPi_surjective_iff` for free actions, `tensorToPi_bijective`,
and — under a free action with invariant ring `R` — `moduleFinite`,
`projective`, `faithfullyFlat`, `formallyUnramified` and `etale`.  Of these,
`projective` supplies the paper's `proposition-0-2(a)`, and `moduleFinite` is
the statement to be reused for the finiteness half of the dichotomy.

The port compiles unchanged because the TauCeti pin and this development's
upgraded pin are of the same generation; every declaration of the new file
depends only on `propext`, `Classical.choice` and `Quot.sound`.  What is *not*
in this file is the bridge from this development's `IsGaloisWithGroup` (the
bijectivity of `deltaToEndRingHom`) to the free-action hypothesis `hG` that the
ported statements take; that bridge is the next round's target.

## Round 364 (2026-10-15, appended)

The ported file gains a section that restates four of its theorems in this
development's notation, with the hypothesis written as the free-action
condition `hG` together with `Algebra.IsInvariant K L G`:
`moduleFinite_of_freeness`, `projective_of_freeness`,
`faithfullyFlat_of_freeness` and `formallyUnramified_of_freeness`.  Of these,
`projective_of_freeness` is the projective half of the paper's
proposition-0-2(a).

This round also corrects an earlier claim of this development.  Since
`deltaToEndRingHom` is a ring homomorphism, `deltaToEndRingHom 1 = 1`, so by its
injectivity the element produced in round 362 is necessarily `x = 1`; the
pointwise identity of that round is therefore vacuous and carries no Galois
content.  The reason is structural: the third clause of `IsGaloisWithGroup`
speaks of the bijectivity of `deltaToEndRingHom`, whose target is
`Module.End R S`, whereas the classical definition speaks of the bijectivity of
`S ⊗[R] S → (G → S)`, `a ⊗ b ↦ (a * g • b)`.  The two targets differ, so their
unit elements differ: in the classical form the unit is the function
`g ↦ [g = 1]` (orthogonality), while here it is the identity endomorphism.  The
step from the one form to the other is the substance of the Chase--Harrison--
Rosenberg equivalence of the two definitions of a Galois extension and is the
next round's target; it is a theorem, not a rewriting.

## Round 365 (2026-10-15, appended)

New file `ABGV52/LocalProduct_ABGV52.lean`: a finite commutative algebra over a
field is a product of local rings, assembled from mathlib's existing pieces.

* `isArtinianRing_of_finite`: `Module.Finite K L` gives `IsArtinianRing L`, via
  `IsArtinianRing.of_finite`;
* `localProductEquiv`: under `IsArtinianRing L`, the canonical isomorphism
  `L ≃ₐ[L] MaximalSpectrum.PiLocalization L`, whose right-hand side is
  `Π I : MaximalSpectrum L, Localization.AtPrime I.1`, via
  `MaximalSpectrum.toPiLocalizationEquiv`;
* `factor_isLocalRing`: each factor is a local ring;
* `finite_maximalSpectrum_of_finite`: the index set is finite;
* `exists_local_product_decomposition`: the packaged form.

Two points of craft.  The `AlgEquiv` type in the statement itself needs the
instance `DiscreteTopology (PrimeSpectrum L)`, so the decomposition can only be
stated in the `IsArtinianRing L` context; passing from `Module.Finite K L` to it
is the separate first item above.  And the instance
`IsArtinianRing.instDiscreteTopologyPrimeSpectrum` lives in
`Mathlib.RingTheory.Spectrum.Prime.Noetherian`, not in the file on prime
spectra.

This discharges the second of the three inputs of the `C_p`-Galois dichotomy
recorded in the working notes; the first (finiteness) is still open and the
third (transitivity of the `C_p`-action) is next.

## Round 366 (2026-10-15, appended)

The bridge from `IsGaloisWithGroup` to the free-action hypothesis is settled in
the field case, and this is a genuine dichotomy between fields and general
commutative rings.

`freeness_condition_of_field`: over a field, a faithful action already gives
`Ideal.span (Set.range fun a => g • a - a) = ⊤` for every `g ≠ 1`, without any
use of the bijectivity of `deltaToEndRingHom`.  Faithfulness supplies an `a`
with `g • a ≠ a`; the difference is then non-zero, hence a unit, hence the ideal
is the whole ring.

`moduleFinite_of_field_galois`: consequently, for a field extension with
`IsGaloisWithGroup` and `Algebra.IsInvariant K L G`, the extension is finite over
the base --- through the ported `moduleFinite_of_freeness`.

The dichotomy is that over a general commutative ring the same argument fails:
the elements `g • a - a` may all be zero divisors, so faithfulness gives no
unit.  The general case therefore still needs the bridge, which is the
Chase--Harrison--Rosenberg equivalence of the two definitions of a Galois
extension.  Since the `L` of the paper is a commutative algebra and not
necessarily a field, the finiteness half is not discharged by this round; what
it does give is the field case, and the candidate route of reducing the domain
case to it.

## Round 367 (2026-10-15, appended)

`ABGV52/LocalProduct_ABGV52.lean` gains the combinatorial core of the third
input of the dichotomy.

`card_orbit_eq_one_or_eq_prime`: an orbit of `Multiplicative (ZMod p)` for prime
`p` has cardinality `1` or `p`.  The proof multiplies the orbit and stabiliser
cardinalities to get `p`, so the orbit cardinality divides a prime.

`card_eq_one_or_eq_prime_of_pretransitive`: if the action is transitive, then the
ambient finite type has cardinality `1` or `p`.

Two craft notes.  The `Fintype` instances for an orbit and for a stabiliser are
not synthesised automatically, so the two statements take them as arguments; in
the intended use `α` is `MaximalSpectrum L`, which is finite.  And the usable
instance is `Fintype (ZMod p)`: from `Fintype (Multiplicative (ZMod p))` alone
`ZMod.card` cannot be applied.

What remains of this third input is its algebraic part: transitivity of the
action on `MaximalSpectrum L` (via a `G`-invariant idempotent argument), the
conclusion `L ≅ K^p` in the case of `p` factors (fixed elements of a product
under a cyclic permutation are diagonal), and the hardest step, that a single
factor forces `L` to be a domain.

## Round 368 (2026-10-15, appended)

`fixed_idempotent_eq_zero_or_one`: if every element of `L` fixed by `G` lies in
the image of the base field `K`, then a `G`-fixed idempotent of `L` is `0` or
`1`.  Such an idempotent is `algebraMap k` for some `k`; idempotence plus
injectivity of `algebraMap` gives `k * k = k`, hence `k * (k - 1) = 0`, and a
field has no zero divisors.

This is the engine of the first algebraic step of the third input of the
dichotomy.  If the action on the factors of the product decomposition were not
transitive, a non-empty proper `G`-stable subset `S` of the index set would give
the `G`-fixed idempotent `sum over i in S of e_i`, neither `0` nor `1`, a
contradiction; transitivity then combines with `card_eq_one_or_eq_prime_of_
pretransitive` of round 367 to give index set `1` or `p`.

The assembly itself is not in this round: it needs the factor permutation induced
by the action to be tied to `localProductEquiv` of round 365.

## Round 369 (2026-10-15, appended)

The finiteness half is reduced to a single named hypothesis, with all the wiring
around it proved.

`DeltaGaloisFreenessHyp` is the bridge: it says that this development's
`IsGaloisWithGroup`, whose third clause is the bijectivity of `deltaToEndRingHom`
into `Module.End R S`, implies the free-action condition used by the classical
theory, equivalently the surjectivity of `S ⊗[R] S → (G → S)`.  It is named,
type-locked, and carries its source: the equivalence of the two definitions of a
Galois extension is the substance of Chase--Harrison--Rosenberg (1965), and it is
a theorem rather than a rewriting.  The field case is proved in this development
(round 366); the general commutative case is not, the elements `g • a - a` being
allowed to be zero divisors there.

`moduleFinite_of_deltaGaloisFreenessHyp` and
`projective_of_deltaGaloisFreenessHyp` then derive, from that hypothesis and
`Algebra.IsInvariant K L G`, that `L` is finite and projective over `K`.  The
latter is the paper's proposition-0-2(a).  Nothing here is claimed to be proved
unconditionally: the hypothesis is recorded, and every conclusion that uses it is
conditional on it.

## Round 370 (2026-10-15, appended)

With the dichotomy phase closed -- the local product decomposition proved, the
finiteness half reduced to one named hypothesis with all its wiring checked --
this round turns to the second phase, the named hypotheses of the main chain.

`rationalFunctionField_algEquivMap`, the second of the two bricks that G1 and G2
need: an isomorphism `K ≃ₐ[F] L` extends to `K(t_1,...,t_n) ≃ₐ[F] L(t_1,...,t_n)`,
by `MvPolynomial.mapAlgEquiv` on the numerator and
`IsFractionRing.algEquivOfAlgEquiv` to pass to fraction fields, the technique
already used for G0.

For the first brick, the flattening of a tower of rational function fields, the
missing API has been located: `MvPolynomial.sumAlgEquiv` together with
`finSumFinEquiv`.  What is still missing is the passage from polynomials over a
fraction field to polynomials over the base, that is
`FractionRing (MvPolynomial sigma (FractionRing A)) ≃ FractionRing (MvPolynomial
sigma A)`, for which no ready-made lemma was found.

A note of round 2 of this file is corrected here: the remark that
`MvPolynomial.map`, `map_map` and `renameEquiv` do not exist was a reading of the
old pin.  On the upgraded pin `MvPolynomial.map` and `MvPolynomial.renameEquiv`
are both present; `MvPolynomial.finSumEquiv` indeed does not exist and is
superseded by `sumAlgEquiv`.

## Round 371 (2026-10-15, appended)

A search of mathlib by content, rather than by name, shows that
`Mathlib/Algebra/MvPolynomial/` and the fraction ring file have no lemmas in
common, so the bridge from polynomials over a fraction field to polynomials over
the base has to be built here.

`RationalFunctionFieldTowerHyp`, with a type lock, records the first brick of G1
and G2: the flattening `(K(t_k))(s_n) ≅ K(u_{k+n})` of a tower of rational
function fields.  `isStablyRational_rationalFunctionField` then derives G1, the
add-variables closure, from that brick: from `K(t_n) ≅ F(x_m)` one gets
`(K(t_k))(s_n) ≅ K(u_{k+n}) ≅ K(u_{n+k}) ≅ (K(t_n))(s_k) ≅ (F(x_m))(s_k) ≅
F(x_{m+k})`, using the brick three times, the extension of isomorphisms of round
370 once, and commutativity of addition once.  The statement takes the brick both
for the extension `K/F` and for `F/F`.

The brick itself is not proved here.  Its proof is fixed for the next round: show
that `MvPolynomial sigma (FractionRing A)` is the localisation of
`MvPolynomial sigma A` at the non-zero divisors, the surjectivity clause by
clearing denominators with the finite product of the denominators of the
coefficients over the support.

Two craft notes: eliminating a `Nonempty` into a large type trips
`propRecLargeElim`, so `Classical.choice` is used instead; and for the same
reason `h.1` cannot be used to project a `Nonempty`.

## Round 372 (2026-10-15, appended)

`mvPolynomial_tower`, unconditional: `K[x_1,...,x_k][y_1,...,y_n]` and
`K[u_1,...,u_{k+n}]` are isomorphic as `K`-algebras.  The proof assembles
`MvPolynomial.sumAlgEquiv`, which identifies `K[S_1 ⊕ S_2]` with
`K[S_1][S_2]`, and `MvPolynomial.renameEquiv` along `finSumFinEquiv`, with
`finCongr` for commutativity of addition.

This is the denominator-free half of the first brick, and it narrows that brick
to a single localisation step: the fraction ring of `MvPolynomial sigma
(FractionRing A)` is the fraction ring of `MvPolynomial sigma A`.  For that step
mathlib was found to have nothing, and the pending proof is the clearing of
denominators described in round 371.

## Round 373 (2026-10-15, appended)

Two parts of the clearing of denominators for the first brick.
`C_mem_nonZeroDivisors`: a non-zero divisor of the base ring remains a non-zero
divisor as a constant polynomial, checked coefficient by coefficient.
`isUnit_algebraMap_fractionRing`: a non-zero divisor becomes a unit in the
fraction ring, by `IsLocalization.map_units`.

These are what the pending localisation statement needs; what remains for it is
its surjectivity clause, the finite product of denominators over the support, and
the equality clause.

Three points of craft, all recurring.  `mem_nonZeroDivisors_iff` is a
conjunction, one clause for each side of the multiplication, not a single
universal statement.  `IsLocalization.map_units` takes an element of the
submonoid, not an element with a membership proof.  And `MvPolynomial.coeff` is
still the dot notation `p.coeff v`, as already corrected in round 364; there is
no `coeff_mul_C`, so one commutes and uses `coeff_C_mul`.  A further trap: over a
domain `simpa` will over-simplify `x * a = 0` into the disjunction
`a = 0 ∨ x = 0`, so the goal has to be fixed by an ascription before `exact`.

## Round 374 (2026-10-15, appended)

`exists_denom_mul_eq_algebraMap`: every element of the fraction ring, multiplied
by a suitable non-zero divisor, lies in the image of the base.  This is the
coefficient-level statement of clearing denominators, obtained from
`IsLocalization.surj`, whose shape is
`exists x : R x M, z * algebraMap R S x.2 = algebraMap R S x.1`.

The polynomial-level version, which is the substance of the surjectivity clause
of the pending localisation statement, is *not* in this round: the draft ran into
ten API errors, among them that `Finset.prod_mem` does not exist.  The draft was
withdrawn and its proof plan, with the offending names, is kept in the file as a
block comment; nothing is claimed to be proved there.

## Round 375 (2026-10-15, appended)

`prod_mem_nonZeroDivisors`: a finite product of non-zero divisors is a non-zero
divisor, by `Submonoid.prod_mem`; the name `Finset.prod_mem` does not exist.

The polynomial-level clearing lemma is again not in this round.  Two rounds of
iteration left three API errors, so the draft was withdrawn and the facts
established while trying are kept in the file as a block comment: the support of
an `MvPolynomial` consists of exponent vectors `sigma →₀ ℕ` rather than elements
of `sigma` (the cause of five type errors); `coeff_map` must be rewritten before
`coeff_sum`; `coeff_map` exists while `map_coeff` does not; the main term is best
closed with a backwards rewrite and `ring`.  Still undetermined: the orientation
of the `if` in `coeff_monomial`, and the lemma giving `coeff = 0` outside the
support, `Finsupp.not_mem_support_iff.mp` being absent.

## Round 376 (2026-10-15, appended)

`exists_denom_mul_eq_map`: every element of `MvPolynomial sigma (FractionRing A)`
becomes, after multiplication by a suitable non-zero divisor (as a constant
polynomial), the image of an element of `MvPolynomial sigma A`.  This is the
substance of the surjectivity clause of the pending localisation statement.  The
proof takes a denominator for each coefficient, multiplies them over the support,
and checks the identity coefficient by coefficient.

Three API questions are now settled, all of which had blocked earlier attempts:
the `if` in `coeff_monomial` reads `if v = u`, matching `Finset.sum_ite_eq'`
rather than `Finset.sum_eq_single`; `Finset.prod_eq_mul_prod_diff_singleton` is
stated for an element *outside* the finset, so `Finset.mul_prod_erase` is the one
needed; and `coeff = 0` outside the support comes from
`MvPolynomial.mem_support_iff`, since `Finsupp.not_mem_support_iff` does not
exist.

One process note.  Interval-style scripted edits failed twice this round and one
of them silently overwrote a lemma committed in the previous round; the file was
restored with `git checkout` and the lemma inserted by line number instead.  Edits
to the development are henceforth done by reading the file, inserting or
replacing by line number, and compiling the single file immediately.

## Round 377 (2026-10-15, appended)

A search of mathlib by content, across the whole library rather than one
directory, turned up the bridge this development had been trying to build for
three rounds: `MvPolynomial.isLocalization`, in
`Mathlib/RingTheory/MvPolynomial/Localization.lean`, states that if `S` is the
localization of `R` at a submonoid `M`, then `MvPolynomial sigma S` is the
localization of `MvPolynomial sigma R` at `M.map C`.  The earlier verdicts that
mathlib had no such bridge were false, and the cause was that the searches were
confined to `Mathlib/Algebra/MvPolynomial/` while the file lives under
`Mathlib/RingTheory/MvPolynomial/`.  The reconnaissance rule now requires a
verdict of "mathlib has nothing" to record which directories were searched.

`map_C_le_nonZeroDivisors` is added: the image of the non-zero divisors of `R`
under `C` consists of non-zero divisors of `MvPolynomial sigma R`, which is the
hypothesis `M ≤ nonZeroDivisors R` needed by
`IsFractionRing.isFractionRing_of_isLocalization`.

The tower brick itself is *not* in this round.  With the bridge available, its
remaining obstacle is the instance `Algebra S T` for
`S = MvPolynomial sigma (FractionRing R)`, which has to be built through
`IsLocalization.lift`, together with the corresponding `IsScalarTower`.

## Round 378 (2026-10-15, appended)

`coeffMap`: the coefficient ring `K(t_1,...,t_k)`, that is `FractionRing A` for
`A = MvPolynomial (Fin k) K`, maps into the larger fraction ring
`FractionRing (MvPolynomial (Fin n) A)`.  The map is obtained from
`IsFractionRing.lift` applied to the composite `A → A[x] → T`, which is
injective because the target is a field.

This is the first component of the tower.  It yields an `Algebra` structure of
the coefficient ring on `T`, through `RingHom.toAlgebra`, and then, by
`MvPolynomial.eval₂Hom`, the instance `Algebra (MvPolynomial (Fin n)
(FractionRing A)) T` that `IsFractionRing.isFractionRing_of_isLocalization`
needs; that instance was the obstacle identified in round 377.

The tower statement itself is not in this round.  What remains is the
`IsScalarTower`, the assembly through `isFractionRing_of_isLocalization`, the
isomorphism between the two fraction rings, and the composition with
`mvPolynomial_tower`.

## Round 379 (2026-10-15, appended)

`towerAlgHom`: the ring homomorphism from `MvPolynomial (Fin n) (FractionRing A)`
to `FractionRing (MvPolynomial (Fin n) A)`, built by `MvPolynomial.eval₂Hom` from
the coefficient embedding of round 378, sending the variables to the images of
the `X i`.

The matching `IsScalarTower`, the third component, is not in this round.  The way
to do it is recorded: it must not be stated as a separate theorem, since
`IsScalarTower` is a class and passing the instance explicitly with `@` is
rejected; it belongs inside the proof of the tower, as
`letI := (towerAlgHom K k n).toAlgebra` followed by
`haveI := IsScalarTower.of_algebraMap_eq (fun x => ...)`.

One more API fact is recorded for the next attempt: the cases of
`MvPolynomial.induction_on` are `C`, `add` and `mul_X`; there is no `mul`.

## Round 381 (2026-10-15, appended)

Two computations for the algebraic part of the third dichotomy input, on the
split side where `L` is a product of copies of `K` permuted by `G`.

`eq_of_perm_transitive`: under a transitive permutation action, coordinates
along an orbit are equal.  `eq_const_of_perm_fixed`: consequently a fixed
function is constant, that is diagonal.  This is the computation behind
`L ≅ K^p ⟹ L^G ≅ K`.

Togther with the orbit cardinality lemma of round 367 (orbits of size 1 or p) and
the idempotent lemma of round 368 (a fixed idempotent is 0 or 1), the
mathematical content of the third input is now in place.  What is not in place is
the wiring: the action of `G` on the set of factors has to be constructed from
`localProductEquiv` of round 365, and the domain case still has to be argued.

## Round 382 (2026-10-15, appended)

A whole-library search, as the reconnaissance rule now requires, shows that
`PrimeSpectrum` already carries a `MulSemiringAction` in
`Mathlib/RingTheory/Spectrum/Prime/Basic.lean`, so the action of a group of ring
automorphisms on the prime spectrum does not have to be built here.  What is
still missing is its descent to `MaximalSpectrum`, the set of factors of the
product decomposition, which has no such instance in mathlib.

`card_eq_prime_of_pretransitive_of_nontrivial`: if the action is transitive, the
group has prime order `p`, and there are at least two factors, then the number of
factors is `p`.  This is immediate from the orbit lemma of round 367, and gives
the number of factors in the split case of the third dichotomy input.

One API fact: the orbit lemma of round 367 is stated for
`Multiplicative (ZMod p)` rather than for a general group, so it has to be
invoked with that signature.

## Round 383 (2026-10-15, appended)

No new theorem in this round; it records the last gap in the wiring of the third
dichotomy input.  The instance giving the action of `G` on `MaximalSpectrum` is
not in place, and the obstruction is a single identification: that the pointwise
action `g • I` on ideals agrees with
`Ideal.map (MulSemiringAction.toRingEquiv G R g) I`.  No lemma stating this was
found in the library.

What the search did confirm is available: the action on `PrimeSpectrum`, in
`Mathlib/RingTheory/Spectrum/Prime/Basic.lean`; `MulSemiringAction.toRingEquiv`,
turning the action into ring automorphisms; and
`Ideal.isMaximal_map_iff_of_bijective`, by which maximality is preserved along
`map` under a bijection.  So what remains is to prove that identification, or to
prove maximality of `g • I` directly, avoiding it.

## Round 384 (2026-10-15, appended)

The gap recorded in round 383 turns out not to be a gap.  In
`Mathlib/RingTheory/Ideal/Pointwise.lean` the pointwise action on ideals is
*defined* as `Ideal.map (MulSemiringAction.toRingHom _ _ a)`, and
`Ideal.pointwise_smul_def` states exactly the identification that was reported as
missing.  This is the fifth verdict of "not in the library" in this development
to be overturned by a wider search, and all five have the same cause.

The instance itself is still not in place.  It fails because no `SMul M (Ideal R)`
or `MulAction M (Ideal R)` instance is synthesized, even with the file imported;
the instance there is probably stated in the general form
`SMul M N` with `IsScalarTower M N R`, and has to be instantiated in that form.

The failing attempt introduced `sorryAx`, so it was withdrawn at once, and the
tree is again free of `sorry`.  The facts confirmed this round are recorded:
`Ideal.pointwise_smul_def`, `Ideal.isMaximal_map_iff_of_bijective`, and that
`MulSemiringAction.toRingEquiv` needs `Group M` rather than `Monoid M`.

## Round 386 (2026-10-15, appended)

`maximalSpectrumMulAction`: the action of a group of ring automorphisms on
`MaximalSpectrum R`, that is on the set of factors of the product decomposition
of round 365.  Maximality of the image follows from `Ideal.pointwise_smul_def`,
which identifies the pointwise action on ideals with
`Ideal.map (MulSemiringAction.toRingHom _ _ a)`, and from
`Ideal.isMaximal_map_iff_of_bijective`, maximality being preserved along `map`
under the bijective ring homomorphism `MulSemiringAction.toRingEquiv`, which
requires `Group M` rather than `Monoid M`.

The reason the earlier attempts failed was that the action instance on ideals is
declared with `scoped[Pointwise]`, available only in the `Pointwise` locale, so
`open scoped Pointwise` is needed; neither a missing hypothesis nor a missing
import was at fault.  Adding the declaration at the end of the file, rather than
editing it in place, avoided the earlier mishaps with block comments.

## Round 389 (2026-10-15, appended)

`isPretransitive_of_orbit_eq_univ`: if every orbit of an action is the whole
type, the action is transitive.  This is the last step of the transitivity
argument for the third dichotomy input, turning the statement obtained from the
idempotent lemma, that an orbit indicator equals one, into transitivity.

The lemma depends on no axioms at all.  Two API facts made it work:
`MulAction.mem_orbit_iff` reads `a₂ ∈ orbit γ a₁ ↔ ∃ x, x • a₁ = a₂`, and
`MulAction.IsPretransitive` is a class, so it must be proved with the anonymous
constructor; the anonymous function used in round 388 failed for that reason.

## Round 390 (2026-10-15, appended)

`smul_mem_orbit`: an orbit is invariant under the action, that is `g • j` lies in
the orbit of `j`.  The lemma depends on no axioms.

This is the ingredient that makes the orbit indicator, the sum of the `Pi.single`
idempotents over an orbit, invariant under the action.  With the idempotent lemma
of round 368, which says that an invariant idempotent is 0 or 1, the indicator is
therefore 1, so the orbit is everything, and the interface lemma of round 389
turns that into transitivity.

## Round 394 (2026-10-15, appended)

`isIdempotentElem_pi_single`: the single-point indicator `Pi.single i 1` is
idempotent.  With the orthogonality of distinct indicators this gives the
idempotency of the orbit indicator, the sum of the indicators over an orbit, which
with orbit invariance of round 390 and the idempotent lemma of round 368 forces
that indicator to be 1, hence the orbit to be everything, and round 389 turns that
into transitivity.

Two API points: the type family of `Pi.single` is named `M`, not `alpha`, and the
same holds for `Pi.mul_apply` and the evaluation lemmas; and `simp` alone does not
see through the pointwise product, so the proof proceeds by `funext`, then
`Pi.mul_apply`, then a case split on `j = i`.

## Round 395 (2026-10-15, appended)

`pi_single_mul_pi_single_eq_zero`: indicators of distinct points are orthogonal.
With the idempotency of round 394 this makes the orbit indicator, the sum of the
indicators over an orbit, idempotent; orbit invariance of round 390 and the
idempotent lemma of round 368 then force it to be 1, the orbit to be everything,
and round 389 turns that into transitivity.

The proof follows the pointwise pattern established in round 394: funext, then
Pi.mul_apply, then a case split on k = i, with the evaluation lemmas at the
family name M.
