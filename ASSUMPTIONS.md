# Literature assumptions

The library contains 72 named literature theorems whose proofs are admitted
with `sorry`. The manuscript-specific applications and deductions are proved
from these inputs. Their transitive proofs use `sorryAx` in addition to Lean’s
standard `propext`, `Classical.choice` and `Quot.sound`; no custom axiom is used.
The literature theorems themselves have not been proved in this library.

The inventory below gives each admitted declaration, its mathematical meaning,
source locator and correspondence qualifications. Each source link leads to the
full Lean statement, including its domains, hypotheses and coefficient maps.
Bibliographic keys refer to [references.bib](references.bib).

## Scope and conventions

The main conclusions concern primes p ≥ 5, 1 ≤ m < p and rational ξ distinct
from 0 and 1. The valuation conditions vₚ(ξ) ≥ 3 or vₚ(1−ξ) ≥ 3 supply the
ordinary hypothesis. One eigenform and compatible coefficient embeddings are
chosen before the good-prime quantifiers. The general ordinary criterion is
also proved. The principal declarations are in
[PrimeEulerMain.lean](HilbertModularity/Hypergeometric/PrimeEulerMain.lean).

The geometric Frobenius convention, fixed primitive projector and κ normalization
are explicit. Covariant Tate and cohomological dual actions are distinguished;
no hidden Tate twist is used. The revised normalization uses the proved direct
finite-sum identity. The involution comparison character is uniform in ξ at each
fixed coefficient realization; a single character across all realizations is not
asserted by that result. Residual associated-graded equivalence does not fix an
ordering of the invariant line and quotient.

The general Euler compatible system uses cyclotomic completion carriers, with
real-field containment of its common polynomials and weight-one purity on its
common good set. It does not reconstruct carriers over the smaller real
completions or assert purity at additional exceptional primes. The geometric,
cohomological, comparison and modularity existence inputs below retain their
specified actual objects and maps; these constructions are admitted where
stated, even when downstream consequences have Lean proofs.

The manuscript’s discussion of a general shallow-divisibility ordinary locus is
context, not a theorem asserted by this library. The proved geometric application
uses the explicit deep-cusp conditions. No mathematical conjecture or open
problem is relabelled as a proved result.

## Named inputs

### 1. `exists_primeFive_cyclotomicPrime_with_reducedRoot_and_realResidue`

[Lean statement](HilbertModularity/Examples/PrimeFiveOrientedPrimes.lean)

[MilneANT, Proposition 6.2(b), printed pp.96–97; Example 8.18,
printed p.143]: a specified primitive fifth root `r` in the prime field
gives a full cyclotomic prime with reduced ζ₅ equal to `r`. Its contraction
to the real subfield retains residue cardinality `q`, since both residue
fields contain 𝔽_q and the full one equals 𝔽_q. This standard
Dedekind–Kummer corollary asserts no curve or labelled trace statement.

### 2. `exists_primeFive_realPrime_of_mod_five_eq_one`

[Lean statement](HilbertModularity/Examples/PrimeFiveSplitPrimes.lean)

[MilneANT, Example 8.18, printed p.143, and §§8.14–8.16,
pp.141–142]: away from five, arithmetic Frobenius on the fifth cyclotomic
field sends ζ₅ to ζ₅^q. If q≡1 mod5 it is trivial, so q splits completely
in the full field and hence has a degree-one prime in its real subfield.
This standard splitting input asserts no orientation of the fifth-root
character and no trace or Frobenius polynomial of the example curve.

### 3. `integral_and_smoothOfRelativeDimension_one`

[Lean statement](HilbertModularity/Geometry/DoubleCoverCurve.lean)

The standard two-chart construction of a smooth integral hyperelliptic
curve from a nonconstant separable branch equation. The transition identity
identifies `g` with the reciprocal branch equation of `f`, with `n` fixing the
homogenizing degree. Separability of `f` gives distinct finite branch points;
separability of `g` checks the reciprocal chart, including infinity. Positive
degree and separability also exclude a square branch equation, giving an
integral generic curve. These are the two charts in [src_poonen_curves,
§2.8.1, printed pp. 36–37]; uniqueness of the smooth projective model is in
§2.1.2, printed p. 23. This input makes no assertion about regularity or
stability of a model over a valuation ring.

### 4. `genusTwoGeometricFrobeniusPolynomial`

[Lean statement](HilbertModularity/Geometry/Etale/FiniteFieldGenusTwoFrobenius.lean)

[src_milne_lec, Theorem 25.1, Proposition 27.3, Theorem 27.6,
Remark 27.7, Theorem 27.12, Propositions 29.10 and 29.12, printed pp.145–168]
gives the first two power traces, the functional equation and the relation
between geometric Galois Frobenius and pullback by the q-power morphism.
[src_poonen_curves, §2.8.1, printed pp.36–37] gives genus two for a monic
separable degree-six branch polynomial in odd characteristic.
[proetale2015, Lemma 6.8.2(1) and Proposition 6.8.4(1), printed pp.58–59;
Corollary 5.1.5] identifies the continuous-coefficient pro-étale construction
with the usual ℓ-adic system; the connected curve has surjective constant
H⁰ reduction maps, so the degree-one inverse-limit term vanishes. The
quadratic-field count uses the mapped equation of the same curve. This is a
standard composite input, not a verbatim theorem of any one source. It
asserts no numerical count or labelled real-multiplication factor.

### 5. `geometricH1_equiv_dualTate_of_pointedJacobian`

[Lean statement](HilbertModularity/Geometry/Etale/FiniteFieldJacobianCohomology.lean)

[MilneJacobian2021, Corollary 9.6, printed p.32] identifies the first
étale cohomology of a pointed smooth curve with that of its Jacobian by the
actual Abel–Jacobi map. [MilneAV, Chapter I, Theorem 12.1(a), printed p.55]
identifies the latter with the dual of the covariant Tate module. The
comparison is Galois equivariant and has no Tate twist; for geometric
Frobenius this agrees with [src_milne_lec, Remark 29.11, printed p.168].
[proetale2015, Corollary 5.1.5, Lemma 6.8.2(1), Proposition 6.8.4(1)]
passes from the classical continuous ℓ-adic system to the actual pro-étale
cohomology carrier used here. This standard composite interface asserts no
point count, RM decomposition, character value or numeric polynomial.

### 6. `exists_goodReductionModels_outside_finite`

[Lean statement](HilbertModularity/Geometry/GroupScheme/GoodReductionModels.lean)

An abelian variety over a number field has actual good-reduction models
outside one finite set of primes. This is a named standard literature input.

[src_stacks_spreading, Lemma 32.10.1, Tag 01ZM] descends the finite-presentation
scheme, multiplication, inverse, identity and the finitely many group identities
to some `O_K[1/N]`. Smoothness descends by Lemma 32.8.9 (Tag 0C0C), and properness
by Lemma 32.13.1 (Tag 081F). For the resulting proper smooth family, the Stein
factor is finite etale by Lemma 76.36.9 (Tag 0E0D); its generic degree is one,
so after shrinking the base the fibres are geometrically connected. Base
change to each displayed valuation ring gives the models and group-scheme
isomorphisms below. These are standard combined consequences of the cited
results, not a verbatim single theorem. No representation, RM action, trace,
coefficient prime, or manuscript conclusion is included in the input.

### 7. `exists_hyperellipticJacobian_goodReduction_withSpecialFiber`

[Lean statement](HilbertModularity/Geometry/GroupScheme/HyperellipticGoodReduction.lean)

The relative Jacobian of the actual smooth two-chart double cover has
the supplied pointed Jacobian as generic fibre and the pointed Jacobian of
the *reduced equation* as special fibre. The special point and Abel–Jacobi
map are the fields of the returned `PointedCurveJacobian`; the generic
identification and the special Jacobian belong to the same model `B`.

This is the standard relative Picard/Jacobian and base-change result
[MilneJacobian2021, Proposition 6.1, printed p.19; Theorem 8.1 and paragraph
following it, printed pp.27–28; Corollary 12.3 and proof, printed p.39],
applied to the monic two-chart hyperelliptic model with separable residue
polynomial [src_poonen_curves, §2.8.1, printed pp.36–37]. It is a standard
composite interface, not a numeric Frobenius or RM assertion.

### 8. `exists_darmon_abelianScheme`

[Lean statement](HilbertModularity/Geometry/GroupScheme/HypergeometricExistence.lean)

The integral base triple is realized by one abelian scheme with real multiplication.
The basis is over the actual coefficient tensor algebra, and its local monodromy is the
standard triple through actual generators of the three geometric inertia groups.
We use [DarmonFibres, Section 3, Propositions 3.2 and 3.4].
The coefficient basis implements the covariant, determinant-one simultaneous
conjugacy convention for all three matrices.

We follow [DarmonFibres, Section 3, Propositions 3.2 and 3.4].
The monodromy statement uses actual rational-function inertia and the actual
Tate action of the one abelian scheme. The local generators retain their usual conjugacy choices and share the
compatible root-of-unity orientation fixed on printed p. 2, with the specified
real cyclotomic trace label. No global generation or arithmetic exact-sequence
conclusion is included, and no descent to ℚ is asserted.

The convention is covariant Tate monodromy. The geometric rank-two
determinant-one representation is self-dual; this identifies the dual convention
by one simultaneous change of basis for all three local monodromy matrices.
The all-prime comparison uses Proposition 3.4 as well as the Tate-module
discussion in Section 3. Positive multiplication being finite, étale and
surjective is exposed standard characteristic-zero abelian-scheme geometry;
these are obligations of the stated existence theorem.

### 9. `exists_integralRationalTateComparison`

[Lean statement](HilbertModularity/Geometry/GroupScheme/IntegralRationalTateComparison.lean)

The standard rationalization comparison for the same integral RM action.
The full RM diagram fixes the homomorphism O_F→E, as in [DarmonFibres,
printed p.5, From hypergeometric abelian varieties to rigid representations].
The finite-module completion theorem is [mathlib_5ed296525643,
Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean,
AdicCompletion.ofTensorProductEquivOfFiniteNoetherian]. Rational Tate
functoriality is [MilneAV, Chapter I, §10, Proposition 10.5 and the following
functoriality discussion, p.45; rationalization definition, p.46]. The comparison
is the resulting scalar-localization identity on the inverse-limit Tate module;
it does not require freeness or an abelian-variety existence assertion for the
group scheme in its signature. Only scalar rationalization and equivariance
are admitted. The selected family and canonical diagrams are constructed separately.

### 10. `exists_primePlusFamilyData`

[Lean statement](HilbertModularity/Geometry/GroupScheme/PrimeHypergeometricExistence.lean)

Joint existence of the prime plus family and its labelled geometric data.
The source is [DarmonFibres, Section 3 Example 3 and Propositions 3.2/3.4],
[DarmonRigid, printed pp. 420 and 431, Theorem 2.6(2), proof's last
parenthetical] and [DarmonMestre, Propositions 2.1–2.3]. Their parameters agree by
`s = 2t - 1`. The pointed Abel–Jacobi property fixes this selected family's
generic and nonsingular rational fibres to the displayed plus curve, and its
integral RM acts on those same fibres. The plus infinity trace is `+tau`, as in
[DarmonMestre, Proposition 3.1, proof, printed pp. 308–309]. One roots and path
system supplies the common inertia generators at every prime: apply
[src_milne_lec, Theorem 21.3, printed p. 130, and pp. 131–132] to the same
finite division covers and pass to inverse limits. Naturality preserves RM;
geometric rank-two determinant-one self-duality gives the covariant Tate
convention. Positive finite étale surjective multiplication and rational Tate
rank are the standard characteristic-zero abelian-scheme properties included
in this input. This is a composite literature consequence, not a verbatim
single theorem. It does not identify this choice with `darmonFamily`, remove
an arithmetic twist, or assert the final p-adic determinant or ordinarity.
The exact correspondence of all fields of this joint structure remains subject
to source review; the auxiliary determinant display is not included.

The cited plus Jacobian is chosen once, together with its integral real multiplication
and its rational point of exact prime order. The labelled auxiliary division-point
determinant is stated separately and is not part of the existence admission.
The chosen family here is independent of the earlier abstract
`darmonFamily` witness. The joint choice keeps the arithmetic properties attached to
the same abelian scheme. See [DarmonFibres, Section 3, Example 3 and Propositions
3.2 and 3.4], [DarmonRigid, Theorem 2.6(2)] and [DarmonMestre, Section 4].

### 11. `primePlusDarmonMestreTateRealization_literature`

[Lean statement](HilbertModularity/Geometry/GroupScheme/PrimePlusComplementTate.lean)

[DarmonMestre, Proposition 2.1, correspondence (5), printed p. 307;
Proposition 2.3 and its proof, printed pp. 307--308], together with standard
rational Tate functoriality and finite base change, provides
the *same geometric map* and the quotient-map/rotation action on its Tate
realization. The completed RM-linearity uses the source trace correspondence
and one generic coefficient relabelling; it does not allow fibrewise labels.
The Tate isogeny step itself is formalized as
`GroupScheme.tateFiniteSurjectiveEquiv`; the admitted content is the
source-specific correspondence and its coherent realization on these fibres.
This is a named literature interface, not an ordinary or modularity premise.

### 12. `smooth_geometricallyReduced_literature`

[Lean statement](HilbertModularity/Geometry/GroupScheme/PrimePlusRMComparison.lean)

Smooth scheme morphisms have geometrically reduced fibres. This standard
literature input combines [src_stacks_smooth_reduced, Tag 01VB] (smoothness
is stable under base change) with [src_stacks_smooth_reduced, Tag 056T]
(a scheme smooth over a field is geometrically reduced), applied to each
residue-field fibre. The total-space reduction below uses Mathlib's flat/fibre
criterion separately.

Darmon--Mestre's full generic endomorphism-ring calculation is about a specified
correspondence action on the Chebyshev Jacobian [DarmonMestre, Proposition 2.1,
printed p. 306]. The selected plus Jacobian is that pointed curve after
`s = 2t - 1`, but its chosen integral action is independent. The statements
below derive faithful generic restriction and fullness of the selected action,
then compare it with any supplied full correspondence action by one coefficient
relabelling. The curve identity alone does not identify the coefficient labels.

### 13. `darmonMestreChebyshevGenericEndomorphisms`

[Lean statement](HilbertModularity/Geometry/GroupScheme/PrimePlusRMComparison.lean)

The **generic** full endomorphism ring of the Chebyshev Jacobian `J₂`
is isomorphic to `𝓞 K_p`. The geometric computation is [TTV, Theorem 1 and
the remark after Section 2]; descent of all generic endomorphisms to `K_p`
is [DarmonMestre, Proposition 2.1, printed pp. 306--307]. Darmon--Mestre
also specify an action by correspondence (5), with `ω` acting as `ηζ`, but
this interface records only the full-ring isomorphism, not that specified
action. Here `s = 2t - 1`; no full-ring assertion is made for specialized
fibres. This named literature interface is a conditional premise.

Darmon--Mestre's full generic endomorphism-ring calculation is about a specified
correspondence action on the Chebyshev Jacobian [DarmonMestre, Proposition 2.1,
printed p. 306]. The selected plus Jacobian is that pointed curve after
`s = 2t - 1`, but its chosen integral action is independent. The statements
below derive faithful generic restriction and fullness of the selected action,
then compare it with any supplied full correspondence action by one coefficient
relabelling. The curve identity alone does not identify the coefficient labels.

### 14. `exists_primePlusRaynaudUniformization_of_scaledModel`

[Lean statement](HilbertModularity/Geometry/GroupScheme/PrimePlusRaynaudStableApplication.lean)

[SGA7I, Exposé IX, §§8.2 and 12.3; RaynaudRigid, §1 Theorem 1,
pp. 473–474, and §3(a)–(b), p. 475] Semistable Picard reduction and rigid
uniformization for the actual proper flat scaled cover. The hypothesis
`hgeometry` supplies its geometrically reduced connected special fibre, two
defined projective-line components, all rational split nodes and their local
equations, including the possible nonregular equations `xy = π^n`. The
punctured parameter has smooth connected generic fibre; `hJacobian` fixes the
same pointed Jacobian and its real-multiplication action. `hparameter` matches
the integral model's generic parameter to that fibre. The result asserts only
the cited period/torus construction and its functorial actions; the ordinary
quotient is deduced separately below.

### 15. `exists_complementCuspGenerators`

[Lean statement](HilbertModularity/Geometry/ProjectiveLine/ComplementCuspGenerators.lean)

**Named literature input.** The characteristic-zero Riemann existence
comparison and its functoriality [src_milne_lec, Remark 3.3(a)--(c), p.27;
Theorem 3.4, p.28], together with the arithmetic exact sequence and punctured
sphere presentation [src_milne_lec, pp.29--30], give these actual geometric
generators. See also [GPRV, Theorem 3.15, p.11]. The normalization by compatible
roots and conjugates of local inertia is [DarmonFibres, section 1, p.2];
section 2, p.3 records the product-one choice.

Over the complex numbers, take a positively oriented loop around zero with
a straight stem from `1/2`, and its image under the holomorphic map `1-z`.
These loops are exchanged exactly and generate the twice-punctured plane
group. Their product inverse is the infinity loop. Riemann existence transfers
this description, with its scheme-induced automorphism, to the actual
geometric kernel. Changing to the specified generic fibre path conjugates
the inertia lifts. Choose the common root system with the specified primitive
`N`-th root sum; no coefficient embedding of a representation is chosen here.
These standard topological and inertia-transport consequences are included in
this one literature input, rather than asserted as a verbatim source theorem.

In particular this input does not assert invariance of any chosen Euler or
Darmon local system. The invariance of its monodromy matrices remains a
separate manuscript deduction.

### 16. `geometricEquiv_of_standard_localMonodromy_charZero`

[Lean statement](HilbertModularity/Geometry/ProjectiveLine/LocalMonodromyRigidity.lean)

**Named literature input.** [YunRigid2014, §3.1.1, p.33; §3.2,
p.35; Proposition 3.2.7 and Theorem 3.2.8, p.39] gives the local-system
dictionary, numerical cohomological rigidity criterion and physical rigidity
on `P¹`. The last theorem explicitly cites [KatzRigid1996, Theorem 5.0.2];
that attribution is through the inspected Yun text, not an independently
inspected quotation from Katz.

Here the geometric base has characteristic zero. Each of the three standard
local matrices is non-scalar and has a one-dimensional centralizer in the
trace-free endomorphisms; the Swan conductors vanish. Irreducibility is absolute:
a nontrivial unipotent has its unique invariant line defined over `L`.
Consequently the global trace-free invariants vanish, and the sum of the three
Artin conductors is `6 = 2 * dim(sl₂)`. Yun's criterion gives cohomological
rigidity, hence geometric uniqueness over an algebraic closure of `L`.
The space of intertwiners is the kernel of linear equations over `L`; scalar
extension preserves that kernel, and a nonzero intertwiner between these
irreducible rank-two actions is invertible. This descends the equivalence to
`L`. These standard specialization and coefficient-descent consequences are
included in this single admission. No source is claimed to state the entire
Lean signature verbatim. In particular, no restriction on the coefficient
prime is inferred from a restriction on the characteristic of the geometric
base, and no freeness of the local monodromy action is asserted.

The standard rank-two triple is cohomologically rigid on the three-punctured
projective line. The geometric uniqueness input uses [YunRigid2014,
Proposition 3.2.7 and Theorem 3.2.8], the latter stating Katz's Theorem 5.0.2.
It applies to every finite `p`-adic coefficient extension, including `p = 2`.
The older odd-coefficient API remains a proved specialization, consistent
with the standing restriction in [DarmonFibres, §1, Proposition 2.4].
The actual local classes, their orientation and coefficient label are fixed.
No arithmetic comparison character or manuscript-family comparison is assumed.

### 17. `exists_iso_extending_dense_open_of_smooth_proper_curve`

[Lean statement](HilbertModularity/Geometry/SmoothProperCurveExtension.lean)

An open immersion between dense opens of integral proper smooth curves
extends to an isomorphism over the field. The dimension-one hypothesis is
essential: an analogous assertion fails for higher-dimensional proper
varieties. Poonen gives the uniqueness of smooth projective curve models
[src_poonen_curves, §2.1.2, printed p. 23]. Passing from the proper-curve
hypotheses here through the valuative criterion is part of this admitted input.

### 18. `exists_rationalTateEndomorphism_polynomial`

[Lean statement](HilbertModularity/Geometry/TateModule/EndomorphismCompatibility.lean)

The characteristic polynomial and trace of a rational algebraic endomorphism
are independent of the auxiliary prime.

[MilneAV, Chapter I, Theorem 10.9, pp. 46–47; Remark 10.11, p. 47;
Proposition 10.20, pp. 50–52]. Properness, smoothness and geometric connectedness
make the commutative group scheme an abelian variety. Remark 10.11 extends the
endomorphism polynomial to `End⁰(A)` by clearing denominators; the rational
endomorphism here is `c * f`. Proposition 10.20 identifies its polynomial and
trace with those of the covariant rational Tate map for every prime different
from the ground-field characteristic. The prime exclusion is `(p : K) ≠ 0`.
The polynomial is `det(X - f)`, and the statement is independent of the chosen
finite basis. No Frobenius specialization, RM projector or manuscript comparison
is included in this named literature admission.

### 19. `localGenericFiber_endomorphism_bijective`

[Lean statement](HilbertModularity/Geometry/TateModule/GoodReduction.lean)

Endomorphisms extend uniquely across good reduction.

[BLR, §1.2, Proposition 8] identifies an abelian scheme over a discrete
valuation ring with the Néron model of its generic fibre. Apply its mapping
property, as stated in [MilneAV, Chapter I, Theorem 17.1 and Remark 17.2, p. 70],
to this same smooth model. Uniqueness preserves the group operations.
Only the resulting bijection of actual endomorphisms is admitted.

### 20. `exists_goodReductionTateSpecialization`

[Lean statement](HilbertModularity/Geometry/TateModule/GoodReduction.lean)

Prime-to-residue-characteristic Tate specialization is natural for model
endomorphisms and takes arithmetic Galois Frobenius to algebraic Frobenius.

[MilneAV, Chapter IV, Theorem 3.5 and its proof, pp. 141–142; paragraph after
Corollary 3.6, p. 142], using the good-reduction model of Chapter I, §17.
The algebraic endomorphism is chosen on the special fibre before any auxiliary
prime or absolute Frobenius lift. The equivalence may depend on those choices.
Naturality is that of the prime-power torsion reduction maps in the proof.
Inertia acts trivially. The convention is covariant Tate modules and arithmetic
Frobenius; the cohomological dual at geometric Frobenius has the same polynomial.
There is no twist in this input and no assertion about labelled RM factors.

### 21. `goodReduction_dualTateFrobenius_comparison`

[Lean statement](HilbertModularity/Geometry/TateModule/GoodReductionFrobenius.lean)

**Literature input.** The same good-reduction specialization gives both
transported-basis Frobenius polynomials and a linear equivalence intertwining
the full dual Tate Frobenius operators. These are two API consequences of the
single specialization isomorphism in [MilneAV, IV Theorem 3.5 and paragraph
after Corollary 3.6, pp.141–142; II §1, p.75]. They retain the same abelian
model, residue field, auxiliary prime and geometric Frobenius conventions.
The joint input keeps the existing basis interface available while exposing
the operator comparison needed by the selected-model application. No numeric
polynomial, coefficient label or manuscript comparison character is admitted.

### 22. `labelledDualTate_hodgeTate_of_totallyReal`

[Lean statement](HilbertModularity/Geometry/TateModule/RealMultiplicationHodgeTate.lean)

[src_brinon_conrad, Theorem 2.2.3, p. 13; Example 2.4.13, pp. 24–25]
gives the functorial smooth-proper Hodge–Tate comparison. Its degree-one
application to this abelian variety is identified with the contragredient Tate
module by [MilneAV, I Theorem 12.1(a), p. 55]. Endomorphism functoriality and
finite coefficient extension retain the specified RM idempotent and every
embedding of the local base field.

The multiplicities use the standard complex-torus description
[MilneAV, I Proposition 2.1, pp. 10–11; Theorem 2.9, p. 14]. At each complex
embedding of the ground number field, complex conjugation exchanges the
holomorphic and antiholomorphic pieces and preserves each totally real RM
label. Their equal dimensions sum to the rank two of this labelled factor,
so both are one. Characteristic-zero comparison and base change transport
these dimensions to each local embedding. These comparison and labelled
linear-algebra consequences are included in this named literature input;
none of the cited passages is claimed to state this entire Lean signature
verbatim. The convention is cohomological weights `{0,1}`, cyclotomic weight
`-1`, with no Tate twist and no good-reduction hypothesis at `p`.

This is the standard geometric input for the cohomological RM factor in
[TripathiGoswamiRevised, Theorem `thm:RMgeneral`]. It concerns the actual
abelian variety, its endomorphism action and its contragredient Tate factor.
It does not assert an Euler comparison, determinant identity or modularity.

### 23. `exists_labelledTatePairing_of_full_realMultiplication`

[Lean statement](HilbertModularity/Geometry/TateModule/RealMultiplicationPairing.lean)

Polarization and Weil-pairing input for **full totally real** endomorphisms.
The underlying proper smooth geometrically connected group is an abelian
variety. Its projectivity and an ample line bundle over `K` follow from
[MilneAV, Chapter I, Theorem 6.4 and Proposition 6.6(d), pp. 29–31].
Choose this line bundle and its polarization. The canonical
pairing, its nondegeneracy and Galois equivariance are [MilneAV, Chapter I,
Section 13, pp. 57--58, Lemma 13.1 and Proposition 13.2(a),(d)]. Rationalizing
removes the finite polarization kernel. The Rosati adjointness identity is in
Section 14, p. 61, and positivity is Theorem 14.3, p. 62.

Here `φ` identifies the full endomorphism ring with `𝓞 F`, so Rosati acts on
`F`. A positive involution on a totally real field is the identity: otherwise
`y = a - a† ≠ 0` has `y† = -y`, contradicting positivity of
`Tr(y y†) = -Tr(y²)`. Thus the specified RM action is self-adjoint. After
splitting coefficients, distinct embedding summands are orthogonal, and the
restriction to each summand is nondegenerate. Choosing a basis of the Tate
twist writes its Galois action as the cyclotomic multiplier below.

These standard consequences of the cited pairing and Rosati theorems are
included in this named admission; they are not a verbatim theorem of Milne.
No rank, determinant, manuscript comparison or specialized fullness is admitted.
The convention is covariant Tate modules and arithmetic cyclotomic action.

### 24. `exists_fiberLabelledTatePairing_of_generic_full_realMultiplication`

[Lean statement](HilbertModularity/Geometry/TateModule/RelativeRealMultiplicationPairing.lean)

Relative polarization and Weil pairing, specialized to the punctured line.
This is the standard relative consequence of [MilneAV, Chapter I, Theorem 6.4,
Proposition 6.6(d), Section 13 Lemma 13.1 and Proposition 13.2(a),(d), and
Section 14 Theorem 14.3], together with [MilneAbelianMotives, Theorem 3.5].
The latter extends homomorphisms of generic abelian fibres uniquely over a
connected noetherian normal base; our punctured line is such a base.

Choose a generic polarization. Full totally real generic endomorphisms force
its Rosati involution to fix the specified RM action. Extend the polarization
to the dual abelian scheme, and extend an integral multiple of its inverse.
Uniqueness extends both multiplication identities, symmetry and RM
self-adjointness. The specialized map is therefore a symmetric isogeny at
every fibre. Its rational Weil pairing is alternating, nondegenerate and
cyclotomic-equivariant. Self-adjointness makes distinct split coefficient
summands orthogonal, so each labelled restriction is nondegenerate.

This named input includes those standard relative-duality and pairing
consequences, not a verbatim assertion of Theorem 3.5. It assumes neither rank
two nor any determinant identity. Fullness is imposed only at the generic
point; no fullness of specialized endomorphisms is asserted. The convention
is covariant Tate modules and arithmetic cyclotomic action.

### 25. `tateRepresentation_isSemisimple`

[Lean statement](HilbertModularity/Geometry/TateModule/Semisimplicity.lean)

Faltings semisimplicity, as stated in [MilneAV, Chapter IV, Appendix,
Theorem 3, p. 159]. The appendix specifies a number field `K`, its absolute
Galois group, an abelian variety `A/K`, and `V_ℓ A = ℚ_ℓ ⊗ T_ℓ A`.
Properness, smoothness and geometric connectedness below make the actual
commutative group scheme an abelian variety. The representation is covariant;
there is no dual, coefficient extension, RM projector or Tate twist in this
named literature input. The cited appendix attributes the theorem to
Faltings, Invent. Math. 73 (1983), 349–366, with erratum 75 (1984), 381.

### 26. `polynomial_derivative_isEtaleAt`

[Lean statement](HilbertModularity/Hyperelliptic/SpecialFiberEtaleCoordinate.lean)

The relative polynomial Jacobian criterion, with no field assumption on
the coefficient ring.  For the map `R[t] → R[u]`, `t ↦ H(u)`, invertibility
of `H'(u)` at the chosen prime makes the map étale there.  Indeed the
presentation `R[t,u]/(H(u)-t)` is standard étale on that open; see
[src_stacks_standard_etale, Tags 00UB and 00UC].  This is a literature
interface about polynomial maps, independent of the double cover.

### 27. `commonEulerCompletionAction_isIrreducible_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/ChosenEulerIrreducibility.lean)

**Named literature input.** The symmetric parameters
`(m/N, 1-m/N); (1,1)` are generic for `0<m<N`, with integral upper
and lower sums `1` and `2`. [GPRV, Theorem 10.1, pp.45–46] gives
irreducibility at every nonsingular real-field specialization and every
finite cyclotomic coefficient completion, for all coprime conductors.
The chosen quotient component is the same primitive realization by
[GPRV, Theorem 9.2 and Proposition 9.5, pp.40–41]. The finite κ twist
preserves invariant subspaces, so the raw component has the same
irreducibility. No arbitrary scalar-extension irreducibility is asserted.

This generalizes the former conductor-prime input, whose old public
statement below is a proved specialization. The cited source remains
admitted once; no manuscript comparison or modularity is an input.

### 28. `chosenEffectiveEulerCompatibleSystem_polynomial_properties`

[Lean statement](HilbertModularity/Hypergeometric/EffectiveEulerPolynomialProperties.lean)

**Named literature input.** For `(m/N, 1-m/N); (1,1)`, the
upper and lower sums are integral, the parameters are generic, and the
coprimality hypothesis supplies `(Irr)` by [GPRV, Lemma 8.5, p.30].
Their stabilizer is `{1,-1}`. [GPRV, Theorem 9.2 and its proof (76),
pp.40–41] therefore gives coefficient field contained in `K_N`, without
asserting equality at every specialization. Its proof supplies the real
coefficient action on the new part of the same quotient.

Exactly two parameters are integral, so [GPRV, Theorem 8.25(1), p.37]
gives weight `2-1=1`. [GPRV, Lemma 9.3, p.40] has `δ=0` for these
parameters, hence introduces no norm power. The effective realization
includes the single finite `κ_N^m` factor from Definition 8.8 and Lemma 9.4.
Thus the roots of its geometric-Frobenius polynomial have squared complex
norm equal to the residue cardinality. The sign convention is `det(X-Frob)`
on cohomology, with no Tate twist.

The system-to-original-fibre equivalence is proved in
`chosenEffectiveEulerCompatibleSystem_actionEquiv`. This admission records
only these cited coefficient/purity properties of its common polynomial,
not a comparison character, modularity, or a numerical example value.
Purity is stated at the system's good primes; no assertion at its exceptional
primes is inferred from this interface.

### 29. `exists_properEulerRealDescent_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GaloisDescent.lean)

[GPRV, Theorem 9.2 and Proposition 9.5, pp. 40–41] construct the
raw quotient motive for the coprime symmetric datum. Lemma 8.5, p. 30,
gives `(Irr)` since the scaled exponents `m,-m,m-N` have gcd one with `N`.
The rank-two lisse descent restricts to fixed-`χ₀` proper Euler cohomology
over `F_N`. For even `N`, this RAW descent is not yet the effective
hypergeometric normalization: the separate character of [GPRV, Definition
8.8, Lemma 8.9 and Corollary 8.10] must be tensored to power `m`. No
Frobenius trace, automorphy or Tate twist is asserted here.

The geometric fixed-character summand on the exponent-`m` curve is defined over
the full cyclotomic field.  The descent supplied by [GPRV, Theorem 9.2 and
Proposition 9.5] is chosen on the *generic family*, before specialization.
For odd `N`, the auxiliary `κ_N` of [GPRV, Definition 8.8] is trivial.
No trace identity is built into the descent input.

### 30. `commonEulerCompletionAction_isSemisimple`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationCompatibleSystem.lean)

[MilneAV, Chapter IV, Appendix, Theorem 3, p. 159] records Faltings'
semisimplicity for an abelian variety over a number field. Applied to the
Jacobian of the actual smooth proper Euler quotient, with the standard
curve-`H¹`/Jacobian Tate comparison and characteristic-zero coefficient
extension, it gives semisimplicity of this fixed labelled component.

This source input concerns only the selected cohomological action at one
completion. It does not assume compatible polynomials or automorphy.

### 31. `exists_commonEulerCompletion_frobeniusPolynomial`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationCompatibleSystem.lean)

[GPRV, Definition 8.2 and Theorem 9.2] give the single quotient motive
and its number-field coefficient action. At a good prime the smooth proper
special fibre and its fixed projector yield one algebraic Frobenius polynomial
before choosing `ℓ`. The standard Jacobian endomorphism polynomial is
independent of the auxiliary prime by [MilneAV, Chapter I, Theorem 10.9,
pp. 46–47; Remark 10.11, p. 47; Proposition 10.20, pp. 50–52];
[src_milne_lec, Theorem 20.4, pp. 127–128] compares the smooth proper
cohomology at each auxiliary prime. The polynomial is attached to the
actual chosen quotient action, with the same `χ₀` coefficient label at
every completion. The residue characteristic is excluded at each completion;
the geometric bad set is the canonical `badPrimesBelow x N`.
At prime conductor this is the full labelled quotient `H¹`; at composite
conductor the source uses the new part. The theorem assumes an already chosen
`R` and does not assert its existence outside the prime case.

The cited passages do not state this project's fixed-component
`NumberFieldCompatibleSystem` interface verbatim; that projector and
coefficient-label passage is included in this explicitly admitted standard
comparison and needs source review at integration. It asserts neither the
normalized McCarthy trace nor modularity.

### 32. `exists_smoothProperEulerFamily_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationFamily.lean)

The tame cyclic-cover construction of [EsnaultViehweg, §3, (3.5)–(3.13)
and Lemma 3.15(b)], applied to the Euler equation of [GPRV, Definition 8.2].
On the relative projective line take `L = O(2)` and the section with divisor
`m[0] + (N-m)[1] + m[1/t] + (N-m)[∞]`. Its four sections are disjoint on the
punctured parameter line. The normalized cyclic algebra in (3.7)–(3.10) is
finite over that projective line and has the deck action of (3.9).

The source is written over algebraically closed fields. Its explicit algebra
and multiplication are defined over the cyclotomic ground field. The relative
smoothness assertion uses its local equation (3.13)(c), `z^N = u^a x`, with
`x` a relative parameter and `u` a unit, and the étale branch complement.
The same finite map to the relative projective line gives an affine open
containing each pair of points of the cover, recorded as `pair_affineOpen`.
This is the orbit-in-affine hypothesis of [SGA1, Exposé V, Proposition 1.8]
for any later involution; it does not choose or assert that involution.
The Euler equation is defined over the real field before adjoining `ζ_N`.
The construction over that field gives `realCurve` and its actual
branch-open Euler immersion. Its parameter-preserving cyclotomic
base-change isomorphism agrees on that same affine chart with
`affineFamilyCoefficientMap`, which is induced by the coefficientwise Euler
algebra map preserving both `x` and `y`. This excludes a deck-rotated
identification. The deck action
requires the cyclotomic extension, but the curve itself does not. Its
relative dimension one and pair-affine properties are recorded on the
real form as well as on the cyclotomic form.
This relative application and ground-field descent are included in the named
literature input; Lemma 3.15(b) alone is a statement of absolute nonsingularity.
No Frobenius, cohomological comparison or arithmetic descent is assumed here.

The affine exponent-`m` Euler family already has an actual scheme and parameter
map.  A smooth proper completion is a separate geometric construction.  The
chosen completion below is over the entire punctured parameter line, so its
fibres come from one family, as required by
[TripathiGoswamiRevised, Definition 2.3].

### 33. `exists_genericLocalSystem_of_commonRealEulerQuotient`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationGenericMonodromy.lean)

Generic restriction and geometric path compatibility for the local system
of one selected real Euler quotient. [GPRV, Theorem 9.2 and Proposition 9.5,
pp. 40–41] fix the quotient before choosing the coefficient place.
[src_milne_lec, Theorem 20.4, pp. 127–128] supplies smooth proper
specialization of its finite cohomology sheaves; [proetale2015, Lemma 4.2.12,
Corollary 5.1.6, Example 5.2.2, Definition 6.8.1 and Lemma 6.8.2(1)]
supplies the continuous rational-coefficient comparison. Finite norm/Leray
for the quotient and its fixed component is as in [src_milne_lec,
Proposition 8.3(c), Corollary 8.4, Exercise 12.3 and Theorem 12.7].

This literature interface is the existence of a generic restriction and its
path map. It does not assert a Darmon comparison or finite-order character.
The source passages do not state this project's `EtaleLocalSystem` API
verbatim; the interface records their application to the selected smooth
proper quotient and its fixed coefficient component.

The generic local system is the generic restriction of the *same* chosen
quotient/descent, with an actual path comparison to the original rational
fibre. Its local classes are the external hypergeometric monodromy calculation
of [GPRV, Proposition 3.12 and Theorem 8.20]. The comparison with Darmon's
cohomological factor is deduced below using the checked rigidity theorem.

### 34. `commonRealEulerQuotient_generic_localMonodromy_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationGenericMonodromy.lean)

[GPRV, Proposition 3.12 and Theorem 8.20] identify the three oriented
local classes of the actual generic Euler realization and its geometric
irreducibility under condition `(Irr)`. For the symmetric coprime datum, `(Irr)` follows from the
scaled gcd-one certificate `symmetricParameters_irreducible` and [GPRV,
Lemma 8.5, p. 30]. The parameter `F_gen` is required to be the path-compatible
generic restriction of the *selected* quotient realization, and the displayed
coefficient equation prevents a second exponent relabelling.

These are local-class and irreducibility inputs only. In particular GPRV does
not assert the Darmon comparison which is deduced from them by the project's
rigidity theorem.

The generic local system is the generic restriction of the *same* chosen
quotient/descent, with an actual path comparison to the original rational
fibre. Its local classes are the external hypergeometric monodromy calculation
of [GPRV, Proposition 3.12 and Theorem 8.20]. The comparison with Darmon's
cohomological factor is deduced below using the checked rigidity theorem.

### 35. `commonRealEulerQuotientRealization_labelledHodgeTate_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationHodgeTate.lean)

[GPRV, §10.1, complementary branch fractions] computes one holomorphic
and one antiholomorphic dimension in every `χ₀` coefficient label of the
exponent-`m` Euler cover. [src_brinon_conrad, Theorem 2.2.3 and Example
2.4.13] identifies these with the labelled Hodge–Tate weights of smooth
proper degree-one étale cohomology. The quotient descent here is the chosen
same-map `R.placeDescent` of [GPRV, Proposition 9.5/Theorem 9.2/(76)],
whose fixed-projector comparison retains `χ₀(ζ)=ι(ζ)`. The statement refers
to the *original* two-dimensional arithmetic fibre, with no Tate twist.

For coprime N, [GPRV, §10.1, Case (1), p. 44] gives the Hodge
polynomial x+y because the denominator pair consists of integers, for every
coefficient embedding. The raw quotient has these weights for even N as
well: its effective normalization differs by finite κ [GPRV, Definition
8.8, Corollary 8.10 and Lemma 9.4], which has weight zero. N=3 is
included. This named
literature premise supplies only local comparison and weight
multiplicities. It supplies no determinant finite order, Darmon comparison,
automorphy or Frobenius trace.

The original odd-coprime fibre, with its fixed coefficient embedding and the unshifted
cohomological convention, has weights `{0,1}` at every local label. This is
the external Hodge calculation in [GPRV, §10.1] combined with smooth proper
Hodge–Tate comparison [src_brinon_conrad, Theorem 2.2.3 and Example 2.4.13].
The finite-character deduction from these weights is proved separately.

### 36. `exists_ellAdicCohomologyMorphismPullback`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationMorphismPullback.lean)

Standard morphism pullback for the actual pro-étale cohomology model.
The cited inverse-image and coefficient comparison are the only admitted
construction here; the input makes no assertion about the Euler quotient.
[src_milne_lec, §8, Proposition 8.7; proetale2015, §4]

### 37. `exists_involutionQuotient_of_affineOrbits`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationQuotient.lean)

The finite, possibly nonfree, scheme quotient of an involution whose
two-point orbits lie in affine opens. This is the order-two case of
[SGA1, Exposé V, Propositions 1.1, 1.3 and 1.8]; the exact scheme
statement and its invariant-affine hypothesis are also indexed as
`AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant`
in `fermats_last_theorem` v4_33_1. Neither theorem assumes a free action.

The conclusion is only the absolute quotient and its universal property.
Smoothness over a parameter scheme, real descent, and flat base change are
separate applications.

[GPRV, Proposition 9.5 and proof of Theorem 9.2, pp. 40–41] discuss the
involution and quotient motive. [SGA1, Exposé V, Propositions 1.1, 1.3,
1.8 and 1.9] give the finite nonfree scheme quotient under
the affine-orbit hypothesis and its flat base change. The selected Euler
family now records an affine open around every pair of points, and the
real-to-cyclotomic field extension is flat. Extension of the explicit
reflection to the selected proper *relative* model and smooth proper
real descent remain separate source applications. They are now isolated in
`exists_realEulerReflectionData_of_coprime` and the generic tame-curve
quotient interface, rather than hidden in the final Euler theorem.

The formula `y ↦ 1/y` printed in [GPRV, (73), p. 40] is the formula in
the Kummer coordinate `w = y/(1-x)`. For the Euler coordinate in this
library the checked branch-open formula is
`y ↦ -(1-x)(1-tx)/(txy)`. The theorem
`EulerCover.reflectionNormalizedRoot_inverse` proves the coordinate
transport directly, so the two formulas are not conflated.
Its cohomological realization is a separate construction.

### 38. `exists_realEulerReflectionData_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationQuotient.lean)

[EsnaultViehweg, §3, (3.5)–(3.13)] constructs the same cyclic cover
over the real field, and the family record fixes its cyclotomic base
change. The branch-open involution is `w ↦ 1/w` in the normalized
coordinate, exactly [GPRV, Proposition 9.5, (73), p. 40], as proved by
`reflectionNormalizedRoot_inverse`. Each proper geometric fibre has genus
`N-1 ≥ 2`: density of the generic Euler chart identifies the geometric
generic curve, and proper smooth comparison preserves geometric connectedness
and genus along the connected parameter line [src_milne_lec, Theorem 20.4].
Riemann–Hurwitz for its four primitive branch points gives genus `N-1`.
[DeligneMumford1969, Theorem 1.11 and Lemma 1.12, pp. 84–85] then extend
the generic automorphism uniquely over the smooth stable family. The
parenthetical after Lemma 1.12 explicitly extends its statement to arbitrary
valuation rings; the parameter line is regular. Uniqueness
identifies its cyclotomic base change with the reflection on `𝒞` because
`realBaseChangeIso_affineInclusion` fixes the same dense Euler chart on both
models. An arbitrary over-base isomorphism without that chart equality would
not suffice.

This named source-application interface supplies only the reflection and
the specified model comparison, not a quotient or cohomological claim.

[GPRV, Proposition 9.5 and proof of Theorem 9.2, pp. 40–41] discuss the
involution and quotient motive. [SGA1, Exposé V, Propositions 1.1, 1.3,
1.8 and 1.9] give the finite nonfree scheme quotient under
the affine-orbit hypothesis and its flat base change. The selected Euler
family now records an affine open around every pair of points, and the
real-to-cyclotomic field extension is flat. Extension of the explicit
reflection to the selected proper *relative* model and smooth proper
real descent remain separate source applications. They are now isolated in
`exists_realEulerReflectionData_of_coprime` and the generic tame-curve
quotient interface, rather than hidden in the final Euler theorem.

The formula `y ↦ 1/y` printed in [GPRV, (73), p. 40] is the formula in
the Kummer coordinate `w = y/(1-x)`. For the Euler coordinate in this
library the checked branch-open formula is
`y ↦ -(1-x)(1-tx)/(txy)`. The theorem
`EulerCover.reflectionNormalizedRoot_inverse` proves the coordinate
transport directly, so the two formulas are not conflated.
Its cohomological realization is a separate construction.

### 39. `exists_smoothProperPuncturedCurveInvolutionQuotient`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationQuotient.lean)

Relative properties of a **selected** finite involution quotient of a
smooth proper curve over a characteristic-zero punctured parameter line.
The selected real quotient `(Y, πReal)` is already categorical; its
existence is supplied separately by the checked application of [SGA1,
Exposé V, Propositions 1.1, 1.3 and 1.8]. Corollary 1.5 and the
finite-surjective/proper argument give properness. Since two is invertible,
averaging splits the
invariants from the source algebra and makes them commute even with field
extension; flatness of the quotient follows from the source's flatness.
Each geometric fibre is the quotient of a smooth curve by an involution,
whose invariant local rings are DVRs; the quotient fibres are smooth. The
flat, finitely presented, smooth-fibre criterion is
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` in mathlib
v4_34_0. Properness follows from the finite surjective quotient map and
properness of the source. These standard geometric deductions are retained
as a visible literature interface; it is independent of the Euler equation.

The isomorphism `e` identifies the chosen field-extended curve `X` with the
actual base change of `C`; the compatibility hypothesis forces the quotient
map below to use the same involution on `X`.

[GPRV, Proposition 9.5 and proof of Theorem 9.2, pp. 40–41] discuss the
involution and quotient motive. [SGA1, Exposé V, Propositions 1.1, 1.3,
1.8 and 1.9] give the finite nonfree scheme quotient under
the affine-orbit hypothesis and its flat base change. The selected Euler
family now records an affine open around every pair of points, and the
real-to-cyclotomic field extension is flat. Extension of the explicit
reflection to the selected proper *relative* model and smooth proper
real descent remain separate source applications. They are now isolated in
`exists_realEulerReflectionData_of_coprime` and the generic tame-curve
quotient interface, rather than hidden in the final Euler theorem.

The formula `y ↦ 1/y` printed in [GPRV, (73), p. 40] is the formula in
the Kummer coordinate `w = y/(1-x)`. For the Euler coordinate in this
library the checked branch-open formula is
`y ↦ -(1-x)(1-tx)/(txy)`. The theorem
`EulerCover.reflectionNormalizedRoot_inverse` proves the coordinate
transport directly, so the two formulas are not conflated.
Its cohomological realization is a separate construction.

### 40. `exists_commonRealEulerQuotientRealization_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationQuotientDescent.lean)

[GPRV, Theorem 9.2 and Proposition 9.5, pp. 40–41], in the coprime
symmetric case.  Their involution quotient is formed over `K_N` before
choosing a coefficient place; the real cyclotomic action on its H¹ has a
rank-two labelled component, and pullback to the Euler curve identifies that
component with the fixed `χ₀` summand. The source condition `(Irr)` follows
from `symmetricParameters_irreducible` and [GPRV, Lemma 8.5, p. 30].
This is the RAW cohomological
realization and chosen descent, not an assumption about Frobenius traces,
modularity, or an arithmetic RM comparison.  The `coefficientBaseChange`
field includes the standard rational `ℓ`-adic scalar extension of this same
quotient's H¹ and its labelled correspondence.  Its source correspondence
combines [src_milne_lec, Theorem 20.4, pp. 127–128] for proper smooth
cohomology with [proetale2015, Lemma 6.7.17, printed p. 57] for
finite-coefficient pushforward/tensor compatibility, and [proetale2015,
Definition 6.8.1 and Lemma 6.8.2, printed pp. 58–59; Proposition 6.8.4(3),
p. 59; Proposition 6.8.14 and Remark 6.8.15, pp. 61–62] for finite local
coefficient extension and functorial
sheaves.  GPRV does not state the entire Lean record verbatim.  This
strengthens the previously used joint-choice interface: the equivalence is
required at the same quotient and label for every real-field Galois element,
not just for its cyclotomic subgroup.

The common quotient is geometric data over the real parameter line.  At each
coefficient place, [GPRV, Theorem 9.2 and Proposition 9.5] take the labelled
component of its degree-one cohomology and compare its cyclotomic base change
with the fixed-character Euler summand.  Keeping the common quotient outside
the place data ensures that the specializations are not independent choices.

### 41. `functionFieldMapOfGenericPoint_comp_of_curves`

[Lean statement](HilbertModularity/Hypergeometric/GaloisRealizationQuotientFunctionField.lean)

Canonical pullback on function fields is contravariantly functorial for
smooth projective integral curves.  The maps here are exactly the generic
stalk maps above, and the hypotheses retain the curve and dominant-map
conditions of [src_poonen_curves, §§2.1.1–2.1.2, p. 23].  This established
curve/function-field correspondence is a visible literature premise.

### 42. `properEuler_fixedPrimitive_inertia_eq_one_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/GoodReductionInertia.lean)

[GPRV, Assumption 1 and Remark 7.1, p. 28] identify the smooth good
reduction of this completed Euler fibre. [src_milne_lec, Theorems 20.2 and 20.4,
pp. 127–128] give smooth proper base change for finite torsion cohomology;
the usual ℓ-adic passage and scalar extension give trivial inertia on the
actual proper `H¹` and its fixed `χ₀` projector. The correspondence with the
project's rationalized pro-étale cohomology API is an explicit admitted part
of this literature input. No extra exclusion is made at residue characteristic
two.

### 43. `exists_gprvKappaRealCharacter`

[Lean statement](HilbertModularity/Hypergeometric/GprvKappaCharacter.lean)

One finite real-field extension of the character of
`F_N(ζ₂N)/F_N` [GPRV, Definition 8.8 and Corollary 8.10, p. 33;
Lemma 9.4, p. 40]. The displayed kernel is the exact action on the
cyclotomic extension, rather than an arbitrary quadratic character.
For odd N the extension is chosen trivial. For even N the source gives a
Dirichlet extension to `G_ℚ`, whose restriction to `G_{K_N}` has order at
most two; this interface records that restriction, not an assertion that
the global Dirichlet character is always quadratic or unique. Its finite
ramification is supported at primes dividing `2N`.

This is an existing-literature premise, with no Euler trace, RM comparison
or modularity assertion.

The character κ_N is attached to F_N(ζ₂N)/F_N [GPRV, Definition 8.8],
then extended to the real field using Corollary 8.10 and Lemma 9.4. Its
restriction to F_N is specified by an actual fixing subgroup. Only the
real-field restriction is asserted to have square one; the global Dirichlet
extension need not itself be quadratic for high powers of two.

### 44. `chosenGprvKappaRealCharacter_geometricFrobenius`

[Lean statement](HilbertModularity/Hypergeometric/GprvKappaCharacter.lean)

[GPRV, Lemma 8.9, p. 33] identifies κ_N at a cyclotomic prime away
from 2N with the Nth power-residue character on -1. Geometric Frobenius
has the same value as arithmetic Frobenius because the real restriction
is quadratic [GPRV, Lemma 9.4, p. 40]. The character is the single one
selected from Corollary 8.10, and this statement concerns its restriction
to the actual cyclotomic Galois group. No Euler trace is assumed.

The character κ_N is attached to F_N(ζ₂N)/F_N [GPRV, Definition 8.8],
then extended to the real field using Corollary 8.10 and Lemma 9.4. Its
restriction to F_N is specified by an actual fixing subgroup. Only the
real-field restriction is asserted to have square one; the global Dirichlet
extension need not itself be quadratic for high powers of two.

### 45. `chosenConductorNativeIntegerMap_isLocalHom`

[Lean statement](HilbertModularity/Hypergeometric/PrimePlusConductorResidueComparison.lean)

A finite extension of complete discrete valuations sends the maximal
ideal of the source valuation ring into the target maximal ideal. Applied to
the exact exponent-labelled embedding, this is [MilneANT, Theorem 7.38 and
Corollary 7.42, printed pp. 123–124]. This interface asserts only locality
of the integer map; it contains no Tate, irreducibility or modularity claim.

### 46. `realToFullConductorIntegerMap_isLocalHom`

[Lean statement](HilbertModularity/Hypergeometric/PrimePlusExtendedChecklist.lean)

The integer map is local for this finite extension of complete discrete
valuation fields. [MilneANT, Theorem 7.38 and Corollary 7.42, printed
pp. 123–124] give the unique extending valuation and its ramification and
residue degrees. In particular the extension map sends the maximal ideal
into the maximal ideal and induces the residue-field embedding. This standard local-field input says
nothing about Tate actions or Skinner–Wiles hypotheses.

### 47. `exists_primePlusDecompositionEquiv`

[Lean statement](HilbertModularity/Hypergeometric/PrimePlusLocalDecomposition.lean)

[MilneANT, Proposition 8.10 and the inertia diagram, pp. 139–140;
Proposition 8.13, p. 141; MilneFT, Theorem 7.13] For every prime `Q` of
the global algebraic closure above the unique prime of `Kₚ`, its decomposition
group is conjugate to the image of the chosen local Galois restriction. The
conjugating element depends on `Q`, because the existing embedding into
`PadicAlgCl` is fixed independently of `Q`. The equivalence is continuous and
matches inertia. This is a standard local/global Galois comparison; it does
not assert ordinary reduction or a representation isomorphism.

### 48. `localTeichmullerNaturality_literature`

[Lean statement](HilbertModularity/Hypergeometric/PrimePlusOrdinaryCoefficientExtension.lean)

Functoriality of the canonical multiplicative Teichmüller section for a
continuous local-field map. The source construction is
[mathlib_5ed296525643, `Mathlib/RingTheory/Teichmuller.lean`,
`Perfection.teichmuller₀_spec` and `mk_comp_teichmuller`, lines 136--178].
The specification characterizes the lift by compatible p-power congruences.
The integer map sends powers of the source maximal ideal into the same
powers of the target maximal ideal, and the residue map preserves Frobenius;
thus the image satisfies the target specification. Restriction to units
gives the stated naturality. These standard correspondence steps are included
in this admission. This named standard interface
contains no Skinner--Wiles data or ordinary conclusion.

### 49. `abelianVariety_integralTate_unramifiedOutsideFinite`

[Lean statement](HilbertModularity/Hypergeometric/PrimePlusSelectedChecklist.lean)

An abelian variety over a number field spreads out to an abelian scheme
outside finitely many finite places. The Néron–Ogg–Shafarevich criterion makes
its covariant `p`-adic Tate module unramified away from these places and those
above `p`. Here proper, smooth and geometrically connected are the
abelian-variety conditions on a commutative group scheme over a field. The
spreading-out step uses [src_stacks_spreading, Tags 01ZM, 0C0C, 081F]: descend
the scheme, group maps and identities, then smoothness and properness. Geometric
connectedness persists by the finite étale Stein factorization
[src_stacks_spreading, Tag 0E0D], whose generic degree is one. The local
criterion is [MilneAV, Chapter IV, §3, Theorem 3.5, printed p. 141]; its proof
identifies the unramified action on every prime-power torsion group, hence on
the integral inverse limit. The exceptional set also includes primes above `p`.

### 50. `properEuler_fixedPrimitive_geometricFrobenius_trace_of_coprime`

[Lean statement](HilbertModularity/Hypergeometric/ProperFrobeniusComparison.lean)

[GPRV, Theorem 7.4 and Assumption 1], applied to the actual proper
Euler curve for any coprime exponents `m,N-m,m,N-m`. The geometric prime is away from
`N` and the coefficient characteristic, and `GoodUnit` keeps the four branch
sections distinct. Since the polynomial has degree `N+m`, the infinity term
of [GPRV, Definition 7.2] is zero. The deck projector is the fixed `χ₀`
projector on this exponent-`m` curve. Frobenius is geometric.

The fixed `χ₀` summand of the exponent-`m` proper Euler curve is the object in
[GPRV, Theorem 7.4]. Its raw trace is an admitted literature input below.
Conjugating by the comparison of the chosen generic real-field descent then
gives the trace of its arithmetic specialization. No finite-sum normalization
or Jacobi-sign identity is admitted in that comparison.

### 51. `exists_adicCompletionIntegersEquiv`

[Lean statement](HilbertModularity/NumberTheory/AdicCompletionIntegersComparison.lean)

The canonical inverse-limit completion of global integers is the native
valuation-integer ring of the completed field. This is the global-integer form
of [MilneANT, Lemma 7.25 and Aside 7.30, pp. 116, 119]: localization at `P`
does not change `𝓞 K / Pⁿ`, and the local DVR's inverse-limit completion is
the valuation ring in `P.adicCompletion K`. The map on global integers is the
existing `adicCompletionIntegerMap`; no Tate action or determinant is included.

The inverse limit of the global integer ring modulo powers of a height-one
prime is the valuation ring of the corresponding number-field completion.
The comparison uses localization modulo prime powers before applying the DVR
completion theorem [MilneANT, Theorem 7.23 and Remark 7.24, p. 115; Lemma
7.25, p. 116; Aside 7.30, p. 119].

### 52. `coe_adicCompletionIntegersEquiv_padicInt`

[Lean statement](HilbertModularity/NumberTheory/AdicCompletionIntegersComparison.lean)

The canonical comparison preserves the selected `ℤₚ` coefficient map.
Here the right side is the already defined embedding of `ℚₚ` into the actual
real cyclotomic completion, restricted to `ℤₚ`. This is the scalar part of
[MilneANT, Theorem 7.23, Lemma 7.25 and Aside 7.30, pp. 115–119], together
with the cofinal ramification identity proved in `RealCyclotomicPrime`.
It does not assert an equivalence of Tate actions or a determinant identity.

The inverse limit of the global integer ring modulo powers of a height-one
prime is the valuation ring of the corresponding number-field completion.
The comparison uses localization modulo prime powers before applying the DVR
completion theorem [MilneANT, Theorem 7.23 and Remark 7.24, p. 115; Lemma
7.25, p. 116; Aside 7.30, p. 119].

### 53. `exists_eigenformCohomologicalActions`

[Lean statement](HilbertModularity/NumberTheory/HilbertModularForms/EigenformCohomologicalExistence.lean)

The weight-two Hilbert eigenform Galois construction, in the
geometric-Frobenius and cohomological normalization of
[src_skinner_hilbert_2009, §1, (1), pp. 241–242]. The source constructs a
continuous semisimple representation at each coefficient place, with the
unramified Hecke roots. The precise one-field formulation also uses the local
field-of-definition observation in §2 (p. 244), the spherical Hecke parameter
in §2.4.2 (pp. 252–255), and odd-involution descent (p. 256). The bounded
adelic vector with finite-image center gives a classical cuspidal vector by
the dictionary of [SkinnerWiles, §3.1, pp. 27–29]. These correspondence and
descent steps are included in this admitted literature input; the theorem is
not claimed to appear verbatim in either source. In particular, the output
supplies trace and determinant separately, not a presumed common polynomial.

### 54. `nonempty_arithmeticIdeleRealization`

[Lean statement](HilbertModularity/NumberTheory/HilbertModularForms/FiniteCharacterReciprocity.lean)

Finite-character global class field theory, in arithmetic normalization.

The character has finite image, continuous realizations at the coefficient
completions, and trivial inertia outside `χ.bad`. Thus its open kernel cuts
out a finite abelian extension. Compose its character with the global Artin
map and the specified complex embedding. [MilneCFT, V Proposition 5.2 and
Theorem 5.3, pp.178–179] supply continuity, local compatibility and principal
idele triviality. [MilneCFT, I Theorem 1.1(a), p.20] gives the displayed
uniformizer/arithmetic-Frobenius formula. [MilneCFT, V Remark 5.7(a), p.179]
gives triviality on positive real and complex infinite components. The prime
datum has determinant a uniformizer at `q` and one at all other places.
No de Rham algebraization or modularity assertion is included.

Global reciprocity is used once, with arithmetic Frobenius. Inverting the
resulting idele character gives the geometric-Frobenius convention of the
cohomological comparison in [TripathiGoswami, §3]. The actual cusp form is
then twisted using the existing finite-twist construction.

### 55. `nonempty_heckeLevelRefinement`

[Lean statement](HilbertModularity/NumberTheory/HilbertModularForms/HeckeLevelRefinement.lean)

Compact-open refinement and unramified Hecke level compatibility.

[SkinnerWiles, §3.1, pp.27–30] identifies the restricted product, defines the
finite double-coset sums in (3.1), and explicitly states on p.30 that level
inclusion respects T(q) and S(q) when both local factors are GL₂(O_q).
The passage from an arbitrary compact open K to a product sublevel uses the
restricted-product neighbourhood basis (p.27): outside a finite set K contains
and is contained in the integral local factors. Intersect at the remaining
places with an open subgroup in the finite character kernel. Finite image and
continuity make that kernel open. The common local coset decomposition proves
(3.1) agrees for every right-K-invariant function, independently of analytic
conditions. This is the standard topological/double-coset consequence of those
passages, not an application of the ordinary-family Lemma 3.17.

The same normalized prime element is retained; no measure rescaling or index
factor occurs in these finite sums. No eigenform or automorphic twist is
asserted by this named literature input.

### 56. `skinnerWiles_weightTwoEigenform_withAnalyticData`

[Lean statement](HilbertModularity/NumberTheory/HilbertModularForms/SkinnerWiles.lean)

The cuspidal eigenform consequence of the weight-two case of
[SkinnerWiles, §4.5, Theorem A]. The associated Galois representation and its
arithmetic-Frobenius normalization is displayed in §3.3, (3.2), whose
even-degree assumption is not imposed by Theorem A. `ρ` is
the covariant representation to which the lifting theorem applies. Passing
to geometric Frobenius and dualizing gives `ρᵛ ≃ rᶜᵒʰ`; no finite-order or
Tate twist is inserted. The source calls its output a newform, but this
interface records only the eigenform consequence, since no conductor/newvector
structure has yet been formalized. The analytic properties use the adelic
dictionary in §3.1, pp. 27–29: cusp decay on finitely many reduction sectors
bounds the normalized weight-two lift, and its finite-level nebentype has
finite image. These correspondence steps are included in this input.

We use the covariant normalization of [SkinnerWiles, §4.5, Theorem A].
The automorphic output is a genuine adelic cuspidal Hecke eigenform. The
associated Galois representation uses arithmetic Frobenius, with the
normalization displayed in [SkinnerWiles, §3.3, (3.2)]. General-field
association here comes from Theorem A; §3.3 itself assumes even field degree. Dualizing it and evaluating at geometric Frobenius
gives the cohomological trace and determinant below, with no Tate twist.

### 57. `exists_sphericalEigenform`

[Lean statement](HilbertModularity/NumberTheory/HilbertModularForms/SphericalEigenformExistence.lean)

Simultaneous spherical replacement with algebraic coefficients, combining
[src_skinner_hilbert_2009, §1, (1), p. 242] with
[SkinnerWiles, §3.1, pp. 29–30]. The former is the full away-ℓ
Weil–Deligne compatibility, including monodromy, with geometric Artin
normalization; its Theorem 1 concerns primes above ℓ and is not used here.
The latter gives the cuspidal decomposition, restricted tensor product,
one-dimensional spherical invariant lines, rational finite-level cusp spaces
and rational Hecke operators.

Here is the correspondence included in this admission, rather than a verbatim
quotation. Choose a nonzero irreducible cuspidal constituent of the original
vector. Its common-good Hecke parameters are those of the original vector.
The semisimple Galois action of that constituent agrees with `D` by Frobenius
detection. Full local compatibility implies that a place with trivial inertia
away from ℓ has an unramified local parameter with zero monodromy, hence a
spherical local factor. Choose spherical vectors at all those places in the
restricted tensor product, and fixed vectors at the finitely many others.
Rationality of the finite-level Hecke action puts their eigenvalues in some
number field; take its compositum with the original coefficient field inside
ℂ. This does not claim preservation of the original field. Boundedness and the
finite central character are preserved in this weight-two cuspidal constituent.
The normalized polynomial is `X² - a_q X + Nq ω_q` for geometric Frobenius.
The unramified local parameter also identifies the Hecke polynomial. If its
polynomial in the original completion comes from `f : Polynomial A`, injectivity
of coefficient embeddings identifies the new Hecke polynomial with `f.map i`.
This records the same local compatibility, without constructing scalar extension
of an independently supplied compatible system.

### 58. `character_inertia_range_eq`

[Lean statement](HilbertModularity/NumberTheory/LocalGlobalInertia.lean)

Completion identifies local inertia with global inertia up to conjugacy.
After applying an abelian character, conjugacy disappears, so the image is the
same for every prime over `q`.

This is the infinite-Galois corollary of [MilneANT, Proposition 8.10 and the
following inertia diagram, pp.139–140; Proposition 8.13, p.141], together with
conjugacy of primes over a fixed prime. Passage through finite Galois extensions
uses [MilneFT, Theorem 7.13]. The embedding used by `localGaloisRestriction`
is the one constructed above through the actual completion. This standard
comparison makes no assertion about finiteness, Hodge weights or modularity.

### 59. `integerRing_period_hypotheses`

[Lean statement](HilbertModularity/NumberTheory/PadicDeRham.lean)

**Named literature input.** The valuation integers in the completed
algebraic closure are p-adically complete and p is not a unit.
This is the standard completeness used for `O_C` in [src_brinon_conrad,
section 4.3, p.52, before Proposition 4.3.1] and in the period construction
of section 4.4, pp.56--60. Indeed `p^n O_C` is the closed norm ball of radius
`p^(-n)`; these balls give the same complete topology as the norm on `O_C`,
and `|p|=p^(-1)<1`. This admission supplies no representation or period
comparison and is not a claim that the cited proposition states this
specialization verbatim.

### 60. `rayClassGroup_finite`

[Lean statement](HilbertModularity/NumberTheory/RayClassCharacter.lean)

Named literature input: ray-class finiteness, [MilneCFT, V.1, Theorem 1.7,
pp.150–151]. The fractional description is justified by Lemma 1.5, p.150;
the quotient is the definition on p.149. The finite modulus must be nonzero.
No assertion about a Galois character or its weights is part of this input.

We use fractional ideals prime to a nonzero finite modulus, with all real places
in the infinite modulus. This allows arbitrary real-place signs. Ray-class
finiteness is the named literature input [MilneCFT, V.1, Theorem 1.7].
The zero-infinity-type deduction is the ideal-character step of the revised
manuscript's rank-one zero-weight lemma. No Galois/Hecke comparison is assumed
or proved here.

### 61. `nonempty_narrowClassFieldEquiv`

[Lean statement](HilbertModularity/NumberTheory/UnramifiedAbelianQuotient.lean)

Narrow class field reciprocity, [MilneCFT, V Theorems 3.5–3.6 and
Remark 3.8, p.158; V Example 1.8(b), p.151]. The finite part of the modulus
is the unit ideal and its infinite part contains every real place.

Every finite abelian extension unramified at finite primes has conductor
dividing this modulus. The reciprocity and existence theorems identify their
maximal compositum with this ray class field. The closed normal subgroup
description follows from Galois correspondence [MilneFT, Theorem 7.13].
Only existence of the group isomorphism is used; no Frobenius convention is
chosen by this interface. It contains no particular character or weight
hypothesis, and asserts no manuscript comparison or modularity result.

### 62. `exists_periodStructure_with_hodgeTateComparison`

[Lean statement](HilbertModularity/RepresentationTheory/DeRhamComparison.lean)

**Named literature input.** Fontaine's canonical construction supplies
the Galois action and algebraic-constant embedding on the actual library
period ring. [src_brinon_conrad, section 4.4: Proposition 4.4.2,
Proposition 4.4.6, Definition 4.4.7, and Theorem 4.4.13, pp.57--65]
gives the equivariant Fontaine map, complete valuation ring, period field,
and its local fixed fields. [src_brinon_conrad, Proposition 6.3.2, p.76]
then states that de Rham representations are Hodge--Tate. Its comparison
uses `gr(B_dR)=B_HT` with the usual cyclotomic grading. Our existing
comparison uses weight `n` for the `cyclotomic^(-n)` eigenspace.

The action is pinned through the actual integral, tilt, Witt, localization,
and adic quotient-coordinate maps. The algebraic constants lift their given
`Cp` residues through the canonical Fontaine map. These conditions describe
the functorial Fontaine action, rather than merely an arbitrary action that
extends constants. The structure and comparison are selected together. The
dimension condition is the ordinary invariant-tensor definition, expressed
over `Qp` by restriction of scalars. Finite-dimensional Hausdorff continuous
`Qp`-module topologies are the usual ones. No finite inertia, global character
algebraization, weight-zero assertion, or manuscript conclusion occurs here.

### 63. `geometricFrobenius_eq`

[Lean statement](HilbertModularity/RepresentationTheory/FiniteCharacterFrobenius.lean)

Frobenius conjugacy and restriction in the finite abelian quotient cut out
by a continuous finite character: [MilneANT, §8.14–8.16, pp.141–142].
Finite range and continuity in any coefficient completion make the kernel open;
trivial inertia makes the corresponding finite extension unramified at `q`.
Milne's arithmetic Frobenius equality gives this geometric equality by inversion.
This input concerns only the character, not an RM or Euler representation.

### 64. `finiteCharacterTwist_labelledWeightSpace_finrank`

[Lean statement](HilbertModularity/RepresentationTheory/FiniteCharacterLabelledHodgeTate.lean)

Finite local characters have weight zero at every local label, so
tensoring preserves the labelled multiplicity of every weight.
This is the standard finite-extension invariance of Hodge–Tate weights
[src_brinon_conrad, Theorem 2.4.6, p.20; Theorem 2.4.11 and
Definition 2.4.12, pp.23–24], stated for the
actual coefficient and local-field embeddings. It is a generic
literature interface and makes no Euler, RM, Frobenius or modularity
assertion.

A finite character becomes trivial after a finite local extension. Its
actual tensor period identifies the canonical comparisons, and finite
extension descent preserves each labelled Hodge–Tate multiplicity
[src_brinon_conrad, Theorem 2.4.6, p.20; Theorem 2.4.11 and
Definition 2.4.12, pp.23–24].

### 65. `finiteCharacter_unramifiedOutsideFinite`

[Lean statement](HilbertModularity/RepresentationTheory/FiniteCharacterRamification.lean)

A continuous finite-image character of a number-field absolute Galois
group is trivial on inertia outside finitely many finite primes.

Literature input: [MilneFT, Theorem 7.13(b),(d), p.98] and
[MilneANT, Theorem 3.35, Remark 3.39(b), pp.60,62; Proposition 8.11, p.140].
The finite image in a Hausdorff space is discrete, so the kernel is open.
Its fixed field is a finite Galois extension. Its discriminant ideal has finite
support; away from that support, restriction of absolute inertia is trivial.
Remark 3.39(b) removes the freeness restriction in Theorem 3.35.
This supplies no comparison between representations.

### 66. `frobenius_semisimple_detection`

[Lean statement](HilbertModularity/RepresentationTheory/FrobeniusSemisimpleDetection.lean)

Chebotarev density and Brauer–Nesbitt identify continuous semisimple
representations from their good geometric-Frobenius polynomials. The explicitly
finite exceptional set and coefficient-characteristic exclusion are part of
the signature. This is the local-field form of [MilneAV, Chapter IV, §3,
Lemmas 3.8–3.9, printed pp. 142–143].

The named input below is the Chebotarev–Brauer–Nesbitt step of [MilneAV,
Chapter IV, §3, Lemma 3.8 and its proof on printed pp. 142–143; Lemma 3.9].
Milne states it over `ℚ_[ℓ]` and uses arithmetic Frobenius. The same proof
works over the finite extension `w.adicCompletion E`: replace `ℤ_[ℓ]` by its
valuation ring in the lattice and Nakayama argument, and apply Lemma 3.9 over
the characteristic-zero coefficient field. Equality at geometric Frobenius
gives equality at its inverse, the arithmetic Frobenius, since the matrices are
invertible. The characteristic polynomial hypothesis is imposed away from a
finite set containing ramification and the coefficient characteristic.

This literature theorem remains an open `sorry` obligation. It detects two
independently supplied continuous semisimple representations; its conclusion
does not contain any compatible-system promotion or character comparison.

### 67. `normalizedDeterminant_comparison_and_weights`

[Lean statement](HilbertModularity/RepresentationTheory/HodgeTateDeterminant.lean)

**Hodge–Tate determinant and Tate-twist compatibility.**
[src_brinon_conrad, Theorem 2.4.11, p.23; Definition 2.4.12 and following
paragraph, p.24] states exact tensor compatibility and stability under
subquotients. Apply it to the top alternating summand over `E`, then tensor
with `Qp(1)`. The coefficient action is retained by functoriality; splitting
the commuting local-field action gives precisely the displayed labels.
At each label the determinant weight is the sum of the input weights, and
the twist subtracts one. Only comparison bijectivity and off-weight vanishing
are asserted, as needed downstream. This is a named literature admission.

`weights τ` lists all multiplicities, including repeats. The actual local
absolute Galois group, continuous action, finite coefficient extension and
every embedding of the local field are explicit. No geometric realization
or manuscript-specific comparison is asserted.

The standard tensor compatibility of Hodge–Tate comparison is the literature
boundary. The rank-two specialization below proves the weight calculation used
in [TripathiGoswamiRevised, Proposition 2.5].

### 68. `finite_inertia_of_character_zeroWeightSpan`

[Lean statement](HilbertModularity/RepresentationTheory/HodgeTateInertia.lean)

A continuous finite-coefficient character whose actual fixed periods span
the completed tensor has finite image on actual valuation-residue inertia.

We follow [Caruso2019, Theorem 2.2.1]. The assertion is the rank-one
coefficient-field specialization of the theorem that a continuous finite-dimensional
Qp representation with spanning fixed Cp periods has finite inertia.

### 69. `comparison_injective`

[Lean statement](HilbertModularity/RepresentationTheory/HodgeTateInjectivity.lean)

**Serre–Tate injectivity**, in the untwisted-eigenspace formulation of
[src_brinon_conrad, Lemma 2.3.1 and Remark 2.3.2, pp.16–17]. Apply that result
to `W = Cp ⊗[Qp] V`. Our weight `q` uses the eigencharacter `χ^(-q)`, exactly
the source's `W[q]`; each summand map sends `c ⊗ x` to `c • x`.

The hypotheses retain a finite embedded local base field, the actual absolute
Galois group with its Krull topology, and a finite-dimensional continuous
representation. No such assertion is made for an arbitrary abstract group.
This is an admitted literature theorem, not a proof of the Serre–Tate lemma.

The Serre–Tate lemma [src_brinon_conrad, Lemma 2.3.1, p.16;
Remark 2.3.2, p.17] applies to the completed period tensor of a continuous
finite-dimensional representation of the actual local absolute Galois group.
This named literature input does not assert that the representation is
Hodge–Tate or that its comparison map is surjective.

### 70. `finite_inertia_of_character_ne_coefficient_prime`

[Lean statement](HilbertModularity/RepresentationTheory/LocalCharacterInertia.lean)

The standard finite-inertia corollary of local reciprocity away from the
coefficient characteristic. Sources: [MilneCFT, I Theorem 1.1, p.20;
I §§1.8–1.11, pp.22–24]. Inertia in the abelianization is the local unit
group; principal units are pro-`p`. The inverse image of an open pro-`ell`
subgroup of the coefficient units is open. Its intersection with principal
units has trivial image, since a group both pro-`p` and pro-`ell` is trivial.
The remaining quotient is finite. This elementary topological-group corollary
is included in the admission, not attributed as a verbatim source theorem.
No finiteness of the whole character, weight or global hypothesis is assumed.

### 71. `isSemisimple_mapCoefficients`

[Lean statement](HilbertModularity/RepresentationTheory/SemisimpleCoefficientMap.lean)

A finite-dimensional semisimple representation in characteristic zero remains
semisimple under extension of its coefficient field.

Literature input: [Sharafdini2008, p. 5, Theorem 2.6], explicitly citing
[NagaoTsushima1989, Theorem II.5.4]: a finite-dimensional semisimple algebra over
a perfect field is separable. Apply this to the image of the group algebra in
`End_K(K^n)`. The original faithful semisimple module forces that image algebra's
radical to vanish. Characteristic zero makes `K` perfect; separability makes the
extended image algebra semisimple, so its extended module is semisimple.
In the displayed coordinates its group action is exactly `mapCoefficients`.
This standard representation corollary, including the image-algebra argument,
is admitted here; the cited theorem itself is an algebra statement.
No finiteness assumption on `G` is imposed or used.

### 72. `residualFactors_independent_of_freeLattice`

[Lean statement](HilbertModularity/RepresentationTheory/IntegralCharacterTwist.lean)

The *unordered* Jordan–Hölder factors of the reduction of a finite free
stable lattice over a discrete valuation ring are independent of the lattice.
Serre proves lattice independence for finite groups over a complete DVR in
[SerreFiniteGroups, Chapter 15, §15.2, Theorem 32, p. 125]. Its proof uses only
commensurability of the two stable lattices, so applies to an arbitrary group
when the stable lattices are already given; completeness is not used there.
The common map from the DVR to the finite field has maximal-ideal kernel,
and scalar extension from the residue field preserves equality of
Grothendieck classes.
This associated-graded product equivalence does not identify the character
on the chosen invariant subrepresentation.
