/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.GoodReduction

/-! # A common finite set of bad-reduction primes

Spreading out an abelian variety gives actual good-reduction models outside
one finite set, chosen independently of any Tate coefficient prime.
-/

public section

open CategoryTheory
open scoped NumberField

namespace AlgebraicGeometry.GroupScheme

/-- An abelian variety over a number field has actual good-reduction models
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
coefficient prime, or manuscript conclusion is included in the input. -/
theorem exists_goodReductionModels_outside_finite
    (K : Type*) [Field K] [NumberField K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom] :
    ∃ bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)), bad.Finite ∧
      ∀ P, P ∉ bad →
        ∃ (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K))))),
          IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
            Nonempty (A ≅ localGenericFiber K P B) := by
  sorry

end AlgebraicGeometry.GroupScheme
