/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Extending a map between smooth proper curves

The valuative criterion extends a morphism from a dense open of a regular
curve to a proper target. Applied in both directions, it extends an open
isomorphism to an isomorphism of proper curves. The proof of this standard
curve theorem is a separate literature input; its geometric hypotheses are
kept explicit at every application. -/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- An open immersion between dense opens of integral proper smooth curves
extends to an isomorphism over the field. The dimension-one hypothesis is
essential: an analogous assertion fails for higher-dimensional proper
varieties. Poonen gives the uniqueness of smooth projective curve models
[src_poonen_curves, §2.1.2, printed p. 23]. Passing from the proper-curve
hypotheses here through the valuative criterion is part of this admitted input.
 -/
theorem exists_iso_extending_dense_open_of_smooth_proper_curve
    {K : Type*} [Field K] {C C' U : Scheme}
    (c : C ⟶ Spec (CommRingCat.of K))
    (c' : C' ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [IsIntegral C'] [IsProper c'] [Smooth c']
    (i : U ⟶ C) [IsOpenImmersion i] (hi : DenseRange i)
    (j : U ⟶ C') [IsOpenImmersion j]
    (hj : j ≫ c' = i ≫ c) :
    ∃ e : C ≅ C', e.hom ≫ c' = c ∧ i ≫ e.hom = j := by
  sorry

end AlgebraicGeometry.Scheme
