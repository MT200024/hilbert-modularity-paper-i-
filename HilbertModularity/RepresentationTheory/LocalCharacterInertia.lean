/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.HodgeTateInertia

/-! # Inertia of rank-one characters away from the coefficient prime

Local class field theory identifies abelian inertia with the local unit group.
Its open principal-unit subgroup is pro-`p`, so its continuous image in the
units of a finite `ell`-adic coefficient field is finite when `p ≠ ell`.
-/

public noncomputable section

namespace HilbertModularity

/-- The standard finite-inertia corollary of local reciprocity away from the
coefficient characteristic. Sources: [MilneCFT, I Theorem 1.1, p.20;
I §§1.8–1.11, pp.22–24]. Inertia in the abelianization is the local unit
group; principal units are pro-`p`. The inverse image of an open pro-`ell`
subgroup of the coefficient units is open. Its intersection with principal
units has trivial image, since a group both pro-`p` and pro-`ell` is trivial.
The remaining quotient is finite. This elementary topological-group corollary
is included in the admission, not attributed as a verbatim source theorem.
No finiteness of the whole character, weight or global hypothesis is assumed. -/
theorem finite_inertia_of_character_ne_coefficient_prime
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hne : p ≠ ell)
    (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (E : Type) [NontriviallyNormedField E] [CompleteSpace E]
    [Algebra ℚ_[ell] E] [ContinuousSMul ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
    (χ : Gal(PadicAlgCl p/K) →* Eˣ) (hχ : Continuous χ) :
    (Set.range (χ.comp (PadicAlgCl.inertia p K).subtype)).Finite := by
  sorry

end HilbertModularity
