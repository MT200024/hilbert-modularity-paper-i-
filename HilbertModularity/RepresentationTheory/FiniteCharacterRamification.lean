/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter

/-! # Finite ramification of continuous finite-image characters -/

public section

open NumberField IsDedekindDomain

namespace HilbertModularity

/-- A continuous finite-image character of a number-field absolute Galois
group is trivial on inertia outside finitely many finite primes.

Literature input: [MilneFT, Theorem 7.13(b),(d), p.98] and
[MilneANT, Theorem 3.35, Remark 3.39(b), pp.60,62; Proposition 8.11, p.140].
The finite image in a Hausdorff space is discrete, so the kernel is open.
Its fixed field is a finite Galois extension. Its discriminant ideal has finite
support; away from that support, restriction of absolute inertia is trivial.
Remark 3.39(b) removes the freeness restriction in Theorem 3.35.
This supplies no comparison between representations. -/
theorem finiteCharacter_unramifiedOutsideFinite
    {F L : Type*} [Field F] [NumberField F]
    [Field L] [TopologicalSpace L] [T2Space L]
    (ν : HilbertModularForms.AbsoluteGalois F →* Lˣ)
    (hνc : Continuous ν) (hνfin : (Set.range ν).Finite) :
    ∃ bad : Set (HeightOneSpectrum (𝓞 F)), bad.Finite ∧
      ∀ q, q ∉ bad →
        ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
          ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
            ∀ g : HilbertModularForms.AbsoluteGalois F,
              g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → ν g = 1 := by
  sorry

end HilbertModularity
