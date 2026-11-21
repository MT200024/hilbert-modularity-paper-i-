/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientCohomology

/-! # The real cyclotomic component of quotient cohomology

Theorem 9.2 of [GPRV] takes a labelled component of degree-one cohomology of
the quotient from Proposition 9.5.  The quotient's full cohomology need not
have rank two.  This module describes the component as an actual simultaneous
eigenspace for the real cyclotomic action, before comparing it with the fixed
`χ₀` projector on the Euler cover.
-/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]

/-- The action on actual quotient-fibre cohomology induced by the
`ζ_N + ζ_N⁻¹` correspondences in [GPRV, Theorem 9.2, proof, (76)].
Its construction and its commutation with Galois are part of the cited
cohomological comparison, not consequences of the scheme quotient alone. -/
structure RealCyclotomicQuotientAction where
  endomorphism : realCyclotomicField N →+*
    Module.End L (GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L)
  commutes_galois : ∀ (a : realCyclotomicField N)
      (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
        AlgebraicClosure (realCyclotomicField N))
      (v : GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L),
    endomorphism a (geometricRealEulerQuotientGaloisRepresentation
      N m 𝒞 𝒬 ξ ℓ L g v) =
      geometricRealEulerQuotientGaloisRepresentation
        N m 𝒞 𝒬 ξ ℓ L g (endomorphism a v)

/-- The coefficient label on the real cyclotomic field is the restriction
of the fixed exponent-`m` curve embedding `ι`.  Relative to the base
`m = 1` family this evaluates `ζ + ζ⁻¹` at `ι(ζ^m + ζ⁻m)`. -/
def realCyclotomicQuotientLabel
    (ι : cyclotomicField N →+* L) : realCyclotomicField N →+* L :=
  ι.comp (realEulerCoefficientInclusion N)

/-- At the generator labelled by `m`, the real coefficient action has
the manuscript's explicit `ι(ζ^m + ζ⁻m)` value. -/
@[simp] theorem realCyclotomicQuotientLabel_tau
    (ι : cyclotomicField N →+* L) (k : ℕ) :
    realCyclotomicQuotientLabel N L ι (tau N k) =
      ι ((root N) ^ k + (root N)⁻¹ ^ k) := by
  simp [realCyclotomicQuotientLabel]

/-- The exact `χ₀`-labelled summand of the quotient cohomology, expressed
without identifying it with the entire degree-one cohomology. -/
def RealCyclotomicQuotientAction.component
    (A : RealCyclotomicQuotientAction N m 𝒞 𝒬 ξ ℓ L)
    (ι : cyclotomicField N →+* L) :
    Submodule L (GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) where
  carrier := {v | ∀ a : realCyclotomicField N,
    A.endomorphism a v = (realCyclotomicQuotientLabel N L ι a) • v}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro x y hx hy a
    change A.endomorphism a (x + y) =
      (realCyclotomicQuotientLabel N L ι a) • (x + y)
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' := by
    intro c x hx a
    rw [map_smul, hx a, smul_comm]

/-- The eigenvalue equation defining membership in the labelled quotient
component, exposed for arguments in downstream modules. -/
theorem RealCyclotomicQuotientAction.component_spec
    (A : RealCyclotomicQuotientAction N m 𝒞 𝒬 ξ ℓ L)
    (ι : cyclotomicField N →+* L)
    (v : A.component N m 𝒞 𝒬 ξ ℓ L ι)
    (a : realCyclotomicField N) :
    A.endomorphism a v.1 = realCyclotomicQuotientLabel N L ι a • v.1 :=
  v.2 a

/-- The labelled component is stable under the actual Galois action on
the quotient cohomology. -/
theorem RealCyclotomicQuotientAction.component_stable
    (A : RealCyclotomicQuotientAction N m 𝒞 𝒬 ξ ℓ L)
    (ι : cyclotomicField N →+* L)
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (v : A.component N m 𝒞 𝒬 ξ ℓ L ι) :
    geometricRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L g v.1 ∈
      A.component N m 𝒞 𝒬 ξ ℓ L ι := by
  intro a
  rw [A.commutes_galois a g v.1, v.2 a, map_smul]

end HilbertModularity.Hypergeometric
