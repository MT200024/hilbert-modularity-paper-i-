/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.Cohomology
public import Mathlib.RepresentationTheory.Subrepresentation

/-! # The affine primitive Euler realization

The fixed primitive projector on the actual geometric affine Euler cover has an
image stable under the arithmetic Galois group of the cyclotomic field.  This
module records the resulting subrepresentation, without asserting its rank or
a descent to the real cyclotomic field.  The proper-curve comparison and the
chosen descent in [GPRV, Theorem 9.2 and Proposition 9.5] are separate inputs
to the effective realization of [TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] [CharZero L]
  [FiniteDimensional ℚ_[ℓ] L]

/-- The actual affine geometric Euler cohomology selected by the fixed
character `χ₀(ζ)=ι(ζ)` on the exponent-`m` curve. -/
def affinePrimitiveGaloisSubrepresentation (m : ℕ) (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    Subrepresentation
      (EulerCover.geometricCoefficientGaloisRepresentation N m t ℓ (L := L) 1) where
  toSubmodule :=
    (EulerCover.cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι 1).range
  apply_mem_toSubmodule σ := by
    intro v hv
    exact EulerCover.cyclotomicGeometricFixedPrimitiveProjector_galois_mem_range
      N ℓ L m t ι 1 σ hv

/-- The arithmetic Galois action restricted to the actual affine primitive
cohomology of the Euler cover over `F_N`. -/
def affinePrimitiveGaloisRepresentation (m : ℕ) (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    Representation L
      (AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
        AlgebraicClosure (Cyclotomic.cyclotomicField N))
      (affinePrimitiveGaloisSubrepresentation N ℓ L m t ι).toSubmodule :=
  (affinePrimitiveGaloisSubrepresentation N ℓ L m t ι).toRepresentation

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The actual deck action on the affine Galois subrepresentation has the
fixed coefficient character, independently of the exponent `m`. -/
theorem affinePrimitiveGaloisSubrepresentation_deck_eigen (m : ℕ)
    (t : Cyclotomic.cyclotomicField N) (ι : Cyclotomic.cyclotomicField N →+* L)
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    (v : (affinePrimitiveGaloisSubrepresentation N ℓ L m t ι).toSubmodule) :
    EulerCover.geometricCoefficientDeckRepresentation N m t ℓ (L := L) 1 ξ
        (v : EulerCover.GeometricCoefficientCohomology N m t ℓ (L := L) 1) =
      ι ((ξ : (Cyclotomic.cyclotomicField N)ˣ) : Cyclotomic.cyclotomicField N) •
        (v : EulerCover.GeometricCoefficientCohomology N m t ℓ (L := L) 1) := by
  obtain ⟨w, hw⟩ := v.property
  simpa only [hw] using
    EulerCover.cyclotomicGeometricFixedPrimitiveProjector_eigen
      N ℓ L m t ι 1 ξ w

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- On primitive affine cohomology, the Galois action is the restriction of
the action on the actual geometric Euler cover. -/
theorem affinePrimitiveGaloisRepresentation_apply (m : ℕ)
    (t : Cyclotomic.cyclotomicField N) (ι : Cyclotomic.cyclotomicField N →+* L)
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    (v : (affinePrimitiveGaloisSubrepresentation N ℓ L m t ι).toSubmodule) :
    ((affinePrimitiveGaloisRepresentation N ℓ L m t ι σ v :
      (affinePrimitiveGaloisSubrepresentation N ℓ L m t ι).toSubmodule) :
        EulerCover.GeometricCoefficientCohomology N m t ℓ (L := L) 1) =
      EulerCover.geometricCoefficientGaloisRepresentation N m t ℓ (L := L) 1 σ v :=
  (rfl)

end HilbertModularity.Hypergeometric
