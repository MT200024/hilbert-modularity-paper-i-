/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.RationalCoordinate
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # The normal coordinate ring of the punctured parameter line

The same localized polynomial ring used by the affine chart is integrally closed.
Its actual coordinate map into rational functions makes `K(X)` its fraction field.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.ProjectiveLine

/-- The affine coordinate ring of the projective line minus zero, one and infinity. -/
abbrev puncturedCoordinateRing (R : Type*) [CommRing R] :=
  Localization.Away ((Polynomial.X : Polynomial R) * (Polynomial.X - 1))

/-- Over a Noetherian coefficient ring, the affine punctured line is Noetherian. -/
instance punctured_isNoetherian (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNoetherian (punctured R) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (puncturedAffineIso R).hom

variable (K : Type*) [Field K]

/-- The punctured parameter line has an integrally closed coordinate ring. -/
instance puncturedCoordinateRing_isIntegrallyClosed : IsIntegrallyClosed (puncturedCoordinateRing K) := by
  have hX : (Polynomial.X : Polynomial K) * (Polynomial.X - 1) ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero (by simpa using (Polynomial.X_sub_C_ne_zero (1 : K)))
  exact isIntegrallyClosed_of_isLocalization (R := Polynomial K) (puncturedCoordinateRing K)
    (Submonoid.powers ((Polynomial.X : Polynomial K) * (Polynomial.X - 1)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hX)

/-- Rational functions are an algebra through the actual punctured coordinate map. -/
instance puncturedCoordinateRing_ratFuncAlgebra : Algebra (puncturedCoordinateRing K) (RatFunc K) :=
  (puncturedCoordinatesToRatFunc K).toAlgebra

/-- Localization of polynomial coordinates commutes with their rational-function values. -/
instance puncturedCoordinateRing_ratFuncTower :
    IsScalarTower (Polynomial K) (puncturedCoordinateRing K) (RatFunc K) :=
  IsScalarTower.of_algebraMap_eq fun f => (puncturedCoordinatesToRatFunc_algebraMap K f).symm

/-- The generic rational coordinate identifies `K(X)` with the fraction field of the
actual punctured coordinate ring. -/
instance puncturedCoordinateRing_isFractionRing :
    IsFractionRing (puncturedCoordinateRing K) (RatFunc K) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers ((Polynomial.X : Polynomial K) * (Polynomial.X - 1)))
    (puncturedCoordinateRing K) (RatFunc K)

end AlgebraicGeometry.ProjectiveLine
