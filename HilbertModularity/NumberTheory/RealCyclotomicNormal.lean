/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicCompletion
public import Mathlib.FieldTheory.Galois.Abelian

/-! # Normality and local splitting of the real cyclotomic coefficients

The real cyclotomic multiplication field is an abelian Galois extension of the
rationals. Its minimal polynomials therefore split in its actual ramified
completion, providing the primitive projectors used for the local coefficient
labels in [TripathiGoswami, ramified scalar label].
-/

@[expose] public noncomputable section
namespace HilbertModularity.Cyclotomic

/-- The concrete cyclotomic field inherits the abelian Galois structure of a cyclotomic extension. -/
instance cyclotomicField_isAbelianGalois (N : ℕ) [NeZero N] :
    IsAbelianGalois ℚ (cyclotomicField N) :=
  IsCyclotomicExtension.isAbelianGalois {N} ℚ (cyclotomicField N)

/-- The concrete real multiplication field is itself abelian Galois over the rationals. -/
instance realCyclotomicField_isAbelianGalois (N : ℕ) [NeZero N] :
    IsAbelianGalois ℚ (realCyclotomicField N) :=
  IsAbelianGalois.of_algHom (IntermediateField.inclusion (realCyclotomicField_le N))

/-- Any field containing the real multiplication field splits its rational minimal polynomials. -/
theorem splits_minpoly_realCyclotomicField (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] [Algebra (realCyclotomicField N) L]
    [IsScalarTower ℚ (realCyclotomicField N) L] (x : realCyclotomicField N) :
    ((minpoly ℚ x).map (algebraMap ℚ L)).Splits := by
  have h := (Normal.splits (inferInstance : Normal ℚ (realCyclotomicField N)) x).map
    (algebraMap (realCyclotomicField N) L)
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using h

/-- The actual prime-power coefficient completion already splits the global multiplication field. -/
theorem splits_minpoly_realPrimePowerCompletion (p k : ℕ) [Fact p.Prime]
    (x : realCyclotomicField (p ^ (k + 1))) :
    ((minpoly ℚ x).map (algebraMap ℚ (RealPrimePowerCompletion p k))).Splits :=
  splits_minpoly_realCyclotomicField (p ^ (k + 1)) (RealPrimePowerCompletion p k) x

end HilbertModularity.Cyclotomic
