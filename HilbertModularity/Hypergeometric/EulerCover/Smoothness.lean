/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness of the affine Euler cover

The complement of the finite branch sections in the Euler root algebra is smooth
over its coefficient ring when the covering degree is invertible. This is the
affine part of the family in [TripathiGoswamiRevised, Definition 2.3];
the smooth proper normalization is a separate construction.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable {R : Type u} [CommRing R]

/-- The branch-complement coordinate ring is smooth over its coefficient ring. -/
theorem baseRing_smooth (t : R) : Algebra.Smooth R (BaseRing t) := by
  have : Algebra.Smooth R R[X] := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth R[X] (BaseRing t) :=
    Algebra.Smooth.of_isLocalization_Away (branchProduct t)
  exact Algebra.Smooth.comp R R[X] (BaseRing t)

/-- The actual Euler root algebra is smooth on the finite branch complement. -/
theorem coverRing_smooth (N m : ℕ) (t : R) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) : Algebra.Smooth R (CoverRing N m t) := by
  have := baseRing_smooth t
  have := coverRing_etale N m t hN hn
  exact Algebra.Smooth.comp R (BaseRing t) (CoverRing N m t)

/-- The structural map of the actual branch-open Euler cover is smooth. -/
theorem structureMap_smooth (N m : ℕ) (t : R) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) : Smooth (structureMap N m t) := by
  change Smooth (Spec.map (CommRingCat.ofHom
    ((algebraMap (BaseRing t) (CoverRing N m t)).comp
      ((algebraMap R[X] (BaseRing t)).comp Polynomial.C))))
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  have hC : RingHom.Smooth (Polynomial.C : R →+* R[X]) := by
    change RingHom.Smooth (algebraMap R R[X])
    exact RingHom.smooth_algebraMap.mpr (show Algebra.Smooth R R[X] from
      ⟨inferInstance, inferInstance⟩)
  have hB : RingHom.Smooth (algebraMap R[X] (BaseRing t)) :=
    RingHom.smooth_algebraMap.mpr (Algebra.Smooth.of_isLocalization_Away (branchProduct t))
  have hA : RingHom.Smooth (algebraMap (BaseRing t) (CoverRing N m t)) :=
    RingHom.smooth_algebraMap.mpr (by
      have := coverRing_etale N m t hN hn
      infer_instance)
  exact hC.comp (hB.comp hA)

variable (R)

/-- The branch-open Euler family is smooth over the actual punctured parameter line. -/
theorem familyStructureMap_smooth (N m : ℕ) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) : Smooth (familyStructureMap R N m) := by
  let t : ProjectiveLine.puncturedCoordinateRing R :=
    algebraMap R[X] (ProjectiveLine.puncturedCoordinateRing R) X
  have hn' : IsUnit (N : ProjectiveLine.puncturedCoordinateRing R) := by
    simpa using hn.map (algebraMap R (ProjectiveLine.puncturedCoordinateRing R))
  have : Smooth (structureMap N m t) := structureMap_smooth N m t hN hn'
  have : Smooth (ProjectiveLine.puncturedAffineIso R).inv := inferInstance
  change Smooth (structureMap N m t ≫ (ProjectiveLine.puncturedAffineIso R).inv)
  infer_instance

end HilbertModularity.Hypergeometric.EulerCover
