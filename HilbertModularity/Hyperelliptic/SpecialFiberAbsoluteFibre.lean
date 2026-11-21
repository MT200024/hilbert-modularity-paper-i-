/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberStructure

/-! # The quadratic charts as absolute scheme fibres

The polynomial affine line commutes with coefficient base change. Pasting this
square with the quadratic chart pullbacks identifies each chart of the reduced
scaled cover with the fibre of the corresponding family chart over `Spec S`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace HilbertModularity.Hyperelliptic

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

local instance : Algebra R[X] S[X] :=
  (Polynomial.mapRingHom (algebraMap R S)).toAlgebra

/-- The affine line over `S` is the fibre of the affine line over `R`. -/
theorem polynomialSpecialization_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S S[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap R[X] S[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S R[X] S[X])

/-- The finite quadratic chart is the absolute coefficient fibre of the
corresponding chart in the scaled family. -/
theorem finiteSpecializationChart_toSpec_isPullback (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (DoubleCover.ChartRing
          (finiteBranchPolynomial (P.map (algebraMap R S)) 0)))))
      (Spec.map (CommRingCat.ofHom
        (finiteSpecializationMap (algebraMap R S) P t ht)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (DoubleCover.ChartRing (finiteBranchPolynomial P t))))) := by
  have h := (finiteSpecializationChart_isPullback (S := S) P t ht).paste_horiz
    (polynomialSpecialization_isPullback (R := R) (S := S))
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq] using h

/-- The reciprocal quadratic chart is the absolute coefficient fibre; monicity
ensures that its projective transition exponent survives specialization. -/
theorem infinitySpecializationChart_toSpec_isPullback [Nontrivial S]
    (P : R[X]) (t : R) (ht : algebraMap R S t = 0) (hP : P.Monic) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (DoubleCover.ChartRing
          (infinityBranchPolynomial (P.map (algebraMap R S)) 0)))))
      (Spec.map (CommRingCat.ofHom
        (infinitySpecializationMap (algebraMap R S) P t ht hP)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (DoubleCover.ChartRing (infinityBranchPolynomial P t))))) := by
  have h := (infinitySpecializationChart_isPullback (S := S) P t ht hP).paste_horiz
    (polynomialSpecialization_isPullback (R := R) (S := S))
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq] using h

end HilbertModularity.Hyperelliptic
