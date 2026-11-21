/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.BaseChange

/-! # Specialization of the affine Euler family

The punctured parameter has an actual evaluation map at every point where the
parameter and its complement are units. Scalar extension along this map gives
the affine Euler cover in [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u v
variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The parameter coordinate on the punctured affine line. -/
abbrev familyParameter : ProjectiveLine.puncturedCoordinateRing R :=
  algebraMap R[X] (ProjectiveLine.puncturedCoordinateRing R) X

/-- Evaluation of the punctured parameter at a legitimate coefficient point. -/
def parameterEval (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    ProjectiveLine.puncturedCoordinateRing R →+* S :=
  Localization.awayLift (Polynomial.eval₂RingHom (algebraMap R S) t)
    ((X : R[X]) * (X - 1)) (by
      have ht1 : IsUnit (t - 1) := by simpa only [neg_sub] using h1t.neg
      simpa using ht.mul ht1)

/-- Evaluation has its expected values on polynomial parameter coordinates. -/
theorem parameterEval_algebraMap (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) (p : R[X]) :
    parameterEval R t ht h1t
      (algebraMap R[X] (ProjectiveLine.puncturedCoordinateRing R) p) =
      Polynomial.eval₂ (algebraMap R S) t p := by
  unfold parameterEval
  exact IsLocalization.Away.lift_eq ((X : R[X]) * (X - 1)) _ p

/-- The parameter coordinate specializes to the chosen point. -/
theorem parameterEval_familyParameter (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    parameterEval R t ht h1t (familyParameter R) = t := by
  rw [familyParameter, parameterEval_algebraMap]
  simp

/-- The original coefficient ring maps into the fiber by its given algebra map. -/
theorem parameterEval_coeff (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) (r : R) :
    parameterEval R t ht h1t
      (algebraMap R[X] (ProjectiveLine.puncturedCoordinateRing R) (C r)) =
      algebraMap R S r := by
  rw [parameterEval_algebraMap]
  simp

/-- The actual Euler-family algebra specializes to the prescribed Euler fiber. -/
def familyCoverSpecializationMap (N m : ℕ) (t : S) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    CoverRing N m (familyParameter R) →+* CoverRing N m t := by
  have h := parameterEval_familyParameter R t ht h1t
  exact h ▸ coverRingMap (parameterEval R t ht h1t) N m (familyParameter R)

/-- Specialization carries the family's covering coordinate to the fiber coordinate. -/
theorem familyCoverSpecializationMap_root (N m : ℕ) (t : S)
    (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    familyCoverSpecializationMap R N m t ht h1t (coverRoot N m (familyParameter R)) =
      coverRoot N m t := by
  let f := parameterEval R t ht h1t
  let τ := familyParameter R
  have transport_root (u : S) (h : f τ = u) :
      (h ▸ coverRingMap f N m τ) (coverRoot N m τ) = coverRoot N m u := by
    cases h
    exact coverRingMap_root f N m τ
  simpa only [familyCoverSpecializationMap] using
    transport_root t (parameterEval_familyParameter R t ht h1t)

/-- Specialization intertwines the actual deck actions on the family and fiber. -/
theorem familyCoverSpecializationMap_deck (N : ℕ) [NeZero N] (m : ℕ)
    (t : S) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ζ : rootsOfUnity N (ProjectiveLine.puncturedCoordinateRing R)) :
    (familyCoverSpecializationMap R N m t ht h1t).comp
        (deckAlgebraAction N m (familyParameter R) ζ).toRingHom =
      (deckAlgebraAction N m t
        (rootsOfUnity.mapHom N (parameterEval R t ht h1t) ζ)).toRingHom.comp
          (familyCoverSpecializationMap R N m t ht h1t) := by
  let f := parameterEval R t ht h1t
  let τ := familyParameter R
  have transport_deck (u : S) (h : f τ = u) :
      (h ▸ coverRingMap f N m τ).comp (deckAlgebraAction N m τ ζ).toRingHom =
        (deckAlgebraAction N m u (rootsOfUnity.mapHom N f ζ)).toRingHom.comp
          (h ▸ coverRingMap f N m τ) := by
    cases h
    exact coverRingMap_deck f N m τ ζ
  simpa only [familyCoverSpecializationMap] using
    transport_deck t (parameterEval_familyParameter R t ht h1t)

/-- The fiber is the scalar extension of the actual affine Euler family. -/
def familyCoverSpecializationEquiv (N m : ℕ) (t : S)
    [Algebra (ProjectiveLine.puncturedCoordinateRing R) S]
    (heval : algebraMap (ProjectiveLine.puncturedCoordinateRing R) S
      (familyParameter R) = t) :
    (S ⊗[ProjectiveLine.puncturedCoordinateRing R]
      CoverRing N m (familyParameter R)) ≃ₐ[S] CoverRing N m t := by
  exact heval ▸ coverBaseChangeEquiv (R := ProjectiveLine.puncturedCoordinateRing R)
    (S := S) N m (familyParameter R)

end HilbertModularity.Hypergeometric.EulerCover
