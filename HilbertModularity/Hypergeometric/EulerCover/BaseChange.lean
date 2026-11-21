/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.DeckTransformations

/-! # Base change of the affine Euler cover

The concrete localized root algebra for the Euler family commutes with arbitrary
coefficient changes. The covering coordinate and its deck action retain the
normalization of [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/-- The branch complement commutes with change of coefficients. -/
theorem branchProduct_map (t : R) :
    (branchProduct t).map f = branchProduct (f t) := by
  simp [branchProduct]

/-- The Euler equation commutes with change of coefficients. -/
theorem branchPolynomial_map (N m : ℕ) (t : R) :
    (branchPolynomial N m t).map f = branchPolynomial N m (f t) := by
  simp [branchPolynomial]

/-- Change the coefficient ring in the coordinates of the branch complement. -/
def baseRingMap (t : R) : BaseRing t →+* BaseRing (f t) :=
  Localization.awayLift
    ((algebraMap S[X] (BaseRing (f t))).comp (Polynomial.mapRingHom f))
    (branchProduct t) (by
      simpa [branchProduct_map] using
        (IsLocalization.Away.algebraMap_isUnit (branchProduct (f t)) :
          IsUnit (algebraMap S[X] (BaseRing (f t)) (branchProduct (f t)))))

/-- On polynomial coordinates, the localized map is exactly coefficient change. -/
theorem baseRingMap_algebraMap (t : R) (p : R[X]) :
    baseRingMap f t (algebraMap R[X] (BaseRing t) p) =
      algebraMap S[X] (BaseRing (f t)) (p.map f) := by
  unfold baseRingMap
  exact IsLocalization.Away.lift_eq (branchProduct t) _ p

/-- The actual Euler radicand commutes with coefficient change. -/
theorem radicand_map (N m : ℕ) (t : R) :
    baseRingMap f t (radicand N m t) = radicand N m (f t) := by
  rw [radicand, baseRingMap_algebraMap, branchPolynomial_map]
  rfl

/-- The defining monic polynomial commutes with the localized coefficient map. -/
theorem coverPolynomial_map (N m : ℕ) (t : R) :
    (coverPolynomial N m t).map (baseRingMap f t) = coverPolynomial N m (f t) := by
  simp [coverPolynomial, radicand_map]

/-- The actual covering algebra has a functorial coefficient-change map. -/
def coverRingMap (N m : ℕ) (t : R) :
    CoverRing N m t →+* CoverRing N m (f t) :=
  AdjoinRoot.map (baseRingMap f t) (coverPolynomial N m t)
    (coverPolynomial N m (f t)) (by rw [coverPolynomial_map])

/-- Coefficient change sends the actual covering coordinate to the new coordinate. -/
theorem coverRingMap_root (N m : ℕ) (t : R) :
    coverRingMap f N m t (coverRoot N m t) = coverRoot N m (f t) :=
  AdjoinRoot.map_root (baseRingMap f t) (coverPolynomial N m t)
    (coverPolynomial N m (f t)) _

/-- Coefficient change respects the map from branch-complement coordinates. -/
theorem coverRingMap_algebraMap (N m : ℕ) (t : R) (a : BaseRing t) :
    coverRingMap f N m t (algebraMap (BaseRing t) (CoverRing N m t) a) =
      algebraMap (BaseRing (f t)) (CoverRing N m (f t)) (baseRingMap f t a) := by
  simp [coverRingMap, AdjoinRoot.map]

/-- Coefficient change by the identity fixes the branch-complement ring. -/
theorem baseRingMap_id (t : R) :
    baseRingMap (RingHom.id R) t = RingHom.id (BaseRing t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
  apply RingHom.ext
  intro p
  change baseRingMap (RingHom.id R) t (algebraMap R[X] (BaseRing t) p) =
    algebraMap R[X] (BaseRing t) p
  rw [baseRingMap_algebraMap]
  simp

/-- Consecutive coefficient changes agree with change along the composite map. -/
theorem baseRingMap_comp {T : Type*} [CommRing T] (g : S →+* T) (t : R) :
    baseRingMap (g.comp f) t =
      (baseRingMap g (f t)).comp (baseRingMap f t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
  apply RingHom.ext
  intro p
  change baseRingMap (g.comp f) t (algebraMap R[X] (BaseRing t) p) =
    baseRingMap g (f t) (baseRingMap f t (algebraMap R[X] (BaseRing t) p))
  rw [baseRingMap_algebraMap, baseRingMap_algebraMap, baseRingMap_algebraMap]
  congr 1
  ext n
  simp

/-- Identity coefficient change fixes the actual covering algebra. -/
theorem coverRingMap_id (N m : ℕ) (t : R) :
    coverRingMap (RingHom.id R) N m t = RingHom.id (CoverRing N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change coverRingMap (RingHom.id R) N m t
        (algebraMap (BaseRing t) (CoverRing N m t) a) =
      algebraMap (BaseRing t) (CoverRing N m t) a
    rw [coverRingMap_algebraMap, baseRingMap_id]
    rfl
  · change coverRingMap (RingHom.id R) N m t (coverRoot N m t) = coverRoot N m t
    simpa using coverRingMap_root (RingHom.id R) N m t

/-- Two coefficient changes on the actual Euler algebra compose. -/
theorem coverRingMap_comp {T : Type*} [CommRing T] (g : S →+* T)
    (N m : ℕ) (t : R) :
    coverRingMap (g.comp f) N m t =
      (coverRingMap g N m (f t)).comp (coverRingMap f N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change coverRingMap (g.comp f) N m t
        (algebraMap (BaseRing t) (CoverRing N m t) a) =
      coverRingMap g N m (f t) (coverRingMap f N m t
        (algebraMap (BaseRing t) (CoverRing N m t) a))
    rw [coverRingMap_algebraMap, coverRingMap_algebraMap, coverRingMap_algebraMap,
      baseRingMap_comp]
    rfl
  · change coverRingMap (g.comp f) N m t (coverRoot N m t) =
      coverRingMap g N m (f t) (coverRingMap f N m t (coverRoot N m t))
    rw [coverRingMap_root, coverRingMap_root, coverRingMap_root]
    rfl

section AlgebraBaseChange

variable [Algebra R S]

/-- Coefficient change is an algebra map over the original coefficient ring. -/
def coverRingMapAlgHom (N m : ℕ) (t : R) :
    CoverRing N m t →ₐ[R] CoverRing N m (algebraMap R S t) where
  toRingHom := coverRingMap (algebraMap R S) N m t
  commutes' r := by
    change coverRingMap (algebraMap R S) N m t
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap R[X] (BaseRing t) (C r))) =
      algebraMap (BaseRing (algebraMap R S t))
        (CoverRing N m (algebraMap R S t))
        (algebraMap S[X] (BaseRing (algebraMap R S t)) (C (algebraMap R S r)))
    rw [coverRingMap_algebraMap, baseRingMap_algebraMap, map_C]

/-- The canonical map from the scalar-extended old cover to the new cover. -/
def coverTensorMap (N m : ℕ) (t : R) :
    (S ⊗[R] (CoverRing N m t)) →ₐ[S] CoverRing N m (algebraMap R S t) :=
  Algebra.TensorProduct.lift (Algebra.ofId S (CoverRing N m (algebraMap R S t)))
    (coverRingMapAlgHom (R := R) (S := S) N m t)
    (fun _ _ => Commute.all _ _)

/-- Polynomial coordinates of the scalar-extended cover. -/
def tensorPolynomialMap (N m : ℕ) (t : R) :
    S[X] →+* (S ⊗[R] (CoverRing N m t)) :=
  Polynomial.eval₂RingHom (algebraMap S (S ⊗[R] (CoverRing N m t)))
    ((Algebra.TensorProduct.includeRight :
      CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
      (algebraMap R[X] (CoverRing N m t) X))

/-- Polynomial coordinates agree with the old coordinates after scalar extension. -/
theorem tensorPolynomialMap_map (N m : ℕ) (t : R) (p : R[X]) :
    tensorPolynomialMap (R := R) (S := S) N m t (p.map (algebraMap R S)) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
        (algebraMap R[X] (CoverRing N m t) p) := by
  have h : (tensorPolynomialMap (R := R) (S := S) N m t).comp
        (Polynomial.mapRingHom (algebraMap R S)) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)).toRingHom.comp
        (algebraMap R[X] (CoverRing N m t)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [tensorPolynomialMap, Polynomial.eval₂RingHom, Algebra.TensorProduct.includeRight_apply]
      rw [show (algebraMap R[X] (CoverRing N m t)) (C a) =
        algebraMap R (CoverRing N m t) a from
        IsScalarTower.algebraMap_apply R R[X] (CoverRing N m t) a]
      simpa only [Algebra.smul_def, mul_one] using
        (TensorProduct.smul_tmul (R := R) a (1 : S) (1 : CoverRing N m t))
    · simp [tensorPolynomialMap, Polynomial.eval₂RingHom]
  exact congrArg (fun k : R[X] →+* S ⊗[R] (CoverRing N m t) => k p) h

/-- The old branch product is invertible in the scalar-extended cover. -/
theorem isUnit_tensorBranchProduct (N m : ℕ) (t : R) :
    IsUnit (tensorPolynomialMap (R := R) (S := S) N m t
      (branchProduct (algebraMap R S t))) := by
  rw [← branchProduct_map, tensorPolynomialMap_map]
  have hu : IsUnit (algebraMap R[X] (CoverRing N m t) (branchProduct t)) := by
    have h := (IsLocalization.Away.algebraMap_isUnit (branchProduct t) :
      IsUnit (algebraMap R[X] (BaseRing t) (branchProduct t)))
    simpa [IsScalarTower.algebraMap_apply R[X] (BaseRing t) (CoverRing N m t)] using
      h.map (algebraMap (BaseRing t) (CoverRing N m t))
  exact hu.map (Algebra.TensorProduct.includeRight :
    CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)).toRingHom

/-- Map the new localized base coordinates into the scalar-extended old cover. -/
def tensorBaseRingMap (N m : ℕ) (t : R) :
    BaseRing (algebraMap R S t) →+* (S ⊗[R] (CoverRing N m t)) :=
  Localization.awayLift (tensorPolynomialMap (R := R) (S := S) N m t)
    (branchProduct (algebraMap R S t))
    (isUnit_tensorBranchProduct (R := R) (S := S) N m t)

/-- The localized tensor map has its prescribed values on polynomial coordinates. -/
theorem tensorBaseRingMap_algebraMap (N m : ℕ) (t : R) (p : S[X]) :
    tensorBaseRingMap (R := R) (S := S) N m t
      (algebraMap S[X] (BaseRing (algebraMap R S t)) p) =
      tensorPolynomialMap (R := R) (S := S) N m t p := by
  unfold tensorBaseRingMap
  exact IsLocalization.Away.lift_eq (branchProduct (algebraMap R S t)) _ p

/-- The localized tensor map undoes coefficient change on the old base ring. -/
theorem tensorBaseRingMap_baseRingMap (N m : ℕ) (t : R) (a : BaseRing t) :
    tensorBaseRingMap (R := R) (S := S) N m t (baseRingMap (algebraMap R S) t a) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
        (algebraMap (BaseRing t) (CoverRing N m t) a) := by
  have h : (tensorBaseRingMap (R := R) (S := S) N m t).comp
        (baseRingMap (algebraMap R S) t) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)).toRingHom.comp
        (algebraMap (BaseRing t) (CoverRing N m t)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
    apply RingHom.ext
    intro p
    change tensorBaseRingMap (R := R) (S := S) N m t
        (baseRingMap (algebraMap R S) t (algebraMap R[X] (BaseRing t) p)) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
        (algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap R[X] (BaseRing t) p))
    rw [baseRingMap_algebraMap, tensorBaseRingMap_algebraMap,
      tensorPolynomialMap_map]
    congr 1
  exact congrArg (fun k : BaseRing t →+* S ⊗[R] (CoverRing N m t) => k a) h

/-- The localized tensor map respects the new coefficient algebra. -/
def tensorBaseRingAlgHom (N m : ℕ) (t : R) :
    BaseRing (algebraMap R S t) →ₐ[S] S ⊗[R] (CoverRing N m t) where
  toRingHom := tensorBaseRingMap (R := R) (S := S) N m t
  commutes' s := by
    change tensorBaseRingMap (R := R) (S := S) N m t
      (algebraMap S[X] (BaseRing (algebraMap R S t)) (C s)) =
        algebraMap S (S ⊗[R] (CoverRing N m t)) s
    rw [tensorBaseRingMap_algebraMap]
    simp [tensorPolynomialMap, Polynomial.eval₂RingHom]

/-- The old root satisfies the base-changed equation in the tensor algebra. -/
theorem tensorCoverRoot_pow (N m : ℕ) (t : R) :
    ((Algebra.TensorProduct.includeRight :
      CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
      (coverRoot N m t)) ^ N =
      tensorBaseRingMap (R := R) (S := S) N m t
        (radicand N m (algebraMap R S t)) := by
  rw [← radicand_map (algebraMap R S) N m t,
    tensorBaseRingMap_baseRingMap, ← map_pow, coverRoot_pow]

/-- The universal root algebra map from the new cover back to the tensor algebra. -/
def coverTensorInverse (N m : ℕ) (t : R) :
    CoverRing N m (algebraMap R S t) →ₐ[S] S ⊗[R] (CoverRing N m t) :=
  AdjoinRoot.liftAlgHom (coverPolynomial N m (algebraMap R S t))
    (tensorBaseRingAlgHom (R := R) (S := S) N m t)
    ((Algebra.TensorProduct.includeRight :
      CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) (coverRoot N m t))
    (by
      simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      exact sub_eq_zero.mpr (tensorCoverRoot_pow (R := R) (S := S) N m t))

/-- The tensor map evaluates a pure tensor by coefficient change. -/
theorem coverTensorMap_tmul (N m : ℕ) (t : R)
    (s : S) (a : CoverRing N m t) :
    coverTensorMap (R := R) (S := S) N m t (s ⊗ₜ[R] a) =
      algebraMap S (CoverRing N m (algebraMap R S t)) s *
        coverRingMap (algebraMap R S) N m t a := by
  simp [coverTensorMap, Algebra.TensorProduct.lift_tmul, coverRingMapAlgHom]

/-- The tensor inverse sends the new covering coordinate to the old root. -/
theorem coverTensorInverse_root (N m : ℕ) (t : R) :
    coverTensorInverse (R := R) (S := S) N m t
      (coverRoot N m (algebraMap R S t)) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) (coverRoot N m t) := by
  simp [coverTensorInverse, coverRoot, AdjoinRoot.liftAlgHom_root]

/-- The tensor inverse restricts to the prescribed localized base map. -/
theorem coverTensorInverse_algebraMap (N m : ℕ) (t : R)
    (a : BaseRing (algebraMap R S t)) :
    coverTensorInverse (R := R) (S := S) N m t
      (algebraMap (BaseRing (algebraMap R S t))
        (CoverRing N m (algebraMap R S t)) a) =
      tensorBaseRingMap (R := R) (S := S) N m t a := by
  simp [coverTensorInverse, AdjoinRoot.liftAlgHom, tensorBaseRingAlgHom]

/-- Pulling the coefficient-changed old cover back along the tensor inverse recovers it. -/
theorem coverTensorInverse_coverRingMap (N m : ℕ) (t : R)
    (a : CoverRing N m t) :
    coverTensorInverse (R := R) (S := S) N m t
      (coverRingMap (algebraMap R S) N m t a) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) a := by
  have h : (coverTensorInverse (R := R) (S := S) N m t).toRingHom.comp
        (coverRingMap (algebraMap R S) N m t) =
      (Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro b
      change coverTensorInverse (R := R) (S := S) N m t
          (coverRingMap (algebraMap R S) N m t
            (algebraMap (BaseRing t) (CoverRing N m t) b)) =
        (Algebra.TensorProduct.includeRight :
          CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
          (algebraMap (BaseRing t) (CoverRing N m t) b)
      rw [coverRingMap_algebraMap, coverTensorInverse_algebraMap,
        tensorBaseRingMap_baseRingMap]
    · change coverTensorInverse (R := R) (S := S) N m t
          (coverRingMap (algebraMap R S) N m t (coverRoot N m t)) =
        (Algebra.TensorProduct.includeRight :
          CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) (coverRoot N m t)
      rw [coverRingMap_root, coverTensorInverse_root]
  exact congrArg (fun k : CoverRing N m t →+* S ⊗[R] (CoverRing N m t) => k a) h

/-- The tensor inverse is a left inverse of the canonical base-change map. -/
theorem coverTensorInverse_comp_coverTensorMap (N m : ℕ) (t : R) :
    (coverTensorInverse (R := R) (S := S) N m t).comp
        (coverTensorMap (R := R) (S := S) N m t) =
      AlgHom.id S (S ⊗[R] (CoverRing N m t)) := by
  apply Algebra.TensorProduct.ext'
  intro s a
  simp [coverTensorMap_tmul, coverTensorInverse_coverRingMap,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- The tensor map agrees with coefficient change on the old cover. -/
theorem coverTensorMap_includeRight (N m : ℕ) (t : R)
    (a : CoverRing N m t) :
    coverTensorMap (R := R) (S := S) N m t
      ((Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) a) =
      coverRingMap (algebraMap R S) N m t a := by
  simp [Algebra.TensorProduct.includeRight_apply, coverTensorMap_tmul]

/-- The tensor map returns the new polynomial coordinates exactly. -/
theorem coverTensorMap_tensorPolynomialMap (N m : ℕ) (t : R) (p : S[X]) :
    coverTensorMap (R := R) (S := S) N m t
      (tensorPolynomialMap (R := R) (S := S) N m t p) =
      algebraMap S[X] (CoverRing N m (algebraMap R S t)) p := by
  have h : (coverTensorMap (R := R) (S := S) N m t).toRingHom.comp
        (tensorPolynomialMap (R := R) (S := S) N m t) =
      algebraMap S[X] (CoverRing N m (algebraMap R S t)) := by
    apply Polynomial.ringHom_ext
    · intro s
      simp [tensorPolynomialMap, Polynomial.eval₂RingHom]
      simpa [IsScalarTower.algebraMap_apply S S[X]
        (CoverRing N m (algebraMap R S t))] using
        (coverTensorMap_tmul (R := R) (S := S) N m t s (1 : CoverRing N m t))
    · simp [tensorPolynomialMap, Polynomial.eval₂RingHom]
      change coverTensorMap (R := R) (S := S) N m t
          ((Algebra.TensorProduct.includeRight :
            CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
            (algebraMap R[X] (CoverRing N m t) X)) =
        algebraMap S[X] (CoverRing N m (algebraMap R S t)) X
      rw [coverTensorMap_includeRight]
      calc
        coverRingMap (algebraMap R S) N m t
            (algebraMap R[X] (CoverRing N m t) X) =
          coverRingMap (algebraMap R S) N m t
            (algebraMap (BaseRing t) (CoverRing N m t)
              (algebraMap R[X] (BaseRing t) X)) := by
                rw [IsScalarTower.algebraMap_apply R[X] (BaseRing t) (CoverRing N m t)]
        _ = algebraMap (BaseRing (algebraMap R S t))
            (CoverRing N m (algebraMap R S t))
            (algebraMap S[X] (BaseRing (algebraMap R S t)) X) := by
                rw [coverRingMap_algebraMap, baseRingMap_algebraMap, map_X]
        _ = algebraMap S[X] (CoverRing N m (algebraMap R S t)) X := by
                rw [IsScalarTower.algebraMap_apply S[X]
                  (BaseRing (algebraMap R S t)) (CoverRing N m (algebraMap R S t))]
  exact congrArg (fun k : S[X] →+* CoverRing N m (algebraMap R S t) => k p) h

/-- The tensor map undoes the localization map on every new base coordinate. -/
theorem coverTensorMap_tensorBaseRingMap (N m : ℕ) (t : R)
    (a : BaseRing (algebraMap R S t)) :
    coverTensorMap (R := R) (S := S) N m t
      (tensorBaseRingMap (R := R) (S := S) N m t a) =
      algebraMap (BaseRing (algebraMap R S t))
        (CoverRing N m (algebraMap R S t)) a := by
  have h : (coverTensorMap (R := R) (S := S) N m t).toRingHom.comp
        (tensorBaseRingMap (R := R) (S := S) N m t) =
      algebraMap (BaseRing (algebraMap R S t))
        (CoverRing N m (algebraMap R S t)) := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (branchProduct (algebraMap R S t)))
    apply RingHom.ext
    intro p
    change coverTensorMap (R := R) (S := S) N m t
        (tensorBaseRingMap (R := R) (S := S) N m t
          (algebraMap S[X] (BaseRing (algebraMap R S t)) p)) =
      algebraMap (BaseRing (algebraMap R S t))
        (CoverRing N m (algebraMap R S t))
        (algebraMap S[X] (BaseRing (algebraMap R S t)) p)
    rw [tensorBaseRingMap_algebraMap, coverTensorMap_tensorPolynomialMap]
    rfl
  exact congrArg (fun k : BaseRing (algebraMap R S t) →+*
      CoverRing N m (algebraMap R S t) => k a) h

/-- The canonical base-change map is also a left inverse of its tensor inverse. -/
theorem coverTensorMap_comp_coverTensorInverse (N m : ℕ) (t : R) :
    (coverTensorMap (R := R) (S := S) N m t).comp
        (coverTensorInverse (R := R) (S := S) N m t) =
      AlgHom.id S (CoverRing N m (algebraMap R S t)) := by
  have h : ((coverTensorMap (R := R) (S := S) N m t).comp
        (coverTensorInverse (R := R) (S := S) N m t)).toRingHom =
      (AlgHom.id S (CoverRing N m (algebraMap R S t))).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change coverTensorMap (R := R) (S := S) N m t
          (coverTensorInverse (R := R) (S := S) N m t
            (algebraMap (BaseRing (algebraMap R S t))
              (CoverRing N m (algebraMap R S t)) a)) =
        algebraMap (BaseRing (algebraMap R S t))
          (CoverRing N m (algebraMap R S t)) a
      rw [coverTensorInverse_algebraMap, coverTensorMap_tensorBaseRingMap]
    · change coverTensorMap (R := R) (S := S) N m t
          (coverTensorInverse (R := R) (S := S) N m t
            (coverRoot N m (algebraMap R S t))) =
        coverRoot N m (algebraMap R S t)
      rw [coverTensorInverse_root, coverTensorMap_includeRight, coverRingMap_root]
  apply AlgHom.ext
  intro a
  exact congrArg (fun k : CoverRing N m (algebraMap R S t) →+*
    CoverRing N m (algebraMap R S t) => k a) h

/-- The scalar extension of the actual affine Euler algebra is the Euler algebra
over the new coefficient ring. This equivalence preserves both localized base
coordinates and the adjoined covering coordinate. -/
def coverBaseChangeEquiv (N m : ℕ) (t : R) :
    (S ⊗[R] (CoverRing N m t)) ≃ₐ[S]
      CoverRing N m (algebraMap R S t) :=
  AlgEquiv.ofAlgHom (coverTensorMap (R := R) (S := S) N m t)
    (coverTensorInverse (R := R) (S := S) N m t)
    (coverTensorMap_comp_coverTensorInverse (R := R) (S := S) N m t)
    (coverTensorInverse_comp_coverTensorMap (R := R) (S := S) N m t)

/-- The base-change equivalence sends the old covering coordinate to the new one. -/
theorem coverBaseChangeEquiv_root (N m : ℕ) (t : R) :
    coverBaseChangeEquiv (R := R) (S := S) N m t
      ((Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) (coverRoot N m t)) =
      coverRoot N m (algebraMap R S t) := by
  change coverTensorMap (R := R) (S := S) N m t
      ((Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t)) (coverRoot N m t)) =
    coverRoot N m (algebraMap R S t)
  rw [coverTensorMap_includeRight, coverRingMap_root]

/-- The base-change equivalence preserves the actual branch-complement inclusion. -/
theorem coverBaseChangeEquiv_baseRing (N m : ℕ) (t : R) (a : BaseRing t) :
    coverBaseChangeEquiv (R := R) (S := S) N m t
      ((Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
        (algebraMap (BaseRing t) (CoverRing N m t) a)) =
      algebraMap (BaseRing (algebraMap R S t))
        (CoverRing N m (algebraMap R S t))
        (baseRingMap (algebraMap R S) t a) := by
  change coverTensorMap (R := R) (S := S) N m t
      ((Algebra.TensorProduct.includeRight :
        CoverRing N m t →ₐ[R] S ⊗[R] (CoverRing N m t))
        (algebraMap (BaseRing t) (CoverRing N m t) a)) = _
  rw [coverTensorMap_includeRight, coverRingMap_algebraMap]

end AlgebraBaseChange

/-- Coefficient change preserves the original coefficient structural map. -/
theorem coverRingMap_coeff (N m : ℕ) (t : R) (r : R) :
    coverRingMap f N m t
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap R[X] (BaseRing t) (C r))) =
      algebraMap (BaseRing (f t)) (CoverRing N m (f t))
        (algebraMap S[X] (BaseRing (f t)) (C (f r))) := by
  rw [coverRingMap_algebraMap, baseRingMap_algebraMap, map_C]

section SchemeBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)

/-- The coefficient map induces the corresponding map between actual affine Euler schemes. -/
def affineSchemeBaseChange (N m : ℕ) (t : A) :
    affineScheme N m (g t) ⟶ affineScheme N m t :=
  Spec.map (CommRingCat.ofHom (coverRingMap g N m t))

/-- Base change respects the original coefficient-parameter structural morphism. -/
theorem affineSchemeBaseChange_structureMap (N m : ℕ) (t : A) :
    affineSchemeBaseChange g N m t ≫ structureMap N m t =
      structureMap N m (g t) ≫ Spec.map (CommRingCat.ofHom g) := by
  rw [affineSchemeBaseChange, structureMap, structureMap]
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact coverRingMap_coeff g N m t r

end SchemeBaseChange

/-- Under coefficient change, scaling by a root of unity commutes with the
actual deck action on the Euler algebra. -/
theorem coverRingMap_deck (N : ℕ) [NeZero N] (m : ℕ) (t : R)
    (ζ : rootsOfUnity N R) :
    (coverRingMap f N m t).comp (deckAlgebraAction N m t ζ).toRingHom =
      (deckAlgebraAction N m (f t) (rootsOfUnity.mapHom N f ζ)).toRingHom.comp
        (coverRingMap f N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change coverRingMap f N m t
        ((deckAlgebraAction N m t ζ)
          (algebraMap (BaseRing t) (CoverRing N m t) a)) =
      (deckAlgebraAction N m (f t) (rootsOfUnity.mapHom N f ζ))
        (coverRingMap f N m t
          (algebraMap (BaseRing t) (CoverRing N m t) a))
    rw [(deckAlgebraAction N m t ζ).commutes,
      coverRingMap_algebraMap, (deckAlgebraAction N m (f t)
        (rootsOfUnity.mapHom N f ζ)).commutes]
  · change coverRingMap f N m t
        ((deckAlgebraAction N m t ζ) (coverRoot N m t)) =
      (deckAlgebraAction N m (f t) (rootsOfUnity.mapHom N f ζ))
        (coverRingMap f N m t (coverRoot N m t))
    rw [deckAlgebraAction_root, coverRingMap_root, deckAlgebraAction_root]
    simp only [Algebra.smul_def, map_mul, coverRingMap_algebraMap,
      baseRingMap_algebraMap, map_C]
    rw [coverRingMap_root]
    rfl

end HilbertModularity.Hypergeometric.EulerCover
