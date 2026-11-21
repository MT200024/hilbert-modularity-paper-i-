/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeGenericRank
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricRanks
public import HilbertModularity.Geometry.TateModule.RelativeRealMultiplicationPairing
public import HilbertModularity.Geometry.GroupScheme.HypergeometricRanks
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientTensor
public import HilbertModularity.NumberTheory.RealCyclotomicNormal
public import HilbertModularity.RepresentationTheory.ScalarConjugationInvariants

/-! # Cyclotomic determinant on every selected plus fibre

Rank transports along a geometric path from the generic inertia realization.
The relative polarized pairing retains the original integral RM action and
the same coefficient label. Their rank-two determinant consequence applies
to every characteristic-zero field-valued nonsingular fibre.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

universe u

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

section Algebraic

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ a : realCyclotomicField p,
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)
  (K : Type) [Field K] [CharZero K]
  (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p))

/-- The fixed-labelled native Tate factor of the actual selected plus fibre. -/
@[expose] def primePlusFiberTateFactor :=
  endomorphismLabelledTate K (fiber K (primePlusFamily p hp) x)
    ℓ (realCyclotomicField p) L hL
    ((fiberEndomorphismMap K (primePlusFamily p hp) x).comp
      (primePlusRealMultiplication p hp)) σ

attribute [irreducible] primePlusFiberTateFactor

/-- Generic rank two persists at every nonsingular fibre with the same label. -/
theorem finrank_primePlusFiberTateFactor :
    Module.finrank L (primePlusFiberTateFactor p hp ℓ L hL σ K x).toSubmodule = 2 := by
  let e := Scheme.finiteArithmeticFiberIso (RatFunc (realCyclotomicField p)) K
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p)) x
  have hr := HasStandardInertiaRealization.finrank_labelledTateLocalSystem
    p (primePlusFamily p hp) (primePlusRealMultiplication p hp)
    (primePlusData p hp).multiplication_finite
    (primePlusData p hp).multiplication_etale
    (primePlusData_hasStandardInertiaRealization p hp) ℓ L hL σ
  have hx := (labelledTateGeometricPathIso (RatFunc (realCyclotomicField p)) K e
    (primePlusFamily p hp) ℓ L (realCyclotomicField p)
    (primePlusRealMultiplication p hp) hL σ).toLinearEquiv.finrank_eq.symm.trans hr
  unfold primePlusFiberTateFactor
  exact (finrank_endomorphismLabelledTate_fiber K (primePlusFamily p hp) ℓ L x
    (realCyclotomicField p) (primePlusRealMultiplication p hp) hL σ).trans hx

end Algebraic

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ a : realCyclotomicField p,
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)
  (K : Type) [Field K] [CharZero K]
  (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p))

/-- The relative Weil pairing on the actual selected fibre; specialized
endomorphism rings may be larger than the specified real multiplication. -/
theorem primePlusFiberTateFactor_hasPairing :
    ∃ B : (primePlusFiberTateFactor p hp ℓ L hL σ K x).toSubmodule →ₗ[L]
        Module.Dual L (primePlusFiberTateFactor p hp ℓ L hL σ K x).toSubmodule,
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      ∀ g v w,
        B ((primePlusFiberTateFactor p hp ℓ L hL σ K x).toRepresentation g v)
          ((primePlusFiberTateFactor p hp ℓ L hL σ K x).toRepresentation g w) =
        (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L) * B v w := by
  let : Smooth (primePlusFamily p hp).X.hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℚ (realCyclotomicField p)) _
  unfold primePlusFiberTateFactor
  exact exists_fiberLabelledTatePairing_of_generic_full_realMultiplication
    (realCyclotomicField p) (primePlusFamily p hp) ℓ (realCyclotomicField p) L hL
    (primePlusRealMultiplication p hp) inferInstance
    (primePlusGenericRMAction_bijective p hp) K x σ

/-- Exact cyclotomic determinant of every fixed-labelled selected plus fibre.
The rank and pairing are established above; no determinant is admitted. -/
theorem primePlusFiberTateFactor_det
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (LinearMap.det (A := L)
      (M := (primePlusFiberTateFactor p hp ℓ L hL σ K x).toSubmodule))
      ((primePlusFiberTateFactor p hp ℓ L hL σ K x).toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L) := by
  have h := primePlusFiberTateFactor_hasPairing p hp ℓ L hL σ K x
  with_reducible
    exact HilbertModularity.linearMap_det_eq_of_exists_alternating_similitude
      (K := L) (V := (primePlusFiberTateFactor p hp ℓ L hL σ K x).toSubmodule)
      (finrank_primePlusFiberTateFactor p hp ℓ L hL σ K x)
      (fun g => (primePlusFiberTateFactor p hp ℓ L hL σ K x).toRepresentation g)
      (fun g => (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L)) h g

/-- Relabel the selected fibre determinant across an equality of its RM fields.
Keeping the source field variable makes the equality elimination independent of
the implementation of the real cyclotomic intermediate field. -/
private theorem primePlusFiberTateFactor_det_of_field_eq
    (F : IntermediateField ℚ Qbar) [NumberField F]
    (hF : F = realCyclotomicField p)
    (hFsplit : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* End (primePlusFamily p hp))
    (hφ : Eq.mp
      (congrArg (fun F' : IntermediateField ℚ Qbar =>
        𝓞 F' →+* End (primePlusFamily p hp)) hF) φ =
      primePlusRealMultiplication p hp)
    (τ : F →ₐ[ℚ] L)
    [Module.Finite L (endomorphismLabelledTate K
      (fiber K (primePlusFamily p hp) x) ℓ F L hFsplit
      ((fiberEndomorphismMap K (primePlusFamily p hp) x).comp φ) τ).toSubmodule]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det (A := L)
      (M := (endomorphismLabelledTate K
        (fiber K (primePlusFamily p hp) x) ℓ F L hFsplit
        ((fiberEndomorphismMap K (primePlusFamily p hp) x).comp φ) τ).toSubmodule)
      ((endomorphismLabelledTate K
      (fiber K (primePlusFamily p hp) x) ℓ F L hFsplit
      ((fiberEndomorphismMap K (primePlusFamily p hp) x).comp φ) τ).toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L) := by
  cases hF
  cases hφ
  have h := primePlusFiberTateFactor_det p hp ℓ L hFsplit τ K x g
  unfold primePlusFiberTateFactor at h
  exact h

/-- Determinants descend along an injective extension of coefficient fields. -/
private theorem det_eq_of_baseChange
    {E L V : Type*} [Field E] [Field L] [Algebra E L]
    [AddCommGroup V] [Module E V] [Module.Finite E V] [Module.Free E V]
    (f : V →ₗ[E] V) (d : E)
    (h : LinearMap.det (f.baseChange L) = algebraMap E L d) :
    LinearMap.det f = d := by
  apply (algebraMap E L).injective
  exact (LinearMap.det_baseChange f).symm.trans h

/-- Bundling the completed Tate action does not alter its Galois map. -/
private theorem localCoefficientTateRep_action_generic
    {K' : Type u} [Field K'] {S : Scheme.{u}} (A : CommGrp (Over S))
    (x : Spec (CommRingCat.of K') ⟶ S) (k : ℕ)
    (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)
    (g : AlgebraicClosure K' ≃ₐ[K'] AlgebraicClosure K') :
    (localCoefficientTateRep K' A x p k φ).ρ g =
      localCoefficientTateRepresentation K' A x p k φ g := by
  apply LinearMap.ext
  intro v
  exact (localCoefficientTateRep_apply K' A x p k φ g v).trans
    (localCoefficientTateRepresentation_apply K' A x p k φ g v).symm

/-- The exact determinant on the native completed RM factor of the selected plus Jacobian. -/
theorem primePlusLocalTateRepresentation_det
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    LinearMap.det ((primePlusLocalTateRepresentation p hp ξ).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]) := by
  let E := RealPrimePowerCompletion p 0
  let L := PadicAlgCl p
  let τ : E →ₐ[ℚ_[p]] L := realPrimePowerCompletionEmbedding p 0
  let hsplit : ∀ a : realCyclotomicField (p ^ (0 + 1)),
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits :=
    fun _ => IsAlgClosed.splits _
  let x := ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ
  have hselected : primePlusLocalTateRepresentation p hp ξ =
      localCoefficientTateRep (realCyclotomicField p) (primePlusFamily p hp) x p 0
        (primePlusPrimePowerRealMultiplication p hp) := by
    rfl
  let : Module E (rationalTate (realCyclotomicField p)
      (fiber (realCyclotomicField p) (primePlusFamily p hp) x).X p) :=
    Module.compHom _ (localCoefficientTateAction (realCyclotomicField p)
      (primePlusFamily p hp) x p 0
      (primePlusPrimePowerRealMultiplication p hp)).toRingHom
  let : IsScalarTower ℚ_[p] E
      (rationalTate (realCyclotomicField p)
        (fiber (realCyclotomicField p) (primePlusFamily p hp) x).X p) :=
    localCoefficientTateRepScalarTower (realCyclotomicField p)
      (primePlusFamily p hp) x p 0 (primePlusPrimePowerRealMultiplication p hp)
  let : Algebra E L := τ.toAlgebra
  have e := localCoefficientLabelledTateRepresentationEquiv p 0 L τ
    (realCyclotomicField p) (primePlusFamily p hp) x
    (primePlusPrimePowerRealMultiplication p hp)
    hsplit
  let : Module.Finite E
      (rationalTate (realCyclotomicField p)
        (fiber (realCyclotomicField p) (primePlusFamily p hp) x).X p) :=
    Module.finite_of_finrank_eq_succ
      (show Module.finrank E
        (localCoefficientTateRep (realCyclotomicField p)
          (primePlusFamily p hp) x p 0
          (primePlusPrimePowerRealMultiplication p hp)) = 1 + 1 by
        simpa using finrank_primePlusLocalTateRep_at p hp
          (realCyclotomicField p) x)
  let W := rationalTate (realCyclotomicField p)
    (fiber (realCyclotomicField p) (primePlusFamily p hp) x).X p
  let T := labelledTateSubrepresentation (realCyclotomicField p)
    (fiber (realCyclotomicField p) (primePlusFamily p hp) x).X p
    (realCyclotomicField (p ^ (0 + 1))) L
    hsplit
    (fiberPointsAction (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) (primePlusFamily p hp) x _
      (primePlusPrimePowerRealMultiplication p hp))
    (fiberPointsAction_realized (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) (primePlusFamily p hp) x _
      (primePlusPrimePowerRealMultiplication p hp))
    (localTateCoefficientLabel p 0 L τ)
  let f : (L ⊗[E] W) →ₗ[L] T.toSubmodule := e.toLinearEquiv.toLinearMap
  have hsurj : Function.Surjective f := e.toLinearEquiv.surjective
  let : FiniteDimensional L T.toSubmodule :=
    FiniteDimensional.of_surjective f hsurj
  let : Module.Finite L (endomorphismLabelledTate (realCyclotomicField p)
      (fiber (realCyclotomicField p) (primePlusFamily p hp) x) p
      (realCyclotomicField (p ^ (0 + 1))) L hsplit
      ((fiberEndomorphismMap (realCyclotomicField p)
        (primePlusFamily p hp) x).comp
        (primePlusPrimePowerRealMultiplication p hp))
      (localTateCoefficientLabel p 0 L τ)).toSubmodule := by
    unfold endomorphismLabelledTate
    change Module.Finite L T.toSubmodule
    infer_instance
  have hdet : LinearMap.det (A := L) (M := T.toSubmodule)
      (T.toRepresentation g) =
      LinearMap.det (A := L) (M := L ⊗[E] W)
        (((localCoefficientTateRepresentation
        (realCyclotomicField p) (primePlusFamily p hp) x p 0
        (primePlusPrimePowerRealMultiplication p hp)).baseChange L) g) :=
    e.det_eq g
  have hT : LinearMap.det (A := L) (M := T.toSubmodule)
      (T.toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients
        (realCyclotomicField p) p L g : L) := by
    have h := primePlusFiberTateFactor_det_of_field_eq p hp p L
        (realCyclotomicField p) x
        (realCyclotomicField (p ^ (0 + 1)))
        (primePlusPrimePowerField_eq p) hsplit
        (primePlusPrimePowerRealMultiplication p hp)
        (primePlusPrimePowerRealMultiplication_eq p hp)
        (localTateCoefficientLabel p 0 L τ) g
    unfold endomorphismLabelledTate at h
    exact h
  have hbase : LinearMap.det
      (((localCoefficientTateRep (realCyclotomicField p) (primePlusFamily p hp) x p 0
        (primePlusPrimePowerRealMultiplication p hp)).ρ g).baseChange L) =
      algebraMap E L (algebraMap ℚ_[p] E
        ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p])) := by
    rw [localCoefficientTateRep_action_generic]
    calc
      _ = (Field.cyclotomicCharacterWithCoefficients
          (realCyclotomicField p) p L g : L) := hdet.symm.trans hT
      _ = algebraMap E L (algebraMap ℚ_[p] E
          ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p])) := by
        simp only [Field.cyclotomicCharacterWithCoefficients_coe]
        exact IsScalarTower.algebraMap_apply ℚ_[p] E L _
  have hbase' : LinearMap.det (((primePlusLocalTateRepresentation p hp ξ).ρ g).baseChange L) =
      algebraMap E L (algebraMap ℚ_[p] E
        ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p])) := by
    rw [hselected]
    exact hbase
  exact det_eq_of_baseChange
    ((primePlusLocalTateRepresentation p hp ξ).ρ g)
    (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
      ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]))
    hbase'

end HilbertModularity.Hypergeometric
