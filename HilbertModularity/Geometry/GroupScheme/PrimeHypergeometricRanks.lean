/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficients
public import HilbertModularity.NumberTheory.CyclotomicCompletion
public import HilbertModularity.NumberTheory.CyclotomicLocalGalois

/-! # Tate rank of the explicit prime plus family

The dimension of the covariant Tate module is part of the chosen plus-family
existence package, sourced to [DarmonFibres, Section 3, Example 3 and
Propositions 3.2 and 3.4]. This theorem exposes it for the same selected
family and every nonsingular arithmetic fibre.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- The rational Tate module of every plus-family fibre has twice the RM degree. -/
theorem finrank_primePlusRationalTate_at (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p)) :
    Module.finrank ℚ_[p]
      (rationalTate K (fiber K (primePlusFamily p hp) x).X p) =
        Module.finrank ℚ (realCyclotomicField p) * 2 := by
  let D := primePlusData p hp
  let : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
    fun n => D.multiplication_finite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
  let : ∀ n : ℕ, Etale (p ^ n • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
    fun n => D.multiplication_etale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
  exact D.rationalTateRank K x

/-- The exponent-zero prime-power field is the selected prime coefficient field. -/
theorem primePlusPrimePowerField_eq :
    realCyclotomicField (p ^ (0 + 1)) = realCyclotomicField p := by
  have hz : zeta (p ^ (0 + 1)) = zeta p := by
    congr 1
    simp
  unfold realCyclotomicField
  rw [hz]

/-- The prime conductor RM action in the prime-power coefficient API. -/
def primePlusPrimePowerRealMultiplication :
    𝓞 (realCyclotomicField (p ^ (0 + 1))) →+* End (primePlusFamily p hp) :=
  Eq.mpr
    (congrArg (fun F : IntermediateField ℚ Qbar =>
      𝓞 F →+* End (primePlusFamily p hp)) (primePlusPrimePowerField_eq p))
    (primePlusRealMultiplication p hp)

/-- The prime-power coefficient API uses the selected plus family's original
real multiplication at exponent zero. -/
theorem primePlusPrimePowerRealMultiplication_eq :
    Eq.mp
      (congrArg (fun F : IntermediateField ℚ Qbar =>
        𝓞 F →+* End (primePlusFamily p hp))
        (primePlusPrimePowerField_eq p))
      (primePlusPrimePowerRealMultiplication p hp) =
        primePlusRealMultiplication p hp := by
  let h := congrArg (fun F : IntermediateField ℚ Qbar =>
    𝓞 F →+* End (primePlusFamily p hp)) (primePlusPrimePowerField_eq p)
  change Eq.mp h (Eq.mpr h (primePlusRealMultiplication p hp)) = _
  have hcancel {A B : Type} (h' : A = B) (b : B) :
      Eq.mp h' (Eq.mpr h' b) = b := by
    cases h'
    rfl
  exact hcancel h _

/-- The completed RM action on the selected plus family's actual Tate module
has rank two. This uses the rational Tate dimension of the same selected
family and the single local factor of its real cyclotomic coefficient field. -/
theorem finrank_primePlusLocalTateRep_at (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p)) :
    Module.finrank (RealPrimePowerCompletion p 0)
      (localCoefficientTateRep K (primePlusFamily p hp) x p 0
        (primePlusPrimePowerRealMultiplication p hp)) = 2 := by
  let V := localCoefficientTateRep K (primePlusFamily p hp) x p 0
    (primePlusPrimePowerRealMultiplication p hp)
  let : Module ℚ_[p] V := localCoefficientTateRepRationalModule K _ x p 0 _
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0) V :=
    localCoefficientTateRepScalarTower K _ x p 0 _
  have hR : Module.finrank ℚ_[p] V =
      Module.finrank ℚ (realCyclotomicField p) * 2 := by
    change Module.finrank ℚ_[p]
      (rationalTate K (fiber K (primePlusFamily p hp) x).X p) = _
    exact finrank_primePlusRationalTate_at p hp K x
  have hdeg : 0 < Module.finrank ℚ (realCyclotomicField p) :=
    Module.finrank_pos
  have hVpos : 0 < Module.finrank ℚ_[p] V := by
    rw [hR]
    omega
  let : Module.Finite ℚ_[p] V := by
    cases hdim : Module.finrank ℚ_[p] V with
    | zero => omega
    | succ n => exact Module.finite_of_finrank_eq_succ hdim
  let : Module.Finite (RealPrimePowerCompletion p 0) V :=
    Module.Finite.of_restrictScalars_finite ℚ_[p] _ V
  have hL : Module.finrank ℚ_[p] (RealPrimePowerCompletion p 0) =
      Module.finrank ℚ (realCyclotomicField p) := by
    rw [← (realPrimePowerCompletionTensorEquiv p 0).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange]
    have hz : zeta (p ^ (0 + 1)) = zeta p := by
      congr 1
      simp
    have hfield : realCyclotomicField (p ^ (0 + 1)) = realCyclotomicField p := by
      unfold realCyclotomicField
      rw [hz]
    rw [hfield]
  have htower := Module.finrank_mul_finrank ℚ_[p] (RealPrimePowerCompletion p 0) V
  rw [hL, hR] at htower
  exact Nat.eq_of_mul_eq_mul_left hdeg htower

/-- The completion restriction at prime conductor, with the exponent-one
coefficient field simplified to the actual prime cyclotomic field. -/
private theorem primePlusCyclotomicField_eq :
    realCyclotomicField (p ^ (0 + 1)) = realCyclotomicField p := by
  have hz : zeta (p ^ (0 + 1)) = zeta p := by
    congr 1
    simp
  unfold realCyclotomicField
  rw [hz]

private def transportGaloisRestriction {F E : IntermediateField ℚ Qbar}
    (h : F = E) (f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      Gal(AlgebraicClosure F/F)) :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      Gal(AlgebraicClosure E/E) := by
  cases h
  exact f

private theorem continuous_transportGaloisRestriction
    {F E : IntermediateField ℚ Qbar} (h : F = E)
    (f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      Gal(AlgebraicClosure F/F)) (hf : Continuous f) :
    Continuous (transportGaloisRestriction p h f) := by
  cases h
  exact hf

def primePlusLocalGaloisRestriction :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      Gal(AlgebraicClosure (realCyclotomicField p)/realCyclotomicField p) :=
  transportGaloisRestriction p (primePlusCyclotomicField_eq p)
    (realPrimePowerLocalGaloisRestriction p 0)

/-- The selected prime family's local Galois restriction is continuous. -/
theorem continuous_primePlusLocalGaloisRestriction :
    Continuous (primePlusLocalGaloisRestriction p) :=
  continuous_transportGaloisRestriction p (primePlusCyclotomicField_eq p)
    (realPrimePowerLocalGaloisRestriction p 0)
    (continuous_realPrimePowerLocalGaloisRestriction p 0)

/-- The completed Tate representation on the selected plus-family fibre. -/
@[expose] def primePlusLocalTateRepresentation
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Rep (RealPrimePowerCompletion p 0)
      Gal(AlgebraicClosure (realCyclotomicField p)/realCyclotomicField p) :=
  localCoefficientTateRep (realCyclotomicField p)
    (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
    (primePlusPrimePowerRealMultiplication p hp)

/-- The local Galois action on the completed Tate module of the selected
plus-curve Jacobian fibre, restricted through the chosen cyclotomic completion. -/
@[expose] def primePlusDecompositionRepresentation
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Rep (RealPrimePowerCompletion p 0)
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) :=
  Rep.of ((primePlusLocalTateRepresentation p hp ξ).ρ.comp
    (primePlusLocalGaloisRestriction p))

/-- The selected plus fibre has completed RM Tate rank two. -/
theorem finrank_primePlusLocalTateRepresentation
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Module.finrank (RealPrimePowerCompletion p 0)
      (primePlusLocalTateRepresentation p hp ξ) = 2 := by
  unfold primePlusLocalTateRepresentation
  have h := finrank_primePlusLocalTateRep_at p hp (realCyclotomicField p)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  with_reducible exact h

/-- The completed rank-two factor is finite dimensional over its coefficient field. -/
instance primePlusLocalTateRepresentation_finite
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Module.Finite (RealPrimePowerCompletion p 0)
      (primePlusLocalTateRepresentation p hp ξ) := by
  exact Module.finite_of_finrank_eq_succ
    (show Module.finrank (RealPrimePowerCompletion p 0)
      (primePlusLocalTateRepresentation p hp ξ) = 1 + 1 by
      simpa using finrank_primePlusLocalTateRepresentation p hp ξ)

/-- Restricting the selected plus Jacobian's Tate action to the decomposition
group leaves its completed RM rank unchanged. -/
theorem finrank_primePlusDecompositionRepresentation
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Module.finrank (RealPrimePowerCompletion p 0)
      (primePlusDecompositionRepresentation p hp ξ) = 2 := by
  change Module.finrank (RealPrimePowerCompletion p 0)
    (primePlusLocalTateRepresentation p hp ξ) = 2
  exact finrank_primePlusLocalTateRepresentation p hp ξ

end HilbertModularity.Hypergeometric
