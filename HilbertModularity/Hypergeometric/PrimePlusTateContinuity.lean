/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricDeterminant
public import HilbertModularity.Topology.TateModule.PrimeCoefficients
public import Mathlib.NumberTheory.LocalField.Basic

/-! # Continuity of the selected plus Jacobian's specialized Tate action

Native finite Tate coordinates give continuous matrices after any specialization
preserving p-adic scalars. No topology on the RM completion is needed.
-/

public section
noncomputable section

open scoped NumberField ValuativeRel
open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel

namespace AlgebraicGeometry.GroupScheme

open HilbertModularity.Cyclotomic CategoryTheory

/-- Canonical p-adic scalars in the real-prime completion act natively on
an integral Tate module with real multiplication. -/
theorem realPrimeIntegralTate_smul_padic
    (K : Type*) [Field K] (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (φ : 𝓞 (realCyclotomicField p) →+* End A)
    (z : ℤ_[p]) (v : integralTate K A.X p) :
    letI := realPrimeIntegralTateModule K A p hp φ
    TateModule.coefficientPrimeRingEquiv p (𝓞 (realCyclotomicField p))
      (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
      (realPrimeRamification_pos p hp) (span_realPrimeGenerator_pow p hp)
      (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z) • v = z • v := by
  let := pointsCoefficientModule K A (𝓞 (realCyclotomicField p)) φ
  exact TateModule.coefficientPrime_smul_padic p (𝓞 (realCyclotomicField p))
    (Points K (AlgebraicClosure K) A.X)
    (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
    (realPrimeRamification_pos p hp) (span_realPrimeGenerator_pow p hp) z v

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic IsNonarchimedeanLocalField

/-- Canonical p-adic scalars in the selected RM completion act on the native
Tate lattice by its original p-adic scalar multiplication. -/
theorem primePlusIntegralTate_smul_padic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (z : ℤ_[p]) (v : integralTate (realCyclotomicField p) (primePlusFiber p hp ξ).X p) :
    letI := primePlusIntegralTateModule p hp ξ
    TateModule.coefficientPrimeRingEquiv p (𝓞 (realCyclotomicField p))
      (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
      (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
      (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z) • v = z • v := by
  with_reducible
    exact realPrimeIntegralTate_smul_padic (realCyclotomicField p)
      (primePlusFiber p hp ξ) p (by omega) (primePlusFiberRealMultiplication p hp ξ) z v

/-- A selected integral Tate coordinate specialized to a p-adic coefficient
ring is continuous whenever specialization preserves native p-adic scalars. -/
theorem primePlusIntegralTate_coordinate_continuous
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℤ_[p] E]
    [TopologicalSpace E] [IsTopologicalRing E] [ContinuousSMul ℤ_[p] E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (hβ : ∀ z : ℤ_[p], ((𝒪[E]).subtype.comp β)
      (TateModule.coefficientPrimeRingEquiv p (𝓞 (realCyclotomicField p))
        (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
        (realPrimeRamification_pos p (by omega))
        (span_realPrimeGenerator_pow p (by omega))
        (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
          algebraMap ℤ_[p] E z)
    (i : Fin 2) :
    letI := primePlusIntegralTateModule p hp ξ
    Continuous (fun v : integralTate (realCyclotomicField p)
      (primePlusFiber p hp ξ).X p =>
      ((𝒪[E]).subtype.comp β) ((primePlusIntegralTateBasis p hp ξ).repr v i)) := by
  let := pointsCoefficientModule (realCyclotomicField p) (primePlusFiber p hp ξ)
    (𝓞 (realCyclotomicField p)) (primePlusFiberRealMultiplication p hp ξ)
  let := primePlusIntegralTateModule p hp ξ
  have : Module.Finite ℤ_[p]
      (integralTate (realCyclotomicField p) (primePlusFiber p hp ξ).X p) :=
    integralTate_finite_of_multiplication (realCyclotomicField p)
      (primePlusFiber p hp ξ).X p
  exact TateModule.continuous_coordinate_of_padic_smul p
    (Points (realCyclotomicField p) (AlgebraicClosure (realCyclotomicField p))
      (primePlusFiber p hp ξ).X)
    _ (primePlusIntegralTate_smul_padic p hp ξ)
    ((𝒪[E]).subtype.comp β) hβ (primePlusIntegralTateBasis p hp ξ) i

/-- Continuity of the actual selected Tate matrices follows from compatibility
with native p-adic scalars. This supplies the continuity row of
[TripathiGoswamiRevised, Proposition `SW-checklist`]. -/
theorem primePlusTateFieldCoordinateAction_continuous_of_padicScalars
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℤ_[p] E]
    [TopologicalSpace E] [IsTopologicalRing E] [ContinuousSMul ℤ_[p] E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (hβ : ∀ z : ℤ_[p], ((𝒪[E]).subtype.comp β)
      (TateModule.coefficientPrimeRingEquiv p (𝓞 (realCyclotomicField p))
        (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
        (realPrimeRamification_pos p (by omega))
        (span_realPrimeGenerator_pow p (by omega))
        (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
          algebraMap ℤ_[p] E z)
    (i j : Fin 2) :
    Continuous (fun g : (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
        AlgebraicClosure (realCyclotomicField p)) =>
      primePlusTateFieldCoordinateAction p hp ξ β g (Pi.single j 1) i) := by
  let := pointsCoefficientModule (realCyclotomicField p) (primePlusFiber p hp ξ)
    (𝓞 (realCyclotomicField p)) (primePlusFiberRealMultiplication p hp ξ)
  let := primePlusIntegralTateModule p hp ξ
  let α : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* E := (𝒪[E]).subtype.comp β
  have horbit (v : integralTate (realCyclotomicField p)
      (primePlusFiber p hp ξ).X p) :
      Continuous (fun g : (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
        AlgebraicClosure (realCyclotomicField p)) =>
        primePlusIntegralTateRepresentation p hp ξ g v) := by
    have : Smooth (primePlusFamily p hp).X.hom :=
      (primePlusFamily_smoothOfRelativeDimension p hp).smooth
    have : IsProper (primePlusFiber p hp ξ).X.hom :=
      fiber_isProper (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    have : Smooth (primePlusFiber p hp ξ).X.hom :=
      fiber_smooth (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    have hnative := continuous_integralTateRepresentation
      (realCyclotomicField p) (primePlusFiber p hp ξ).X p
    have hpair : Continuous (fun g : (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
        AlgebraicClosure (realCyclotomicField p)) =>
        (g, v)) := continuous_id.prodMk continuous_const
    have h := hnative.comp hpair
    exact h.congr (fun g =>
      (primePlusIntegralTateRepresentation_apply_native p hp ξ g v).symm)
  have hentry (g : (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
        AlgebraicClosure (realCyclotomicField p))) :
      primePlusTateFieldCoordinateAction p hp ξ β g (Pi.single j 1) i =
        α (((primePlusIntegralTateBasis p hp ξ).repr
          (primePlusIntegralTateRepresentation p hp ξ g
            ((primePlusIntegralTateBasis p hp ξ) j))) i) := by
    rw [primePlusTateFieldCoordinateAction_apply]
    exact coordinateAction_baseChange_entry
      (primePlusIntegralTateBasis p hp ξ)
      (primePlusIntegralTateRepresentation p hp ξ g) α i j
  have hcoordinate : Continuous (fun v : integralTate (realCyclotomicField p)
      (primePlusFiber p hp ξ).X p => α ((primePlusIntegralTateBasis p hp ξ).repr v i)) :=
    primePlusIntegralTate_coordinate_continuous p hp ξ β hβ i
  exact (hcoordinate.comp (horbit ((primePlusIntegralTateBasis p hp ξ) j))).congr
    (fun g => (hentry g).symm)

end HilbertModularity.Hypergeometric
