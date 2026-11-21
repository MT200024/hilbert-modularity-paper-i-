/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.RealCyclotomic
public import HilbertModularity.Geometry.GroupScheme.PrimeGenericDeterminant
public import HilbertModularity.Geometry.GroupScheme.HypergeometricFamily
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LabelledFiber

/-! # Rank of the selected generic Tate factor

The generic rank in Darmon's simultaneous inertia realization is transported
through the native arithmetic fibre comparison, retaining the specified action.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

namespace AlgebraicGeometry.GroupScheme

/-- Rank transport for the specified integral action on a field-valued fibre. -/
theorem finrank_endomorphismLabelledTate_fiber
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (A : CommGrp (Over S)) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ n : ℕ, IsFinite (ℓ ^ n • 𝟙 A).hom.hom.hom.left]
    [∀ n : ℕ, Etale (ℓ ^ n • 𝟙 A).hom.hom.hom.left]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L] (x : Spec (CommRingCat.of K) ⟶ S)
    (F : Type) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L) :
    Module.finrank L (endomorphismLabelledTate K (fiber K A x) ℓ F L hL
      ((fiberEndomorphismMap K A x).comp φ) σ).toSubmodule =
    Module.finrank L ((labelledTateLocalSystem K A ℓ L F φ hL σ).obj
      (Scheme.etaleFiberPoint K S x)) := by
  unfold endomorphismLabelledTate
  exact (labelledTateLocalSystemArithmeticFiberIso K A ℓ L x F φ hL σ
    ).toLinearEquiv.finrank_eq.symm

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ x : realCyclotomicField p,
    ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)

/-- The native selected generic summand has rank two, in every splitting label. -/
theorem finrank_primePlusGenericTateFactor :
    Module.finrank L (primePlusGenericTateFactor p hp ℓ L hL σ).toSubmodule = 2 := by
  have hr := HasStandardInertiaRealization.finrank_labelledTateLocalSystem
    p (primePlusFamily p hp) (primePlusRealMultiplication p hp)
    (primePlusData p hp).multiplication_finite
    (primePlusData p hp).multiplication_etale
    (primePlusData_hasStandardInertiaRealization p hp) ℓ L hL σ
  have he := finrank_endomorphismLabelledTate_fiber
    (RatFunc (realCyclotomicField p)) (primePlusFamily p hp) ℓ L
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))
    (realCyclotomicField p) (primePlusRealMultiplication p hp) hL σ
  unfold primePlusGenericTateFactor
  exact he.trans hr

/-- The determinant identity for the selected generic factor, with its
rank derived from the simultaneous inertia realization. -/
theorem primePlusGenericTateFactor_det
    (g : AlgebraicClosure (RatFunc (realCyclotomicField p)) ≃ₐ[RatFunc (realCyclotomicField p)]
      AlgebraicClosure (RatFunc (realCyclotomicField p))) :
    (LinearMap.det (A := L) (M := (primePlusGenericTateFactor p hp ℓ L hL σ).toSubmodule))
      ((primePlusGenericTateFactor p hp ℓ L hL σ).toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients (RatFunc (realCyclotomicField p)) ℓ L g : L) := by
  have h := primePlusGenericTateFactor_hasPairing p hp ℓ L hL σ inferInstance
  with_reducible
    exact HilbertModularity.linearMap_det_eq_of_exists_alternating_similitude
      (K := L) (V := (primePlusGenericTateFactor p hp ℓ L hL σ).toSubmodule)
      (finrank_primePlusGenericTateFactor p hp ℓ L hL σ)
      (fun g => (primePlusGenericTateFactor p hp ℓ L hL σ).toRepresentation g)
      (fun g => (Field.cyclotomicCharacterWithCoefficients
        (RatFunc (realCyclotomicField p)) ℓ L g : L)) h g

end HilbertModularity.Hypergeometric
