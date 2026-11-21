/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeFiberDeterminant
public import HilbertModularity.Examples.PrimeFiveSelectedRMProduct
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Rank-two bases of actual native plus-family RM dual factors -/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

/-- The selected fibre's native factor has the rank proved for the same
plus-family arithmetic fibre. -/
theorem finrank_primePlusNativeLabelledTate
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    Module.finrank L (endomorphismLabelledTate
      (realCyclotomicField p) (primePlusFiber p hp ξ) ℓ
      (realCyclotomicField p) L hL
      (primePlusFiberRealMultiplication p hp ξ) σ).toSubmodule = 2 := by
  have h := finrank_primePlusFiberTateFactor p hp ℓ L hL σ
    (realCyclotomicField p)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  unfold primePlusFiberTateFactor endomorphismLabelledTate at h
  unfold endomorphismLabelledTate primePlusFiberRealMultiplication
    primePlusFiber parameterFiber
  with_reducible exact h

/-- Every actual native RM cohomological factor has a two-coordinate
basis; no basis or trace is an arithmetic premise. -/
theorem exists_primePlusNativeDualFactorBasis
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    Nonempty (Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate
        (realCyclotomicField p) (primePlusFiber p hp ξ) ℓ
        (realCyclotomicField p) L hL
        (primePlusFiberRealMultiplication p hp ξ) σ).toSubmodule)) := by
  let V := (endomorphismLabelledTate
    (realCyclotomicField p) (primePlusFiber p hp ξ) ℓ
    (realCyclotomicField p) L hL
    (primePlusFiberRealMultiplication p hp ξ) σ).toSubmodule
  let : FiniteDimensional L V := by infer_instance
  have hrank : Module.finrank L V = 2 :=
    finrank_primePlusNativeLabelledTate p hp ξ ℓ L hL σ
  have hdual : Module.finrank L (Module.Dual L V) = 2 := by
    exact (Subspace.dual_finrank_eq (K := L) (V := V)).trans hrank
  exact ⟨Module.finBasisOfFinrankEq L (Module.Dual L V) hdual⟩

end HilbertModularity.Examples
