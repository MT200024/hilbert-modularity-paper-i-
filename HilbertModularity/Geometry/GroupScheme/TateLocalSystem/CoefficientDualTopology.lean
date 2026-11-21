/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem.Duality
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientDual
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientTopology

/-! # Continuous cohomological labelled Tate families

The dual of the actual continuous labelled Tate family realizes the
cohomological factor convention of [TripathiGoswami], with the same
embedding and the native contragredient arithmetic fibres.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [Surjective (p • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

/-- The actual continuous cohomological factor of the labelled Tate family. -/
def labelledCohomologicalTateEtaleLocalSystem (σ : F →ₐ[ℚ] L) :
    Scheme.EtaleLocalSystem K S L :=
  (labelledTateEtaleLocalSystem K A p L F φ hL σ).cohDual

/-- The continuous cohomological factor has exactly the previously constructed algebraic family. -/
theorem labelledCohomologicalTateEtaleLocalSystem_algebraicFunctor (σ : F →ₐ[ℚ] L) :
    (labelledCohomologicalTateEtaleLocalSystem K A p L F φ hL σ).algebraicFunctor =
      labelledCohomologicalTateLocalSystem K A p L F φ hL σ := rfl

/-- Arithmetic specialization of the continuous cohomological factor is the native dual Tate factor. -/
def labelledCohomologicalTateEtaleLocalSystemArithmeticEquiv
    (x : Spec (CommRingCat.of K) ⟶ S) (σ : F →ₐ[ℚ] L) :
    Representation.Equiv
      ((labelledCohomologicalTateEtaleLocalSystem K A p L F φ hL σ).arithmeticRepresentation x)
      (labelledDualTateFactor K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) σ) :=
  labelledCohomologicalTateLocalSystemArithmeticEquiv K A p L F φ hL x σ

end AlgebraicGeometry.GroupScheme
