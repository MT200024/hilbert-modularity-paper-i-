/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficients
public import HilbertModularity.Geometry.TateModule.FiniteGeneration
public import HilbertModularity.RepresentationTheory.ScalarConjugationContinuity
public import HilbertModularity.Topology.TateModule.FiniteFree
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Native topology for completed Tate coefficients

The completed real-multiplication action is continuous on the original rational
Tate topology. The underlying Galois action is the original continuous action on
compatible geometric torsion points. This supplies the topological coefficient
bridge in [TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField
open HilbertModularity.Cyclotomic
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p k : ℕ) [Fact p.Prime]
  (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)

/-- The completed-coefficient Tate representation carries its original rational Tate topology. -/
@[instance_reducible] def localCoefficientTateRepTopology :
    TopologicalSpace (localCoefficientTateRep K A x p k φ) :=
  inferInstanceAs (TopologicalSpace (rationalTate K (fiber K A x).X p))

attribute [local instance] localCoefficientTateRepTopology
  localCoefficientTateRepRationalModule localCoefficientTateRepScalarTower

/-- The actual Galois action is jointly continuous in the original Tate topology. -/
theorem continuous_localCoefficientTateRep [CharZero K]
    [IsSeparated (fiber K A x).X.hom] [LocallyOfFiniteType (fiber K A x).X.hom] :
    Continuous fun y : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ×
        localCoefficientTateRep K A x p k φ =>
      (localCoefficientTateRep K A x p k φ).ρ y.1 y.2 :=
  continuous_tateRepresentation K (fiber K A x).X p

variable [IsFinite (multiplicationMap K (fiber K A x).X p).left]
  [Surjective (multiplicationMap K (fiber K A x).X p).left]

/-- Finite surjective geometric multiplication gives the native rational module topology. -/
theorem localCoefficientTateRepRationalModuleTopology :
    IsModuleTopology ℚ_[p] (localCoefficientTateRep K A x p k φ) :=
  inferInstanceAs (IsModuleTopology ℚ_[p] (rationalTate K (fiber K A x).X p))

attribute [local instance] localCoefficientTateRepRationalModuleTopology

/-- The actual completion action is jointly continuous on the native rational Tate module. -/
theorem localCoefficientTateRepContinuousSMul :
    ContinuousSMul (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) where
  continuous_smul := by
    let : IsModuleTopology ℚ_[p] (RealPrimePowerCompletion p k) :=
      isModuleTopologyOfFiniteDimensional
    change Continuous fun y : RealPrimePowerCompletion p k × rationalTate K (fiber K A x).X p =>
      localCoefficientTateAction K A x p k φ y.1 y.2
    exact IsModuleTopology.continuous_bilinear_of_finite_left
      (localCoefficientTateAction K A x p k φ).toLinearMap

attribute [local instance] localCoefficientTateRepContinuousSMul

/-- The original Tate topology is also the ordinary module topology for the completion. -/
theorem localCoefficientTateRepModuleTopology :
    IsModuleTopology (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) := by
  let V := localCoefficientTateRep K A x p k φ
  let : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[p] V
  apply IsModuleTopology.of_continuous_id
  let : TopologicalSpace V := moduleTopology (RealPrimePowerCompletion p k) V
  let : IsModuleTopology (RealPrimePowerCompletion p k) V := ⟨rfl⟩
  let : ContinuousAdd V := IsModuleTopology.toContinuousAdd (RealPrimePowerCompletion p k) V
  let : ContinuousSMul (RealPrimePowerCompletion p k) V :=
    IsModuleTopology.toContinuousSMul (RealPrimePowerCompletion p k) V
  let : ContinuousSMul ℚ_[p] V := ⟨by
    have h := ((continuous_algebraMap ℚ_[p] (RealPrimePowerCompletion p k)).comp
      (continuous_fst : Continuous (fun z : ℚ_[p] × V => z.1))).smul continuous_snd
    change Continuous (fun z : ℚ_[p] × V =>
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) z.1 • z.2) at h
    apply h.congr
    intro z
    exact IsScalarTower.algebraMap_smul (RealPrimePowerCompletion p k) z.1 z.2⟩
  exact IsModuleTopology.continuous_of_linearMap
    (aA := localCoefficientTateRepTopology K A x p k φ) (LinearMap.id : V →ₗ[ℚ_[p]] V)

attribute [local instance] localCoefficientTateRepModuleTopology
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))

omit [IsFinite (multiplicationMap K (fiber K A x).X p).left]
  [Surjective (multiplicationMap K (fiber K A x).X p).left] in
/-- The actual tensor conjugate carries its coefficient-module topology. -/
@[instance_reducible] def localConjugateTateRepTopology :
    TopologicalSpace (Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
      (localCoefficientTateRep K A x p k φ)) :=
  moduleTopology (RealPrimePowerCompletion p k) _

attribute [local instance] localConjugateTateRepTopology

omit [IsFinite (multiplicationMap K (fiber K A x).X p).left]
  [Surjective (multiplicationMap K (fiber K A x).X p).left] in
/-- The tensor-conjugate topology is the ordinary topology of a module over the completion. -/
theorem localConjugateTateRepModuleTopology :
    IsModuleTopology (RealPrimePowerCompletion p k)
      (Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
        (localCoefficientTateRep K A x p k φ)) := ⟨rfl⟩

attribute [local instance] localConjugateTateRepModuleTopology

/-- The native Tate module is semilinearly homeomorphic to its actual local coefficient conjugate. -/
def localConjugateTateContinuousEquiv :
    ContinuousLinearEquiv
      ((realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv :
        RealPrimePowerCompletion p k →+* RealPrimePowerCompletion p k)
      (σ' := ((realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv.symm :
        RealPrimePowerCompletion p k →+* RealPrimePowerCompletion p k))
      (localCoefficientTateRep K A x p k φ)
      (Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
        (localCoefficientTateRep K A x p k φ)) :=
  Rep.scalarConjugateContinuousEquiv
    (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (localCoefficientTateRep K A x p k φ)
    (continuous_realPrimePowerCompletionAutomorphism p k m hm)
    (realPrimePowerCompletionAutomorphism p k m hm).symm.toLinearMap.continuous_of_finiteDimensional

/-- The actual local coefficient conjugate has jointly continuous Galois action. -/
theorem continuous_localConjugateTateRep [CharZero K]
    [IsSeparated (fiber K A x).X.hom] [LocallyOfFiniteType (fiber K A x).X.hom] :
    Continuous fun y : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ×
        Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
          (localCoefficientTateRep K A x p k φ) =>
      (Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
        (localCoefficientTateRep K A x p k φ)).ρ y.1 y.2 :=
  Rep.continuous_scalarConjugate
    (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (localCoefficientTateRep K A x p k φ)
    (continuous_realPrimePowerCompletionAutomorphism p k m hm)
    (realPrimePowerCompletionAutomorphism p k m hm).symm.toLinearMap.continuous_of_finiteDimensional
    (continuous_localCoefficientTateRep K A x p k φ)

end AlgebraicGeometry.GroupScheme
