/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricFamily
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficients

/-! # Local coefficient conjugates of the chosen Darmon Tate representation

The native rational Tate fibre of the one chosen prime-power Darmon family
carries its actual real-multiplication completion action. Its local label is
the scalar tensor along the canonical completion automorphism, with unchanged
base-field Galois group. The construction uses every rational nonsingular
parameter in [TripathiGoswami,
eq:local-m-conjugate]. The named Darmon existence theorem remains the sole
later-batch input; no integral torsion decomposition is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

/-- A rational nonsingular parameter viewed in the actual real multiplication field. -/
def darmonRationalParameter (N : ℕ) [NeZero N] (ξ : ProjectiveLine.Parameter ℚ) :
    ProjectiveLine.Parameter (realCyclotomicField N) :=
  ⟨algebraMap ℚ (realCyclotomicField N) ξ, by
    constructor
    · intro h
      apply ξ.property.1
      apply (algebraMap ℚ (realCyclotomicField N)).injective
      simpa using h
    · intro h
      apply ξ.property.2
      apply (algebraMap ℚ (realCyclotomicField N)).injective
      simpa using h⟩

/-- The chosen parameter point has the original rational coordinate. -/
@[simp] theorem darmonRationalParameter_val (N : ℕ) [NeZero N] (ξ : ProjectiveLine.Parameter ℚ) :
    (darmonRationalParameter N ξ).val = algebraMap ℚ (realCyclotomicField N) ξ := rfl

variable (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))
  (ξ : ProjectiveLine.Parameter ℚ)

/-- The actual local coefficient action on the native Tate fibre of the same chosen family. -/
def darmonLocalTateAction :=
  GroupScheme.localCoefficientTateAction (realCyclotomicField (p ^ (k + 1)))
    (darmonFamily (p ^ (k + 1)) hN)
    (ProjectiveLine.puncturedPoint (realCyclotomicField (p ^ (k + 1)))
      (darmonRationalParameter (p ^ (k + 1)) ξ)) p k
    (darmonRealMultiplication (p ^ (k + 1)) hN)

/-- The native rational Tate representation over the actual real-multiplication completion. -/
def darmonLocalTateRepresentation :=
  GroupScheme.localCoefficientTateRep (realCyclotomicField (p ^ (k + 1)))
    (darmonFamily (p ^ (k + 1)) hN)
    (ProjectiveLine.puncturedPoint (realCyclotomicField (p ^ (k + 1)))
      (darmonRationalParameter (p ^ (k + 1)) ξ)) p k
    (darmonRealMultiplication (p ^ (k + 1)) hN)

/-- Rational p-adic scalars on the chosen Tate object, through its actual completion action. -/
@[instance_reducible] def darmonLocalTateRationalModule :
    Module ℚ_[p] (darmonLocalTateRepresentation p k hN ξ) :=
  Module.compHom _ (algebraMap ℚ_[p] (RealPrimePowerCompletion p k))

attribute [local instance] darmonLocalTateRationalModule

/-- The chosen rational scalar structure is compatible with the actual completion action. -/
theorem darmonLocalTateScalarTower :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) (darmonLocalTateRepresentation p k hN ξ) where
  smul_assoc r a v := by
    change (algebraMap ℚ_[p] (RealPrimePowerCompletion p k) r * a) • v =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) r • (a • v)
    exact mul_smul _ _ _

/-- The manuscript local label is the genuine coefficient conjugate of that same chosen Tate fibre. -/
def darmonLocalScalarConjugate (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Rep (RealPrimePowerCompletion p k)
      (AlgebraicClosure (realCyclotomicField (p ^ (k + 1))) ≃ₐ[realCyclotomicField (p ^ (k + 1))]
        AlgebraicClosure (realCyclotomicField (p ^ (k + 1)))) :=
  Rep.localCoefficientConjugate p k m hm (darmonLocalTateRepresentation p k hN ξ)

/-- The chosen-family conjugate is exactly the previously constructed native Tate conjugate. -/
theorem darmonLocalScalarConjugate_eq (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    darmonLocalScalarConjugate p k hN ξ m hm =
      GroupScheme.localConjugateTateRepresentation (realCyclotomicField (p ^ (k + 1)))
        (darmonFamily (p ^ (k + 1)) hN)
        (ProjectiveLine.puncturedPoint (realCyclotomicField (p ^ (k + 1)))
      (darmonRationalParameter (p ^ (k + 1)) ξ)) p k
        (darmonRealMultiplication (p ^ (k + 1)) hN) m hm :=
  (GroupScheme.localConjugateTateRepresentation_eq (realCyclotomicField (p ^ (k + 1)))
    (darmonFamily (p ^ (k + 1)) hN)
    (ProjectiveLine.puncturedPoint (realCyclotomicField (p ^ (k + 1)))
      (darmonRationalParameter (p ^ (k + 1)) ξ)) p k
    (darmonRealMultiplication (p ^ (k + 1)) hN) m hm).symm

/-- In the labelled tensor, Galois still acts only on the original chosen Tate factor. -/
theorem darmonLocalScalarConjugate_tmul (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
    (g : AlgebraicClosure (realCyclotomicField (p ^ (k + 1))) ≃ₐ[realCyclotomicField (p ^ (k + 1))]
      AlgebraicClosure (realCyclotomicField (p ^ (k + 1))))
    (a : RealPrimePowerCompletion p k) (v : darmonLocalTateRepresentation p k hN ξ) :
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    (darmonLocalScalarConjugate p k hN ξ m hm).ρ g
        (a ⊗ₜ[RealPrimePowerCompletion p k] v) =
      a ⊗ₜ[RealPrimePowerCompletion p k] (darmonLocalTateRepresentation p k hN ξ).ρ g v :=
  Rep.localCoefficientConjugate_tmul p k m hm (darmonLocalTateRepresentation p k hN ξ) g a v

/-- Commuting the tensor factors gives the manuscript order, with the same Galois action. -/
theorem darmonLocalScalarConjugate_comm_tmul (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
    (g : AlgebraicClosure (realCyclotomicField (p ^ (k + 1))) ≃ₐ[realCyclotomicField (p ^ (k + 1))]
      AlgebraicClosure (realCyclotomicField (p ^ (k + 1))))
    (a : RealPrimePowerCompletion p k) (v : darmonLocalTateRepresentation p k hN ξ) :
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    TensorProduct.comm (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k)
        (darmonLocalTateRepresentation p k hN ξ)
        ((darmonLocalScalarConjugate p k hN ξ m hm).ρ g
          (a ⊗ₜ[RealPrimePowerCompletion p k] v)) =
      (darmonLocalTateRepresentation p k hN ξ).ρ g v ⊗ₜ[RealPrimePowerCompletion p k] a :=
  Rep.scalarConjugate_comm_tmul (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (darmonLocalTateRepresentation p k hN ξ) g a v

/-- The same chosen native Tate representation at the actual generic point of the parameter curve. -/
def darmonGenericLocalTateRepresentation :=
  GroupScheme.localCoefficientTateRep (RatFunc (realCyclotomicField (p ^ (k + 1))))
    (darmonFamily (p ^ (k + 1)) hN)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField (p ^ (k + 1)))) p k
    (darmonRealMultiplication (p ^ (k + 1)) hN)

/-- The generic ramified local label is the literal scalar conjugate of the same chosen family. -/
def darmonGenericLocalScalarConjugate (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :=
  Rep.localCoefficientConjugate p k m hm (darmonGenericLocalTateRepresentation p k hN)

/-- Generic Galois acts on the original Tate tensorand, with unchanged base function field. -/
theorem darmonGenericLocalScalarConjugate_tmul (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
    (g : AlgebraicClosure (RatFunc (realCyclotomicField (p ^ (k + 1))))
      ≃ₐ[RatFunc (realCyclotomicField (p ^ (k + 1)))]
        AlgebraicClosure (RatFunc (realCyclotomicField (p ^ (k + 1)))))
    (a : RealPrimePowerCompletion p k) (v : darmonGenericLocalTateRepresentation p k hN) :
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    (darmonGenericLocalScalarConjugate p k hN m hm).ρ g
        (a ⊗ₜ[RealPrimePowerCompletion p k] v) =
      a ⊗ₜ[RealPrimePowerCompletion p k] (darmonGenericLocalTateRepresentation p k hN).ρ g v :=
  Rep.localCoefficientConjugate_tmul p k m hm (darmonGenericLocalTateRepresentation p k hN) g a v

end HilbertModularity.Hypergeometric
