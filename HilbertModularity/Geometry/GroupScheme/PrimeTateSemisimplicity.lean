/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Semisimplicity
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricResidual
public import HilbertModularity.Geometry.GroupScheme.PrimeFiberDeterminant
public import HilbertModularity.Geometry.TateModule.FiniteGeneration
public import HilbertModularity.RepresentationTheory.SemisimpleBaseChange

/-! # Semisimplicity for the selected plus Jacobian

The application retains the actual selected fibre and every auxiliary prime.
-/

public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

/-- Apply Faltings [MilneAV, Chapter IV, Appendix, Theorem 3, p. 159]
to the selected plus Jacobian, deriving the geometric hypotheses from its
existing family construction. -/
theorem primePlusFiber_tateRepresentation_isSemisimple
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (tateRepresentation (realCyclotomicField p)
      (primePlusFiber p hp ξ).X ℓ).IsSemisimpleRepresentation := by
  let : Smooth (primePlusFamily p hp).X.hom :=
    SmoothOfRelativeDimension.smooth
      (Module.finrank ℚ (realCyclotomicField p)) _
  unfold primePlusFiber parameterFiber
  exact tateRepresentation_isSemisimple (realCyclotomicField p) _ ℓ

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ a : realCyclotomicField p,
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)

omit [IsScalarTower ℚ ℚ_[ℓ] L] in
/-- The actual fixed RM label is semisimple after coefficient extension.
This follows from Faltings and characteristic-zero scalar extension, followed
by passage to the invariant labelled subspace; no labelled conclusion is admitted. -/
theorem primePlusFiber_labelled_isSemisimple :
    let S := endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ) σ
    @Representation.IsSemisimpleRepresentation L _ S.toSubmodule _ _
      S.toSubmodule.addCommGroup S.toSubmodule.module S.toRepresentation := by
  let : Module.Finite ℚ_[ℓ]
      (rationalTate (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ) := by
    change Module.Finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]]
      integralTate (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ)
    infer_instance
  have h := Representation.isSemisimple_baseChange L _
    (primePlusFiber_tateRepresentation_isSemisimple p hp ξ ℓ)
  unfold endomorphismLabelledTate
  exact Representation.isSemisimple_subrepresentation _ h _

omit [IsScalarTower ℚ ℚ_[ℓ] L] in
/-- The cohomological dual of the selected fixed-label factor is semisimple.
The contragredient action is used without a Tate twist. -/
theorem primePlusFiber_labelled_dual_isSemisimple :
    (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      σ).toRepresentation.dual.IsSemisimpleRepresentation := by
  let : Module.Finite ℚ_[ℓ]
      (rationalTate (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ) := by
    change Module.Finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]]
      integralTate (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ)
    infer_instance
  have h := primePlusFiber_labelled_isSemisimple p hp ξ ℓ L hL σ
  unfold endomorphismLabelledTate at h ⊢
  exact Representation.isSemisimple_dual _ h

end HilbertModularity.Hypergeometric
