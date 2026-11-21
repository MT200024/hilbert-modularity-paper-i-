/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveGoodReductionFrobenius
public import HilbertModularity.Examples.PrimeFiveRMBlockFactorization
public import HilbertModularity.Geometry.GroupScheme.Isomorphism
public import HilbertModularity.RepresentationTheory.Duality

/-! # From a good model's generic fibre to its selected Jacobian

An isomorphism of the generic fibres preserves the full cohomological Tate
Frobenius polynomial. The model and selected Jacobian remain the actual
objects named by the isomorphism.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open GroupScheme

attribute [local instance] Ideal.Quotient.field

/-- Transport the full dual Tate Frobenius matrix from a good model's generic
fibre to the selected abelian variety through their actual group-scheme
isomorphism. This is a proved isomorphism invariance, with no new admission. -/
theorem exists_selectedDualTateBasis_of_goodModel
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (e : A ≅ localGenericFiber K P B)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bB : Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ] (rationalTate K (localGenericFiber K P B).X ℓ))) :
    ∃ bA : Module.Basis ι ℚ_[ℓ]
        (Module.Dual ℚ_[ℓ] (rationalTate K A.X ℓ)),
      (LinearMap.toMatrix bA bA ((tateRepresentation K A.X ℓ).dual g)).charpolyRev =
        (LinearMap.toMatrix bB bB
          ((tateRepresentation K (localGenericFiber K P B).X ℓ).dual g)).charpolyRev := by
  let eT := tateEquiv K ℓ e
  let d := HilbertModularity.representationDualEquiv eT
  exact ⟨bB.map d.symm.toLinearEquiv,
    congrArg Matrix.charpolyRev (toMatrix_map_representationEquiv d.symm bB g)⟩

end HilbertModularity.Examples
