/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricCoefficients
public import HilbertModularity.RepresentationTheory.ScalarAction

/-! # Actual Tate monodromy linear over the real-multiplication coefficient algebra -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option maxHeartbeats 1000000 in
/-- The same native Tate representation is linear over its actual coefficient tensor algebra. -/
def coefficientTateMonodromy :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    Representation (ℚ_[p] ⊗[ℚ] F) (Scheme.etaleFundamentalGroup K x) V :=
  Representation.withScalarAction (rationalTateMonodromy K x A p)
    (geometricTensorTateAction K A p F φ x).toRingHom (fun σ a => by
      apply LinearMap.ext
      intro v
      exact rationalTateMonodromy_tensorCoefficients K A p F φ x σ a v)

/-- Changing the coefficient ring does not change the actual geometric action on vectors. -/
@[simp] theorem coefficientTateMonodromy_apply (σ : Scheme.etaleFundamentalGroup K x)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    coefficientTateMonodromy K A p F φ x σ v = rationalTateMonodromy K x A p σ v := rfl

end AlgebraicGeometry.GroupScheme
