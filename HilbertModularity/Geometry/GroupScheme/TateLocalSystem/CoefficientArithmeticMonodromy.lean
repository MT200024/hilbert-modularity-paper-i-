/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientMonodromy
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientTensorFactor
public import HilbertModularity.RepresentationTheory.SurjectiveRestriction

/-! # Arithmetic comparison over the native coefficient algebra

The geometric-to-arithmetic Tate comparison respects the original real
multiplication. Restricting monodromy to the absolute Galois group therefore
retains the coefficient label, before extending the coefficient field.
-/

public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)

/-- The native coefficient-linear monodromy restricts to the actual arithmetic
Tate representation, with the same scheme-induced coefficient action. -/
def coefficientTateArithmeticRepresentationEquiv :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    let W := rationalTate K (fiber K A x).X p
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
      Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
    Representation.Equiv ((coefficientTateMonodromy K A p F φ x).comp
      (Scheme.galoisToEtaleFundamentalGroup K x))
        (fiberCoefficientTateRepresentation K A x p F φ) := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := rationalTate K (fiber K A x).X p
  letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  refine .mk (coefficientRationalGeometricFiberTateEquiv K A p F φ x) ?_
  intro g
  apply LinearMap.ext
  intro v
  exact congrArg (fun f => f v)
    ((rationalGeometricFiberTateEquiv K A x p).isIntertwining' g)

/-- When the arithmetic point surjects onto the fundamental group, the native
coefficient specialization and the labelled local system have the same full
monodromy. This applies at the generic point of the punctured line. -/
def coefficientTateMonodromyLabelledEquiv
    (L : Type u) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L)
    (hsurj : Function.Surjective (Scheme.galoisToEtaleFundamentalGroup K x)) :
    let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
      Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] F) L :=
      (Algebra.TensorProduct.coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
    Representation.Equiv ((coefficientTateMonodromy K A p F φ x).baseChange L)
      (Scheme.fiberMonodromy K S (labelledTateLocalSystem K A p L F φ hL σ) x) := by
  let V := TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))
  let W := rationalTate K (fiber K A x).X p
  letI : Module (ℚ_[p] ⊗[ℚ] F) V :=
    Module.compHom V (geometricTensorTateAction K A p F φ x).toRingHom
  letI : Module (ℚ_[p] ⊗[ℚ] F) W :=
    Module.compHom W (fiberTensorTateAction K A x p F φ).toRingHom
  letI : Algebra (ℚ_[p] ⊗[ℚ] F) L :=
    (Algebra.TensorProduct.coefficientTensorEmbedding ℚ ℚ_[p] F L σ).toAlgebra
  apply Representation.Equiv.ofCompSurjective _ hsurj
  exact ((coefficientTateArithmeticRepresentationEquiv K A x p F φ).baseChange L).trans
    (labelledTateLocalSystemCoefficientTensorEquiv K A x p F φ L hL σ).symm

end AlgebraicGeometry.GroupScheme
