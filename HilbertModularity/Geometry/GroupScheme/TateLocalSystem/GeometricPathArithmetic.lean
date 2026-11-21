/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricPathMonodromy
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LabelledFiber

/-! # Arithmetic specialization of coefficient-labelled Tate paths -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (C : Type u) [Field C] [Algebra ℚ_[p] C]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ C]
  (hC : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ C)).Splits)

set_option maxHeartbeats 2000000 in
/-- Transported arithmetic loops recover the actual arithmetic action on the same labelled family. -/
def labelledTateGeometricPathArithmeticEquiv (τ : F →ₐ[ℚ] C) :
    Representation.Equiv
      ((Scheme.fiberMonodromy K S (labelledTateLocalSystem K A p C F φ hC τ) x).comp
        (Scheme.galoisAlongGeometricFiberPath K L e).toMonoidHom)
      (Scheme.arithmeticFiberRepresentation L S (labelledTateLocalSystem L A p C F φ hC τ) y) := by
  let E := (labelledTateGeometricPathIso K L e A p C F φ hC τ).toLinearEquiv
  refine .mk E ?_
  intro g
  have h := (labelledTateGeometricPathRepresentationEquiv K L e A p C F φ hC τ).isIntertwining'
    (Scheme.galoisAlongGeometricFiberPath K L e g)
  change E.toLinearMap.comp
      (Scheme.fiberMonodromy K S (labelledTateLocalSystem K A p C F φ hC τ) x
        (Scheme.galoisAlongGeometricFiberPath K L e g)) =
    (Scheme.fiberMonodromy L S (labelledTateLocalSystem L A p C F φ hC τ) y
      (Scheme.geometricFiberPathGroupEquiv K L e
        (Scheme.galoisAlongGeometricFiberPath K L e g))).comp E.toLinearMap at h
  rw [Scheme.geometricFiberPathGroupEquiv_galoisAlong] at h
  exact h

set_option maxHeartbeats 2000000 in
/-- The transported labelled representation is the native labelled Tate subrepresentation
of the actual scheme-theoretic pullback fibre. -/
def labelledTateGeometricPathFiberEquiv (τ : F →ₐ[ℚ] C) :
    Representation.Equiv
      ((Scheme.fiberMonodromy K S (labelledTateLocalSystem K A p C F φ hC τ) x).comp
        (Scheme.galoisAlongGeometricFiberPath K L e).toMonoidHom)
      (labelledTateSubrepresentation L (fiber L A y).X p F C hC
        (fiberPointsAction L (AlgebraicClosure L) A y (𝓞 F) φ)
        (fiberPointsAction_realized L (AlgebraicClosure L) A y (𝓞 F) φ) τ).toRepresentation :=
  (labelledTateGeometricPathArithmeticEquiv K L e A p C F φ hC τ).trans
    (labelledTateLocalSystem_arithmeticEquiv L A p C y F φ hC τ)

end AlgebraicGeometry.GroupScheme
