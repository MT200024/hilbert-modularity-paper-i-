/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathMonodromy
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Fiber

/-! # Arithmetic specialization through an actual geometric Tate path

Transport the arithmetic loops of the specialized point to a common geometric
base point. The resulting Tate representation is the ordinary covariant Tate
representation of the actual scheme-theoretic pullback fibre.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Arithmetic loops transported through a path give the integral Tate representation
of the actual fibre over the second field. -/
def integralTateGeometricPathArithmeticEquiv :
    Representation.Equiv
      ((integralTateMonodromy K x A p).comp
        (Scheme.galoisAlongGeometricFiberPath K L e).toMonoidHom)
      (integralTateRepresentation L (fiber L A y).X p) := by
  let E := integralTateGeometricPathEquiv K L e A p
  let d : Representation.Equiv
      ((integralTateMonodromy K x A p).comp
        (Scheme.galoisAlongGeometricFiberPath K L e).toMonoidHom)
      ((integralTateMonodromy L y A p).comp (Scheme.galoisToEtaleFundamentalGroup L y)) :=
    .mk E (by
      intro g
      have h := (integralTateGeometricPathRepresentationEquiv K L e A p).isIntertwining'
        (Scheme.galoisAlongGeometricFiberPath K L e g)
      change E.toLinearMap.comp
          (integralTateMonodromy K x A p (Scheme.galoisAlongGeometricFiberPath K L e g)) =
        (integralTateMonodromy L y A p
          (Scheme.geometricFiberPathGroupEquiv K L e
            (Scheme.galoisAlongGeometricFiberPath K L e g))).comp E.toLinearMap at h
      rw [Scheme.geometricFiberPathGroupEquiv_galoisAlong] at h
      exact h)
  exact d.trans (integralGeometricFiberTateEquiv L A y p)

/-- The same arithmetic specialization statement holds for the rational covariant Tate module. -/
def rationalTateGeometricPathArithmeticEquiv :
    Representation.Equiv
      ((rationalTateMonodromy K x A p).comp
        (Scheme.galoisAlongGeometricFiberPath K L e).toMonoidHom)
      (tateRepresentation L (fiber L A y).X p) :=
  (integralTateGeometricPathArithmeticEquiv K L e A p).baseChange ℚ_[p]

end AlgebraicGeometry.GroupScheme
