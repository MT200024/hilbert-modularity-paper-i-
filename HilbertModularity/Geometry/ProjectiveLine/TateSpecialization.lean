/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.GenericFiberPath
public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathArithmetic
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricPathArithmetic

/-! # Actual Tate specialization from the generic fibre of the punctured line

Every rational parameter uses the same generic geometric Tate module and the
same group scheme. Its arithmetic loops act through the path constructed from
finite étale covers, and the resulting representation is the covariant Tate
representation of the actual pullback fibre.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K] (A : CommGrp (Over (punctured K)))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (x : Spec (CommRingCat.of K) ⟶ punctured K)

/-- The generic geometric integral Tate representation specializes to the actual
integral Tate representation at every rational point of the punctured line. -/
def puncturedIntegralTateSpecializationEquiv :
    Representation.Equiv
      ((GroupScheme.integralTateMonodromy (RatFunc K) (puncturedRationalPoint K) A p).comp
        (puncturedArithmeticLoops K x).toMonoidHom)
      (GroupScheme.integralTateRepresentation K (GroupScheme.fiber K A x).X p) :=
  GroupScheme.integralTateGeometricPathArithmeticEquiv (RatFunc K) K
    (puncturedGenericFiberPath K x) A p

/-- The same single generic geometric rational Tate representation specializes
to the ordinary rational Tate representation of each actual pullback fibre. -/
def puncturedTateSpecializationEquiv :
    Representation.Equiv
      ((GroupScheme.rationalTateMonodromy (RatFunc K) (puncturedRationalPoint K) A p).comp
        (puncturedArithmeticLoops K x).toMonoidHom)
      (GroupScheme.tateRepresentation K (GroupScheme.fiber K A x).X p) :=
  GroupScheme.rationalTateGeometricPathArithmeticEquiv (RatFunc K) K
    (puncturedGenericFiberPath K x) A p

variable (C : Type u) [Field C] [Algebra ℚ_[p] C]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ C]
  (hC : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ C)).Splits)

set_option maxHeartbeats 2000000 in
/-- Each coefficient-labelled factor of the single generic geometric Tate module
specializes to the same labelled Tate factor of every actual rational fibre. -/
def puncturedLabelledTateSpecializationEquiv (τ : F →ₐ[ℚ] C) :
    Representation.Equiv
      ((Scheme.fiberMonodromy (RatFunc K) (punctured K)
        (GroupScheme.labelledTateLocalSystem (RatFunc K) A p C F φ hC τ)
          (puncturedRationalPoint K)).comp (puncturedArithmeticLoops K x).toMonoidHom)
      (GroupScheme.labelledTateSubrepresentation K (GroupScheme.fiber K A x).X p F C hC
        (GroupScheme.fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (GroupScheme.fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) τ).toRepresentation :=
  GroupScheme.labelledTateGeometricPathFiberEquiv (RatFunc K) K
    (puncturedGenericFiberPath K x) A p C F φ hC τ

end AlgebraicGeometry.ProjectiveLine
