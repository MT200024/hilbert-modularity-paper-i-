/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.CoordinateRing
public import HilbertModularity.Geometry.Etale.GeometricPathGroup

/-! # Paths from the generic point to arithmetic specializations of the punctured line

The actual finite étale fibre over the rational-function field is isomorphic
to the fibre over each rational point. This constructs the continuous
arithmetic specialization map into a single generic fundamental group.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ punctured K)

/-- A path from the actual generic geometric fibre to the fibre at a rational point. -/
def puncturedGenericFiberPath :
    Scheme.finiteArithmeticFiberFunctor (RatFunc K) (puncturedRationalPoint K) ≅
      Scheme.finiteArithmeticFiberFunctor K x :=
  Scheme.finiteArithmeticFiberIso (RatFunc K) K (puncturedRationalPoint K) x

/-- Actual arithmetic loops at a rational parameter, based at the generic geometric fibre. -/
def puncturedArithmeticLoops :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ*
      Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) :=
  Scheme.galoisAlongGeometricFiberPath (RatFunc K) K (puncturedGenericFiberPath K x)

/-- Conjugation by the chosen actual path recovers the arithmetic action at the parameter. -/
@[simp] theorem puncturedGenericFiberPath_arithmeticLoops
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Scheme.geometricFiberPathGroupEquiv (RatFunc K) K (puncturedGenericFiberPath K x)
      (puncturedArithmeticLoops K x g) = Scheme.galoisToEtaleFundamentalGroup K x g :=
  Scheme.geometricFiberPathGroupEquiv_galoisAlong _ _ _ _

end AlgebraicGeometry.ProjectiveLine
