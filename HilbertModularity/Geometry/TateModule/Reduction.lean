/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule
public import HilbertModularity.RepresentationTheory.TateModule.Reduction

/-! # Geometric torsion as reduction of the covariant Tate module

The finite representation below acts on actual geometric `p`-torsion points.
Under genuine `p`-divisibility of the point group it is equivariantly the scalar
reduction of its actual compatible-family Tate module. This supplies the
unlabelled integral/torsion comparison required before the RM-prime torsion
step in [TripathiGoswami]. No divisibility or RM-prime identification for the
chosen Darmon scheme is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

attribute [local instance] TateModule.torsionCoefficientAlgebra
  TateModule.torsionCoefficientScalarTower

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime]

/-- The actual subgroup of geometric points annihilated by `p`. -/
abbrev pTorsion := TateModule.Torsion p (Points K (AlgebraicClosure K) A) 1

/-- The absolute Galois action on the actual geometric `p`-torsion module. -/
def pTorsionRepresentation :
    Representation (ZMod (p ^ 1)) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (pTorsion K A p) :=
  TateModule.torsionRepresentation p _ _ 1

omit [Fact p.Prime] in
@[simp]
theorem pTorsionRepresentation_apply
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : pTorsion K A p) :
    (pTorsionRepresentation K A p g x : Points K (AlgebraicClosure K) A) =
      g • (x : Points K (AlgebraicClosure K) A) := rfl

/-- Divisibility of the geometric point group identifies the actual residual Tate action with geometric torsion. -/
def residualIntegralTateEquiv
    (hpdiv : Function.Surjective (fun x : Points K (AlgebraicClosure K) A => p • x)) :
    ((integralTateRepresentation K A p).baseChange (ZMod (p ^ 1))).Equiv
      (pTorsionRepresentation K A p) :=
  TateModule.residualRepresentationEquiv p _ _ hpdiv

@[simp]
theorem residualIntegralTateEquiv_tmul
    (hpdiv : Function.Surjective (fun x : Points K (AlgebraicClosure K) A => p • x))
    (a : ZMod (p ^ 1)) (x : integralTate K A p) :
    residualIntegralTateEquiv K A p hpdiv (a ⊗ₜ[ℤ_[p]] x) =
      a • TateModule.projection p (Points K (AlgebraicClosure K) A) 1 x := rfl

omit [Fact p.Prime] in
/-- The geometric finite-torsion action has continuous orbit maps. -/
theorem continuous_pTorsionRepresentation [IsSeparated A.hom] [LocallyOfFiniteType A.hom]
    (x : pTorsion K A p) : Continuous (fun g => pTorsionRepresentation K A p g x) :=
  TateModule.continuous_torsionRepresentation p _ _ 1 x

end AlgebraicGeometry.GroupScheme
