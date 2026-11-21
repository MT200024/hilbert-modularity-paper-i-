/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionPoints
public import HilbertModularity.Geometry.FinitePointLifting
public import HilbertModularity.Topology.TateModule.FiniteGeneration

/-! # Finite generation of geometric Tate fibres over an arbitrary base -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S)) (p : ℕ)
  [IsFinite (p • 𝟙 A).hom.hom.hom.left] [Etale (p • 𝟙 A).hom.hom.hom.left]

/-- Finite étale multiplication has a finite geometric torsion group at every base point. -/
theorem finite_geometricTorsion :
    Finite (TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) 1) := by
  simp only [TateModule.Torsion, pow_one]
  exact Finite.of_equiv _ (finiteTorsionFiberPointsEquiv K x A p).toEquiv

omit [Etale (p • 𝟙 A).hom.hom.hom.left] in
/-- Finite surjective multiplication makes geometric points over an arbitrary base p-divisible. -/
theorem geometricPoints_nsmul_surjective [Surjective (p • 𝟙 A).hom.hom.hom.left] :
    Function.Surjective (fun a : Additive (Scheme.geometricPointOver K x ⟶ A.X) => p • a) := by
  intro b
  obtain ⟨a, ha⟩ := Scheme.RationalPoint.over_postcomp_surjective (AlgebraicClosure K)
    (Scheme.geometricPointOver K x).hom (p • 𝟙 A).hom.hom.hom b.toMul
  refine ⟨Additive.ofMul a, ?_⟩
  change a ^ p = b.toMul
  exact (CommGrp.comp_nsmul_id A p (Scheme.geometricPointOver K x) a).symm.trans ha

variable [Fact p.Prime]

/-- Geometric finite-surjective multiplication proves finite generation of each actual Tate fibre. -/
theorem integralGeometricTate_finite [Surjective (p • 𝟙 A).hom.hom.hom.left] :
    Module.Finite ℤ_[p] (TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) := by
  let : Finite (TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) 1) :=
    finite_geometricTorsion K x A p
  exact TateModule.integral_finite_of_finite_torsion p _ (geometricPoints_nsmul_surjective K x A p)

end AlgebraicGeometry.GroupScheme
