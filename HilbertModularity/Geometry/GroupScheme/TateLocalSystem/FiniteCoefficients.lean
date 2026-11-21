/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.ScalarExtension
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientDecomposition
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Topology

/-! # Finite-dimensional coefficient families

Finite surjective multiplication makes the extended Tate family and each of its
labelled image families finite dimensional. No particular rank is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [Field L] [Algebra ℚ_[p] L]
  [Surjective (p • 𝟙 A).hom.hom.hom.left]

/-- Scalar extension preserves finite dimensionality of the actual Tate family. -/
instance extendedTateLocalSystem_finite (x : Scheme.EtaleFiberGroupoid K S) :
    Module.Finite L ((extendedTateLocalSystem K A p L).obj x) := by
  have : Module.Finite ℚ_[p] ((rationalTateLocalSystem K A p).obj x) :=
    (tateEtaleLocalSystem K A p).finite x
  exact Module.Finite.equiv (ModuleCat.extendScalarsTensorIso ℚ_[p] L
    ((rationalTateLocalSystem K A p).obj x)).toLinearEquiv.symm

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)

/-- Each image factor of the same Tate family is finite dimensional over the coefficient field. -/
instance labelledTateLocalSystem_finite (σ : F →ₐ[ℚ] L)
    (x : Scheme.EtaleFiberGroupoid K S) :
    Module.Finite L ((labelledTateLocalSystem K A p L F φ hL σ).obj x) :=
  Module.Finite.equiv (labelledTateLocalSystemFiberIso K A p L F φ hL σ x).toLinearEquiv.symm

end AlgebraicGeometry.GroupScheme
