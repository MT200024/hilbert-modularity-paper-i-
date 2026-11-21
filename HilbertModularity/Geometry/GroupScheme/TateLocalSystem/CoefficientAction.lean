/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Endomorphism
public import HilbertModularity.NumberTheory.RingOfIntegers.ScalarExtension
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Real multiplication on the single Tate family

An integral coefficient action on one group scheme acts on its whole rational
Tate family. Arithmetic fibre comparison carries this action to the action of
the same endomorphisms on the actual pullback fibre.
-/

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

/-- The integer action on one scheme extends to a number-field action on its entire Tate family. -/
def numberFieldTateLocalSystemAction : F →ₐ[ℚ] End (rationalTateLocalSystem K A p) :=
  NumberField.RingOfIntegers.rationalExtension F
    ((rationalTateLocalSystemEndomorphismMap K A p).comp φ)

/-- On algebraic integers the family action is induced by the original scheme endomorphism. -/
@[simp]
theorem numberFieldTateLocalSystemAction_integer (a : 𝓞 F) :
    numberFieldTateLocalSystemAction K A p F φ (a : F) =
      rationalTateLocalSystemMap K p (φ a) :=
  NumberField.RingOfIntegers.rationalExtension_apply F _ a


/-- The coefficient tensor algebra acts on the same rational Tate family. -/
def tensorTateLocalSystemAction : ℚ_[p] ⊗[ℚ] F →ₐ[ℚ_[p]] End (rationalTateLocalSystem K A p) :=
  NumberField.RingOfIntegers.tensorExtension F ℚ_[p]
    ((rationalTateLocalSystemEndomorphismMap K A p).comp φ)

/-- Integral coefficients in the tensor action are the original scheme endomorphisms. -/
@[simp]
theorem tensorTateLocalSystemAction_integer (a : 𝓞 F) :
    tensorTateLocalSystemAction K A p F φ ((1 : ℚ_[p]) ⊗ₜ[ℚ] (a : F)) =
      rationalTateLocalSystemMap K p (φ a) :=
  NumberField.RingOfIntegers.tensorExtension_integer F ℚ_[p] _ a

/-- Pure tensor coefficients multiply the number-field action by the Tate scalar. -/
@[simp]
theorem tensorTateLocalSystemAction_tmul (c : ℚ_[p]) (a : F) :
    tensorTateLocalSystemAction K A p F φ (c ⊗ₜ[ℚ] a) =
      c • numberFieldTateLocalSystemAction K A p F φ a := by
  change algebraMap ℚ_[p] (End (rationalTateLocalSystem K A p)) c *
      numberFieldTateLocalSystemAction K A p F φ a = _
  exact (Algebra.smul_def _ _).symm


end AlgebraicGeometry.GroupScheme
