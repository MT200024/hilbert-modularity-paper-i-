/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Cohomology.Functoriality
public import HilbertModularity.RepresentationTheory.ScalarExtension

/-! # Automorphisms acting on actual pro-étale cohomology

Cohomological pullback is contravariant. Since scheme automorphisms multiply
in function-composition order, their opposite group acts on the integral
and rational p-adic cohomology groups. This records the variance explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The opposite scheme-automorphism group acts by actual integral cohomological pullback. -/
def ellAdicCohomologyAutRepresentation (n : ℕ) :
    Representation ℤ_[ℓ] (Aut X)ᵐᵒᵖ (X.EllAdicCohomology ℓ n) where
  toFun g := (ellAdicCohomologyLinearEquiv g.unop ℓ n).toLinearMap
  map_one' := by
    ext x
    exact ellAdicCohomologyEquiv_refl X ℓ n x
  map_mul' g h := by
    ext x
    exact ellAdicCohomologyEquiv_trans ℓ g.unop h.unop n x

/-- The integral automorphism representation is the previously constructed cohomology map. -/
theorem ellAdicCohomologyAutRepresentation_apply (n : ℕ) (g : (Aut X)ᵐᵒᵖ)
    (x : X.EllAdicCohomology ℓ n) :
    ellAdicCohomologyAutRepresentation X ℓ n g x =
      ellAdicCohomologyEquiv g.unop ℓ n x := rfl

/-- Rational cohomological pullback is scalar extension of the actual integral action. -/
def rationalEllAdicCohomologyAutRepresentation (n : ℕ) :
    Representation ℚ_[ℓ] (Aut X)ᵐᵒᵖ (X.RationalEllAdicCohomology ℓ n) :=
  Representation.baseChange ℚ_[ℓ] (ellAdicCohomologyAutRepresentation X ℓ n)

/-- Rational automorphisms act on the integral factor and fix the coefficient tensorand. -/
@[simp] theorem rationalEllAdicCohomologyAutRepresentation_tmul (n : ℕ)
    (g : (Aut X)ᵐᵒᵖ) (a : ℚ_[ℓ]) (x : X.EllAdicCohomology ℓ n) :
    rationalEllAdicCohomologyAutRepresentation X ℓ n g (a ⊗ₜ[ℤ_[ℓ]] x) =
      a ⊗ₜ[ℤ_[ℓ]] ellAdicCohomologyEquiv g.unop ℓ n x := rfl

end AlgebraicGeometry.Scheme
