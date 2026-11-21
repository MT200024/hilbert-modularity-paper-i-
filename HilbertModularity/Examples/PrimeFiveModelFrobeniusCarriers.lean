/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveGoodReductionFrobenius

/-! # Dual Tate carriers and Frobenius maps on a fixed abelian variety

The base field, actual group scheme, and Galois element are independent
arguments. A selected good model is inserted only after these carriers and
maps have been elaborated.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HilbertModularity.Examples

open GroupScheme

/-- Cohomological dual Tate space of an actual group scheme over a field. -/
abbrev fieldDualTate (k : Type*) [Field k]
    (A : CommGrp (Over (Spec (CommRingCat.of k))))
    (ℓ : ℕ) [Fact ℓ.Prime] :=
  Module.Dual ℚ_[ℓ] (rationalTate k A.X ℓ)

/-- Galois action on that cohomological dual, with its argument fixed before
any good-reduction model or residue quotient is inserted. -/
def fieldDualTateAction (k : Type*) [Field k]
    (A : CommGrp (Over (Spec (CommRingCat.of k))))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
    Module.End ℚ_[ℓ] (fieldDualTate k A ℓ) :=
  (tateRepresentation k A.X ℓ).dual g

end HilbertModularity.Examples
