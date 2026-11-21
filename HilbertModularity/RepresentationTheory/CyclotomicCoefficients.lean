/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicCompletion
public import HilbertModularity.RepresentationTheory.ScalarConjugation

/-! # Local cyclotomic coefficient labels

The local label acts through the automorphism of the actual real cyclotomic
completion. It changes coefficients while retaining the original acting group.
The specialization to the Darmon Tate representation in [TripathiGoswami]
requires its real-multiplication action separately.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open HilbertModularity.Cyclotomic

namespace Rep

variable (p k m : ℕ) [Fact p.Prime] (hm : m.Coprime (p ^ (k + 1)))
variable {G : Type*} [Monoid G] (V : Rep (RealPrimePowerCompletion p k) G)

/-- The local coefficient label on a representation over the real prime-power completion. -/
def localCoefficientConjugate : Rep (RealPrimePowerCompletion p k) G :=
  scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv V

/-- Galois acts only on the representation tensorand, with the same acting group. -/
theorem localCoefficientConjugate_tmul (g : G) (a : RealPrimePowerCompletion p k) (v : V) :
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    (localCoefficientConjugate p k m hm V).ρ g (a ⊗ₜ[RealPrimePowerCompletion p k] v) =
      a ⊗ₜ[RealPrimePowerCompletion p k] V.ρ g v := rfl

/-- Every local coefficient label preserves the dimension. -/
theorem finrank_localCoefficientConjugate :
    Module.finrank (RealPrimePowerCompletion p k) (localCoefficientConjugate p k m hm V) =
      Module.finrank (RealPrimePowerCompletion p k) V :=
  finrank_scalarConjugate _ V

/-- The local coefficient label transports all stable subspaces of the original representation. -/
def localCoefficientSubrepresentationEquiv :
    Subrepresentation V.ρ ≃o Subrepresentation (localCoefficientConjugate p k m hm V).ρ :=
  scalarConjugateSubrepresentationEquiv _ V

end Rep
