/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.AbsoluteFrobenius
public import HilbertModularity.RepresentationTheory.Duality

/-! # Duality between arithmetic and geometric Frobenius

For a covariant Galois representation, its cohomological dual at geometric
Frobenius has the same characteristic polynomial as the original action at
arithmetic Frobenius. The dual action already inverts the group element, so
this conversion introduces no Tate twist or reciprocal polynomial.

This is the convention bridge needed when using a theorem stated for a
covariant Tate action to obtain the cohomological normalization of
[TripathiGoswami, Remark 2.4].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F K V : Type*} [Field F] [NumberField F] [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Duality and the geometric/arithmetic inverse cancel at Frobenius. The
identity holds in every finite dimension and for any chosen lift; no
ramification or characteristic-polynomial hypothesis is needed. -/
theorem charpoly_dual_geometricFrobenius_eq_arithmetic
    (ρ : Representation K (Gal(AlgebraicClosure F/F)) V)
    (P : Ideal (𝓞 F)) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (ρ.dual (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (ρ (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
  simpa only [NumberField.geometricFrobenius, Subgroup.coe_inv] using
    (charpoly_dual_inv ρ
      (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q :
        Gal(AlgebraicClosure F/F)))

end HilbertModularity
