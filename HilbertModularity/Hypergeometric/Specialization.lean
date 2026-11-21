/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FiniteField
public import HilbertModularity.NumberTheory.PowerResidue
public import HilbertModularity.NumberTheory.LocalSpecialization

@[expose] public section

/-! # Arithmetic specializations of the rank-two finite hypergeometric function

The character and residue argument in this module are constructed from the actual
cyclotomic prime and the parameter. The additive character is fixed explicitly.
-/

namespace HilbertModularity.Cyclotomic

open scoped NumberField
open IsDedekindDomain Hypergeometric
attribute [local instance] Ideal.Quotient.field

noncomputable section

variable (N : ℕ) [NeZero N] (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)

/-- The finite residue field at the chosen cyclotomic prime. -/
local instance instFintypeSpecializationResidue : Fintype (𝓞 (cyclotomicField N) ⧸ P.asIdeal) := Fintype.ofFinite _

/-- McCarthy's rank-two value at an actual good cyclotomic specialization. -/
def mccarthyValue (m : ℕ) (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) : Qbar :=
  symmetricMcCarthySum θ (powerResidueMulChar N P.asIdeal hP) m (P.specialization ξ hξ.valuation_eq_one.le)

/-- The specialized value is the explicit normalized Gauss sum with the
positive power-residue character and the canonical local residue of the parameter. -/
theorem mccarthyValue_eq (m : ℕ)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    let A := powerResidueMulChar N P.asIdeal hP ^ m
    mccarthyValue N P hP m θ ξ hξ =
      -(1 / ((Fintype.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) : Qbar) - 1)) *
      ∑ χ : MulChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar,
        gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 /
          (gaussSum A θ * gaussSum A⁻¹ θ) * χ (P.specialization ξ hξ.valuation_eq_one.le) :=
  rankTwoMcCarthySum_eq θ hθ _ _

/-- Every Gauss denominator in the actual arithmetic specialization is nonzero. -/
theorem mccarthyValue_denominator_ne_zero (m : ℕ)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1) :
    gaussSum (powerResidueMulChar N P.asIdeal hP ^ m) θ *
      gaussSum (powerResidueMulChar N P.asIdeal hP ^ m)⁻¹ θ ≠ 0 :=
  mul_ne_zero (HilbertModularity.Hypergeometric.gaussSum_ne_zero θ hθ _)
    (HilbertModularity.Hypergeometric.gaussSum_ne_zero θ hθ _)

/-- The inverse power-residue convention gives exactly the same arithmetic value;
no scalar or quadratic-character correction occurs. -/
theorem mccarthyValue_inverse_convention (m : ℕ)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    symmetricMcCarthySum θ (powerResidueMulChar N P.asIdeal hP)⁻¹ m (P.specialization ξ hξ.valuation_eq_one.le) =
      mccarthyValue N P hP m θ ξ hξ :=
  symmetricMcCarthySum_inv θ _ m _

/-- The arithmetic McCarthy value equals the normalized finite sum for every
character-group generator compatible with the positive power-residue convention. -/
theorem mccarthyValue_eq_gprvSymmetricSum (m : ℕ) (hm : m ≤ N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ω : MulChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar)
    (hω : orderOf ω = Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1)
    (hχ : ω ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1) / N) =
      powerResidueMulChar N P.asIdeal hP)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ ξ hξ =
      gprvSymmetricSum θ ω N m (P.specialization ξ hξ.valuation_eq_one.le) := by
  apply symmetricMcCarthySum_eq_gprvSymmetricSum θ hθ ω _
    (by simpa only [Nat.card_eq_fintype_card] using hω) N m
    (by simpa only [Nat.card_eq_fintype_card] using dvd_residue_card_sub_one N P.asIdeal hP) hm
    (by simpa only [Nat.card_eq_fintype_card] using hχ)
  exact P.specialization_ne_zero ξ hξ.valuation_eq_one

/-- The inverse arithmetic convention in [GPRV, Section 6.3] gives the same value
for the symmetric numerator pair. This also proves independence of the compatible generator. -/
theorem mccarthyValue_eq_gprvSymmetricSum_inverse (m : ℕ) (hm : m ≤ N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ω : MulChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar)
    (hω : orderOf ω = Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1)
    (hχ : ω ^ ((Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1) / N) =
      (powerResidueMulChar N P.asIdeal hP)⁻¹)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ ξ hξ =
      gprvSymmetricSum θ ω N m (P.specialization ξ hξ.valuation_eq_one.le) := by
  rw [← mccarthyValue_inverse_convention N P hP m θ ξ hξ]
  apply symmetricMcCarthySum_eq_gprvSymmetricSum θ hθ ω _
    (by simpa only [Nat.card_eq_fintype_card] using hω) N m
    (by simpa only [Nat.card_eq_fintype_card] using dvd_residue_card_sub_one N P.asIdeal hP) hm
    (by simpa only [Nat.card_eq_fintype_card] using hχ)
  exact P.specialization_ne_zero ξ hξ.valuation_eq_one

/-- The arithmetic normalized finite sum of [GPRV, Section 6.3], with the inverse
power-residue convention and the actual residue of the specialization parameter. -/
def gprvValue (m : ℕ) (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) : Qbar :=
  gprvSymmetricSum θ (powerResidueGenerator N P.asIdeal hP)⁻¹ N m
    (P.specialization ξ hξ.valuation_eq_one.le)

/-- McCarthy and GPRV arithmetic normalizations agree, with no scalar or character
factor, for every good specialization away from the level. -/
theorem mccarthyValue_eq_gprvValue (m : ℕ) (hm : m ≤ N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ ξ hξ = gprvValue N P hP m θ ξ hξ := by
  apply mccarthyValue_eq_gprvSymmetricSum_inverse N P hP m hm θ hθ
    (powerResidueGenerator N P.asIdeal hP)⁻¹
  · rw [orderOf_inv, powerResidueGenerator_orderOf]
  · rw [inv_pow, powerResidueGenerator_pow]

end

end HilbertModularity.Cyclotomic
