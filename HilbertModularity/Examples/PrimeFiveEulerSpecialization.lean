/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveEulerTransport
public import HilbertModularity.Examples.PrimeFiveSelectedJacobian
public import HilbertModularity.Hypergeometric.GaloisDescent
import Mathlib.Tactic.NormNum

/-! # The actual Euler parameter at the worked primes

The rational parameter 125 reduces through the selected cyclotomic prime to
the element used in the direct finite sums. This identifies the finite Euler
scalar with the specialization in the chosen local-system trace theorem.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance eulerSpecialFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance eulerSpecialElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance eulerSpecialFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The chosen level-five Euler parameter is the natural number 125 in the
full cyclotomic field. -/
theorem primeFive_realEulerParameter_eq_125 :
    realEulerParameter 5 primeFiveParameter = (125 : cyclotomicField 5) := by
  rw [realEulerParameter_eq_inclusion, realEulerCoefficientInclusion_eq,
    primeFiveParameter_val]
  rfl

private theorem primeFive_specialization_congr
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    {x y : cyclotomicField 5} (h : x = y)
    (hx : P.valuation (cyclotomicField 5) x ≤ 1)
    (hy : P.valuation (cyclotomicField 5) y ≤ 1) :
    P.specialization x hx = P.specialization y hy := by
  cases h
  rfl

private theorem nat_not_mem_of_residue_equiv
    (q : ℕ) [Fact q.Prime]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod q)
    (n : ℕ) (hn : (n : ZMod q) ≠ 0) :
    (n : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal := by
  intro hp
  apply hn
  have hz : Ideal.Quotient.mk P.asIdeal (n : 𝓞 (cyclotomicField 5)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hp
  calc
    (n : ZMod q) = e (Ideal.Quotient.mk P.asIdeal (n : 𝓞 (cyclotomicField 5))) := by simp
    _ = 0 := by rw [hz, map_zero]

/-- Prime-field residues of 125 and 124 make the actual Euler parameter a
good unit at the selected cyclotomic prime. -/
theorem primeFive_realEulerParameter_goodUnit
    (q : ℕ) [Fact q.Prime]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod q)
    (h125 : (125 : ZMod q) ≠ 0) (h124 : (124 : ZMod q) ≠ 0) :
    P.GoodUnit (realEulerParameter 5 primeFiveParameter) := by
  rw [primeFive_realEulerParameter_eq_125]
  change P.GoodUnit (algebraMap (𝓞 (cyclotomicField 5)) (cyclotomicField 5)
    (125 : 𝓞 (cyclotomicField 5)))
  apply (P.goodUnit_algebraMap_iff (125 : 𝓞 (cyclotomicField 5))).mpr
  constructor
  · exact nat_not_mem_of_residue_equiv q P e 125 h125
  · intro h
    have hneg : 1 - (125 : 𝓞 (cyclotomicField 5)) = -(124 : 𝓞 (cyclotomicField 5)) := by
      norm_num
    rw [hneg] at h
    exact nat_not_mem_of_residue_equiv q P e 124 h124 (P.asIdeal.neg_mem_iff.mp h)

/-- The local specialization of the rational parameter agrees with its
ordinary residue under the specified field equivalence. -/
theorem primeFive_realEulerParameter_specialization
    (q : ℕ) [Fact q.Prime]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod q)
    (h125 : (125 : ZMod q) ≠ 0) (h124 : (124 : ZMod q) ≠ 0) :
    let hgood := primeFive_realEulerParameter_goodUnit q P e h125 h124
    P.specialization (realEulerParameter 5 primeFiveParameter)
      hgood.valuation_eq_one.le = e.symm 125 := by
  have hspec : P.specialization (realEulerParameter 5 primeFiveParameter)
      (primeFive_realEulerParameter_goodUnit q P e h125 h124).valuation_eq_one.le =
        Ideal.Quotient.mk P.asIdeal (125 : 𝓞 (cyclotomicField 5)) := by
    have hparam : realEulerParameter 5 primeFiveParameter =
        algebraMap (𝓞 (cyclotomicField 5)) (cyclotomicField 5)
          (125 : 𝓞 (cyclotomicField 5)) := by
      simpa only [map_ofNat] using primeFive_realEulerParameter_eq_125
    exact (primeFive_specialization_congr P hparam _ _).trans
      (P.specialization_algebraMap (125 : 𝓞 (cyclotomicField 5)))
  dsimp only
  rw [hspec]
  apply e.injective
  have hmk : Ideal.Quotient.mk P.asIdeal (125 : 𝓞 (cyclotomicField 5)) =
      (125 : 𝓞 (cyclotomicField 5) ⧸ P.asIdeal) :=
    map_ofNat (Ideal.Quotient.mk P.asIdeal) 125
  rw [hmk]
  rw [e.apply_symm_apply]
  exact map_ofNat e 125

/-- The Euler trace evaluated at the actual local specialization at eleven
is the directly computed McCarthy value. -/
theorem primeFive_orientedEulerValue_at_specialization_11
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1) :
    let hgood := primeFive_realEulerParameter_goodUnit 11 P e (by decide) (by decide)
    primeFiveComplexEmbedding
      (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
        (P.specialization (realEulerParameter 5 primeFiveParameter)
          hgood.valuation_eq_one.le)) = ((Real.sqrt 5 : ℂ) - 1) / 2 := by
  dsimp only
  rw [primeFive_realEulerParameter_specialization 11 P e (by decide) (by decide)]
  exact primeFive_orientedEulerValue_11 P.asIdeal hP e he θ hθ

/-- The same actual specialization identity at forty-one. -/
theorem primeFive_orientedEulerValue_at_specialization_41
    (P : HeightOneSpectrum (𝓞 (cyclotomicField 5)))
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P.asIdeal)
    (e : (𝓞 (cyclotomicField 5) ⧸ P.asIdeal) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P.asIdeal (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1) :
    let hgood := primeFive_realEulerParameter_goodUnit 41 P e (by decide) (by decide)
    primeFiveComplexEmbedding
      (normalizedCyclotomicEulerTrace 5 P.asIdeal hP 1
        (P.specialization (realEulerParameter 5 primeFiveParameter)
          hgood.valuation_eq_one.le)) = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  dsimp only
  rw [primeFive_realEulerParameter_specialization 41 P e (by decide) (by decide)]
  exact primeFive_orientedEulerValue_41 P.asIdeal hP e he θ hθ

end HilbertModularity.Examples
