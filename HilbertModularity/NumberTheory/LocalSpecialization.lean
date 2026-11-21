/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

/-! # Good unit specializations at finite primes

The multiplicative adic valuation equals `1` precisely when its additive exponent is
zero. Reduction is taken through the valuation ring, identified with the localization
at the prime, and then through its canonical residue-field isomorphism.
-/

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

noncomputable section

/-- Both the parameter and its complement have valuation exponent zero. -/
structure GoodUnit (P : HeightOneSpectrum R) (x : K) : Prop where
  valuation_eq_one : P.valuation K x = 1
  complement_valuation_eq_one : P.valuation K (1 - x) = 1

/-- An element integral at `P`, regarded as an element of the local valuation ring. -/
def localElement (P : HeightOneSpectrum R) (x : K) (hx : P.valuation K x ≤ 1) :
    P.valuationSubringAtPrime K :=
  ⟨x, by rw [valuationSubringAtPrime_eq_valuationSubring]; exact hx⟩

@[simp] theorem coe_localElement (P : HeightOneSpectrum R) (x : K)
    (hx : P.valuation K x ≤ 1) : (P.localElement x hx : K) = x := rfl

/-- The adic valuation has the localization at `P` as its ring of integers. -/
theorem localIntegers (P : HeightOneSpectrum R) :
    (P.valuation K).Integers (P.valuationSubringAtPrime K) := by
  rw [valuationSubringAtPrime_eq_valuationSubring]
  exact Valuation.valuationSubring.integers _

/-- Reduction from the local valuation ring to the original prime quotient. -/
def localResidue (P : HeightOneSpectrum R) :
    P.valuationSubringAtPrime K →+* R ⧸ P.asIdeal :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
    (P.valuationSubringAtPrime K)).symm.toRingHom.comp (IsLocalRing.residue _)

/-- Nonzero residue is equivalent to being a unit in the local valuation ring. -/
theorem localResidue_ne_zero_iff (P : HeightOneSpectrum R)
    (x : P.valuationSubringAtPrime K) :
    P.localResidue x ≠ 0 ↔ IsUnit x := by
  change (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
    (P.valuationSubringAtPrime K)).symm (IsLocalRing.residue _ x) ≠ 0 ↔ _
  exact (RingEquiv.map_ne_zero_iff _).trans
    (IsLocalRing.residue_ne_zero_iff_isUnit x)

/-- The specialization of an element integral at the prime. -/
def specialization (P : HeightOneSpectrum R) (x : K) (hx : P.valuation K x ≤ 1) :
    R ⧸ P.asIdeal := P.localResidue (P.localElement x hx)

/-- Specializing an integer agrees with the quotient map at the prime. -/
@[simp] theorem specialization_algebraMap (P : HeightOneSpectrum R) (x : R) :
    P.specialization (algebraMap R K x) (P.valuation_le_one x) =
      Ideal.Quotient.mk P.asIdeal x := by
  change (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
    (P.valuationSubringAtPrime K)).symm
      ((IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
        (P.valuationSubringAtPrime K)) (Ideal.Quotient.mk P.asIdeal x)) = _
  exact RingEquiv.symm_apply_apply _ _

/-- Local reduction on a global integer is the original prime quotient map. -/
@[simp] theorem localResidue_algebraMap (P : HeightOneSpectrum R) (x : R) :
    P.localResidue (algebraMap R (P.valuationSubringAtPrime K) x) =
      Ideal.Quotient.mk P.asIdeal x :=
  P.specialization_algebraMap x

/-- For an integral local parameter, nonzero residue is equivalent to valuation exponent zero. -/
theorem specialization_ne_zero_iff (P : HeightOneSpectrum R) (x : K)
    (hx : P.valuation K x ≤ 1) :
    P.specialization x hx ≠ 0 ↔ P.valuation K x = 1 :=
  (P.localResidue_ne_zero_iff _).trans P.localIntegers.isUnit_iff_valuation_eq_one

/-- A parameter of valuation exponent zero has nonzero specialization. -/
theorem specialization_ne_zero (P : HeightOneSpectrum R) (x : K)
    (hx : P.valuation K x = 1) : P.specialization x hx.le ≠ 0 := by
  apply (P.localResidue_ne_zero_iff _).mpr
  exact (P.localIntegers.isUnit_iff_valuation_eq_one).mpr hx

/-- Good unit specializations avoid both singular parameters `0` and `1`. -/
theorem GoodUnit.specialization_ne_zero_one {P : HeightOneSpectrum R} {x : K}
    (h : P.GoodUnit x) :
    P.specialization x h.valuation_eq_one.le ≠ 0 ∧ P.specialization x h.valuation_eq_one.le ≠ 1 := by
  refine ⟨P.specialization_ne_zero x h.valuation_eq_one, ?_⟩
  have hsub : P.localElement (1 - x) h.complement_valuation_eq_one.le = 1 - P.localElement x h.valuation_eq_one.le :=
    Subtype.ext rfl
  have hn := P.specialization_ne_zero (1 - x) h.complement_valuation_eq_one
  dsimp [specialization] at hn ⊢
  rw [hsub, map_sub, map_one] at hn
  intro heq
  exact hn (by rw [heq, sub_self])

/-- At an integral element, good specialization means avoiding the prime for both
that element and its complement. -/
theorem goodUnit_algebraMap_iff (P : HeightOneSpectrum R) (x : R) :
    P.GoodUnit (algebraMap R K x) ↔ x ∉ P.asIdeal ∧ 1 - x ∉ P.asIdeal := by
  constructor
  · intro h
    exact ⟨(valuation_eq_one_iff_notMem (K := K) P).mp h.valuation_eq_one,
      (valuation_eq_one_iff_notMem (K := K) P).mp (by
        simpa only [map_sub, map_one] using h.complement_valuation_eq_one)⟩
  · rintro ⟨hx, hsub⟩
    exact ⟨(valuation_eq_one_iff_notMem (K := K) P).mpr hx, by
      simpa only [map_sub, map_one] using
        (valuation_eq_one_iff_notMem (K := K) (v := P)).mpr hsub⟩

end

end IsDedekindDomain.HeightOneSpectrum
