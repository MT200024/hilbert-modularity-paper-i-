/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerSpecialization

/-! # Cyclotomic coefficients in the Euler trace formula

The Euler sum has values in the actual cyclotomic coefficient field before a
place of that field is chosen.  The comparison with the algebraic-closure-valued
finite sum fixes the positive power-residue convention of
[TripathiGoswamiRevised, Definition 2.3 and the finite-trace formula].
The proper-cohomology Frobenius comparison is [GPRV, Theorem 7.4].
-/

public noncomputable section

namespace HilbertModularity.Cyclotomic

open scoped NumberField
open IsDedekindDomain
open HilbertModularity.Hypergeometric
attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]

local instance instFintypeCyclotomicResidue (P : Ideal (𝓞 (cyclotomicField N)))
    [P.IsMaximal] : Fintype (𝓞 (cyclotomicField N) ⧸ P) :=
  Fintype.ofFinite _

/-- The chosen inclusion of cyclotomic roots of unity into the fixed algebraic
closure, as an equivalence on roots of order dividing `N`. -/
def cyclotomicRootValueEquiv :
    rootsOfUnity N (cyclotomicField N) ≃* rootsOfUnity N Qbar :=
  MulEquiv.ofBijective (rootsOfUnity.mapHom N (cyclotomicField N).val.toRingHom)
    (rootsOfUnity.mapHom_bijective N _ (root_isPrimitiveRoot N)
      (zeta_isPrimitiveRoot N))

/-- The distinguished power-residue character with values in the actual
cyclotomic field, before any choice of an ℓ-adic place. -/
def cyclotomicPowerResidueCharacter
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    (𝓞 (cyclotomicField N) ⧸ P)ˣ →* rootsOfUnity N (cyclotomicField N) :=
  (cyclotomicRootValueEquiv N).symm.toMonoidHom.comp
    (powerResidueCharacter N P hP)

/-- The cyclotomic-valued character extended by zero at the residue-field zero. -/
def cyclotomicPowerResidueMulChar
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    MulChar (𝓞 (cyclotomicField N) ⧸ P) (cyclotomicField N) :=
  MulChar.ofUnitHom ((rootsOfUnity N (cyclotomicField N)).subtype.comp
    (cyclotomicPowerResidueCharacter N P hP))

/-- The character in the cyclotomic field gives the previously established
algebraic character after the fixed inclusion into `Qbar`. -/
theorem cyclotomicPowerResidueMulChar_val
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P)
    (x : 𝓞 (cyclotomicField N) ⧸ P) :
    (cyclotomicField N).val (cyclotomicPowerResidueMulChar N P hP x) =
      powerResidueMulChar N P hP x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp only [MulChar.map_zero, map_zero]
  · let u : (𝓞 (cyclotomicField N) ⧸ P)ˣ := Units.mk0 x hx
    have hu : (u : 𝓞 (cyclotomicField N) ⧸ P) = x := rfl
    rw [← hu]
    simp only [cyclotomicPowerResidueMulChar, MulChar.ofUnitHom_coe,
      powerResidueMulChar_apply_unit]
    have hχ : cyclotomicRootValueEquiv N
        (cyclotomicPowerResidueCharacter N P hP u) =
        powerResidueCharacter N P hP u := by
      simp [cyclotomicPowerResidueCharacter]
    exact congrArg (fun z : rootsOfUnity N Qbar => ((z : Qbarˣ) : Qbar)) hχ

/-- The finite Euler count in the cyclotomic coefficient field.  The exponent
`m` is in the curve equation; the character remains the fixed `χ₀`. -/
def cyclotomicEulerCurveSum
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (m : ℕ)
    (t : 𝓞 (cyclotomicField N) ⧸ P) : cyclotomicField N :=
  ∑ y : 𝓞 (cyclotomicField N) ⧸ P,
    cyclotomicPowerResidueMulChar N P hP
      (y ^ m * (1 - y) ^ (N - m) * (1 - t * y) ^ m)

/-- Its image in `Qbar` is precisely the existing finite-sum normalization. -/
theorem cyclotomicEulerCurveSum_val
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (m : ℕ)
    (t : 𝓞 (cyclotomicField N) ⧸ P) :
    (cyclotomicField N).val (cyclotomicEulerCurveSum N P hP m t) =
      ∑ y : 𝓞 (cyclotomicField N) ⧸ P,
        powerResidueMulChar N P hP
          (y ^ m * (1 - y) ^ (N - m) * (1 - t * y) ^ m) := by
  classical
  simp only [cyclotomicEulerCurveSum, map_sum, cyclotomicPowerResidueMulChar_val]

/-- The symmetric trace scalar before choosing an ℓ-adic coefficient place.
The factor at `-1` is the normalization of the descended cohomological family;
the character in the Euler curve sum is still the fixed `χ₀`. -/
def normalizedCyclotomicEulerTrace
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (m : ℕ)
    (t : 𝓞 (cyclotomicField N) ⧸ P) : cyclotomicField N :=
  -((cyclotomicPowerResidueMulChar N P hP ^ m) (-1)) *
    cyclotomicEulerCurveSum N P hP m t

/-- The normalization factor separated from the raw fixed-character Euler sum. -/
theorem normalizedCyclotomicEulerTrace_eq_mul
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (m : ℕ)
    (t : 𝓞 (cyclotomicField N) ⧸ P) :
    normalizedCyclotomicEulerTrace N P hP m t =
      -((cyclotomicPowerResidueMulChar N P hP ^ m) (-1)) *
        cyclotomicEulerCurveSum N P hP m t := by
  rfl

/-- At a chosen coefficient embedding, the normalized trace is the same
finite Euler sum with each root of unity sent to that coefficient field.
This keeps the fixed character on the exponent-`m` curve. -/
theorem normalizedCyclotomicEulerTrace_map
    {L : Type*} [Field L] (ι : cyclotomicField N →+* L)
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) (m : ℕ)
    (t : 𝓞 (cyclotomicField N) ⧸ P) :
    ι (normalizedCyclotomicEulerTrace N P hP m t) =
      -ι ((cyclotomicPowerResidueMulChar N P hP ^ m) (-1)) *
        ∑ y : 𝓞 (cyclotomicField N) ⧸ P,
          ι (cyclotomicPowerResidueMulChar N P hP
            (y ^ m * (1 - y) ^ (N - m) * (1 - t * y) ^ m)) := by
  classical
  simp only [normalizedCyclotomicEulerTrace, cyclotomicEulerCurveSum,
    map_neg, map_mul, map_sum]

/-- The cyclotomic trace scalar specializes to McCarthy's normalized value
at every arithmetic good prime, including eligible residue characteristic two.
This is the direct finite-sum deduction from
[TripathiGoswamiRevised, equation (2.4) and its proof]. -/
theorem normalizedCyclotomicEulerTrace_val_mccarthyValue
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    (cyclotomicField N).val
      (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization ξ hξ.valuation_eq_one.le)) =
      mccarthyValue N P hP m θ ξ hξ := by
  classical
  have hpow : (cyclotomicField N).val
      ((cyclotomicPowerResidueMulChar N P.asIdeal hP ^ m) (-1)) =
      (powerResidueMulChar N P.asIdeal hP ^ m) (-1) := by
    have hc := (cyclotomicPowerResidueMulChar N P.asIdeal hP).pow_apply_coe m
      (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ)
    have hq := (powerResidueMulChar N P.asIdeal hP).pow_apply_coe m
      (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ)
    have hc' : (cyclotomicPowerResidueMulChar N P.asIdeal hP ^ m) (-1) =
        cyclotomicPowerResidueMulChar N P.asIdeal hP (-1) ^ m := by
      simpa only [Units.val_neg, Units.val_one] using hc
    have hq' : (powerResidueMulChar N P.asIdeal hP ^ m) (-1) =
        powerResidueMulChar N P.asIdeal hP (-1) ^ m := by
      simpa only [Units.val_neg, Units.val_one] using hq
    rw [hc', hq', map_pow, cyclotomicPowerResidueMulChar_val]
  unfold normalizedCyclotomicEulerTrace
  rw [map_mul, map_neg, hpow, cyclotomicEulerCurveSum_val]
  exact (mccarthyValue_eq_eulerCurveSum N P hP m hm hmN θ hθ ξ hξ).symm

end HilbertModularity.Cyclotomic
