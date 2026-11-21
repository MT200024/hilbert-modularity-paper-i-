/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.PrimeFive
public import HilbertModularity.Hyperelliptic.PrimeFiveFiniteFields
public import HilbertModularity.Geometry.FiniteFieldPoints
public import Mathlib.FieldTheory.Finite.GaloisField

/-! # Quadratic-field point counts for the level-five curve

The explicit finite-field computations give counts of actual rational points
of the projective completion in [TripathiGoswami].
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace HilbertModularity.Hyperelliptic

/-- Euler's finite computation counts actual projective rational points after adding infinity. -/
theorem primeFive_projective_card_euler {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : ringChar K ≠ 2) :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : K))) =
      primeFiveEulerCount K + 2 := by
  change Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec
    (plusPolynomial 5 (125 : K)) 3 (plusPolynomial_evenDegree 5 (by decide) 125))) = _
  rw [AlgebraicGeometry.Hyperelliptic.card_rationalPoint_euler _ _ _
    (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : K)).monic hK]
  simp only [primeFiveEulerCount_eq, plusPolynomial_five, primeFivePolynomial_eval]

/-- The curve over the quadratic extension of `𝔽₁₁` is smooth. -/
theorem primeFive_quadratic_11_smooth :
    Smooth (plusCurveToSpec 5 (by decide) (125 : QuadraticField11)) :=
  primeFive_fiber_smooth (by decide) (by decide) (by decide) (by decide)

/-- The curve over the quadratic extension of `𝔽₄₁` is smooth. -/
theorem primeFive_quadratic_41_smooth :
    Smooth (plusCurveToSpec 5 (by decide) (125 : QuadraticField41)) :=
  primeFive_fiber_smooth (by decide) (by decide) (by decide) (by decide)

/-- The actual completed curve has 163 points over the quadratic extension of `𝔽₁₁`. -/
theorem primeFive_count_121 :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : QuadraticField11))) =
      163 := by
  rw [primeFive_projective_card_euler (by rw [ringChar.eq QuadraticField11 11]; decide),
    primeFive_euler_count_121]

/-- The actual completed curve has 1783 points over the quadratic extension of `𝔽₄₁`. -/
theorem primeFive_count_1681 :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : QuadraticField41))) =
      1783 := by
  rw [primeFive_projective_card_euler (by rw [ringChar.eq QuadraticField41 41]; decide),
    primeFive_euler_count_1681]

/-- The Euler count is independent of the chosen isomorphic finite-field model. -/
theorem primeFiveEulerCount_congr {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] (e : K ≃+* L) :
    primeFiveEulerCount K = primeFiveEulerCount L := by
  rw [primeFiveEulerCount_eq, primeFiveEulerCount_eq, ← Fintype.card_congr e.toEquiv]
  apply Fintype.sum_equiv e.toEquiv
  intro x
  dsimp
  have hv : (e x + 2) * (e x ^ 5 - 5 * e x ^ 3 + 5 * e x + 2 - 500) =
      e ((x + 2) * (x ^ 5 - 5 * x ^ 3 + 5 * x + 2 - 500)) := by simp [map_ofNat]
  rw [hv, ← map_pow]
  simp only [← map_zero e, ← map_one e, e.injective.eq_iff]

/-- The projective count over any field of 121 elements is 163. -/
theorem primeFive_count_of_card_eq_121 {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K = 121) :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : K))) = 163 := by
  let e : QuadraticField11 ≃+* K :=
    FiniteField.ringEquivOfCardEq (quadraticField11_card.trans hK.symm)
  let : CharP K 11 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 11
  rw [primeFive_projective_card_euler (by rw [ringChar.eq K 11]; decide),
    ← primeFiveEulerCount_congr e, primeFive_euler_count_121]

/-- The projective count over any field of 1681 elements is 1783. -/
theorem primeFive_count_of_card_eq_1681 {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K = 1681) :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : K))) = 1783 := by
  let e : QuadraticField41 ≃+* K :=
    FiniteField.ringEquivOfCardEq (quadraticField41_card.trans hK.symm)
  let : CharP K 41 := charP_of_injective_ringHom (f := e.toRingHom) e.injective 41
  rw [primeFive_projective_card_euler (by rw [ringChar.eq K 41]; decide),
    ← primeFiveEulerCount_congr e, primeFive_euler_count_1681]

end HilbertModularity.Hyperelliptic
