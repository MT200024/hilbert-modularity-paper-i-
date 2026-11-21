/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.HyperellipticPoints
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Logic.Equiv.Prod

/-! # Counting hyperelliptic points over finite fields

Euler's criterion reduces point counting to one polynomial evaluation and one
power test per base coordinate. The formula counts actual rational points of
the projective completion through the chart equivalence.
-/

@[expose] public noncomputable section

open Polynomial

namespace AlgebraicGeometry.Hyperelliptic

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Euler's criterion gives the number of square roots of a field element. -/
theorem card_square_roots (hK : ringChar K ≠ 2) (a : K) :
    Nat.card {y : K // y ^ 2 = a} =
      if a = 0 then 1 else if a ^ (Fintype.card K / 2) = 1 then 2 else 0 := by
  classical
  have h := quadraticChar_card_sqrts hK a
  have hc : (Nat.card {y : K // y ^ 2 = a} : ℤ) = quadraticChar K a + 1 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  by_cases ha : a = 0
  · simp [ha] at hc ⊢
  · rw [ite_eq_right ha]
    by_cases hp : a ^ (Fintype.card K / 2) = 1
    · rw [ite_eq_left hp]
      rw [(quadraticChar_one_iff_isSquare ha).mpr ((FiniteField.isSquare_iff hK ha).mpr hp)] at hc
      norm_num at hc
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast hc
    · rw [ite_eq_right hp]
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr
        (fun hs => hp ((FiniteField.isSquare_iff hK ha).mp hs))] at hc
      norm_num at hc
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast hc

omit [DecidableEq K] in
/-- Affine solutions are counted by summing the square-root counts over the first coordinate. -/
theorem card_affineSolutions (f : K[X]) :
    Nat.card (AffineSolutions f) = ∑ x : K, Nat.card {y : K // y ^ 2 = f.eval x} := by
  unfold AffineSolutions
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun x y : K => y ^ 2 = f.eval x)),
    Nat.card_sigma]

/-- A finite-field point-count formula requiring only linearly many Euler tests. -/
theorem card_rationalPoint_euler (f : K[X]) (n : ℕ) (hf : f.natDegree = 2 * n)
    (hm : f.Monic) (hK : ringChar K ≠ 2) :
    Nat.card (AlgebraicGeometry.Scheme.RationalPoint (toSpec f n hf)) =
      (∑ x : K, if f.eval x = 0 then 1
        else if (f.eval x) ^ (Fintype.card K / 2) = 1 then 2 else 0) + 2 := by
  rw [card_rationalPoint f n hf hm (Ring.two_ne_zero hK), card_affineSolutions]
  simp_rw [card_square_roots hK]

end AlgebraicGeometry.Hyperelliptic
