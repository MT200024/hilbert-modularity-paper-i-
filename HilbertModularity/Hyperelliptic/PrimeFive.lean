/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.PlusCurve
public import HilbertModularity.Geometry.HyperellipticPoints
public import HilbertModularity.Examples.PrimeFive
public import Mathlib.Algebra.Field.ZMod

/-! # The level-five rational specialization

The curve in the normalization example of [TripathiGoswami] is the
actual smooth projective plus curve at parameter `125`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace HilbertModularity.Hyperelliptic

/-- The integral equation of the level-five normalization example. -/
def primeFivePolynomial (R : Type*) [CommRing R] : R[X] :=
  (X + 2) * (X ^ 5 - 5 * X ^ 3 + 5 * X - 498)

/-- The displayed integral polynomial is exactly the plus-family specialization. -/
theorem plusPolynomial_five (R : Type*) [CommRing R] :
    plusPolynomial 5 (125 : R) = primeFivePolynomial R := by
  simp only [plusPolynomial, primeFivePolynomial, Nat.cast_ofNat]
  have h5 := Chebyshev.C_add_two R 3
  have h4 := Chebyshev.C_add_two R 2
  have h3 := Chebyshev.C_add_two R 1
  norm_num at h5 h4 h3
  rw [h5, h4, h3, Chebyshev.C_two]
  norm_num [map_sub, map_mul, map_ofNat]
  ring

/-- The smooth projective rational curve used in the normalization example. -/
def primeFiveCurve : Scheme := plusCurve 5 (by decide) (125 : ℚ)

/-- The structural morphism of the level-five rational curve. -/
def primeFiveCurveToSpec : primeFiveCurve ⟶ Spec (CommRingCat.of ℚ) :=
  plusCurveToSpec 5 (by decide) 125

instance primeFiveCurveToSpec_isProper : IsProper primeFiveCurveToSpec :=
  plusCurveToSpec_isProper 5 (by decide) 125

instance primeFiveCurveToSpec_smooth : Smooth primeFiveCurveToSpec :=
  plusCurveToSpec_smooth 5 (by decide) 125 (by norm_num) (by norm_num)

/-- The original affine equation is an open chart of the completed rational curve. -/
def primeFiveAffineInclusion :
    Spec (CommRingCat.of (DoubleCover.ChartRing (plusPolynomial 5 (125 : ℚ)))) ⟶
      primeFiveCurve := plusAffineInclusion 5 (by decide) 125

instance primeFiveAffineInclusion_isOpenImmersion : IsOpenImmersion primeFiveAffineInclusion :=
  plusAffineInclusion_isOpenImmersion 5 (by decide) 125

/-- The displayed affine curve is dense in its projective completion. -/
theorem primeFiveAffineInclusion_denseRange : DenseRange primeFiveAffineInclusion :=
  plusAffineInclusion_denseRange 5 (by decide) 125

/-- The integral polynomial specializes to the displayed equation in every coefficient ring. -/
theorem primeFivePolynomial_eval {R : Type*} [CommRing R] (x : R) :
    (primeFivePolynomial R).eval x =
      (x + 2) * (x ^ 5 - 5 * x ^ 3 + 5 * x + 2 - 500) := by
  simp only [primeFivePolynomial, eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_ofNat]
  ring

/-- The same integral equation defines the finite-field plus fibre. -/
theorem primeFive_affine_card {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    Nat.card (AlgebraicGeometry.Hyperelliptic.AffineSolutions (plusPolynomial 5 (125 : K))) =
      (Finset.univ.filter (fun xy : K × K =>
        xy.2 ^ 2 = (xy.1 + 2) * (xy.1 ^ 5 - 5 * xy.1 ^ 3 + 5 * xy.1 + 2 - 500))).card := by
  unfold AlgebraicGeometry.Hyperelliptic.AffineSolutions
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [plusPolynomial_five, primeFivePolynomial_eval]

/-- Projective points of the level-five fibre include exactly two points at infinity. -/
theorem primeFive_projective_card {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : K))) =
      (Finset.univ.filter (fun xy : K × K =>
        xy.2 ^ 2 = (xy.1 + 2) * (xy.1 ^ 5 - 5 * xy.1 ^ 3 + 5 * xy.1 + 2 - 500))).card + 2 := by
  change Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec
    (plusPolynomial 5 (125 : K)) 3 (plusPolynomial_evenDegree 5 (by decide) 125))) = _
  rw [AlgebraicGeometry.Hyperelliptic.card_rationalPoint _ _ _
    (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : K)).monic h2, primeFive_affine_card]

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The displayed equation is preserved by every coefficient-ring specialization. -/
theorem primeFivePolynomial_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    (primeFivePolynomial R).map φ = primeFivePolynomial S := by
  simp [primeFivePolynomial]

/-- The finite-field fibre is smooth whenever the branch polynomial has good reduction. -/
theorem primeFive_fiber_smooth {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (h5 : (5 : K) ≠ 0) (ht0 : (125 : K) ≠ 0) (ht1 : (125 : K) ≠ 1) :
    Smooth (plusCurveToSpec 5 (by decide) (125 : K)) :=
  AlgebraicGeometry.Hyperelliptic.smooth_toSpec _ _ _
    (plusPolynomial_separable 5 (by decide) h2 h5 125 ht0 ht1) h2

/-- The eleven-element fibre is a smooth projective completion of the reduced equation. -/
theorem primeFive_fiber_11_smooth :
    Smooth (plusCurveToSpec 5 (by decide) (125 : ZMod 11)) :=
  primeFive_fiber_smooth (by decide) (by decide) (by decide) (by decide)

/-- The forty-one-element fibre is a smooth projective completion of the reduced equation. -/
theorem primeFive_fiber_41_smooth :
    Smooth (plusCurveToSpec 5 (by decide) (125 : ZMod 41)) :=
  primeFive_fiber_smooth (by decide) (by decide) (by decide) (by decide)

/-- The actual projective curve has thirteen rational points over the field of eleven elements. -/
theorem primeFive_count_11 :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : ZMod 11))) = 13 := by
  rw [primeFive_projective_card (by decide), Examples.c5_affine_count_11]

/-- The actual projective curve has forty-three rational points over the field of forty-one elements. -/
theorem primeFive_count_41 :
    Nat.card (Scheme.RationalPoint (plusCurveToSpec 5 (by decide) (125 : ZMod 41))) = 43 := by
  rw [primeFive_projective_card (by decide), Examples.c5_affine_count_41]

end HilbertModularity.Hyperelliptic
