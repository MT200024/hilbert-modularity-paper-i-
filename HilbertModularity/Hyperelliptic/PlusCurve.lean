/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Hyperelliptic
public import HilbertModularity.Hyperelliptic.Plus
public import HilbertModularity.Hyperelliptic.CyclotomicPolynomial

/-! # The prime-level plus curve

The plus curve of [TripathiGoswami] is the smooth projective completion
of `y² = (x+2)(f(x)+2-4t)`. We construct the completion as the finite double
cover of `P¹` with both polynomial charts, and prove smoothness and properness
as well as density of the original affine equation.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace HilbertModularity.Hyperelliptic

variable {K : Type*} [Field K]

/-- The plus-family branch polynomial has even degree for every odd index. -/
theorem plusPolynomial_evenDegree (p : ℕ) (hp : Odd p) (t : K) :
    (plusPolynomial p t).natDegree = 2 * ((p + 1) / 2) := by
  have hp0 : p ≠ 0 := by obtain ⟨k, hk⟩ := hp; omega
  rw [(plusPolynomial_isMonicOfDegree p hp0 t).natDegree_eq]
  obtain ⟨k, hk⟩ := hp
  omega

/-- The actual projective double-cover completion of the plus-family affine equation. -/
def plusCurve (p : ℕ) (hp : Odd p) (t : K) : Scheme :=
  AlgebraicGeometry.Hyperelliptic.curve (plusPolynomial p t) ((p + 1) / 2)
    (plusPolynomial_evenDegree p hp t)

/-- The hyperelliptic projection of the plus curve to the projective line. -/
def plusCurveProjection (p : ℕ) (hp : Odd p) (t : K) :
    plusCurve p hp t ⟶ ProjectiveLine K :=
  AlgebraicGeometry.Hyperelliptic.projection (plusPolynomial p t) ((p + 1) / 2)
    (plusPolynomial_evenDegree p hp t)

instance plusCurveProjection_isFinite (p : ℕ) (hp : Odd p) (t : K) :
    IsFinite (plusCurveProjection p hp t) :=
  DoubleCover.toProjectiveLine_isFinite _ _ _ _

/-- The plus curve as a scheme over its coefficient field. -/
def plusCurveToSpec (p : ℕ) (hp : Odd p) (t : K) :
    plusCurve p hp t ⟶ Spec (CommRingCat.of K) :=
  AlgebraicGeometry.Hyperelliptic.toSpec (plusPolynomial p t) ((p + 1) / 2)
    (plusPolynomial_evenDegree p hp t)

/-- The original affine equation embedded in its completion. -/
def plusAffineInclusion (p : ℕ) (hp : Odd p) (t : K) :
    Spec (CommRingCat.of (DoubleCover.ChartRing (plusPolynomial p t))) ⟶ plusCurve p hp t :=
  DoubleCover.finiteChart (plusPolynomial p t) (plusPolynomial p t).reverse ((p + 1) / 2)
    (AlgebraicGeometry.Hyperelliptic.reverse_transition _ _ (plusPolynomial_evenDegree p hp t))

instance plusAffineInclusion_isOpenImmersion (p : ℕ) (hp : Odd p) (t : K) :
    IsOpenImmersion (plusAffineInclusion p hp t) :=
  DoubleCover.finiteChart_isOpenImmersion _ _ _ _

/-- No component of the plus-curve completion is disjoint from the original affine equation. -/
theorem plusAffineInclusion_denseRange (p : ℕ) (hp : Odd p) (t : K) :
    DenseRange (plusAffineInclusion p hp t) :=
  DoubleCover.finiteChart_denseRange _ _ _ _

instance plusCurveToSpec_isProper (p : ℕ) (hp : Odd p) (t : K) :
    IsProper (plusCurveToSpec p hp t) :=
  AlgebraicGeometry.Hyperelliptic.toSpec_isProper _ _ _

/-- Away from zero and one, the completed plus curve is smooth in characteristic zero. -/
theorem plusCurveToSpec_smooth [CharZero K] (p : ℕ) (hp : Odd p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : Smooth (plusCurveToSpec p hp t) := by
  have hp0 : p ≠ 0 := by obtain ⟨k, hk⟩ := hp; omega
  exact AlgebraicGeometry.Hyperelliptic.smooth_toSpec _ _ _
    (plusPolynomial_separable p hp (by norm_num) (Nat.cast_ne_zero.mpr hp0) t ht0 ht1)
    (by norm_num)

/-- The Chebyshev branch polynomial is the exact cyclotomic equation used in the manuscript. -/
theorem plusPolynomial_eq_cyclotomic [CharZero K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (t : K) :
    plusPolynomial p t = (X + 2) * (cyclotomicChebyshevPolynomial ζ p + 2 - C (4 * t)) := by
  rw [cyclotomicChebyshevPolynomial_eq_chebyshev hp hp2 hζ]
  simp only [plusPolynomial, map_sub, map_ofNat]
  ring

end HilbertModularity.Hyperelliptic
