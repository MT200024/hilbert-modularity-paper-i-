/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.FunctionField

/-! # The rational involution on the symmetric Euler curve

For the exponent-`m` model of [TripathiGoswamiRevised, Definition 2.3],
the `j = -1` involution of [GPRV, Proposition 9.5] takes the following form
on the branch-open chart.  Its field-level identities are independent of a
coefficient prime.  The quotient of the smooth proper family and its étale
cohomology are separate geometric constructions.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric.EulerCover

variable {F : Type*} [Field F]

/-- The base coordinate of the real-descent involution. -/
def reflectionX (t x : F) : F := (t * x)⁻¹

@[simp] theorem reflectionX_eq (t x : F) :
    reflectionX t x = (t * x)⁻¹ := by
  unfold reflectionX
  rfl

/-- The covering coordinate of the real-descent involution in the
exponent-`m` model.  The sign is forced by the original Euler equation. -/
def reflectionY (t x y : F) : F :=
  -((1 - x) * (1 - t * x)) / (t * x * y)

@[simp] theorem reflectionY_eq (t x y : F) :
    reflectionY t x y = -((1 - x) * (1 - t * x)) / (t * x * y) := by
  unfold reflectionY
  rfl

/-- The base reflection coordinate commutes with extension of scalars. -/
theorem map_reflectionX {E : Type*} [Field E] (φ : F →+* E)
    (t x : F) : φ (reflectionX t x) = reflectionX (φ t) (φ x) := by
  simp [reflectionX]

/-- The covering reflection coordinate commutes with extension of scalars. -/
theorem map_reflectionY {E : Type*} [Field E] (φ : F →+* E)
    (t x y : F) : φ (reflectionY t x y) =
      reflectionY (φ t) (φ x) (φ y) := by
  simp [reflectionY]

private theorem branch_reflection_algebra (N m : ℕ) (hm : m ≤ N)
    {s x q r : F} (hs : s ≠ 0) (hx : x ≠ 0) :
    ((s⁻¹)^m * ((-r) / s)^(N - m) * ((-q) / x)^m) *
      (x^m * q^(N - m) * r^m) = (-(q * r) / s)^N := by
  have hfirst : ((-r) / s) * q = -(q * r) / s := by
    field_simp
  have hsecond : (s⁻¹ * ((-q) / x)) * (x * r) = -(q * r) / s := by
    field_simp
  calc
    ((s⁻¹)^m * ((-r) / s)^(N - m) * ((-q) / x)^m) *
        (x^m * q^(N - m) * r^m) =
      (((-r) / s) * q)^(N - m) *
        ((s⁻¹ * ((-q) / x)) * (x * r))^m := by
          simp only [mul_pow]
          ring
    _ = (-(q * r) / s)^(N - m) * (-(q * r) / s)^m := by
      rw [hfirst, hsecond]
    _ = (-(q * r) / s)^N := by
      rw [← pow_add, Nat.sub_add_cancel hm]

/-- The reflected base coordinate is again off the zero branch. -/
theorem reflectionX_ne_zero {t x : F} (ht : t ≠ 0) (hx : x ≠ 0) :
    reflectionX t x ≠ 0 := by
  exact inv_ne_zero (mul_ne_zero ht hx)

/-- The base-coordinate transformation is an involution. -/
theorem reflectionX_reflectionX {t x : F} (ht : t ≠ 0) (hx : x ≠ 0) :
    reflectionX t (reflectionX t x) = x := by
  unfold reflectionX
  field_simp

/-- Its covering-coordinate transformation is an involution wherever the
four branch factors and the covering coordinate are nonzero. -/
theorem reflectionY_reflectionY {t x y : F}
    (ht : t ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h1x : 1 - x ≠ 0) (h1tx : 1 - t * x ≠ 0) :
    reflectionY t (reflectionX t x) (reflectionY t x y) = y := by
  unfold reflectionY reflectionX
  field_simp
  ring

/-- Reflection conjugates the deck scaling by `ζ` to its inverse. -/
theorem reflectionY_deck {t x y ζ : F}
    (hζ : ζ ≠ 0) :
    reflectionY t x (ζ * y) = ζ⁻¹ * reflectionY t x y := by
  unfold reflectionY
  field_simp

/-- The rational reflection preserves the exponent-`m` Euler equation on the
branch-open chart.  This is the coordinate identity underlying the generic
real-descent quotient of [GPRV, Proposition 9.5]. -/
theorem reflection_preserves_equation (N m : ℕ) (hm : m ≤ N)
    {t x y : F} (ht : t ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hcurve : y^N = x^m * (1 - x)^(N - m) * (1 - t * x)^m) :
    (reflectionY t x y)^N =
      (reflectionX t x)^m * (1 - reflectionX t x)^(N - m) *
        (1 - t * reflectionX t x)^m := by
  have hs : t * x ≠ 0 := mul_ne_zero ht hx
  have hbaseOne : 1 - reflectionX t x = -(1 - t * x) / (t * x) := by
    unfold reflectionX
    field_simp
    ring
  have hbaseTwo : 1 - t * reflectionX t x = -(1 - x) / x := by
    unfold reflectionX
    field_simp
    ring
  have hY : reflectionY t x y * y =
      -((1 - x) * (1 - t * x)) / (t * x) := by
    unfold reflectionY
    field_simp
  have hYpow := congrArg (fun z : F => z^N) hY
  rw [mul_pow] at hYpow
  have hbranch := branch_reflection_algebra N m hm hs hx
    (s := t * x) (x := x) (q := 1 - x) (r := 1 - t * x)
  have hprod : (reflectionY t x y)^N * y^N =
      ((reflectionX t x)^m * (1 - reflectionX t x)^(N - m) *
        (1 - t * reflectionX t x)^m) * y^N := by
    rw [hYpow, hcurve]
    rw [hbaseOne, hbaseTwo, reflectionX]
    exact hbranch.symm
  exact (mul_right_cancel₀ (pow_ne_zero N hy)) hprod

/-- Points of the exponent-`m` Euler curve on the complement of its four
branch sections.  The nonvanishing conditions make the rational reflection
a regular map on this chart. -/
structure OpenEulerPoint (N m : ℕ) (t : F) where
  x : F
  y : F
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  one_sub_x_ne_zero : 1 - x ≠ 0
  one_sub_tx_ne_zero : 1 - t * x ≠ 0
  equation : y^N = x^m * (1 - x)^(N - m) * (1 - t * x)^m

/-- Two branch-open Euler points agree when their affine coordinates agree. -/
@[ext] theorem OpenEulerPoint.ext {N m : ℕ} {t : F}
    {p q : OpenEulerPoint N m t} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  cases hx
  cases hy
  rfl

/-- The rational formulas give an actual map of branch-open Euler points. -/
def reflectOpenEulerPoint (N m : ℕ) (hm : m ≤ N) {t : F} (ht : t ≠ 0)
    (p : OpenEulerPoint N m t) : OpenEulerPoint N m t where
  x := reflectionX t p.x
  y := reflectionY t p.x p.y
  x_ne_zero := reflectionX_ne_zero ht p.x_ne_zero
  y_ne_zero := by
    unfold reflectionY
    exact div_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero p.one_sub_x_ne_zero p.one_sub_tx_ne_zero))
      (mul_ne_zero (mul_ne_zero ht p.x_ne_zero) p.y_ne_zero)
  one_sub_x_ne_zero := by
    have h : 1 - reflectionX t p.x = -(1 - t * p.x) / (t * p.x) := by
      unfold reflectionX
      field_simp [p.x_ne_zero, ht]
      ring
    rw [h]
    exact div_ne_zero (neg_ne_zero.mpr p.one_sub_tx_ne_zero)
      (mul_ne_zero ht p.x_ne_zero)
  one_sub_tx_ne_zero := by
    have h : 1 - t * reflectionX t p.x = -(1 - p.x) / p.x := by
      unfold reflectionX
      field_simp [p.x_ne_zero, ht]
      ring
    rw [h]
    exact div_ne_zero (neg_ne_zero.mpr p.one_sub_x_ne_zero) p.x_ne_zero
  equation := reflection_preserves_equation N m hm ht p.x_ne_zero p.y_ne_zero
    p.equation

/-- The reflected branch-open base coordinate. -/
@[simp] theorem reflectOpenEulerPoint_x (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) (p : OpenEulerPoint N m t) :
    (reflectOpenEulerPoint N m hm ht p).x = reflectionX t p.x :=
  (rfl)

/-- The reflected branch-open covering coordinate. -/
@[simp] theorem reflectOpenEulerPoint_y (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) (p : OpenEulerPoint N m t) :
    (reflectOpenEulerPoint N m hm ht p).y = reflectionY t p.x p.y :=
  (rfl)

/-- The reflection is an involution on the actual branch-open curve. -/
theorem reflectOpenEulerPoint_involutive (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) (p : OpenEulerPoint N m t) :
    reflectOpenEulerPoint N m hm ht (reflectOpenEulerPoint N m hm ht p) = p := by
  cases p with
  | mk x y hx hy h1x h1tx heq =>
    simp only [reflectOpenEulerPoint]
    congr 1
    · exact reflectionX_reflectionX ht hx
    · exact reflectionY_reflectionY ht hx hy h1x h1tx

/-- The self-equivalence of the branch-open Euler curve underlying the
real-field quotient in [GPRV, Proposition 9.5]. -/
def openEulerReflection (N m : ℕ) (hm : m ≤ N) {t : F} (ht : t ≠ 0) :
    OpenEulerPoint N m t ≃ OpenEulerPoint N m t where
  toFun := reflectOpenEulerPoint N m hm ht
  invFun := reflectOpenEulerPoint N m hm ht
  left_inv := reflectOpenEulerPoint_involutive N m hm ht
  right_inv := reflectOpenEulerPoint_involutive N m hm ht

/-- The usual deck scaling on the branch-open exponent-`m` Euler curve. -/
def scaleOpenEulerPoint (N m : ℕ) {t ζ : F} (hζ : ζ ≠ 0) (hζN : ζ^N = 1)
    (p : OpenEulerPoint N m t) : OpenEulerPoint N m t where
  x := p.x
  y := ζ * p.y
  x_ne_zero := p.x_ne_zero
  y_ne_zero := mul_ne_zero hζ p.y_ne_zero
  one_sub_x_ne_zero := p.one_sub_x_ne_zero
  one_sub_tx_ne_zero := p.one_sub_tx_ne_zero
  equation := by
    rw [mul_pow, hζN, one_mul]
    exact p.equation

/-- Reflection conjugates the actual deck scaling to inverse scaling on
branch-open points, as in [GPRV, Proposition 9.5, equation (76)]. -/
theorem reflectOpenEulerPoint_scale (N m : ℕ) (hm : m ≤ N)
    {t ζ : F} (ht : t ≠ 0) (hζ : ζ ≠ 0) (hζN : ζ^N = 1)
    (p : OpenEulerPoint N m t) :
    reflectOpenEulerPoint N m hm ht (scaleOpenEulerPoint N m hζ hζN p) =
      scaleOpenEulerPoint N m (inv_ne_zero hζ)
        (by rw [inv_pow, hζN, inv_one]) (reflectOpenEulerPoint N m hm ht p) := by
  cases p
  simp only [reflectOpenEulerPoint, scaleOpenEulerPoint]
  congr 1
  exact reflectionY_deck hζ

end HilbertModularity.Hypergeometric.EulerCover
