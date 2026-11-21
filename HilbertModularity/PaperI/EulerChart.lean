module

public import HilbertModularity.PaperI.QuotientCoordinates
public import HilbertModularity.Hypergeometric.GaloisRealizationInvolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The Euler chart and the signed hyperelliptic model -/
@[expose] public section

namespace HilbertModularity.PaperI
open HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K] {N m : ℕ} {t : K}

/-- The normalized Kummer coordinate on the original Euler chart. -/
theorem kummer_on_euler_chart (hm : m ≤ N) (P : OpenEulerPoint N m t) :
    (P.y / (1 - P.x)) ^ N = (P.x * (1 - t * P.x) / (1 - P.x)) ^ m := by
  rw [div_pow, div_pow, mul_pow, P.equation]
  rw [div_eq_div_iff (pow_ne_zero _ P.one_sub_x_ne_zero) (pow_ne_zero _ P.one_sub_x_ne_zero)]
  calc
    _ = P.x ^ m * (1 - t * P.x) ^ m * ((1 - P.x) ^ (N - m) * (1 - P.x) ^ m) := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hm]

/-- In Kummer coordinates, the chosen Euler reflection inverts the coordinate w. -/
theorem reflection_on_euler_chart (hm : m ≤ N) (ht : t ≠ 0) (P : OpenEulerPoint N m t) :
    let P' := reflectOpenEulerPoint N m hm ht P
    P'.y / (1 - P'.x) = (P.y / (1 - P.x))⁻¹ := by
  simp only [reflectOpenEulerPoint_x, reflectOpenEulerPoint_y]
  have hx := mul_ne_zero ht P.x_ne_zero
  have htx : t * P.x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp P.one_sub_tx_ne_zero))
  have hs : 1 - (t * P.x)⁻¹ = (t * P.x - 1) / (t * P.x) := by
    calc
      _ = (t * P.x) / (t * P.x) - 1 / (t * P.x) := by rw [div_self hx, one_div]
      _ = _ := (sub_div _ _ _).symm
  rw [reflectionX_eq, reflectionY_eq, inv_div, hs]
  apply (div_eq_div_iff (div_ne_zero htx hx) P.y_ne_zero).mpr
  field_simp [ht, P.x_ne_zero, P.y_ne_zero]
  ring

/-- The normalized w and h coordinates are units on the branch-open chart. -/
def chartW (P : OpenEulerPoint N m t) : Kˣ :=
  Units.mk0 (P.y / (1 - P.x)) (div_ne_zero P.y_ne_zero P.one_sub_x_ne_zero)

def chartH (P : OpenEulerPoint N m t) : Kˣ :=
  Units.mk0 (P.x * (1 - t * P.x) / (1 - P.x))
    (div_ne_zero (mul_ne_zero P.x_ne_zero P.one_sub_tx_ne_zero) P.one_sub_x_ne_zero)

def chartU (P : OpenEulerPoint N m t) (b c : ℤ) : Kˣ :=
  chartW P ^ b * chartH P ^ c

theorem chartU_powers (P : OpenEulerPoint N m t) (hm : m ≤ N) (b c : ℤ)
    (hb : b * (m : ℤ) + c * (N : ℤ) = 1) :
    (chartU P b c) ^ N = chartH P ∧ (chartU P b c) ^ m = chartW P := by
  have h : (chartW P) ^ N = (chartH P) ^ m := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, chartW, chartH, Units.val_mk0] using kummer_on_euler_chart hm P
  have hh := kummer_bezout hb (chartW P) (chartH P) (by simpa using h)
  simpa only [zpow_natCast, chartU] using hh

theorem chartU_reflection (P : OpenEulerPoint N m t) (hm : m ≤ N) (ht : t ≠ 0) (b c : ℤ) :
    chartU (reflectOpenEulerPoint N m hm ht P) b c = (chartU P b c)⁻¹ := by
  let P' := reflectOpenEulerPoint N m hm ht P
  have hw : chartW P' = (chartW P)⁻¹ := Units.ext (reflection_on_euler_chart hm ht P)
  have hh : chartH P' = (chartH P)⁻¹ := by
    apply Units.ext
    simp only [P', chartH, Units.val_mk0, Units.val_inv_eq_inv_val, reflectOpenEulerPoint_x, reflectionX_eq]
    have htx : t * P.x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp P.one_sub_tx_ne_zero))
    have hs : 1 - (t * P.x)⁻¹ = (t * P.x - 1) / (t * P.x) := by field_simp [ht, P.x_ne_zero]
    rw [hs]
    field_simp [ht, P.x_ne_zero, P.one_sub_x_ne_zero, P.one_sub_tx_ne_zero, htx]
    ring
  change chartW P' ^ b * chartH P' ^ c = (chartW P ^ b * chartH P ^ c)⁻¹
  rw [hw, hh, inv_zpow, inv_zpow, mul_inv]

/-- The Bézout substitution lands on D_t and conjugates the chosen Euler descent
to the negative hyperelliptic reflection. -/
theorem euler_chart_to_signed_cover (P : OpenEulerPoint N m t) (hm : m ≤ N) (ht : t ≠ 0)
    (b c : ℤ) (hb : b * (m : ℤ) + c * (N : ℤ) = 1) :
    let u : K := chartU P b c
    let Y := 2 * t * P.x - (1 + u ^ N)
    let P' := reflectOpenEulerPoint N m hm ht P
    let u' : K := chartU P' b c
    Y ^ 2 = (u ^ N) ^ 2 + (2 - 4 * t) * u ^ N + 1 ∧
      u' = u⁻¹ ∧ 2 * t * P'.x - (1 + u' ^ N) = -Y / u ^ N := by
  let u : K := chartU P b c
  have hu : u ≠ 0 := Units.ne_zero _
  have huN : u ^ N = P.x * (1 - t * P.x) / (1 - P.x) := by
    exact congrArg (fun v : Kˣ => (v : K)) (chartU_powers P hm b c hb).1
  have quad := kummer_quadratic P.one_sub_x_ne_zero huN
  have hr := congrArg (fun v : Kˣ => (v : K)) (chartU_reflection P hm ht b c)
  have hu' : (chartU (reflectOpenEulerPoint N m hm ht P) b c : K) = u⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using hr
  refine ⟨euler_discriminant quad, hu', ?_⟩
  rw [hu', reflectOpenEulerPoint_x, reflectionX_eq, inv_pow]
  simpa only [one_div] using reflected_ordinate P.x_ne_zero ht (pow_ne_zero _ hu) quad

end HilbertModularity.PaperI
