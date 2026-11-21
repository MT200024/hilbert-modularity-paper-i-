module

public import HilbertModularity.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Signed quotients of the prime-level Euler cover -/
public section
namespace HilbertModularity.PaperI
variable {K : Type*} [Field K]

theorem kummer_bezout {m p b c : ℤ} (hbez : b*m+c*p=1) (w h : Kˣ) (hw : w^p=h^m) :
    (w^b*h^c)^p=h ∧ (w^b*h^c)^m=w := by
  constructor
  · rw [mul_zpow, ← zpow_mul, mul_comm b p, zpow_mul, hw, ← zpow_mul,
      ← zpow_mul, ← zpow_add, mul_comm m b, hbez, zpow_one]
  · calc
      _ = w^(b*m)*(h^m)^c := by rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm c m]
      _ = w^(b*m+c*p) := by rw [← hw, ← zpow_mul, mul_comm p c, zpow_add]
      _ = w := by rw [hbez, zpow_one]

theorem kummer_quadratic {x t a : K} (hx : 1-x ≠ 0) (ha : a=x*(1-t*x)/(1-x)) :
    t*x^2-(1+a)*x+a=0 := by
  have h := (eq_div_iff hx).mp ha
  linear_combination h

theorem euler_discriminant {x t a : K} (h : t*x^2-(1+a)*x+a=0) :
    (2*t*x-(1+a))^2 = a^2+(2-4*t)*a+1 := by linear_combination (4*t)*h

theorem reflected_ordinate {x t a : K} (hx : x ≠ 0) (ht : t ≠ 0) (ha : a ≠ 0)
    (h : t*x^2-(1+a)*x+a=0) :
    2*t*(1/(t*x))-(1+a⁻¹) = -(2*t*x-(1+a))/a := by
  field_simp [hx, ht, ha]
  linear_combination 2*h

theorem signed_quotient_equation {k : ℕ} (u y t s : K) (hu : u ≠ 0) (hs : s^2=1)
    (hy : y^2=(u^(2*k+1))^2+(2-4*t)*u^(2*k+1)+1) :
    (y*(u+s)/u^(k+1))^2 = (u+u⁻¹+2*s)*
      ((Polynomial.Chebyshev.C K (2*k+1 : ℕ)).eval (u+u⁻¹)+2-4*t) := by
  rw [Polynomial.Chebyshev.C_eval_add_inv _ _ hu, div_pow, mul_pow, ← pow_mul,
    show (k+1)*2=(2*k+1)+1 by omega, pow_succ u (2*k+1), hy, inv_pow]
  generalize hn : u^(2*k+1) = a
  have ha : a ≠ 0 := hn ▸ pow_ne_zero _ hu
  field_simp [ha, hu]
  linear_combination (a^2+(2-4*t)*a+1)*hs

theorem signed_coordinate_invariant (k : ℕ) (u y s : K) (hu : u ≠ 0) (hs : s^2=1) :
    (s*y/u^(2*k+1))*(u⁻¹+s)/(u⁻¹)^(k+1) = y*(u+s)/u^(k+1) := by
  rw [inv_pow, div_inv_eq_mul, show 2*k+1=k+k+1 by omega,
    pow_succ u (k+k), pow_add, pow_succ u k]
  generalize hw : u^k=a
  have ha : a ≠ 0 := hw ▸ pow_ne_zero _ hu
  field_simp [hu, ha]
  linear_combination (y*u)*hs

theorem complement_cover {p : ℕ} (hp : Odd p) (u y t : K)
    (hy : y^2=(u^p)^2+(2-4*t)*u^p+1) :
    y^2=((-u)^p)^2+(2-4*(1-t))*(-u)^p+1 := by rw [hp.neg_pow, hy]; ring

theorem reciprocal_quadratic (u : K) (hu : u ≠ 0) : u^2-(u+u⁻¹)*u+1=0 := by
  field_simp [hu]
  ring

end HilbertModularity.PaperI
