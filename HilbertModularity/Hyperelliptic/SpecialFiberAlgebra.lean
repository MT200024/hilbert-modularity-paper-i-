/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.Projective
public import HilbertModularity.Geometry.Hyperelliptic

/-! # The two components of a square-branch quadratic chart

In the special fibre of the scaled cover the quadratic equation is `w² = H²`.
Evaluation at `w = H` and `w = -H` gives the two component coordinate maps.
Their joint image remembers the gluing at the zeros of `H`: the difference of
the two component functions is divisible by `H`.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The coordinate ring of a square-branch affine chart. -/
abbrev SquareBranchRing (H : k[X]) :=
  AlgebraicGeometry.DoubleCover.ChartRing (H ^ 2)

/-- Restriction of the quadratic chart to the component `w = H`. -/
def positiveComponent (H : k[X]) : SquareBranchRing H →ₐ[k] k[X] :=
  AlgebraicGeometry.Hyperelliptic.eval (H ^ 2) X H (by simp)

/-- Restriction of the quadratic chart to the component `w = -H`. -/
def negativeComponent (H : k[X]) : SquareBranchRing H →ₐ[k] k[X] :=
  AlgebraicGeometry.Hyperelliptic.eval (H ^ 2) X (-H) (by simp)

@[simp] theorem positiveComponent_apply (H : k[X]) (z : SquareBranchRing H) :
    positiveComponent H z = z.re + z.im * H := by
  simp [positiveComponent, AlgebraicGeometry.Hyperelliptic.eval_apply]

@[simp] theorem negativeComponent_apply (H : k[X]) (z : SquareBranchRing H) :
    negativeComponent H z = z.re - z.im * H := by
  simp [negativeComponent, AlgebraicGeometry.Hyperelliptic.eval_apply]
  ring

/-- Both component restrictions, with their common base coordinate. -/
def componentPair (H : k[X]) : SquareBranchRing H →ₐ[k] k[X] × k[X] where
  toFun z := (positiveComponent H z, negativeComponent H z)
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by
    apply Prod.ext <;> simp [positiveComponent_apply, negativeComponent_apply] <;> ring
  map_mul' z w := by
    apply Prod.ext <;> simp [positiveComponent_apply, negativeComponent_apply] <;> ring
  commutes' r := by simp

@[simp] theorem componentPair_apply (H : k[X]) (z : SquareBranchRing H) :
    componentPair H z = (z.re + z.im * H, z.re - z.im * H) := by
  simp [componentPair]

/-- A pair in the image agrees modulo the intersection polynomial. -/
theorem componentPair_difference_dvd (H : k[X]) (z : SquareBranchRing H) :
    H ∣ (componentPair H z).1 - (componentPair H z).2 := by
  refine ⟨2 * z.im, ?_⟩
  simp [componentPair_apply]
  ring

/-- In characteristic different from two, the two components detect every section. -/
theorem componentPair_injective (H : k[X]) (hH : H ≠ 0) (h2 : (2 : k) ≠ 0) :
    Function.Injective (componentPair H) := by
  intro z w hzw
  have hp : z.re + z.im * H = w.re + w.im * H := by
    exact congrArg Prod.fst (by simpa only [componentPair_apply] using hzw)
  have hm : z.re - z.im * H = w.re - w.im * H := by
    exact congrArg Prod.snd (by simpa only [componentPair_apply] using hzw)
  have htwo : (2 : k[X]) ≠ 0 := by
    simpa only [map_ofNat] using (Polynomial.C_ne_zero.mpr h2)
  have hr : z.re = w.re := by
    have h : (2 : k[X]) * (z.re - w.re) = 0 := by
      linear_combination hp + hm
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left htwo)
  have hi : z.im = w.im := by
    have h : (2 : k[X]) * ((z.im - w.im) * H) = 0 := by
      linear_combination hp - hm
    have hh := (mul_eq_zero.mp h).resolve_left htwo
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hH)
  exact QuadraticAlgebra.ext hr hi

/-- The joint image consists exactly of pairs agreeing modulo `H`. -/
theorem mem_range_componentPair_iff (H : k[X]) (h2 : (2 : k) ≠ 0)
    (f g : k[X]) :
    (f, g) ∈ Set.range (componentPair H) ↔ H ∣ f - g := by
  constructor
  · rintro ⟨z, hz⟩
    have h := componentPair_difference_dvd H z
    simpa only [hz, Prod.fst, Prod.snd] using h
  · rintro ⟨q, hq⟩
    let c : k[X] := C ((2 : k)⁻¹)
    have hc : c * 2 = 1 := by
      simpa only [c, map_mul, map_one, map_ofNat] using
        congrArg (C : k →+* k[X]) (inv_mul_cancel₀ h2)
    let z : SquareBranchRing H := ⟨c * (f + g), c * q⟩
    refine ⟨z, ?_⟩
    have hplus : c * (f + g) + (c * q) * H = f := by
      linear_combination -(c * hq) + f * hc
    have hminus : c * (f + g) - (c * q) * H = g := by
      linear_combination c * hq + g * hc
    apply Prod.ext
    · simpa [componentPair_apply, z] using hplus
    · simpa [componentPair_apply, z] using hminus

end HilbertModularity.Hyperelliptic
