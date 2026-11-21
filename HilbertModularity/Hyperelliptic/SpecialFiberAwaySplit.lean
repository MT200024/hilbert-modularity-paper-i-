/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberAlgebra
public import HilbertModularity.Hyperelliptic.SpecialFiberCharts
public import HilbertModularity.Geometry.QuadraticLocalization

/-! # The two sheets away from the branch divisor

On the complement of the branch polynomial, the square-branch quadratic
algebra is the product of its two component rings. This applies to both
charts of the actual special fibre. -/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {S : Type*} [CommRing S]

/-- Evaluation at the two square roots of `h²`. -/
def squareBranchPair (h : S) : QuadraticAlgebra S (h ^ 2) 0 →ₐ[S] S × S where
  toFun z := (z.re + z.im * h, z.re - z.im * h)
  map_zero' := by simp
  map_one' := by
    change ((1 : S) + 0 * h, (1 : S) - 0 * h) = (1, 1)
    simp
  map_add' z w := by
    apply Prod.ext <;> simp <;> ring
  map_mul' z w := by
    apply Prod.ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring
  commutes' r := by simp

@[simp] theorem squareBranchPair_apply (h : S) (z : QuadraticAlgebra S (h ^ 2) 0) :
    squareBranchPair h z = (z.re + z.im * h, z.re - z.im * h) := (rfl)

/-- Inverting the branch polynomial separates the two signed sheets. -/
def squareBranchSplitEquiv (h : S) (h2 : IsUnit (2 : S)) (hh : IsUnit h) :
    QuadraticAlgebra S (h ^ 2) 0 ≃ₐ[S] S × S := by
  let c : S := (↑(h2.unit⁻¹) : S)
  let q : S := (↑(hh.unit⁻¹) : S)
  have hc : c * 2 = 1 := by
    simpa only [c, h2.unit_spec] using Units.inv_mul h2.unit
  have hq : q * h = 1 := by
    simpa only [q, hh.unit_spec] using Units.inv_mul hh.unit
  let inv : S × S → QuadraticAlgebra S (h ^ 2) 0 :=
    fun p => ⟨c * (p.1 + p.2), c * q * (p.1 - p.2)⟩
  have left (z : QuadraticAlgebra S (h ^ 2) 0) :
      inv (squareBranchPair h z) = z := by
    apply QuadraticAlgebra.ext
    · change c * ((z.re + z.im * h) + (z.re - z.im * h)) = z.re
      linear_combination z.re * hc
    · change c * q * ((z.re + z.im * h) - (z.re - z.im * h)) = z.im
      linear_combination q * h * z.im * hc + z.im * hq
  have right (p : S × S) : squareBranchPair h (inv p) = p := by
    rcases p with ⟨f, g⟩
    apply Prod.ext
    · change c * (f + g) + c * q * (f - g) * h = f
      linear_combination c * (f - g) * hq + f * hc
    · change c * (f + g) - c * q * (f - g) * h = g
      linear_combination -c * (f - g) * hq + g * hc
  apply AlgEquiv.ofBijective (squareBranchPair h)
  constructor
  · intro x y hxy
    calc
      x = inv (squareBranchPair h x) := (left x).symm
      _ = inv (squareBranchPair h y) := congrArg inv hxy
      _ = y := left y
  · intro p
    exact ⟨inv p, right p⟩

@[simp] theorem squareBranchSplitEquiv_apply (h : S)
    (h2 : IsUnit (2 : S)) (hh : IsUnit h)
    (z : QuadraticAlgebra S (h ^ 2) 0) :
    squareBranchSplitEquiv h h2 hh z =
      (z.re + z.im * h, z.re - z.im * h) := by
  change squareBranchPair h z = _
  exact squareBranchPair_apply h z

/-- The localization of a square-branch chart at its branch polynomial is a
product of the two localized component rings. -/
def squareBranchAwaySplitEquiv {k : Type*} [Field k] (H : k[X])
    (h2 : (2 : k) ≠ 0) :
    let A := Localization.Away H
    QuadraticAlgebra A ((algebraMap k[X] A H) ^ 2) 0 ≃ₐ[A] A × A := by
  let A := Localization.Away H
  have htwoPoly : IsUnit (2 : k[X]) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr h2).map (C : k →+* k[X])
  have htwo : IsUnit (2 : A) := by
    simpa only [map_ofNat] using htwoPoly.map (algebraMap k[X] A)
  have hH : IsUnit (algebraMap k[X] A H) :=
    IsLocalization.Away.algebraMap_isUnit H
  exact squareBranchSplitEquiv (algebraMap k[X] A H) htwo hH

/-- Coefficient extension from the original square-branch chart to its
complement of the branch divisor. -/
def squareBranchAwayBaseChange {k : Type*} [Field k] (H : k[X]) :
    let A := Localization.Away H
    SquareBranchRing H →+*
      QuadraticAlgebra A ((algebraMap k[X] A H) ^ 2) 0 where
  toFun z := ⟨algebraMap k[X] (Localization.Away H) z.re,
    algebraMap k[X] (Localization.Away H) z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext
    · change (algebraMap k[X] (Localization.Away H)) (1 : k[X]) = 1
      simp
    · change (algebraMap k[X] (Localization.Away H)) (0 : k[X]) = 0
      simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- The splitting of the localized chart is induced by its existing positive
and negative component maps. -/
theorem squareBranchAwaySplitEquiv_baseChange {k : Type*} [Field k]
    (H : k[X]) (h2 : (2 : k) ≠ 0) (z : SquareBranchRing H) :
    let A := Localization.Away H
    squareBranchAwaySplitEquiv H h2 (squareBranchAwayBaseChange H z) =
      (algebraMap k[X] A (positiveComponent H z),
        algebraMap k[X] A (negativeComponent H z)) := by
  dsimp
  rw [squareBranchAwaySplitEquiv, squareBranchSplitEquiv_apply]
  simp [squareBranchAwayBaseChange, positiveComponent_apply, negativeComponent_apply]

/-- The actual finite special-fibre chart splits away from `X * P`. -/
def finiteSpecialFiberAwaySplitEquiv {k : Type*} [Field k] (P : k[X])
    (h2 : (2 : k) ≠ 0) :
    let A := Localization.Away (finiteComponentPolynomial P)
    QuadraticAlgebra A
      (algebraMap k[X] A (finiteBranchPolynomial P 0)) 0 ≃ₐ[A] A × A := by
  dsimp
  rw [finiteBranchPolynomial_zero, map_pow]
  exact squareBranchAwaySplitEquiv (finiteComponentPolynomial P) h2

/-- The actual reciprocal special-fibre chart splits away from `P.reverse`. -/
def infinitySpecialFiberAwaySplitEquiv {k : Type*} [Field k] (P : k[X])
    (h2 : (2 : k) ≠ 0) :
    let A := Localization.Away (infinityComponentPolynomial P)
    QuadraticAlgebra A
      (algebraMap k[X] A (infinityBranchPolynomial P 0)) 0 ≃ₐ[A] A × A := by
  dsimp
  rw [infinityBranchPolynomial_zero, map_pow]
  exact squareBranchAwaySplitEquiv (infinityComponentPolynomial P) h2

end HilbertModularity.Hyperelliptic
