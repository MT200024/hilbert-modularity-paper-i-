/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberAlgebra

/-! # Component charts in the scaled cover's special fibre

At parameter zero the finite and reciprocal branch polynomials are squares.
The two evaluation maps below use precisely the quadratic rings of the
scaled double cover, rather than an abstract copy of its defining equation.
-/

public noncomputable section

open Polynomial LaurentPolynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The finite-chart square root of the special branch section. -/
def finiteComponentPolynomial (P : k[X]) : k[X] := X * P

@[simp] theorem finiteComponentPolynomial_eq (P : k[X]) :
    finiteComponentPolynomial P = X * P := by
  rfl

/-- The reciprocal-chart square root of the special branch section. -/
def infinityComponentPolynomial (P : k[X]) : k[X] := P.reverse

@[simp] theorem infinityComponentPolynomial_eq (P : k[X]) :
    infinityComponentPolynomial P = P.reverse := by
  rfl

theorem finiteBranchPolynomial_zero (P : k[X]) :
    finiteBranchPolynomial P 0 = finiteComponentPolynomial P ^ 2 := by
  simp [finiteBranchPolynomial, finiteComponentPolynomial, mul_pow]

theorem infinityBranchPolynomial_zero (P : k[X]) :
    infinityBranchPolynomial P 0 = infinityComponentPolynomial P ^ 2 := by
  simp [infinityBranchPolynomial, infinityComponentPolynomial]

/-- The chosen signs on the two charts agree under the line-bundle transition. -/
theorem component_transition (P : k[X]) :
    T (-((P.natDegree + 1 : ℕ) : ℤ)) *
      toLaurent (finiteComponentPolynomial P) =
      invert (toLaurent (infinityComponentPolynomial P)) := by
  simp only [finiteComponentPolynomial, infinityComponentPolynomial,
    toLaurent_reverse, map_mul, toLaurent_X, invert_T]
  rw [involutive_invert (toLaurent P), ← mul_assoc, ← T_add]
  push_cast
  ring_nf

/-- Evaluation on the positive branch commutes with the actual chart gluing. -/
theorem positiveComponent_overlap (P : k[X])
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P 0)) :
    let τ := AlgebraicGeometry.DoubleCover.transition
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)
    (τ z).re + (τ z).im * toLaurent (finiteComponentPolynomial P) =
      invert (z.re + z.im * toLaurent (infinityComponentPolynomial P)) := by
  dsimp
  rw [AlgebraicGeometry.DoubleCover.transition_re,
    AlgebraicGeometry.DoubleCover.transition_im, map_add, map_mul]
  rw [mul_assoc, component_transition]

/-- The negative branch has the same sign on both sides of the overlap. -/
theorem negativeComponent_overlap (P : k[X])
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P 0)) :
    let τ := AlgebraicGeometry.DoubleCover.transition
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)
    (τ z).re - (τ z).im * toLaurent (finiteComponentPolynomial P) =
      invert (z.re - z.im * toLaurent (infinityComponentPolynomial P)) := by
  dsimp
  rw [AlgebraicGeometry.DoubleCover.transition_re,
    AlgebraicGeometry.DoubleCover.transition_im, map_sub, map_mul]
  rw [mul_assoc, component_transition]

/-- Restriction to the positive component in the actual finite chart. -/
def finitePositiveComponent (P : k[X]) :
    AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0) →ₐ[k] k[X] :=
  AlgebraicGeometry.Hyperelliptic.eval (finiteBranchPolynomial P 0) X
    (finiteComponentPolynomial P) (by rw [finiteBranchPolynomial_zero]; simp)

/-- Restriction to the negative component in the actual finite chart. -/
def finiteNegativeComponent (P : k[X]) :
    AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0) →ₐ[k] k[X] :=
  AlgebraicGeometry.Hyperelliptic.eval (finiteBranchPolynomial P 0) X
    (-finiteComponentPolynomial P) (by rw [finiteBranchPolynomial_zero]; simp)

/-- Restriction to the positive component in the actual reciprocal chart. -/
def infinityPositiveComponent (P : k[X]) :
    AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0) →ₐ[k] k[X] :=
  AlgebraicGeometry.Hyperelliptic.eval (infinityBranchPolynomial P 0) X
    (infinityComponentPolynomial P) (by rw [infinityBranchPolynomial_zero]; simp)

/-- Restriction to the negative component in the actual reciprocal chart. -/
def infinityNegativeComponent (P : k[X]) :
    AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0) →ₐ[k] k[X] :=
  AlgebraicGeometry.Hyperelliptic.eval (infinityBranchPolynomial P 0) X
    (-infinityComponentPolynomial P) (by rw [infinityBranchPolynomial_zero]; simp)

@[simp] theorem finitePositiveComponent_apply (P : k[X])
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)) :
    finitePositiveComponent P z = z.re + z.im * finiteComponentPolynomial P := by
  simp [finitePositiveComponent, AlgebraicGeometry.Hyperelliptic.eval_apply]

@[simp] theorem finiteNegativeComponent_apply (P : k[X])
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)) :
    finiteNegativeComponent P z = z.re - z.im * finiteComponentPolynomial P := by
  simp [finiteNegativeComponent, AlgebraicGeometry.Hyperelliptic.eval_apply]
  ring

@[simp] theorem infinityPositiveComponent_apply (P : k[X])
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)) :
    infinityPositiveComponent P z = z.re + z.im * infinityComponentPolynomial P := by
  simp [infinityPositiveComponent, AlgebraicGeometry.Hyperelliptic.eval_apply]

@[simp] theorem infinityNegativeComponent_apply (P : k[X])
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)) :
    infinityNegativeComponent P z = z.re - z.im * infinityComponentPolynomial P := by
  simp [infinityNegativeComponent, AlgebraicGeometry.Hyperelliptic.eval_apply]
  ring

@[simp] theorem finitePositiveComponent_coordinate (P : k[X]) :
    finitePositiveComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0)) X) = X := by
  unfold finitePositiveComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_coordinate _ _ _ _

@[simp] theorem finitePositiveComponent_generator (P : k[X]) :
    finitePositiveComponent P QuadraticAlgebra.omega = finiteComponentPolynomial P := by
  unfold finitePositiveComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_generator _ _ _ _

@[simp] theorem finiteNegativeComponent_coordinate (P : k[X]) :
    finiteNegativeComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0)) X) = X := by
  unfold finiteNegativeComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_coordinate _ _ _ _

@[simp] theorem finiteNegativeComponent_generator (P : k[X]) :
    finiteNegativeComponent P QuadraticAlgebra.omega = -finiteComponentPolynomial P := by
  unfold finiteNegativeComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_generator _ _ _ _

@[simp] theorem infinityPositiveComponent_coordinate (P : k[X]) :
    infinityPositiveComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0)) X) = X := by
  unfold infinityPositiveComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_coordinate _ _ _ _

@[simp] theorem infinityPositiveComponent_generator (P : k[X]) :
    infinityPositiveComponent P QuadraticAlgebra.omega = infinityComponentPolynomial P := by
  unfold infinityPositiveComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_generator _ _ _ _

@[simp] theorem infinityNegativeComponent_coordinate (P : k[X]) :
    infinityNegativeComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0)) X) = X := by
  unfold infinityNegativeComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_coordinate _ _ _ _

@[simp] theorem infinityNegativeComponent_generator (P : k[X]) :
    infinityNegativeComponent P QuadraticAlgebra.omega = -infinityComponentPolynomial P := by
  unfold infinityNegativeComponent
  exact AlgebraicGeometry.Hyperelliptic.eval_generator _ _ _ _

@[simp] theorem finitePositiveComponent_base (P f : k[X]) :
    finitePositiveComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0)) f) = f := by
  unfold finitePositiveComponent
  rw [AlgebraicGeometry.Hyperelliptic.algHom_algebraMap]
  simp

@[simp] theorem finiteNegativeComponent_base (P f : k[X]) :
    finiteNegativeComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0)) f) = f := by
  unfold finiteNegativeComponent
  rw [AlgebraicGeometry.Hyperelliptic.algHom_algebraMap]
  simp

@[simp] theorem infinityPositiveComponent_base (P f : k[X]) :
    infinityPositiveComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0)) f) = f := by
  unfold infinityPositiveComponent
  rw [AlgebraicGeometry.Hyperelliptic.algHom_algebraMap]
  simp

@[simp] theorem infinityNegativeComponent_base (P f : k[X]) :
    infinityNegativeComponent P
      (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0)) f) = f := by
  unfold infinityNegativeComponent
  rw [AlgebraicGeometry.Hyperelliptic.algHom_algebraMap]
  simp

/-- The two finite components meet exactly over the zeros of `X * P`. -/
theorem finiteComponents_meet_iff (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k) :
    (finiteComponentPolynomial P).eval x =
      -(finiteComponentPolynomial P).eval x ↔ x = 0 ∨ P.eval x = 0 := by
  rw [eq_neg_iff_add_eq_zero, ← two_mul]
  rw [mul_eq_zero]
  simp only [h2, false_or]
  simp [finiteComponentPolynomial, mul_eq_zero]

/-- Monicity makes the two components disjoint at the reciprocal origin. -/
theorem infinityComponentPolynomial_eval_zero (P : k[X]) (hP : P.Monic) :
    (infinityComponentPolynomial P).eval 0 = 1 := by
  simpa only [infinityComponentPolynomial, ← coeff_zero_eq_eval_zero,
    coeff_zero_reverse] using hP.leadingCoeff

theorem infinityComponents_disjoint_at_zero (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    (infinityComponentPolynomial P).eval 0 ≠
      -(infinityComponentPolynomial P).eval 0 := by
  rw [infinityComponentPolynomial_eval_zero P hP]
  intro h
  have : (2 : k) = 0 := by linear_combination h
  exact h2 this

end HilbertModularity.Hyperelliptic
