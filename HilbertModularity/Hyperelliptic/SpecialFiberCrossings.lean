/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberComponents
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Local crossing equations of the square-branch fibre

The square-branch chart factors as two branches. At a simple zero of its
branch polynomial, division by `X - C x` gives a factor with nonzero value at
`x`. These are algebraic certificates for a transverse crossing; identifying
the completed local ring as a node is a separate scheme-theoretic step.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The two equations of the components multiply to zero in the actual chart. -/
theorem component_crossing_equation (H : k[X]) :
    ((QuadraticAlgebra.omega : SquareBranchRing H) -
      algebraMap k[X] (SquareBranchRing H) H) *
      ((QuadraticAlgebra.omega : SquareBranchRing H) +
      algebraMap k[X] (SquareBranchRing H) H) = 0 := by
  calc
    _ = (QuadraticAlgebra.omega : SquareBranchRing H) ^ 2 -
        (algebraMap k[X] (SquareBranchRing H) H) ^ 2 := by ring
    _ = 0 := by
      rw [AlgebraicGeometry.DoubleCover.chartGenerator_sq, map_pow]
      exact sub_self _

/-- At a root, the branch polynomial is the coordinate parameter times its quotient. -/
theorem branch_factor_at_root (H : k[X]) (x : k) (hx : H.eval x = 0) :
    H = (X - C x) * (H /ₘ (X - C x)) := by
  exact (mul_divByMonic_eq_iff_isRoot.mpr hx).symm

/-- The quotient factor takes the derivative value at the root. -/
theorem branch_quotient_eval (H : k[X]) (x : k) :
    (H /ₘ (X - C x)).eval x = H.derivative.eval x := by
  have h := congrArg (eval x)
    (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative H x)
  simpa using h

/-- A simple zero makes the second factor a unit in the local ring at the zero. -/
theorem branch_quotient_eval_ne_zero (H : k[X]) (x : k)
    (hx : H.derivative.eval x ≠ 0) :
    (H /ₘ (X - C x)).eval x ≠ 0 := by
  simpa only [branch_quotient_eval] using hx

/-- The finite-chart crossing equation is the one for the scaled cover. -/
theorem finite_component_crossing_equation (P : k[X]) :
    ((QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0)) -
      algebraMap k[X] _ (finiteComponentPolynomial P)) *
      ((QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0)) +
      algebraMap k[X] _ (finiteComponentPolynomial P)) = 0 := by
  rw [finiteBranchPolynomial_zero]
  exact component_crossing_equation (finiteComponentPolynomial P)

/-- The split branch polynomial with the additional zero root. -/
def splitFiniteBranchPolynomial (S : Finset k) : k[X] :=
  X * ∏ x ∈ S, (X - C x)

theorem splitFiniteBranchPolynomial_eq (S : Finset k) :
    splitFiniteBranchPolynomial S = X * ∏ x ∈ S, (X - C x) := (rfl)

/-- The finite intersections are exactly the origin and the listed roots. -/
theorem splitFiniteBranchPolynomial_root_iff (S : Finset k) (x : k) :
    (splitFiniteBranchPolynomial S).eval x = 0 ↔ x = 0 ∨ x ∈ S := by
  classical
  simp [splitFiniteBranchPolynomial, eval_mul, eval_prod,
    Finset.prod_eq_zero_iff, sub_eq_zero]

/-- At a listed root, the derivative is the product of all nonzero differences. -/
theorem splitFiniteBranchPolynomial_derivative_at_root (S : Finset k)
    [DecidableEq k]
    {x : k} (hx : x ∈ S) :
    (splitFiniteBranchPolynomial S).derivative.eval x =
      x * ∏ y ∈ S.erase x, (x - y) := by
  classical
  have hf : splitFiniteBranchPolynomial S =
      X * (X - C x) * ∏ y ∈ S.erase x, (X - C y) := by
    simp only [splitFiniteBranchPolynomial, ← Finset.mul_prod_erase S
      (fun y => X - C y) hx]
    ring
  rw [hf]
  simp [derivative_mul, eval_mul, eval_prod]

/-- Every listed nonzero root is simple when the labels are distinct. -/
theorem splitFiniteBranchPolynomial_derivative_ne_zero (S : Finset k)
    [DecidableEq k]
    {x : k} (hx : x ∈ S) (hx0 : x ≠ 0) :
    (splitFiniteBranchPolynomial S).derivative.eval x ≠ 0 := by
  rw [splitFiniteBranchPolynomial_derivative_at_root S hx]
  apply mul_ne_zero hx0
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  exact sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hy))

/-- The additional root at zero is simple when none of the listed roots is zero. -/
theorem splitFiniteBranchPolynomial_derivative_at_zero (S : Finset k)
    (hzero : 0 ∉ S) :
    (splitFiniteBranchPolynomial S).derivative.eval 0 ≠ 0 := by
  classical
  simp only [splitFiniteBranchPolynomial, derivative_mul, derivative_X,
    one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero]
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (by
    intro h
    exact hzero (h.symm ▸ hy))

/-- All finite crossings are simple under the nonzero, distinct-root hypothesis. -/
theorem splitFiniteBranchPolynomial_simple_roots (S : Finset k)
    (hzero : 0 ∉ S) {x : k}
    (hx : (splitFiniteBranchPolynomial S).eval x = 0) :
    (splitFiniteBranchPolynomial S).derivative.eval x ≠ 0 := by
  classical
  rcases (splitFiniteBranchPolynomial_root_iff S x).mp hx with rfl | hmem
  · exact splitFiniteBranchPolynomial_derivative_at_zero S hzero
  · exact splitFiniteBranchPolynomial_derivative_ne_zero S hmem
      (fun h => hzero (h ▸ hmem))

/-- There is one finite crossing for each split root, plus the origin. -/
theorem splitFiniteBranchPolynomial_crossing_count (S : Finset k)
    [DecidableEq k] (hzero : 0 ∉ S) : (insert (0 : k) S).card = S.card + 1 := by
  simp [hzero]

/-- The actual finite-chart branch is the split polynomial when `P` has this factorization. -/
theorem finiteComponentPolynomial_eq_split (P : k[X]) (S : Finset k)
    (hP : P = ∏ x ∈ S, (X - C x)) :
    finiteComponentPolynomial P = splitFiniteBranchPolynomial S := by
  simp only [finiteComponentPolynomial_eq, splitFiniteBranchPolynomial, hP]

/-- Simple listed roots give the local crossing parameter in the actual finite chart. -/
theorem finiteComponentPolynomial_simple_roots (P : k[X]) (S : Finset k)
    (hP : P = ∏ x ∈ S, (X - C x)) (hzero : 0 ∉ S) {x : k}
    (hx : (finiteComponentPolynomial P).eval x = 0) :
    (finiteComponentPolynomial P).derivative.eval x ≠ 0 := by
  rw [finiteComponentPolynomial_eq_split P S hP] at hx ⊢
  exact splitFiniteBranchPolynomial_simple_roots S hzero hx

end HilbertModularity.Hyperelliptic
