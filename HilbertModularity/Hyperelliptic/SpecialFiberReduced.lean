/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCharts
public import Mathlib.AlgebraicGeometry.Properties

/-! # Reducedness of the square-branch affine fibre

The two branch evaluations embed the quadratic chart into a product of
polynomial rings when the square root is nonzero and the characteristic is
not two.  This detects nilpotents and proves the affine chart is reduced.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The square-branch affine ring is reduced when its branch polynomial is nonzero. -/
theorem squareBranchRing_isReduced (H : k[X]) (hH : H ≠ 0) (h2 : (2 : k) ≠ 0) :
    IsReduced (SquareBranchRing H) := by
  constructor
  intro x hx
  apply componentPair_injective H hH h2
  have hn : IsNilpotent (componentPair H x) := hx.map (componentPair H).toRingHom
  simpa using (IsReduced.eq_zero _ hn)

/-- The actual glued square-branch special fibre is reduced.  Both standard charts
are reduced, and their open immersions cover the glued double cover. -/
theorem scaledDoubleCover_zero_isReduced (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    AlgebraicGeometry.IsReduced (scaledDoubleCover P 0) := by
  have hfinite : finiteComponentPolynomial P ≠ 0 := by
    rw [finiteComponentPolynomial_eq]
    exact mul_ne_zero X_ne_zero hP.ne_zero
  have hinfinity : infinityComponentPolynomial P ≠ 0 := by
    intro h
    have hv := infinityComponentPolynomial_eval_zero P hP
    rw [h] at hv
    simp at hv
  let : IsReduced (AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial P 0)) := by
    rw [finiteBranchPolynomial_zero]
    exact squareBranchRing_isReduced (finiteComponentPolynomial P) hfinite h2
  let : IsReduced (AlgebraicGeometry.DoubleCover.ChartRing
      (infinityBranchPolynomial P 0)) := by
    rw [infinityBranchPolynomial_zero]
    exact squareBranchRing_isReduced (infinityComponentPolynomial P) hinfinity h2
  have : ∀ b,
      AlgebraicGeometry.IsReduced
        ((AlgebraicGeometry.DoubleCover.openCover (finiteBranchPolynomial P 0)
          (infinityBranchPolynomial P 0) (P.natDegree + 1)
          (branch_transition P 0)).X b) := by
    intro b
    cases b <;> dsimp [AlgebraicGeometry.DoubleCover.openCover] <;> infer_instance
  exact AlgebraicGeometry.IsReduced.of_openCover _
    (AlgebraicGeometry.DoubleCover.openCover (finiteBranchPolynomial P 0)
      (infinityBranchPolynomial P 0) (P.natDegree + 1) (branch_transition P 0))

end HilbertModularity.Hyperelliptic
