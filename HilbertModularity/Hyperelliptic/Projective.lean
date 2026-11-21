/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.DoubleCover
public import HilbertModularity.Hyperelliptic.Scaling
public import Mathlib.Algebra.Polynomial.Homogenize

/-! # The projective scaled double cover

The affine branch equation is `w² = u²P(u)² - 4Tu`. The reciprocal chart uses
`z = u⁻¹` and `w∞ = u^(-(d+1))w`, as in [TripathiGoswami], with
`d = P.natDegree`. The exact binary section is homogeneous of degree `2d+2`,
and both dehomogenizations are proved. The relative spectrum is constructed
by gluing its two free quadratic algebras; the generic double-cover API
proves that these are the pullbacks over the standard affine charts of `P¹`.
The construction works over any commutative ring and for every parameter.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial LaurentPolynomial

namespace Polynomial

/-- The reciprocal chart of a homogenized polynomial is its degree-indexed reflection. -/
theorem aeval_homogenize_one_X {R : Type*} [CommRing R]
    (P : R[X]) {n : ℕ} (hn : P.natDegree ≤ n) :
    MvPolynomial.aeval ![1, X] (P.homogenize n) = P.reflect n := by
  apply Polynomial.induction_with_natDegree_le
    (fun Q : R[X] => MvPolynomial.aeval ![1, X] (Q.homogenize n) = Q.reflect n) (N := n)
  · simp
  · intro k r hr hk
    simp [homogenize_C_mul, homogenize_X_pow hk, revAt_le hk]
  · intro Q S hdeg hbound hQ hS
    simp [hQ, hS, reflect_add]
  · exact hn

end Polynomial

namespace HilbertModularity.Hyperelliptic

variable {R : Type*} [CommRing R]

/-- Branch polynomial in the finite-coordinate chart. -/
def finiteBranchPolynomial (P : R[X]) (t : R) : R[X] :=
  X ^ 2 * P ^ 2 - Polynomial.C (4 * t) * X

/-- Branch polynomial in the reciprocal-coordinate chart. -/
def infinityBranchPolynomial (P : R[X]) (t : R) : R[X] :=
  P.reverse ^ 2 - Polynomial.C (4 * t) * X ^ (2 * P.natDegree + 1)

/-- The branch equations differ by the square of the line-bundle transition. -/
theorem branch_transition (P : R[X]) (t : R) :
    invert (toLaurent (infinityBranchPolynomial P t)) =
      T (-((P.natDegree + 1 : ℕ) : ℤ)) ^ 2 * toLaurent (finiteBranchPolynomial P t) := by
  simp only [finiteBranchPolynomial, infinityBranchPolynomial, map_sub, map_mul, map_pow,
    toLaurent_C, toLaurent_X, toLaurent_reverse, invert_C, invert_T]
  rw [involutive_invert (toLaurent P)]
  simp only [T_pow, mul_sub, ← mul_assoc]
  simp only [mul_assoc, ← T_add]
  ring_nf
  rw [T_pow, mul_T_assoc]
  push_cast
  ring_nf

/-- The binary branch section `U²P_h(U,Z)² - 4tUZ^(2d+1)`. -/
def branchSection (P : R[X]) (t : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 ^ 2 * P.homogenize P.natDegree ^ 2 -
    MvPolynomial.C (4 * t) * MvPolynomial.X 0 *
      MvPolynomial.X 1 ^ (2 * P.natDegree + 1)

/-- The branch section has the degree required to multiply the square of `O(-d-1)`. -/
theorem branchSection_isHomogeneous (P : R[X]) (t : R) :
    (branchSection P t).IsHomogeneous (2 * (P.natDegree + 1)) := by
  apply MvPolynomial.IsHomogeneous.sub
  · convert (MvPolynomial.isHomogeneous_X R (0 : Fin 2)).pow 2 |>.mul
      ((P.isHomogeneous_homogenize).pow 2) using 1; omega
  · convert ((MvPolynomial.isHomogeneous_C (Fin 2) (4 * t)).mul
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2))).mul
      ((MvPolynomial.isHomogeneous_X R (1 : Fin 2)).pow (2 * P.natDegree + 1))
      using 1; omega

/-- On `Z = 1` the binary section is exactly the finite branch polynomial. -/
theorem branchSection_finite (P : R[X]) (t : R) :
    MvPolynomial.aeval ![X, 1] (branchSection P t) = finiteBranchPolynomial P t := by
  simp [branchSection, finiteBranchPolynomial]

/-- On `U = 1` the binary section is exactly the reciprocal branch polynomial. -/
theorem branchSection_infinity (P : R[X]) (t : R) :
    MvPolynomial.aeval ![1, X] (branchSection P t) = infinityBranchPolynomial P t := by
  simp [branchSection, infinityBranchPolynomial, Polynomial.aeval_homogenize_one_X,
    Polynomial.reverse]

/-- The scaled double cover with both affine charts glued by the transition of `O(-d-1)`. -/
abbrev scaledDoubleCover (P : R[X]) (t : R) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.DoubleCover.scheme (finiteBranchPolynomial P t)
    (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t)

/-- The scaled double cover projected to the projective line. -/
def scaledDoubleCoverProjection (P : R[X]) (t : R) :
    scaledDoubleCover P t ⟶ AlgebraicGeometry.ProjectiveLine R :=
  AlgebraicGeometry.DoubleCover.toProjectiveLine (finiteBranchPolynomial P t)
    (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t)

/-- The scaled projection restricted to its finite quadratic chart. -/
theorem finiteChart_scaledDoubleCoverProjection (P : R[X]) (t : R) :
    AlgebraicGeometry.DoubleCover.finiteChart (finiteBranchPolynomial P t)
        (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t) ≫
      scaledDoubleCoverProjection P t =
    AlgebraicGeometry.DoubleCover.finiteProjection (finiteBranchPolynomial P t) := by
  exact AlgebraicGeometry.DoubleCover.finiteChart_toProjectiveLine _ _ _ _

/-- The scaled projection restricted to its reciprocal quadratic chart. -/
theorem infinityChart_scaledDoubleCoverProjection (P : R[X]) (t : R) :
    AlgebraicGeometry.DoubleCover.infinityChart (finiteBranchPolynomial P t)
        (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t) ≫
      scaledDoubleCoverProjection P t =
    AlgebraicGeometry.DoubleCover.infinityProjection (infinityBranchPolynomial P t) := by
  exact AlgebraicGeometry.DoubleCover.infinityChart_toProjectiveLine _ _ _ _

/-- The finite chart structure map factors through its affine projection. -/
theorem finiteChart_scaledDoubleCoverProjection_toSpec (P : R[X]) (t : R) :
    AlgebraicGeometry.DoubleCover.finiteChart (finiteBranchPolynomial P t)
        (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t) ≫
      (scaledDoubleCoverProjection P t ≫ AlgebraicGeometry.ProjectiveLine.toSpec R) =
    AlgebraicGeometry.DoubleCover.finiteProjection (finiteBranchPolynomial P t) ≫
      AlgebraicGeometry.ProjectiveLine.toSpec R := by
  exact (CategoryTheory.Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ AlgebraicGeometry.ProjectiveLine.toSpec R)
      (finiteChart_scaledDoubleCoverProjection P t))

/-- The reciprocal chart structure map factors through its affine projection. -/
theorem infinityChart_scaledDoubleCoverProjection_toSpec (P : R[X]) (t : R) :
    AlgebraicGeometry.DoubleCover.infinityChart (finiteBranchPolynomial P t)
        (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t) ≫
      (scaledDoubleCoverProjection P t ≫ AlgebraicGeometry.ProjectiveLine.toSpec R) =
    AlgebraicGeometry.DoubleCover.infinityProjection (infinityBranchPolynomial P t) ≫
      AlgebraicGeometry.ProjectiveLine.toSpec R := by
  exact (CategoryTheory.Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ AlgebraicGeometry.ProjectiveLine.toSpec R)
      (infinityChart_scaledDoubleCoverProjection P t))

/-- The scaled projection is the map from its defining two-chart cover. -/
theorem scaledDoubleCoverProjection_eq (P : R[X]) (t : R) :
    scaledDoubleCoverProjection P t =
      AlgebraicGeometry.DoubleCover.toProjectiveLine (finiteBranchPolynomial P t)
        (infinityBranchPolynomial P t) (P.natDegree + 1) (branch_transition P t) :=
  (rfl)

end HilbertModularity.Hyperelliptic
