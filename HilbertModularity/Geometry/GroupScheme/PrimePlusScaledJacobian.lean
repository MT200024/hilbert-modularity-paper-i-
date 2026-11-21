/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.PlusCurveModelComparison
public import HilbertModularity.Geometry.DoubleCoverCurve

/-! # The scaled model has the selected plus Jacobian

The change of affine coordinates extends across the smooth proper generic
fibre. Its pointed Jacobian is the fibre of the *same* prime plus family that
carries the integral real multiplication and tensor-Tate triple. -/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry HilbertModularity.Cyclotomic
  HilbertModularity.Hyperelliptic

namespace HilbertModularity.Hypergeometric

private theorem finiteBranchPolynomial_natDegree_pos
    {K : Type*} [Field K] (P : K[X]) (t : K) (ht : t ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    0 < (finiteBranchPolynomial P t).natDegree := by
  have h4 : (4 : K) ≠ 0 := by
      convert mul_ne_zero h2 h2 using 1; ring
  have hc : (finiteBranchPolynomial P t).coeff 1 = -(4 * t) := by
    simp [finiteBranchPolynomial,
      Polynomial.coeff_sub,
      Polynomial.coeff_X_pow_mul']
  have hne : (finiteBranchPolynomial P t).coeff 1 ≠ 0 := by
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero h4 ht)
  exact lt_of_lt_of_le (by omega : 0 < 1)
    (Polynomial.le_natDegree_of_ne_zero hne)

/-- An isomorphism of the actual proper scaled curve with the plus curve
identifies the selected arithmetic fibre as its pointed Jacobian. This is
the direct interface for a model certificate that supplies the generic-fibre
isomorphism, independently of how that certificate is proved. -/
def primePlusScaledFiberJacobianOfIso (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (e : Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
        (ξ.val / (2 - tau p 1) ^ p)) ≅
      Over.mk (plusCurveToSpec p (primePlusData p hp).p_odd ξ.val)) :
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          (ξ.val / (2 - tau p 1) ^ p)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          (ξ.val / (2 - tau p 1) ^ p))) b
        (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) :=
  ⟨plusBranchOver p (primePlusData p hp).p_odd ξ.val ≫ e.inv,
    (primePlusRationalFiberJacobian p hp ξ).transport e⟩

/-- The selected arithmetic family's fibre is the pointed Jacobian of the
printed scaled curve. Generic smoothness and integrality follow from the
squarefree branch equations; neither claims regularity of an integral model.
The distinguished scaled point is the
inverse image of the branch point under the unique extended curve isomorphism.
The comparison is obtained from the affine substitution and the standard
smooth-proper curve extension theorem; no new arithmetic input is used. -/
def primePlusRealScaledFiberJacobian (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          (ξ.val / (2 - tau p 1) ^ p)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          (ξ.val / (2 - tau p 1) ^ p))) b
        (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  let t : realCyclotomicField p := ξ.val / (2 - tau p 1) ^ p
  have ht : t ≠ 0 := div_ne_zero ξ.property.1
    (pow_ne_zero _ (realCyclotomicScale_ne_zero p))
  have h2 : (2 : realCyclotomicField p) ≠ 0 := by norm_num
  have hscaled := AlgebraicGeometry.DoubleCover.integral_and_smoothOfRelativeDimension_one
    (finiteBranchPolynomial (realScaledRootPolynomial p) t)
    (infinityBranchPolynomial (realScaledRootPolynomial p) t)
    ((realScaledRootPolynomial p).natDegree + 1)
    (branch_transition (realScaledRootPolynomial p) t)
    (realScaledFiniteBranch_separable p hp ξ.val ξ.property.1 ξ.property.2)
    (realScaledInfinityBranch_separable p hp ξ.val ξ.property.1 ξ.property.2)
    (finiteBranchPolynomial_natDegree_pos (realScaledRootPolynomial p) t ht h2) h2
  letI : IsIntegral (scaledDoubleCover (realScaledRootPolynomial p) t) :=
    hscaled.1
  letI : SmoothOfRelativeDimension 1
      (scaledModelToSpec (realScaledRootPolynomial p) t) := by
    rw [scaledModelToSpec_eq]
    exact hscaled.2
  have hplus := AlgebraicGeometry.DoubleCover.integral_and_smoothOfRelativeDimension_one
    (plusPolynomial p ξ.val) (plusPolynomial p ξ.val).reverse
    ((p + 1) / 2)
    (AlgebraicGeometry.Hyperelliptic.reverse_transition _ _
      (plusPolynomial_evenDegree p (primePlusData p hp).p_odd ξ.val))
    (plusPolynomial_separable p (primePlusData p hp).p_odd h2
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      ξ.val ξ.property.1 ξ.property.2)
    (plusPolynomial_separable p (primePlusData p hp).p_odd h2
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      ξ.val ξ.property.1 ξ.property.2).reverse
    (by rw [plusPolynomial_evenDegree p (primePlusData p hp).p_odd ξ.val]
        omega) h2
  letI : IsIntegral (plusCurve p (primePlusData p hp).p_odd ξ.val) := hplus.1
  let e := Classical.choose (exists_realScaledModelIso_plusCurve p hp ξ.val
    ξ.property.1 ξ.property.2)
  have he := (Classical.choose_spec (exists_realScaledModelIso_plusCurve p hp ξ.val
    ξ.property.1 ξ.property.2)).1
  let eo : Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
      (ξ.val / (2 - tau p 1) ^ p)) ≅
      Over.mk (plusCurveToSpec p (primePlusData p hp).p_odd ξ.val) :=
    Over.isoMk e he
  exact primePlusScaledFiberJacobianOfIso p hp ξ eo

end HilbertModularity.Hypergeometric
