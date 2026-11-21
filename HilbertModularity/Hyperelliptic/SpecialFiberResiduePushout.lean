/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberBranchPushout
public import HilbertModularity.Hyperelliptic.SpecialFiberResidue

/-! # Gluing algebra of the cyclotomic special fibre

The finite chart of the actual scaled residue cover is the fibre product of
its signed component rings along the finite intersection scheme. The latter
is a product of rational residue fields by the separate CRT certificate.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable (p : ℕ) [Fact p.Prime]

/-- The reduced scaled-root polynomial is monic, so its finite-chart branch
polynomial is nonzero. -/
theorem reducedLocalScaledPolynomial_monic :
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)).Monic := by
  rw [localScaledRootPolynomial_reduction_split]
  exact monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

/-- The actual finite chart is the pullback of its two polynomial component
rings over the quotient by their common intersection polynomial. -/
def reducedLocalFiniteChartPushoutEquiv (h2 : (2 : ZMod p) ≠ 0) :
    AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)) 0) ≃+*
      congruentComponentPairs (finiteComponentPolynomial
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p))) :=
  finiteSpecialFiberChartPushoutEquiv _ (reducedLocalScaledPolynomial_monic p) h2

end HilbertModularity.Hyperelliptic
