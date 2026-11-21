/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossings
public import HilbertModularity.NumberTheory.RealCyclotomicResidue

/-! # The cyclotomic special-fibre branch polynomial

The actual local scaled-root polynomial reduces to the product whose roots
are the squares of the half-interval indices. This connects the finite-chart
crossing certificates to the chosen cyclotomic prime.
-/

public noncomputable section

open Polynomial Finset
open scoped NumberField

namespace HilbertModularity.Hyperelliptic


variable (p : ℕ) [Fact p.Prime]

/-- The distinct nonzero roots in the actual cyclotomic residue field. -/
def residueRootSet : Finset (ZMod p) :=
  (Icc 1 ((p - 1) / 2)).image (fun j : ℕ => (j : ZMod p) ^ 2)

theorem residueSquare_injOn :
    Set.InjOn (fun j : ℕ => (j : ZMod p) ^ 2)
      (Icc 1 ((p - 1) / 2) : Finset ℕ) := by
  intro i hi j hj he
  have hi' : i ∈ Set.Icc 0 ((p - 1) / 2) := by
    have h := Finset.mem_Icc.mp hi
    exact ⟨by omega, h.2⟩
  have hj' : j ∈ Set.Icc 0 ((p - 1) / 2) := by
    have h := Finset.mem_Icc.mp hj
    exact ⟨by omega, h.2⟩
  exact Cyclotomic.realLocalReduction_localScaledRoot_injOn p hi' hj'
    (by simpa only [Cyclotomic.realLocalReduction_localScaledRoot] using he)

/-- The actual scaled-root polynomial reduces to the indexed square-root product. -/
theorem localScaledRootPolynomial_reduction :
    (localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p) =
      ∏ j ∈ Icc 1 ((p - 1) / 2),
        (X - C ((j : ZMod p) ^ 2)) := by
  simp only [localScaledRootPolynomial, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C,
    Cyclotomic.realLocalReduction_localScaledRoot]

/-- The reduced actual polynomial is indexed by its distinct residue roots. -/
theorem localScaledRootPolynomial_reduction_split :
    (localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p) =
      ∏ x ∈ residueRootSet p, (X - C x) := by
  rw [localScaledRootPolynomial_reduction]
  change (∏ j ∈ Icc 1 ((p - 1) / 2), (X - C ((j : ZMod p) ^ 2))) =
    ∏ x ∈ (Icc 1 ((p - 1) / 2)).image (fun j : ℕ => (j : ZMod p) ^ 2),
      (X - C x)
  exact (Finset.prod_image (s := Icc 1 ((p - 1) / 2))
    (f := fun x : ZMod p => (X - C x : (ZMod p)[X]))
    (g := fun j : ℕ => (j : ZMod p) ^ 2) (residueSquare_injOn p)).symm

/-- None of the scaled cyclotomic roots reduces to the extra root at zero. -/
theorem zero_not_mem_residueRootSet : (0 : ZMod p) ∉ residueRootSet p := by
  intro h
  rcases Finset.mem_image.mp h with ⟨j, hj, hj0⟩
  have h0' : (0 : ℕ) ∈ Set.Icc 0 ((p - 1) / 2) := by simp
  have hj' : j ∈ Set.Icc 0 ((p - 1) / 2) := by
    have hji := Finset.mem_Icc.mp hj
    exact ⟨by omega, hji.2⟩
  have heq : ((0 : ℕ) : ZMod p) ^ 2 = (j : ZMod p) ^ 2 := by
    simpa using hj0.symm
  have := Cyclotomic.realLocalReduction_localScaledRoot_injOn p h0' hj'
    (by simpa only [Cyclotomic.realLocalReduction_localScaledRoot] using heq)
  have hj1 := (Finset.mem_Icc.mp hj).1
  omega

/-- There are `(p-1)/2` distinct nonzero residue roots for an odd prime. -/
theorem residueRootSet_card (_hp : 3 ≤ p) :
    (residueRootSet p).card = (p - 1) / 2 := by
  classical
  unfold residueRootSet
  rw [Finset.card_image_iff.mpr (residueSquare_injOn p)]
  simp

/-- The finite chart has one extra crossing over zero. -/
theorem reducedLocalFiniteComponent_crossing_count (hp : 3 ≤ p) :
    (insert (0 : ZMod p) (residueRootSet p)).card =
      (p - 1) / 2 + 1 := by
  rw [splitFiniteBranchPolynomial_crossing_count (residueRootSet p)
    (zero_not_mem_residueRootSet p), residueRootSet_card p hp]

/-- The actual finite-chart polynomial has only simple roots after reduction. -/
theorem reducedLocalFiniteComponent_simple_roots {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0) :
    (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).derivative.eval x ≠ 0 := by
  apply finiteComponentPolynomial_simple_roots _ (residueRootSet p)
    (localScaledRootPolynomial_reduction_split p)
    (zero_not_mem_residueRootSet p) hx

end HilbertModularity.Hyperelliptic
