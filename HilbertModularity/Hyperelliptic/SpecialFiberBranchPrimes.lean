/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingPrime
public import HilbertModularity.Hyperelliptic.SpecialFiberCrossings
public import Mathlib.RingTheory.Polynomial.Ideal

/-! # Prime ideals over the finite branch divisor

For a split branch polynomial, every prime of the actual quadratic chart above
its zero divisor is one of the rational crossing primes. This exhausts the
finite-chart points where the two signed components can meet.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- A prime above a rational branch root is the corresponding crossing prime
of the actual quadratic chart. -/
theorem finiteCrossingPrime_eq_of_base_factor
    (P : k[X]) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0)
    (q : Ideal (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)))
    (hq : q.IsPrime)
    (hfactor : algebraMap k[X] _ (X - C x) ∈ q) :
    q = RingHom.ker (finiteCrossingEvaluation P x).toRingHom := by
  let A := AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)
  have hbase : RingHom.ker (evalRingHom x) ≤ Ideal.comap (algebraMap k[X] A) q := by
    rw [Polynomial.ker_evalRingHom]
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact hfactor
  have hH : algebraMap k[X] A (finiteComponentPolynomial P) ∈ q :=
    hbase (by change (finiteComponentPolynomial P).eval x = 0; exact hx)
  have hw : (QuadraticAlgebra.omega : A) ∈ q := by
    have hsq : (QuadraticAlgebra.omega : A) ^ 2 =
        (algebraMap k[X] A (finiteComponentPolynomial P)) ^ 2 := by
      rw [AlgebraicGeometry.DoubleCover.chartGenerator_sq]
      simp only [A, finiteBranchPolynomial_zero, map_pow]
    exact hq.mem_of_pow_mem 2 (hsq.symm ▸ q.pow_mem_of_mem hH 2 (by decide))
  have hle : RingHom.ker (finiteCrossingEvaluation P x).toRingHom ≤ q := by
    intro z hz
    have hre : algebraMap k[X] A z.re ∈ q :=
      hbase (by simpa [RingHom.mem_ker] using
        (mem_finiteCrossingPrime_iff P x hx z).mp hz)
    have hzdecomp : z = algebraMap k[X] A z.re +
        algebraMap k[X] A z.im * QuadraticAlgebra.omega := by
      simpa only [Algebra.smul_def, mul_one] using
        (QuadraticAlgebra.re_smul_add_im_smul z).symm
    rw [hzdecomp]
    exact q.add_mem hre (q.mul_mem_left _ hw)
  exact ((finiteCrossingPrime_isMaximal P x).eq_of_le hq.ne_top hle).symm

/-- Every prime of the finite chart containing the split branch polynomial
is the rational crossing prime at one of its listed zeros. -/
theorem finiteBranchPrimes_eq_crossings [DecidableEq k] (P : k[X]) (S : Finset k)
    (hP : P = ∏ x ∈ S, (X - C x))
    (q : Ideal (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)))
    (hq : q.IsPrime)
    (hbranch : algebraMap k[X] _ (finiteComponentPolynomial P) ∈ q) :
    ∃ x ∈ insert 0 S,
      q = RingHom.ker (finiteCrossingEvaluation P x).toRingHom := by
  classical
  let A := AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)
  let J : Ideal k[X] := Ideal.comap (algebraMap k[X] A) q
  let : J.IsPrime := hq.comap _
  have hJ : splitFiniteBranchPolynomial S ∈ J := by
    change (algebraMap k[X] A) (splitFiniteBranchPolynomial S) ∈ q
    rw [← finiteComponentPolynomial_eq_split P S hP]
    exact hbranch
  have hprod : (X : k[X]) ∈ J ∨ ∃ x ∈ S, X - C x ∈ J := by
    have h := (show J.IsPrime from inferInstance).mem_or_mem
      (show X * ∏ x ∈ S, (X - C x) ∈ J by
        simpa only [splitFiniteBranchPolynomial_eq] using hJ)
    rcases h with hX | hrest
    · exact Or.inl hX
    · exact Or.inr ((Ideal.IsPrime.prod_mem_iff (p := J)).mp hrest)
  rcases hprod with hX | ⟨x, hxS, hxJ⟩
  · refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
    apply finiteCrossingPrime_eq_of_base_factor P 0
    · rw [finiteComponentPolynomial_eq_split P S hP]
      exact (splitFiniteBranchPolynomial_root_iff S 0).mpr (Or.inl rfl)
    · exact hq
    · change (algebraMap k[X] A) X ∈ q at hX
      simpa only [C_0, sub_zero] using hX
  · refine ⟨x, Finset.mem_insert_of_mem hxS, ?_⟩
    apply finiteCrossingPrime_eq_of_base_factor P x
    · rw [finiteComponentPolynomial_eq_split P S hP]
      exact (splitFiniteBranchPolynomial_root_iff S x).mpr (Or.inr hxS)
    · exact hq
    · exact hxJ

end HilbertModularity.Hyperelliptic
