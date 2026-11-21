/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberBranchPrimes
public import HilbertModularity.Hyperelliptic.SpecialFiberAwaySplit

/-! # Prime strata of the square-branch special fibre

At every point away from the branch divisor exactly one signed branch equation
vanishes. Over a split finite branch divisor the remaining primes are precisely
the rational crossings. This is the pointwise algebraic part of the assertion
that the special fibre has no other component intersections; smoothness and
the completed local node criterion are separate statements.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Two factors of a split quadratic equation select exactly one branch at a
prime outside their common divisor. -/
theorem prime_unique_signed_factor {A : Type*} [CommRing A] (w h : A)
    (q : Ideal A) (hq : q.IsPrime) (h2 : IsUnit (2 : A)) (hh : h ∉ q)
    (heq : (w - h) * (w + h) = 0) :
    w - h ∈ q ↔ w + h ∉ q := by
  have hor : w - h ∈ q ∨ w + h ∈ q := hq.mem_or_mem (heq ▸ q.zero_mem)
  have hne : ¬ (w - h ∈ q ∧ w + h ∈ q) := by
    rintro ⟨hp, hn⟩
    have htwoH : (2 : A) * h ∈ q := by
      convert q.sub_mem hn hp using 1 ; ring
    let c : A := ↑h2.unit⁻¹
    have hc : c * 2 = 1 := by
      simpa only [c, h2.unit_spec] using Units.inv_mul h2.unit
    have hmul := q.mul_mem_left c htwoH
    apply hh
    rw [← mul_assoc, hc, one_mul] at hmul
    exact hmul
  tauto

/-- For the actual finite chart with split branch polynomial, every prime is
either a listed rational crossing or lies on exactly one signed component. -/
theorem finiteSpecialFiber_prime_strata [DecidableEq k] (P : k[X]) (S : Finset k)
    (hP : P = ∏ x ∈ S, (X - C x)) (h2 : (2 : k) ≠ 0)
    (q : Ideal (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)))
    (hq : q.IsPrime) :
    (∃ x ∈ insert 0 S,
      q = RingHom.ker (finiteCrossingEvaluation P x).toRingHom) ∨
    (algebraMap k[X] _ (finiteComponentPolynomial P) ∉ q ∧
      ((QuadraticAlgebra.omega - algebraMap k[X] _ (finiteComponentPolynomial P)) ∈ q ↔
        (QuadraticAlgebra.omega + algebraMap k[X] _ (finiteComponentPolynomial P)) ∉ q)) := by
  classical
  by_cases hbranch : algebraMap k[X] _ (finiteComponentPolynomial P) ∈ q
  · exact Or.inl (finiteBranchPrimes_eq_crossings P S hP q hq hbranch)
  · right
    refine ⟨hbranch, ?_⟩
    let A := AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)
    have htwoPoly : IsUnit (2 : k[X]) := by
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr h2).map (C : k →+* k[X])
    have htwo : IsUnit (2 : A) := by
      simpa only [map_ofNat] using htwoPoly.map (algebraMap k[X] A)
    exact prime_unique_signed_factor _ _ q hq htwo hbranch
      (finite_component_crossing_equation P)

/-- Every point of the reciprocal chart above the base-line infinity point is
outside the branch divisor when the original polynomial is monic. -/
theorem infinitySpecialFiber_prime_over_zero_isAway (P : k[X]) (hP : P.Monic)
    (q : Ideal (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)))
    (hq : q.IsPrime)
    (hX : algebraMap k[X] _ X ∈ q) :
    algebraMap k[X] _ (infinityComponentPolynomial P) ∉ q := by
  let A := AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)
  have hbase : RingHom.ker (evalRingHom (0 : k)) ≤
      Ideal.comap (algebraMap k[X] A) q := by
    rw [Polynomial.ker_evalRingHom]
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change algebraMap k[X] A (X - C 0) ∈ q
    simpa only [C_0, sub_zero] using hX
  have hzero : infinityComponentPolynomial P - 1 ∈
      RingHom.ker (evalRingHom (0 : k)) := by
    change (infinityComponentPolynomial P - 1).eval 0 = 0
    rw [eval_sub, infinityComponentPolynomial_eval_zero P hP]
    simp
  have hdiff : algebraMap k[X] A (infinityComponentPolynomial P - 1) ∈ q :=
    hbase hzero
  intro hH
  have hOne : (1 : A) ∈ q := by
    convert q.sub_mem hH hdiff using 1 ; simp [map_sub] ; ring
  apply hq.ne_top
  apply top_unique
  intro x _
  simpa using q.mul_mem_left x hOne

/-- Over infinity, each prime of the actual reciprocal chart belongs to
exactly one signed component. -/
theorem infinitySpecialFiber_prime_over_zero_unique_signed_component
    (P : k[X]) (hP : P.Monic) (h2 : (2 : k) ≠ 0)
    (q : Ideal (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)))
    (hq : q.IsPrime) (hX : algebraMap k[X] _ X ∈ q) :
    (QuadraticAlgebra.omega - algebraMap k[X] _ (infinityComponentPolynomial P)) ∈ q ↔
      (QuadraticAlgebra.omega + algebraMap k[X] _ (infinityComponentPolynomial P)) ∉ q := by
  let A := AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)
  have htwoPoly : IsUnit (2 : k[X]) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr h2).map (C : k →+* k[X])
  have htwo : IsUnit (2 : A) := by
    simpa only [map_ofNat] using htwoPoly.map (algebraMap k[X] A)
  have heq :
      ((QuadraticAlgebra.omega : A) - algebraMap k[X] A (infinityComponentPolynomial P)) *
      ((QuadraticAlgebra.omega : A) + algebraMap k[X] A (infinityComponentPolynomial P)) =
        0 := by
    have hs : algebraMap k[X] A (infinityBranchPolynomial P 0) =
        (algebraMap k[X] A (infinityComponentPolynomial P)) ^ 2 := by
      simp only [infinityBranchPolynomial_zero, map_pow]
    calc
      _ = (QuadraticAlgebra.omega : A) ^ 2 -
          (algebraMap k[X] A (infinityComponentPolynomial P)) ^ 2 := by ring
      _ = 0 := by
        rw [AlgebraicGeometry.DoubleCover.chartGenerator_sq, hs]
        exact sub_self _
  exact prime_unique_signed_factor _ _ q hq htwo
    (infinitySpecialFiber_prime_over_zero_isAway P hP q hq hX) heq

end HilbertModularity.Hyperelliptic
