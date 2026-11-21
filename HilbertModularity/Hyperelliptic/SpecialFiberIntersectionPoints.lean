/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberComponentTopology
public import HilbertModularity.Hyperelliptic.SpecialFiberPrimeStrata
public import HilbertModularity.Hyperelliptic.SpecialFiberRationalCrossings

/-! # Points in the intersection of the two projective components

The signed charts agree at a prime precisely when the square root of their
branch section vanishes at that prime.  This applies to arbitrary scheme
points, including generic points, rather than only field-valued points.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

private theorem finiteSignedChartPrime_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0)
    (q : Spec (CommRingCat.of k[X])) :
    PrimeSpectrum.comap (finitePositiveComponent P).toRingHom q =
        PrimeSpectrum.comap (finiteNegativeComponent P).toRingHom q ↔
      finiteComponentPolynomial P ∈ q.asIdeal := by
  let H := finiteComponentPolynomial P
  let A := AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)
  constructor
  · intro heq
    have hker := congrArg PrimeSpectrum.asIdeal heq
    change Ideal.comap (finitePositiveComponent P).toRingHom q.asIdeal =
      Ideal.comap (finiteNegativeComponent P).toRingHom q.asIdeal at hker
    let e : A := ⟨-H, 1⟩
    have hp : finitePositiveComponent P e = 0 := by
      simp [e, finitePositiveComponent_apply, H]
    have hn : finiteNegativeComponent P e = -(2 : k[X]) * H := by
      simp [e, finiteNegativeComponent_apply, H]
      ring
    have hm : finiteNegativeComponent P e ∈ q.asIdeal := by
      have hz : e ∈ Ideal.comap (finitePositiveComponent P).toRingHom q.asIdeal := by
        change finitePositiveComponent P e ∈ q.asIdeal
        rw [hp]
        exact q.asIdeal.zero_mem
      rw [hker] at hz
      exact hz
    rw [hn] at hm
    have htwo : IsUnit (2 : k[X]) := by
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr h2).map (C : k →+* k[X])
    let c : k[X] := ↑htwo.unit⁻¹
    have hc : c * 2 = 1 := by
      simpa only [c, htwo.unit_spec] using Units.inv_mul htwo.unit
    have hm' : (2 : k[X]) * H ∈ q.asIdeal := by
      have hneg : -((2 : k[X]) * H) ∈ q.asIdeal := by
        convert hm using 1 ; ring
      exact q.asIdeal.neg_mem_iff.mp hneg
    have := q.asIdeal.mul_mem_left c hm'
    rwa [← mul_assoc, hc, one_mul] at this
  · intro hH
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    change finitePositiveComponent P z ∈ q.asIdeal ↔ finiteNegativeComponent P z ∈ q.asIdeal
    rw [finitePositiveComponent_apply, finiteNegativeComponent_apply]
    have hmul : z.im * H ∈ q.asIdeal := q.asIdeal.mul_mem_left _ hH
    constructor
    · intro hp
      have htwice : (2 : k[X]) * (z.im * H) ∈ q.asIdeal :=
        q.asIdeal.mul_mem_left _ hmul
      convert q.asIdeal.sub_mem hp htwice using 1 ; ring
    · intro hn
      have htwice : (2 : k[X]) * (z.im * H) ∈ q.asIdeal :=
        q.asIdeal.mul_mem_left _ hmul
      convert q.asIdeal.add_mem hn htwice using 1 ; ring

/-- Two finite-chart sheet points agree precisely above the branch divisor. -/
theorem finiteSignedChartPoint_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0)
    (q : Spec (CommRingCat.of k[X])) :
    finitePositiveMap P q = finiteNegativeMap P q ↔
      finiteComponentPolynomial P ∈ q.asIdeal := by
  have hinj : Function.Injective (AlgebraicGeometry.DoubleCover.finiteChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)) :=
    (AlgebraicGeometry.DoubleCover.finiteChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)).isOpenEmbedding.injective
  rw [finitePositiveMap_eq, finiteNegativeMap_eq]
  change (Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)) q =
    (Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) ≫
      AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)) q ↔ _
  simp only [Scheme.Hom.comp_apply]
  rw [hinj.eq_iff]
  change PrimeSpectrum.comap (finitePositiveComponent P).toRingHom q =
      PrimeSpectrum.comap (finiteNegativeComponent P).toRingHom q ↔ _
  exact finiteSignedChartPrime_eq_iff P h2 q

end HilbertModularity.Hyperelliptic
