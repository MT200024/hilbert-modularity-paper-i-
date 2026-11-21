/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersectionPoints

/-! # Global intersections of the signed special-fibre components

The two projective sheets cannot meet over the point at infinity.  At every
other point their intersection is detected by the finite branch polynomial.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped QuadraticAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

private theorem infinityComponentPolynomial_not_mem_over_zero
    (P : k[X]) (hP : P.Monic)
    (q : Spec (CommRingCat.of k[X])) (hX : X ∈ q.asIdeal) :
    infinityComponentPolynomial P ∉ q.asIdeal := by
  have hbase : RingHom.ker (evalRingHom (0 : k)) ≤ q.asIdeal := by
    rw [Polynomial.ker_evalRingHom]
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change X - C 0 ∈ q.asIdeal
    simpa only [C_0, sub_zero] using hX
  have hzero : infinityComponentPolynomial P - 1 ∈
      RingHom.ker (evalRingHom (0 : k)) := by
    change (infinityComponentPolynomial P - 1).eval 0 = 0
    rw [eval_sub, infinityComponentPolynomial_eval_zero P hP]
    simp
  intro hH
  have hOne : (1 : k[X]) ∈ q.asIdeal := by
    convert q.asIdeal.sub_mem hH (hbase hzero) using 1 ; ring
  exact q.isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem q.asIdeal hOne isUnit_one)

/-- The signed sheets cannot coincide above the infinity point of the base. -/
theorem infinitySignedChartPoint_ne_of_zero
    (P : k[X]) (hP : P.Monic) (h2 : (2 : k) ≠ 0)
    (q : Spec (CommRingCat.of k[X])) (hX : X ∈ q.asIdeal) :
    infinityPositiveMap P q ≠ infinityNegativeMap P q := by
  intro heq
  have hinj : Function.Injective (AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)) :=
    (AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)).isOpenEmbedding.injective
  have heq' : PrimeSpectrum.comap (infinityPositiveComponent P).toRingHom q =
      PrimeSpectrum.comap (infinityNegativeComponent P).toRingHom q := by
    apply hinj
    rw [infinityPositiveMap_eq, infinityNegativeMap_eq] at heq
    change (Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) ≫
        AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)) q =
      (Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) ≫
        AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)) q at heq
    simp only [Scheme.Hom.comp_apply] at heq
    change (AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0))
        (PrimeSpectrum.comap (infinityPositiveComponent P).toRingHom q) =
      (AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0))
        (PrimeSpectrum.comap (infinityNegativeComponent P).toRingHom q) at heq
    exact heq
  have hker := congrArg PrimeSpectrum.asIdeal heq'
  change Ideal.comap (infinityPositiveComponent P).toRingHom q.asIdeal =
    Ideal.comap (infinityNegativeComponent P).toRingHom q.asIdeal at hker
  let H := infinityComponentPolynomial P
  let A := AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)
  let e : A := ⟨-H, 1⟩
  have hp : infinityPositiveComponent P e = 0 := by
    simp [e, infinityPositiveComponent_apply, H]
  have hn : infinityNegativeComponent P e = -(2 : k[X]) * H := by
    simp [e, infinityNegativeComponent_apply, H]
    ring
  have hm : infinityNegativeComponent P e ∈ q.asIdeal := by
    have hz : e ∈ Ideal.comap (infinityPositiveComponent P).toRingHom q.asIdeal := by
      change infinityPositiveComponent P e ∈ q.asIdeal
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
  have hH : H ∈ q.asIdeal := by
    have := q.asIdeal.mul_mem_left c hm'
    rwa [← mul_assoc, hc, one_mul] at this
  exact infinityComponentPolynomial_not_mem_over_zero P hP q hX hH

/-- The finite chart contains every point of the reciprocal chart with nonzero coordinate. -/
theorem infinityChart_preimage_finiteRange :
    ProjectiveLine.chartMap k 1 0 (by decide) ⁻¹ᵁ
        (ProjectiveLine.chartMap k 0 1 (by decide)).opensRange =
      PrimeSpectrum.basicOpen (X : k[X]) := by
  rw [ProjectiveLine.chartMap_opensRange]
  have h (s : MvPolynomial (Fin 2) k) (hs : s.IsHomogeneous 1) :
      ProjectiveLine.chartMap k 1 0 (by decide) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) s =
        PrimeSpectrum.basicOpen (ProjectiveLine.chartCoordinates k 1 s) :=
    Proj.fromSpecOfUnit_preimage_basicOpen_one (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (ProjectiveLine.chartCoordinates k 1)
      (MvPolynomial.isHomogeneous_X k (0 : Fin 2)) hs
      (by simp [ProjectiveLine.chartCoordinates])
  simpa [ProjectiveLine.chartCoordinates] using h (MvPolynomial.X 1)
    (MvPolynomial.isHomogeneous_X k 1)

/-- A point at which the global signed sheets meet lies on the finite projective chart. -/
theorem globalSignedPoint_eq_implies_finite (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) (y : ProjectiveLine k)
    (heq : positiveGlobalComponent P y = negativeGlobalComponent P y) :
    ∃ q : Spec (CommRingCat.of k[X]),
      ProjectiveLine.chartMap k 0 1 (by decide) q = y := by
  rcases ProjectiveLine.chartMaps_jointly_surjective k y with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact ⟨q, hq⟩
  · by_cases hX : X ∈ q.asIdeal
    · have hne := infinitySignedChartPoint_ne_of_zero P hP h2 q hX
      apply False.elim (hne ?_)
      have hs : infinityPositiveMap P q = infinityNegativeMap P q := by
        simpa only [← Scheme.Hom.comp_apply,
          chartMap_comp_positiveGlobalComponent_infinity,
          chartMap_comp_negativeGlobalComponent_infinity] using
          (show positiveGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) q) =
            negativeGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) q) by
              rw [hq]; exact heq)
      exact hs
    · have hmem : q ∈ PrimeSpectrum.basicOpen (X : k[X]) := hX
      have hy : y ∈ (ProjectiveLine.chartMap k 0 1 (by decide)).opensRange := by
        rw [← hq]
        rw [← infinityChart_preimage_finiteRange] at hmem
        exact hmem
      exact hy

/-- The intersection of the two actual projective sheet images is exactly the
image of the finite branch divisor. In particular, it contains no point above
infinity, including nonclosed scheme points. -/
theorem globalComponent_ranges_inter_eq_finiteBranch
    (P : k[X]) (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    Set.range ⇑(positiveGlobalComponent P) ∩
        Set.range ⇑(negativeGlobalComponent P) =
      {z | ∃ q : Spec (CommRingCat.of k[X]),
        finiteComponentPolynomial P ∈ q.asIdeal ∧ z = finitePositiveMap P q} := by
  ext z
  constructor
  · rintro ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    have hbase := congrArg (scaledDoubleCoverProjection P 0) (hy.trans hy'.symm)
    have hyy : y = y' := by
      simp only [← Scheme.Hom.comp_apply] at hbase
      rw [positiveGlobalComponent_projection,
        negativeGlobalComponent_projection] at hbase
      simpa using hbase
    subst y'
    have heq : positiveGlobalComponent P y = negativeGlobalComponent P y :=
      hy.trans hy'.symm
    obtain ⟨q, hq⟩ := globalSignedPoint_eq_implies_finite P hP h2 y heq
    refine ⟨q, ?_, ?_⟩
    · apply (finiteSignedChartPoint_eq_iff P h2 q).mp
      rw [← hq] at heq
      simpa only [← Scheme.Hom.comp_apply,
        chartMap_comp_positiveGlobalComponent_finite,
        chartMap_comp_negativeGlobalComponent_finite] using heq
    · rw [← hq] at hy
      simpa only [← Scheme.Hom.comp_apply,
        chartMap_comp_positiveGlobalComponent_finite] using hy.symm
  · rintro ⟨q, hbranch, rfl⟩
    have heq := (finiteSignedChartPoint_eq_iff P h2 q).mpr hbranch
    have hp : finitePositiveMap P q =
        positiveGlobalComponent P (ProjectiveLine.chartMap k 0 1 (by decide) q) := by
      simp only [← Scheme.Hom.comp_apply,
        chartMap_comp_positiveGlobalComponent_finite]
    have hn : finiteNegativeMap P q =
        negativeGlobalComponent P (ProjectiveLine.chartMap k 0 1 (by decide) q) := by
      simp only [← Scheme.Hom.comp_apply,
        chartMap_comp_negativeGlobalComponent_finite]
    exact ⟨⟨_, hp.symm⟩, ⟨_, hn.symm.trans heq.symm⟩⟩

/-- The prime of the affine line obtained by evaluating at a rational coordinate. -/
def finiteRootPoint (x : k) : Spec (CommRingCat.of k[X]) :=
  ⟨RingHom.ker (evalRingHom x), RingHom.ker_isPrime _⟩

/-- Membership in the prime of an affine rational point is evaluation to zero. -/
theorem mem_finiteRootPoint_asIdeal_iff (x : k) (f : k[X]) :
    f ∈ (finiteRootPoint x).asIdeal ↔ f.eval x = 0 := by
  change f ∈ RingHom.ker (evalRingHom x) ↔ f.eval x = 0
  simp [RingHom.mem_ker, evalRingHom]

/-- Over a split branch divisor, every intersection point of the two global
components is one of the listed rational crossings. -/
theorem globalComponent_ranges_inter_eq_splitCrossings [DecidableEq k]
    (P : k[X]) (S : Finset k) (hP : P.Monic) (h2 : (2 : k) ≠ 0)
    (hsplit : P = ∏ x ∈ S, (X - C x)) :
    Set.range ⇑(positiveGlobalComponent P) ∩
        Set.range ⇑(negativeGlobalComponent P) =
      {z | ∃ x ∈ insert 0 S, z = finitePositiveMap P (finiteRootPoint x)} := by
  rw [globalComponent_ranges_inter_eq_finiteBranch P hP h2]
  ext z
  constructor
  · rintro ⟨q, hbranch, rfl⟩
    let : q.asIdeal.IsPrime := q.isPrime
    have hsplitBranch : splitFiniteBranchPolynomial S ∈ q.asIdeal := by
      rw [← finiteComponentPolynomial_eq_split P S hsplit]
      exact hbranch
    have hprod : (X : k[X]) ∈ q.asIdeal ∨
        ∃ x ∈ S, X - C x ∈ q.asIdeal := by
      have h := q.isPrime.mem_or_mem
        (show X * ∏ x ∈ S, (X - C x) ∈ q.asIdeal by
          simpa only [splitFiniteBranchPolynomial_eq] using hsplitBranch)
      rcases h with hX | hrest
      · exact Or.inl hX
      · exact Or.inr ((Ideal.IsPrime.prod_mem_iff (p := q.asIdeal)).mp hrest)
    obtain ⟨x, hxS, hx⟩ : ∃ x ∈ insert 0 S, X - C x ∈ q.asIdeal := by
      rcases hprod with hX | ⟨x, hxS, hx⟩
      · exact ⟨0, Finset.mem_insert_self _ _, by simpa only [C_0, sub_zero] using hX⟩
      · exact ⟨x, Finset.mem_insert_of_mem hxS, hx⟩
    have hle : RingHom.ker (evalRingHom x) ≤ q.asIdeal := by
      rw [Polynomial.ker_evalRingHom]
      apply Ideal.span_le.mpr
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      exact hx
    have hmax : (RingHom.ker (evalRingHom x)).IsMaximal := by
      apply RingHom.ker_isMaximal_of_surjective
      intro a
      exact ⟨C a, by simp⟩
    have hq : q = finiteRootPoint x := by
      apply PrimeSpectrum.ext
      exact (hmax.eq_of_le q.isPrime.ne_top hle).symm
    exact ⟨x, hxS, by rw [hq]⟩
  · rintro ⟨x, hxS, rfl⟩
    refine ⟨finiteRootPoint x, ?_, rfl⟩
    rw [finiteComponentPolynomial_eq_split P S hsplit]
    change (splitFiniteBranchPolynomial S).eval x = 0
    exact (splitFiniteBranchPolynomial_root_iff S x).mpr (Finset.mem_insert.mp hxS)

/-- The prime-point description of a crossing agrees with the rational
crossing morphism in the actual projective double cover. -/
theorem globalCrossingPoint_apply (P : k[X]) (x : k) :
    globalCrossingPoint P x (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of k)) =
      finitePositiveMap P (finiteRootPoint x) := by
  have hbase : affinePoint x (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of k)) =
      finiteRootPoint x := by
    apply PrimeSpectrum.ext
    exact affinePoint_apply_generic_asIdeal x
  exact (globalCrossingPoint_apply_finite P x _).trans
    (congrArg (finitePositiveMap P) hbase)

end HilbertModularity.Hyperelliptic
