/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIrreducibleComponents

/-! # Distinct signed components of the square-branch special fibre -/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

private theorem infinitySignedChartPoints_ne (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom)
        z ≠
      Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom)
        z := by
  intro z heq
  let A := AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)
  let e : A := ⟨-infinityComponentPolynomial P, 1⟩
  have hpos : infinityPositiveComponent P e = 0 := by
    rw [infinityPositiveComponent_apply]
    simp [e]
  have hH : infinityComponentPolynomial P ≠ 0 := by
    intro h
    have hv := infinityComponentPolynomial_eval_zero P hP
    rw [h] at hv
    simp at hv
  have h2poly : (2 : k[X]) ≠ 0 := by
    simpa only [map_ofNat] using (Polynomial.C_ne_zero.mpr h2)
  have hneg : infinityNegativeComponent P e ≠ 0 := by
    have he : infinityNegativeComponent P e =
        -(2 : k[X]) * infinityComponentPolynomial P := by
      rw [infinityNegativeComponent_apply]
      simp [e]
      ring
    rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr h2poly) hH
  have hker : RingHom.ker
        (infinityPositiveComponent P).toRingHom =
      RingHom.ker
        (infinityNegativeComponent P).toRingHom := by
    have hh := congrArg PrimeSpectrum.asIdeal heq
    change RingHom.ker (infinityPositiveComponent P).toRingHom =
      RingHom.ker (infinityNegativeComponent P).toRingHom at hh
    exact hh
  have hmem : e ∈ RingHom.ker (infinityPositiveComponent P).toRingHom := hpos
  have hmem' : e ∈ RingHom.ker (infinityNegativeComponent P).toRingHom := hker ▸ hmem
  exact hneg hmem'

/-- The signed sheets are different at the generic point of the reciprocal chart. -/
theorem globalComponent_infinityGeneric_ne (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    positiveGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) z) ≠
      negativeGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) z) := by
  intro z h
  have h' : infinityPositiveMap P z = infinityNegativeMap P z := by
    simpa only [← Scheme.Hom.comp_apply,
      chartMap_comp_positiveGlobalComponent_infinity,
      chartMap_comp_negativeGlobalComponent_infinity] using h
  have hinj : Function.Injective (AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)) :=
    (AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0)).isOpenEmbedding.injective
  apply infinitySignedChartPoints_ne P hP h2
  exact hinj (by simpa only [infinityPositiveMap_eq, infinityNegativeMap_eq,
    Scheme.Hom.comp_apply] using h')

/-- The generic point on the positive reciprocal chart is absent from the negative sheet. -/
theorem positiveGlobalComponent_infinityGeneric_not_mem_negative_range
    (P : k[X]) (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    positiveGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) z) ∉
      Set.range ⇑(negativeGlobalComponent P) := by
  intro z h
  obtain ⟨y, hy⟩ := h
  have hbase := congrArg (scaledDoubleCoverProjection P 0) hy
  have hbase' : (negativeGlobalComponent P ≫ scaledDoubleCoverProjection P 0) y =
      ((ProjectiveLine.chartMap k 1 0 (by decide) ≫ positiveGlobalComponent P) ≫
        scaledDoubleCoverProjection P 0) z := by
    simpa only [Scheme.Hom.comp_apply] using hbase
  have hyz : y = ProjectiveLine.chartMap k 1 0 (by decide) z := by
    rw [negativeGlobalComponent_projection, Category.assoc,
      positiveGlobalComponent_projection] at hbase'
    simpa using hbase'
  subst y
  exact globalComponent_infinityGeneric_ne P hP h2 hy.symm

/-- The generic point on the negative reciprocal chart is absent from the positive sheet. -/
theorem negativeGlobalComponent_infinityGeneric_not_mem_positive_range
    (P : k[X]) (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    negativeGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) z) ∉
      Set.range ⇑(positiveGlobalComponent P) := by
  intro z h
  obtain ⟨y, hy⟩ := h
  have hbase := congrArg (scaledDoubleCoverProjection P 0) hy
  have hbase' : (positiveGlobalComponent P ≫ scaledDoubleCoverProjection P 0) y =
      ((ProjectiveLine.chartMap k 1 0 (by decide) ≫ negativeGlobalComponent P) ≫
        scaledDoubleCoverProjection P 0) z := by
    simpa only [Scheme.Hom.comp_apply] using hbase
  have hyz : y = ProjectiveLine.chartMap k 1 0 (by decide) z := by
    rw [positiveGlobalComponent_projection, Category.assoc,
      negativeGlobalComponent_projection] at hbase'
    simpa using hbase'
  subst y
  exact globalComponent_infinityGeneric_ne P hP h2 hy

/-- The two global projective sheet images are different subsets of the actual special fibre. -/
theorem globalComponent_ranges_ne (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    Set.range ⇑(positiveGlobalComponent P) ≠
      Set.range ⇑(negativeGlobalComponent P) := by
  intro h
  let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
  apply positiveGlobalComponent_infinityGeneric_not_mem_negative_range P hP h2
  rw [← h]
  exact ⟨ProjectiveLine.chartMap k 1 0 (by decide) z, rfl⟩

private theorem irreducible_subset_closed_union {X : Type*} [TopologicalSpace X]
    {C A B : Set X} (hC : IsIrreducible C) (hA : IsClosed A)
    (hB : IsClosed B) (h : C ⊆ A ∪ B) : C ⊆ A ∨ C ⊆ B := by
  have hclosed : ∀ Z ∈ ({A, B} : Finset (Set X)), IsClosed Z := by
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hA
    · exact hB
  have hcover : C ⊆ ⋃₀ (↑({A, B} : Finset (Set X)) : Set (Set X)) := by
    simpa using h
  obtain ⟨Z, hZ, hCZ⟩ := (isIrreducible_iff_sUnion_isClosed.mp hC)
    {A, B} hclosed hcover
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
  rcases hZ with rfl | rfl
  · exact Or.inl hCZ
  · exact Or.inr hCZ

/-- The positive image is one of the actual special fibre's irreducible components. -/
theorem positiveGlobalComponent_mem_irreducibleComponents (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    Set.range ⇑(positiveGlobalComponent P) ∈
      irreducibleComponents (scaledDoubleCover P 0) := by
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨positiveGlobalComponent_range_isClosed P,
    positiveGlobalComponent_range_irreducible P⟩, ?_⟩
  intro C hC hpos
  have hcover : C ⊆ Set.range ⇑(positiveGlobalComponent P) ∪
      Set.range ⇑(negativeGlobalComponent P) := by
    rw [globalComponent_ranges_cover P hP h2]
    exact Set.subset_univ C
  rcases irreducible_subset_closed_union hC.2
    (positiveGlobalComponent_range_isClosed P)
    (negativeGlobalComponent_range_isClosed P) hcover with hleft | hright
  · exact hleft
  · exfalso
    let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    apply positiveGlobalComponent_infinityGeneric_not_mem_negative_range P hP h2
    exact hright (hpos ⟨ProjectiveLine.chartMap k 1 0 (by decide) z, rfl⟩)

/-- The negative image is the other actual special-fibre irreducible component. -/
theorem negativeGlobalComponent_mem_irreducibleComponents (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    Set.range ⇑(negativeGlobalComponent P) ∈
      irreducibleComponents (scaledDoubleCover P 0) := by
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨negativeGlobalComponent_range_isClosed P,
    negativeGlobalComponent_range_irreducible P⟩, ?_⟩
  intro C hC hneg
  have hcover : C ⊆ Set.range ⇑(positiveGlobalComponent P) ∪
      Set.range ⇑(negativeGlobalComponent P) := by
    rw [globalComponent_ranges_cover P hP h2]
    exact Set.subset_univ C
  rcases irreducible_subset_closed_union hC.2
    (positiveGlobalComponent_range_isClosed P)
    (negativeGlobalComponent_range_isClosed P) hcover with hleft | hright
  · exfalso
    let z : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    apply negativeGlobalComponent_infinityGeneric_not_mem_positive_range P hP h2
    exact hleft (hneg ⟨ProjectiveLine.chartMap k 1 0 (by decide) z, rfl⟩)
  · exact hright

/-- The special fibre has exactly the two signed projective sheet images as components. -/
theorem specialFiber_irreducibleComponents_eq_pair (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    irreducibleComponents (scaledDoubleCover P 0) =
      {Set.range ⇑(positiveGlobalComponent P),
        Set.range ⇑(negativeGlobalComponent P)} := by
  ext C
  constructor
  · intro hC
    have hcover : C ⊆ Set.range ⇑(positiveGlobalComponent P) ∪
        Set.range ⇑(negativeGlobalComponent P) := by
      rw [globalComponent_ranges_cover P hP h2]
      exact Set.subset_univ C
    rcases irreducible_subset_closed_union hC.1
      (positiveGlobalComponent_range_isClosed P)
      (negativeGlobalComponent_range_isClosed P) hcover with hpos | hneg
    · have hEq : C = Set.range ⇑(positiveGlobalComponent P) :=
        Set.Subset.antisymm hpos
          (hC.2 (positiveGlobalComponent_range_irreducible P) hpos)
      simp [hEq]
    · have hEq : C = Set.range ⇑(negativeGlobalComponent P) :=
        Set.Subset.antisymm hneg
          (hC.2 (negativeGlobalComponent_range_irreducible P) hneg)
      simp [hEq]
  · intro hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with hpos | hneg
    · simpa [hpos] using positiveGlobalComponent_mem_irreducibleComponents P hP h2
    · simpa [hneg] using negativeGlobalComponent_mem_irreducibleComponents P hP h2

end HilbertModularity.Hyperelliptic
