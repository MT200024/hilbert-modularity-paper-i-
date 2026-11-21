/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCover
public import HilbertModularity.Hyperelliptic.SpecialFiberIntersection
public import Mathlib.AlgebraicGeometry.Properties

/-! # Irreducible components of the square-branch special fibre -/

public noncomputable section

open AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

private theorem projectiveLine_irreducibleSpace : IrreducibleSpace (ProjectiveLine k) := by
  let U : Bool → (ProjectiveLine k).Opens :=
    fun b => match b with
      | false => (ProjectiveLine.chartMap k 0 1 (by decide)).opensRange
      | true => (ProjectiveLine.chartMap k 1 0 (by decide)).opensRange
  have hchart : ∀ b, PreirreducibleSpace (U b) := by
    intro b
    cases b
    · let f := ProjectiveLine.chartMap k 0 1 (by decide)
      have hi : IsIrreducible (Set.range (f : Spec (CommRingCat.of k[X]) →
          ProjectiveLine k)) := by
        have h := (IrreducibleSpace.isIrreducible_univ (Spec (CommRingCat.of k[X]))).image
          (f : Spec (CommRingCat.of k[X]) → ProjectiveLine k) f.continuous.continuousOn
        simpa using h
      exact isPreirreducible_iff_preirreducibleSpace.mp
        (by simpa [U, Scheme.Hom.opensRange] using hi.isPreirreducible)
    · let f := ProjectiveLine.chartMap k 1 0 (by decide)
      have hi : IsIrreducible (Set.range (f : Spec (CommRingCat.of k[X]) →
          ProjectiveLine k)) := by
        have h := (IrreducibleSpace.isIrreducible_univ (Spec (CommRingCat.of k[X]))).image
          (f : Spec (CommRingCat.of k[X]) → ProjectiveLine k) f.continuous.continuousOn
        simpa using h
      exact isPreirreducible_iff_preirreducibleSpace.mp
        (by simpa [U, Scheme.Hom.opensRange] using hi.isPreirreducible)
  have hcover : TopologicalSpace.IsOpenCover U := by
    change (⨆ b, U b) = ⊤
    ext x
    constructor
    · intro _; trivial
    · intro _
      rcases ProjectiveLine.chartMaps_jointly_surjective k x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact TopologicalSpace.Opens.mem_iSup.mpr
          ⟨false, by change x ∈ Set.range ⇑(ProjectiveLine.chartMap k 0 1 (by decide)); exact ⟨y, hy⟩⟩
      · exact TopologicalSpace.Opens.mem_iSup.mpr
          ⟨true, by change x ∈ Set.range ⇑(ProjectiveLine.chartMap k 1 0 (by decide)); exact ⟨y, hy⟩⟩
  have hcommon : ∃ x, x ∈ U false ∧ x ∈ U true := by
    let y : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    have hy : y ∈ PrimeSpectrum.basicOpen (X : k[X]) := by
      change (X : k[X]) ∉ (⊥ : Ideal k[X])
      simp
    refine ⟨ProjectiveLine.chartMap k 0 1 (by decide) y, ?_, ?_⟩
    · change _ ∈ Set.range ⇑(ProjectiveLine.chartMap k 0 1 (by decide))
      exact ⟨y, rfl⟩
    · change ProjectiveLine.chartMap k 0 1 (by decide) y ∈
        (ProjectiveLine.chartMap k 1 0 (by decide)).opensRange
      have hy' : y ∈ ProjectiveLine.chartMap k 0 1 (by decide) ⁻¹ᵁ
          (ProjectiveLine.chartMap k 1 0 (by decide)).opensRange := by
        rw [finiteChart_preimage_infinityRange]
        exact hy
      exact hy'
  have hpair : Pairwise (Function.onFun (fun V W => ¬Disjoint V W) U) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · intro hdis
      obtain ⟨x, hx, hy⟩ := hcommon
      exact (hdis.le_bot ⟨hx, hy⟩).elim
    · intro hdis
      obtain ⟨x, hx, hy⟩ := hcommon
      exact (hdis.le_bot ⟨hy, hx⟩).elim
    · exact (hij rfl).elim
  have : PreirreducibleSpace (ProjectiveLine k) :=
    PreirreducibleSpace.of_isOpenCover hpair hcover hchart
  have : Nonempty (ProjectiveLine k) := by
    let y : Spec (CommRingCat.of k[X]) := ⟨⊥, inferInstance⟩
    exact ⟨ProjectiveLine.chartMap k 0 1 (by decide) y⟩
  exact ⟨inferInstance⟩

/-- The image of the positive signed projective sheet is irreducible. -/
theorem positiveGlobalComponent_range_irreducible (P : k[X]) :
    IsIrreducible (Set.range ⇑(positiveGlobalComponent P)) := by
  let := projectiveLine_irreducibleSpace (k := k)
  have h := (IrreducibleSpace.isIrreducible_univ (ProjectiveLine k)).image
    (positiveGlobalComponent P) (positiveGlobalComponent P).continuous.continuousOn
  simpa using h

/-- The image of the negative signed projective sheet is irreducible. -/
theorem negativeGlobalComponent_range_irreducible (P : k[X]) :
    IsIrreducible (Set.range ⇑(negativeGlobalComponent P)) := by
  let := projectiveLine_irreducibleSpace (k := k)
  have h := (IrreducibleSpace.isIrreducible_univ (ProjectiveLine k)).image
    (negativeGlobalComponent P) (negativeGlobalComponent P).continuous.continuousOn
  simpa using h

/-- The two signed projective sheet images cover the actual special fibre. -/
theorem globalComponent_ranges_cover (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    Set.range ⇑(positiveGlobalComponent P) ∪
      Set.range ⇑(negativeGlobalComponent P) = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  exact globalComponents_jointly_surjective P hP h2 x

/-- The positive signed sheet is topologically closed in the special fibre. -/
theorem positiveGlobalComponent_range_isClosed (P : k[X]) :
    IsClosed (Set.range ⇑(positiveGlobalComponent P)) :=
  (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding (positiveGlobalComponent P)).isClosed_range

/-- The negative signed sheet is topologically closed in the special fibre. -/
theorem negativeGlobalComponent_range_isClosed (P : k[X]) :
    IsClosed (Set.range ⇑(negativeGlobalComponent P)) :=
  (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding (negativeGlobalComponent P)).isClosed_range

end HilbertModularity.Hyperelliptic
