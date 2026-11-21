/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberGlobalComponents

/-! # Coverage by the two components of the square-branch special fibre

The two evaluation kernels have zero product: each product maps to zero on
both branches, and the two evaluations together are injective. Every prime
therefore lies on at least one component. The affine result is transported
through the actual two-chart cover of the scaled double cover.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

universe u

variable {k : Type u} [Field k]

/-- The two evaluation ideals of a nonzero square-branch chart have zero product. -/
theorem componentKernels_mul_eq_bot (H : k[X]) (hH : H ≠ 0) (h2 : (2 : k) ≠ 0) :
    RingHom.ker (positiveComponent H).toRingHom *
      RingHom.ker (negativeComponent H).toRingHom = ⊥ := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    change x * y = 0
    change positiveComponent H x = 0 at hx
    change negativeComponent H y = 0 at hy
    apply componentPair_injective H hH h2
    apply Prod.ext
    · have hz : positiveComponent H (x * y) = 0 := by simp [map_mul, hx]
      simpa [componentPair_apply, positiveComponent_apply] using hz
    · have hz : negativeComponent H (x * y) = 0 := by simp [map_mul, hy]
      simpa [componentPair_apply, negativeComponent_apply] using hz
  · exact bot_le

/-- Every prime of the square-branch affine chart belongs to one of its components. -/
theorem squareBranch_components_cover (H : k[X]) (hH : H ≠ 0)
    (h2 : (2 : k) ≠ 0) :
    Set.range (PrimeSpectrum.comap (positiveComponent H).toRingHom) ∪
      Set.range (PrimeSpectrum.comap (negativeComponent H).toRingHom) = Set.univ := by
  rw [range_comap_of_surjective k[X] _ (positiveComponent_surjective H),
    range_comap_of_surjective k[X] _ (negativeComponent_surjective H),
    ← PrimeSpectrum.zeroLocus_mul, componentKernels_mul_eq_bot H hH h2]
  simp [PrimeSpectrum.zeroLocus]

/-- The square-branch component maps cover the points of their affine chart. -/
theorem squareBranch_components_jointly_surjective (H : k[X]) (hH : H ≠ 0)
    (h2 : (2 : k) ≠ 0)
    (x : Spec (CommRingCat.of (SquareBranchRing H))) :
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom (positiveComponent H).toRingHom) y = x) ∨
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom (negativeComponent H).toRingHom) y = x) := by
  have hx : x ∈ Set.range (PrimeSpectrum.comap (positiveComponent H).toRingHom) ∪
      Set.range (PrimeSpectrum.comap (negativeComponent H).toRingHom) := by
    rw [squareBranch_components_cover H hH h2]
    trivial
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

private theorem componentMaps_jointly_surjective {A : Type u} [CommRing A] [Algebra k A]
    (f g : A →ₐ[k] k[X]) (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (hinj : Function.Injective (fun z : A => (f z, g z)))
    (x : Spec (CommRingCat.of A)) :
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom f.toRingHom) y = x) ∨
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom g.toRingHom) y = x) := by
  have hker : RingHom.ker f.toRingHom * RingHom.ker g.toRingHom = ⊥ := by
    apply le_antisymm
    · rw [Ideal.mul_le]
      intro z hz w hw
      change z * w = 0
      change f z = 0 at hz
      change g w = 0 at hw
      apply hinj
      apply Prod.ext
      · simp [map_mul, hz]
      · simp [map_mul, hw]
    · exact bot_le
  have hcover : Set.range (PrimeSpectrum.comap f.toRingHom) ∪
      Set.range (PrimeSpectrum.comap g.toRingHom) = Set.univ := by
    rw [range_comap_of_surjective k[X] _ hf,
      range_comap_of_surjective k[X] _ hg,
      ← PrimeSpectrum.zeroLocus_mul, hker]
    simp [PrimeSpectrum.zeroLocus]
  have hx : x ∈ Set.range (PrimeSpectrum.comap f.toRingHom) ∪
      Set.range (PrimeSpectrum.comap g.toRingHom) := by
    rw [hcover]
    trivial
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

private theorem signedChartComponents_injective (Q H : k[X])
    (f g : AlgebraicGeometry.DoubleCover.ChartRing Q →ₐ[k] k[X])
    (hf : ∀ z, f z = z.re + z.im * H)
    (hg : ∀ z, g z = z.re - z.im * H)
    (hH : H ≠ 0) (h2 : (2 : k) ≠ 0) :
    Function.Injective (fun z => (f z, g z)) := by
  intro z w hzw
  have hp : z.re + z.im * H = w.re + w.im * H := by
    simpa only [hf] using congrArg Prod.fst hzw
  have hm : z.re - z.im * H = w.re - w.im * H := by
    simpa only [hg] using congrArg Prod.snd hzw
  have htwo : (2 : k[X]) ≠ 0 := by
    simpa only [map_ofNat] using (Polynomial.C_ne_zero.mpr h2)
  have hr : z.re = w.re := by
    have h : (2 : k[X]) * (z.re - w.re) = 0 := by
      linear_combination hp + hm
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left htwo)
  have hi : z.im = w.im := by
    have h : (2 : k[X]) * ((z.im - w.im) * H) = 0 := by
      linear_combination hp - hm
    have hh := (mul_eq_zero.mp h).resolve_left htwo
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hH)
  exact QuadraticAlgebra.ext hr hi

/-- The two finite-chart sheets cover the actual finite chart of the special fibre. -/
theorem finiteComponents_jointly_surjective (P : k[X])
    (hH : finiteComponentPolynomial P ≠ 0) (h2 : (2 : k) ≠ 0)
    (x : Spec (CommRingCat.of
      (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)))) :
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) y = x) ∨
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) y = x) :=
  componentMaps_jointly_surjective (finitePositiveComponent P) (finiteNegativeComponent P)
    (finitePositiveComponent_surjective P) (finiteNegativeComponent_surjective P)
    (signedChartComponents_injective _ _ _ _
      (finitePositiveComponent_apply P) (finiteNegativeComponent_apply P) hH h2) x

/-- The two reciprocal-chart sheets cover the actual chart at infinity. -/
theorem infinityComponents_jointly_surjective (P : k[X])
    (hH : infinityComponentPolynomial P ≠ 0) (h2 : (2 : k) ≠ 0)
    (x : Spec (CommRingCat.of
      (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)))) :
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) y = x) ∨
    (∃ y : Spec (CommRingCat.of k[X]),
      Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) y = x) :=
  componentMaps_jointly_surjective (infinityPositiveComponent P) (infinityNegativeComponent P)
    (infinityPositiveComponent_surjective P) (infinityNegativeComponent_surjective P)
    (signedChartComponents_injective _ _ _ _
      (infinityPositiveComponent_apply P) (infinityNegativeComponent_apply P) hH h2) x

/-- The two projective sheets cover every point of the actual special fibre. -/
theorem globalComponents_jointly_surjective (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) (x : scaledDoubleCover P 0) :
    (∃ y : ProjectiveLine k, positiveGlobalComponent P y = x) ∨
    (∃ y : ProjectiveLine k, negativeGlobalComponent P y = x) := by
  have hfinite : finiteComponentPolynomial P ≠ 0 := by
    rw [finiteComponentPolynomial_eq]
    exact mul_ne_zero X_ne_zero hP.ne_zero
  have hinfinity : infinityComponentPolynomial P ≠ 0 := by
    intro h
    have hv := infinityComponentPolynomial_eval_zero P hP
    rw [h] at hv
    simp at hv
  change (∃ y : ProjectiveLine k, positiveGlobalComponent P y = x) ∨
    (∃ y : ProjectiveLine k, negativeGlobalComponent P y = x)
  rcases AlgebraicGeometry.DoubleCover.charts_jointly_surjective
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0) x with
    ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rcases finiteComponents_jointly_surjective P hfinite h2 y with
      ⟨z, hz⟩ | ⟨z, hz⟩
    · left
      refine ⟨ProjectiveLine.chartMap k 0 1 (by decide) z, ?_⟩
      calc
        positiveGlobalComponent P (ProjectiveLine.chartMap k 0 1 (by decide) z) =
            finitePositiveMap P z := by
          exact congrArg (fun f => f z) (chartMap_comp_positiveGlobalComponent_finite P)
        _ = _ := by
          rw [finitePositiveMap_eq]
          change (AlgebraicGeometry.DoubleCover.finiteChart
            (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
            (P.natDegree + 1) (branch_transition P 0))
              ((Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom)) z) = _
          rw [hz]
    · right
      refine ⟨ProjectiveLine.chartMap k 0 1 (by decide) z, ?_⟩
      calc
        negativeGlobalComponent P (ProjectiveLine.chartMap k 0 1 (by decide) z) =
            finiteNegativeMap P z := by
          exact congrArg (fun f => f z) (chartMap_comp_negativeGlobalComponent_finite P)
        _ = _ := by
          rw [finiteNegativeMap_eq]
          change (AlgebraicGeometry.DoubleCover.finiteChart
            (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
            (P.natDegree + 1) (branch_transition P 0))
              ((Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom)) z) = _
          rw [hz]
  · rcases infinityComponents_jointly_surjective P hinfinity h2 y with
      ⟨z, hz⟩ | ⟨z, hz⟩
    · left
      refine ⟨ProjectiveLine.chartMap k 1 0 (by decide) z, ?_⟩
      calc
        positiveGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) z) =
            infinityPositiveMap P z := by
          exact congrArg (fun f => f z) (chartMap_comp_positiveGlobalComponent_infinity P)
        _ = _ := by
          rw [infinityPositiveMap_eq]
          change (AlgebraicGeometry.DoubleCover.infinityChart
            (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
            (P.natDegree + 1) (branch_transition P 0))
              ((Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom)) z) = _
          rw [hz]
    · right
      refine ⟨ProjectiveLine.chartMap k 1 0 (by decide) z, ?_⟩
      calc
        negativeGlobalComponent P (ProjectiveLine.chartMap k 1 0 (by decide) z) =
            infinityNegativeMap P z := by
          exact congrArg (fun f => f z) (chartMap_comp_negativeGlobalComponent_infinity P)
        _ = _ := by
          rw [infinityNegativeMap_eq]
          change (AlgebraicGeometry.DoubleCover.infinityChart
            (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
            (P.natDegree + 1) (branch_transition P 0))
              ((Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom)) z) = _
          rw [hz]

end HilbertModularity.Hyperelliptic
