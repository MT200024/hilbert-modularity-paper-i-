/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberGlobalComponents

/-! # Rational crossings of the actual special-fibre components

The two global component maps agree over a finite-chart rational point exactly
when the square root of the branch section vanishes there. This is an equality
of morphisms to the actual glued double cover, rather than only an equality of
their coordinate functions.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

theorem specialFiber_eq_doubleCover_scheme (P : k[X]) :
    scaledDoubleCover P 0 = AlgebraicGeometry.DoubleCover.scheme
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0) := (rfl)

/-- A rational point of the affine source chart. -/
def affinePoint (x : k) : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom)

/-- The image of the unique point of `Spec k` under evaluation at `x`. -/
theorem affinePoint_apply_generic_asIdeal (x : k) :
    (affinePoint x (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of k))).asIdeal =
      RingHom.ker (evalRingHom x) := by
  change Ideal.comap (Polynomial.aeval x).toRingHom ⊥ =
    RingHom.ker (evalRingHom x)
  ext f
  simp only [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]
  rfl

/-- Evaluation points of the affine line retain their coordinate. -/
theorem affinePoint_injective : Function.Injective (affinePoint (k := k)) := by
  intro x y h
  have hcat : CommRingCat.ofHom (Polynomial.aeval x : k[X] →ₐ[k] k).toRingHom =
      CommRingCat.ofHom (Polynomial.aeval y : k[X] →ₐ[k] k).toRingHom := by
    simpa only [affinePoint, Spec.map_inj] using h
  have hring := congrArg (fun φ : CommRingCat.of k[X] ⟶ CommRingCat.of k => φ.hom) hcat
  have hX := congrArg (fun φ : k[X] →+* k => φ X) hring
  simpa using hX

/-- The signed finite-chart evaluations agree at `x` precisely at a branch zero. -/
theorem finiteComponent_eval_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k) :
    (Polynomial.aeval x).comp (finitePositiveComponent P) =
      (Polynomial.aeval x).comp (finiteNegativeComponent P) ↔
      (finiteComponentPolynomial P).eval x = 0 := by
  constructor
  · intro h
    have hw := congrArg (fun φ : AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial P 0) →ₐ[k] k => φ QuadraticAlgebra.omega) h
    simp only [AlgHom.comp_apply, finitePositiveComponent_generator,
      finiteNegativeComponent_generator, map_neg, Polynomial.aeval_def] at hw
    have heq : (finiteComponentPolynomial P).eval x =
        -(finiteComponentPolynomial P).eval x := by simpa using hw
    have hz : (2 : k) * (finiteComponentPolynomial P).eval x = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro h
    apply AlgebraicGeometry.Hyperelliptic.algHom_ext
      (finiteBranchPolynomial P 0)
    · simp
    · simp only [AlgHom.comp_apply, finitePositiveComponent_generator,
        finiteNegativeComponent_generator, map_neg]
      have hh : x * P.eval x = 0 := by
        rw [finiteComponentPolynomial_eq] at h
        simpa using h
      simp [hh]

/-- Equality of the two actual affine chart points is the branch-zero equation. -/
theorem finiteComponent_affinePoint_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k) :
    affinePoint x ≫ finitePositiveMap P = affinePoint x ≫ finiteNegativeMap P ↔
      (finiteComponentPolynomial P).eval x = 0 := by
  unfold scaledDoubleCover
  rw [finitePositiveMap_eq, finiteNegativeMap_eq]
  unfold affinePoint
  constructor
  · intro heq
    have hm : Mono (AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)) :=
      IsOpenImmersion.mono _
    have heq' :
        (Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom)) ≫
              AlgebraicGeometry.DoubleCover.finiteChart
                (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
                (P.natDegree + 1) (branch_transition P 0) =
          (Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom)) ≫
              AlgebraicGeometry.DoubleCover.finiteChart
                (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
                (P.natDegree + 1) (branch_transition P 0) := by
      simpa only [Category.assoc] using heq
    have h := (cancel_mono (AlgebraicGeometry.DoubleCover.finiteChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0))).mp heq'
    simp only [← Spec.map_comp, Spec.map_inj] at h
    have hh : (Polynomial.aeval x).comp (finitePositiveComponent P) =
        (Polynomial.aeval x).comp (finiteNegativeComponent P) := by
      apply AlgHom.coe_ringHom_injective
      have hcat : CommRingCat.ofHom ((Polynomial.aeval x).toRingHom.comp
          (finitePositiveComponent P).toRingHom) =
          CommRingCat.ofHom ((Polynomial.aeval x).toRingHom.comp
            (finiteNegativeComponent P).toRingHom) := by
        simpa only [CommRingCat.ofHom_comp] using h
      exact congrArg (fun φ : CommRingCat.of
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)) ⟶
          CommRingCat.of k => φ.hom) hcat
    exact (finiteComponent_eval_eq_iff P h2 x).mp hh
  · intro h
    have hh := (finiteComponent_eval_eq_iff P h2 x).mpr h
    have hs :
        Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) =
          Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact (Spec.map_inj).mpr
        (congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom hh))
    simpa only [Category.assoc] using
      congrArg (fun φ : Spec (CommRingCat.of k) ⟶
          Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
            (finiteBranchPolynomial P 0))) =>
        φ ≫ AlgebraicGeometry.DoubleCover.finiteChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)) hs

/-- The signed reciprocal-chart evaluations agree at `x` precisely at a branch zero. -/
theorem infinityComponent_eval_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k) :
    (Polynomial.aeval x).comp (infinityPositiveComponent P) =
      (Polynomial.aeval x).comp (infinityNegativeComponent P) ↔
      (infinityComponentPolynomial P).eval x = 0 := by
  constructor
  · intro h
    have hw := congrArg (fun φ : AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial P 0) →ₐ[k] k => φ QuadraticAlgebra.omega) h
    simp only [AlgHom.comp_apply, infinityPositiveComponent_generator,
      infinityNegativeComponent_generator, map_neg, Polynomial.aeval_def] at hw
    have heq : (infinityComponentPolynomial P).eval x =
        -(infinityComponentPolynomial P).eval x := by simpa using hw
    have hz : (2 : k) * (infinityComponentPolynomial P).eval x = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro h
    apply AlgebraicGeometry.Hyperelliptic.algHom_ext
      (infinityBranchPolynomial P 0)
    · simp
    · simp only [AlgHom.comp_apply, infinityPositiveComponent_generator,
        infinityNegativeComponent_generator, map_neg]
      rw [infinityComponentPolynomial_eq] at h
      simp [h]

/-- Equality of the two actual reciprocal chart points is the branch-zero equation. -/
theorem infinityComponent_affinePoint_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k) :
    affinePoint x ≫ infinityPositiveMap P = affinePoint x ≫ infinityNegativeMap P ↔
      (infinityComponentPolynomial P).eval x = 0 := by
  unfold scaledDoubleCover
  rw [infinityPositiveMap_eq, infinityNegativeMap_eq]
  unfold affinePoint
  constructor
  · intro heq
    have hm : Mono (AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
        (P.natDegree + 1) (branch_transition P 0)) :=
      IsOpenImmersion.mono _
    have heq' :
        (Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom)) ≫
              AlgebraicGeometry.DoubleCover.infinityChart
                (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
                (P.natDegree + 1) (branch_transition P 0) =
          (Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom)) ≫
              AlgebraicGeometry.DoubleCover.infinityChart
                (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
                (P.natDegree + 1) (branch_transition P 0) := by
      simpa only [Category.assoc] using heq
    have h := (cancel_mono (AlgebraicGeometry.DoubleCover.infinityChart
      (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
      (P.natDegree + 1) (branch_transition P 0))).mp heq'
    simp only [← Spec.map_comp, Spec.map_inj] at h
    have hh : (Polynomial.aeval x).comp (infinityPositiveComponent P) =
        (Polynomial.aeval x).comp (infinityNegativeComponent P) := by
      apply AlgHom.coe_ringHom_injective
      have hcat : CommRingCat.ofHom ((Polynomial.aeval x).toRingHom.comp
          (infinityPositiveComponent P).toRingHom) =
          CommRingCat.ofHom ((Polynomial.aeval x).toRingHom.comp
            (infinityNegativeComponent P).toRingHom) := by
        simpa only [CommRingCat.ofHom_comp] using h
      exact congrArg (fun φ : CommRingCat.of
        (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P 0)) ⟶
          CommRingCat.of k => φ.hom) hcat
    exact (infinityComponent_eval_eq_iff P h2 x).mp hh
  · intro h
    have hh := (infinityComponent_eval_eq_iff P h2 x).mpr h
    have hs :
        Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) =
          Spec.map (CommRingCat.ofHom (Polynomial.aeval x).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact (Spec.map_inj).mpr
        (congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom hh))
    simpa only [Category.assoc] using
      congrArg (fun φ : Spec (CommRingCat.of k) ⟶
          Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
            (infinityBranchPolynomial P 0))) =>
        φ ≫ AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P 0) (infinityBranchPolynomial P 0)
          (P.natDegree + 1) (branch_transition P 0)) hs

/-- The global projective sheets meet over a finite affine rational point exactly
at a root of the scaled branch polynomial. -/
theorem globalComponent_affinePoint_eq_iff (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k) :
    (affinePoint x ≫ ProjectiveLine.chartMap k 0 1 (by decide)) ≫
        positiveGlobalComponent P =
      (affinePoint x ≫ ProjectiveLine.chartMap k 0 1 (by decide)) ≫
        negativeGlobalComponent P ↔
      (finiteComponentPolynomial P).eval x = 0 := by
  rw [Category.assoc, Category.assoc,
    chartMap_comp_positiveGlobalComponent_finite,
    chartMap_comp_negativeGlobalComponent_finite]
  exact finiteComponent_affinePoint_eq_iff P h2 x

/-- The global projective sheets are distinct at infinity when `P` is monic. -/
theorem globalComponent_infinityPoint_ne (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    (affinePoint (0 : k) ≫ ProjectiveLine.chartMap k 1 0 (by decide)) ≫
        positiveGlobalComponent P ≠
      (affinePoint (0 : k) ≫ ProjectiveLine.chartMap k 1 0 (by decide)) ≫
        negativeGlobalComponent P := by
  intro heq
  have hzero := (infinityComponent_affinePoint_eq_iff P h2 0).mp (by
    simpa only [Category.assoc, chartMap_comp_positiveGlobalComponent_infinity,
      chartMap_comp_negativeGlobalComponent_infinity] using heq)
  rw [infinityComponentPolynomial_eval_zero P hP] at hzero
  exact one_ne_zero hzero

end HilbertModularity.Hyperelliptic
