/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCharts

/-! # Algebra of the two signed branches at their intersection

The compatibility relation for maps out of the two components is precisely
agreement of the base map and vanishing of the square root of the branch
section. This is the ring-level universal property behind their intersection.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Two maps out of the signed components agree on the square-branch chart
exactly when they are the same map and kill the branch square root. -/
theorem component_compositions_eq_iff {A : Type*} [CommRing A] [Algebra k A]
    (H : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    f.comp (positiveComponent H) = g.comp (negativeComponent H) ↔
      f = g ∧ f H = 0 := by
  constructor
  · intro h
    have hfg : f = g := by
      apply AlgHom.ext
      intro q
      have hq := congrArg (fun φ : SquareBranchRing H →ₐ[k] A =>
        φ (algebraMap k[X] (SquareBranchRing H) q)) h
      simpa [AlgHom.comp_apply, positiveComponent_apply, negativeComponent_apply] using hq
    refine ⟨hfg, ?_⟩
    have hω := congrArg (fun φ : SquareBranchRing H →ₐ[k] A =>
      φ QuadraticAlgebra.omega) h
    simp only [AlgHom.comp_apply, positiveComponent_apply,
      negativeComponent_apply] at hω
    have hh : f H = -(f H) := by simpa [hfg] using hω
    have hzero : (2 : A) * f H = 0 := by linear_combination hh
    have hunit : (2 : A) * (algebraMap k A) ((2 : k)⁻¹) = 1 := by
      rw [← map_ofNat (algebraMap k A) 2, ← map_mul,
        mul_inv_cancel₀ h2, map_one]
    calc
      f H = 1 * f H := by ring
      _ = ((2 : A) * (algebraMap k A) ((2 : k)⁻¹)) * f H := by rw [hunit]
      _ = ((algebraMap k A) ((2 : k)⁻¹)) * ((2 : A) * f H) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  · rintro ⟨rfl, hH⟩
    apply AlgebraicGeometry.Hyperelliptic.algHom_ext (H ^ 2)
    · simp [AlgHom.comp_apply, positiveComponent_apply, negativeComponent_apply]
    · simp [AlgHom.comp_apply, positiveComponent_apply, negativeComponent_apply, hH]

/-- The coordinate algebra of the intersection of the two signed affine
components is the branch divisor's coordinate algebra. -/
abbrev componentIntersectionRing (H : k[X]) :=
  k[X] ⧸ Ideal.span {H}

/-- Restriction of a component to its intersection with the opposite sign. -/
def componentIntersectionQuotient (H : k[X]) :
    k[X] →ₐ[k] componentIntersectionRing H :=
  Ideal.Quotient.mkₐ k (Ideal.span {H})

theorem componentIntersectionQuotient_apply (H q : k[X]) :
    componentIntersectionQuotient H q = Ideal.Quotient.mk (Ideal.span {H}) q := (rfl)

theorem componentIntersectionQuotient_surjective (H : k[X]) :
    Function.Surjective (componentIntersectionQuotient H) := by
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨f, rfl⟩

theorem componentIntersectionQuotient_H (H : k[X]) :
    componentIntersectionQuotient H H = 0 := by
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr
    (Ideal.subset_span (Set.mem_singleton H))

/-- A map from a component factors uniquely through its branch divisor exactly
when it sends the branch polynomial to zero. -/
theorem componentIntersectionQuotient_factor_iff {A : Type*}
    [CommRing A] [Algebra k A] (H : k[X]) (f : k[X] →ₐ[k] A) :
    f H = 0 ↔ ∃! g : componentIntersectionRing H →ₐ[k] A,
      g.comp (componentIntersectionQuotient H) = f := by
  constructor
  · intro hH
    have hI : ∀ a ∈ Ideal.span {H}, f a = 0 := by
      intro a ha
      have hker : Ideal.span {H} ≤ RingHom.ker f.toRingHom := by
        apply Ideal.span_le.mpr
        intro b hb
        simp only [Set.mem_singleton_iff] at hb
        subst b
        exact hH
      exact hker ha
    refine ⟨Ideal.Quotient.liftₐ (Ideal.span {H}) f hI, ?_, ?_⟩
    · apply AlgHom.ext
      intro a
      rfl
    · intro g hg
      apply Ideal.Quotient.algHom_ext k
      change g.comp (componentIntersectionQuotient H) =
        (Ideal.Quotient.liftₐ (Ideal.span {H}) f hI).comp
          (componentIntersectionQuotient H)
      rw [hg]
      apply AlgHom.ext
      intro a
      rfl
  · rintro ⟨g, hg, _⟩
    have hmem : H ∈ Ideal.span ({H} : Set k[X]) := Ideal.subset_span (Set.mem_singleton H)
    have hzero : componentIntersectionQuotient H H = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    have := congrArg (fun φ : k[X] →ₐ[k] A => φ H) hg
    simpa [AlgHom.comp_apply, hzero] using this.symm

/-- Equality of the signed component maps is represented by the branch
divisor quotient, with no reducedness or simple-root hypothesis. -/
theorem component_compositions_eq_iff_intersection_factor
    {A : Type*} [CommRing A] [Algebra k A]
    (H : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    f.comp (positiveComponent H) = g.comp (negativeComponent H) ↔
      f = g ∧ ∃! q : componentIntersectionRing H →ₐ[k] A,
        q.comp (componentIntersectionQuotient H) = f := by
  rw [component_compositions_eq_iff H h2 f g]
  exact and_congr_right (fun _ => componentIntersectionQuotient_factor_iff H f)

private theorem chartComponent_compositions_eq_iff
    {A : Type*} [CommRing A] [Algebra k A]
    (B H : k[X]) (h2 : (2 : k) ≠ 0)
    (pos neg : AlgebraicGeometry.DoubleCover.ChartRing B →ₐ[k] k[X])
    (hpos : ∀ q : k[X], pos (algebraMap k[X] _ q) = q)
    (hneg : ∀ q : k[X], neg (algebraMap k[X] _ q) = q)
    (hposω : pos QuadraticAlgebra.omega = H)
    (hnegω : neg QuadraticAlgebra.omega = -H)
    (f g : k[X] →ₐ[k] A) :
    f.comp pos = g.comp neg ↔ f = g ∧ f H = 0 := by
  constructor
  · intro h
    have hfg : f = g := by
      apply AlgHom.ext
      intro q
      have hq := congrArg (fun φ : AlgebraicGeometry.DoubleCover.ChartRing B →ₐ[k] A =>
        φ (algebraMap k[X] (AlgebraicGeometry.DoubleCover.ChartRing B) q)) h
      simpa only [AlgHom.comp_apply, hpos, hneg] using hq
    refine ⟨hfg, ?_⟩
    have hω := congrArg (fun φ : AlgebraicGeometry.DoubleCover.ChartRing B →ₐ[k] A =>
      φ QuadraticAlgebra.omega) h
    simp only [AlgHom.comp_apply, hposω, hnegω, map_neg] at hω
    have hh : f H = -(f H) := by simpa [hfg] using hω
    have hzero : (2 : A) * f H = 0 := by linear_combination hh
    have hunit : (2 : A) * (algebraMap k A) ((2 : k)⁻¹) = 1 := by
      rw [← map_ofNat (algebraMap k A) 2, ← map_mul,
        mul_inv_cancel₀ h2, map_one]
    calc
      f H = 1 * f H := by ring
      _ = ((2 : A) * (algebraMap k A) ((2 : k)⁻¹)) * f H := by rw [hunit]
      _ = ((algebraMap k A) ((2 : k)⁻¹)) * ((2 : A) * f H) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  · rintro ⟨rfl, hH⟩
    apply AlgebraicGeometry.Hyperelliptic.algHom_ext B
    · simp only [AlgHom.comp_apply, hpos, hneg]
    · simp only [AlgHom.comp_apply, hposω, hnegω, map_neg, hH, neg_zero]

/-- The scheme-theoretic intersection certificate applies to the actual
finite chart of the scaled double cover at parameter zero. -/
theorem finiteComponent_compositions_eq_iff_intersection_factor
    {A : Type*} [CommRing A] [Algebra k A]
    (P : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    f.comp (finitePositiveComponent P) = g.comp (finiteNegativeComponent P) ↔
      f = g ∧ ∃! q : componentIntersectionRing (finiteComponentPolynomial P) →ₐ[k] A,
        q.comp (componentIntersectionQuotient (finiteComponentPolynomial P)) = f := by
  rw [chartComponent_compositions_eq_iff
    (finiteBranchPolynomial P 0) (finiteComponentPolynomial P) h2
    (finitePositiveComponent P) (finiteNegativeComponent P)
    (finitePositiveComponent_base P) (finiteNegativeComponent_base P)
    (finitePositiveComponent_generator P) (finiteNegativeComponent_generator P) f g]
  exact and_congr_right (fun _ =>
    componentIntersectionQuotient_factor_iff (finiteComponentPolynomial P) f)

/-- The reciprocal chart has the same quotient certificate, with branch
polynomial `P.reverse`. -/
theorem infinityComponent_compositions_eq_iff_intersection_factor
    {A : Type*} [CommRing A] [Algebra k A]
    (P : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    f.comp (infinityPositiveComponent P) = g.comp (infinityNegativeComponent P) ↔
      f = g ∧ ∃! q : componentIntersectionRing (infinityComponentPolynomial P) →ₐ[k] A,
        q.comp (componentIntersectionQuotient (infinityComponentPolynomial P)) = f := by
  rw [chartComponent_compositions_eq_iff
    (infinityBranchPolynomial P 0) (infinityComponentPolynomial P) h2
    (infinityPositiveComponent P) (infinityNegativeComponent P)
    (infinityPositiveComponent_base P) (infinityNegativeComponent_base P)
    (infinityPositiveComponent_generator P) (infinityNegativeComponent_generator P) f g]
  exact and_congr_right (fun _ =>
    componentIntersectionQuotient_factor_iff (infinityComponentPolynomial P) f)

end HilbertModularity.Hyperelliptic
