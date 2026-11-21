/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersectionScheme
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Scheme pullbacks of the signed components

The opposite ring squares are pushouts. Thus the branch quotient represents
the actual fibre product of the two affine component maps, including tests by
non-affine schemes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace HilbertModularity.Hyperelliptic

universe u
variable {k : Type u} [Field k]

private theorem chartComponent_ringHom_eq_iff
    {A : Type u} [CommRing A]
    (Q H : k[X]) (h2 : (2 : k) ≠ 0)
    (pos neg : AlgebraicGeometry.DoubleCover.ChartRing Q →ₐ[k] k[X])
    (hpos : ∀ q : k[X], pos (algebraMap k[X] _ q) = q)
    (hneg : ∀ q : k[X], neg (algebraMap k[X] _ q) = q)
    (hposω : pos QuadraticAlgebra.omega = H)
    (hnegω : neg QuadraticAlgebra.omega = -H)
    (f g : k[X] →+* A)
    (h : f.comp pos.toRingHom = g.comp neg.toRingHom) :
    f = g ∧ f H = 0 := by
  have hfg : f = g := by
    apply RingHom.ext
    intro q
    have hq := congrArg (fun φ : AlgebraicGeometry.DoubleCover.ChartRing Q →+* A =>
      φ (algebraMap k[X] _ q)) h
    simpa [RingHom.comp_apply, hpos, hneg] using hq
  refine ⟨hfg, ?_⟩
  have hω := congrArg (fun φ : AlgebraicGeometry.DoubleCover.ChartRing Q →+* A =>
    φ QuadraticAlgebra.omega) h
  change f (pos QuadraticAlgebra.omega) = g (neg QuadraticAlgebra.omega) at hω
  rw [hposω, hnegω, map_neg, ← hfg] at hω
  have hh : f H = -(f H) := hω
  have hzero : (2 : A) * f H = 0 := by linear_combination hh
  have hpoly : (2 : k[X]) * C ((2 : k)⁻¹) = 1 := by
    change C (2 : k) * C ((2 : k)⁻¹) = 1
    rw [← C_mul, mul_inv_cancel₀ h2, map_one]
  have hunit : (2 : A) * f (C ((2 : k)⁻¹)) = 1 := by
    rw [← map_ofNat f 2, ← map_mul, hpoly, map_one]
  calc
    f H = 1 * f H := by ring
    _ = ((2 : A) * f (C ((2 : k)⁻¹))) * f H := by rw [hunit]
    _ = f (C ((2 : k)⁻¹)) * ((2 : A) * f H) := by ring
    _ = 0 := by rw [hzero, mul_zero]

private theorem chartComponent_ringPushout
    (Q H : k[X]) (h2 : (2 : k) ≠ 0)
    (pos neg : AlgebraicGeometry.DoubleCover.ChartRing Q →ₐ[k] k[X])
    (hpos : ∀ q : k[X], pos (algebraMap k[X] _ q) = q)
    (hneg : ∀ q : k[X], neg (algebraMap k[X] _ q) = q)
    (hposω : pos QuadraticAlgebra.omega = H)
    (hnegω : neg QuadraticAlgebra.omega = -H) :
    IsPushout
      (CommRingCat.ofHom pos.toRingHom)
      (CommRingCat.ofHom neg.toRingHom)
      (CommRingCat.ofHom (componentIntersectionQuotient H).toRingHom)
      (CommRingCat.ofHom (componentIntersectionQuotient H).toRingHom) := by
  refine IsPushout.mk' ?_ ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    have hzero := componentIntersectionQuotient_H H
    have hcomp : (componentIntersectionQuotient H).comp pos =
        (componentIntersectionQuotient H).comp neg := by
      apply AlgebraicGeometry.Hyperelliptic.algHom_ext Q
      · simp only [AlgHom.comp_apply, hpos, hneg]
      · simp [AlgHom.comp_apply, hposω, hnegω, hzero]
    exact congrArg (fun f : _ →ₐ[k] _ => f b) hcomp
  · intro T φ ψ hφ hψ
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨q, rfl⟩ := componentIntersectionQuotient_surjective H x
    have hq := congrArg (fun F : CommRingCat.of k[X] ⟶ T => F.hom q) hφ
    exact hq
  · intro T a b hab
    have hab' : a.hom.comp pos.toRingHom = b.hom.comp neg.toRingHom := by
      exact congrArg (fun F : CommRingCat.of
        (AlgebraicGeometry.DoubleCover.ChartRing Q) ⟶ T => F.hom) hab
    have haH : a.hom H = 0 :=
      (chartComponent_ringHom_eq_iff Q H h2 pos neg hpos hneg hposω hnegω
        a.hom b.hom hab').2
    have hab0 : a = b := by
      apply CommRingCat.hom_ext
      exact (chartComponent_ringHom_eq_iff Q H h2 pos neg hpos hneg hposω hnegω
        a.hom b.hom hab').1
    have hker : ∀ q ∈ Ideal.span ({H} : Set k[X]), a.hom q = 0 := by
      intro q hq
      have hle : Ideal.span ({H} : Set k[X]) ≤ RingHom.ker a.hom := by
        apply Ideal.span_le.mpr
        intro x hx
        simpa only [Set.mem_singleton_iff] using hx ▸ haH
      exact hle hq
    refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {H}) a.hom hker), ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro q
      change (Ideal.Quotient.lift (Ideal.span {H}) a.hom hker)
        (componentIntersectionQuotient H q) = a.hom q
      rw [componentIntersectionQuotient_apply]
      rfl
    · rw [← hab0]
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro q
      change (Ideal.Quotient.lift (Ideal.span {H}) a.hom hker)
        (componentIntersectionQuotient H q) = a.hom q
      rw [componentIntersectionQuotient_apply]
      rfl

/-- The intersection of the actual signed finite-chart components is the
branch divisor `X * P`, as a pullback of schemes. -/
theorem finiteComponent_isPullback (P : k[X]) (h2 : (2 : k) ≠ 0) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (componentIntersectionQuotient (finiteComponentPolynomial P)).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (componentIntersectionQuotient (finiteComponentPolynomial P)).toRingHom))
      (Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom))
      (Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom)) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (chartComponent_ringPushout
      (finiteBranchPolynomial P 0) (finiteComponentPolynomial P) h2
      (finitePositiveComponent P) (finiteNegativeComponent P)
      (finitePositiveComponent_base P) (finiteNegativeComponent_base P)
      (finitePositiveComponent_generator P) (finiteNegativeComponent_generator P))

/-- The intersection of the actual signed reciprocal-chart components is
the branch divisor cut out by `P.reverse`. -/
theorem infinityComponent_isPullback (P : k[X]) (h2 : (2 : k) ≠ 0) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (componentIntersectionQuotient (infinityComponentPolynomial P)).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (componentIntersectionQuotient (infinityComponentPolynomial P)).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom)) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (chartComponent_ringPushout
      (infinityBranchPolynomial P 0) (infinityComponentPolynomial P) h2
      (infinityPositiveComponent P) (infinityNegativeComponent P)
      (infinityPositiveComponent_base P) (infinityNegativeComponent_base P)
      (infinityPositiveComponent_generator P) (infinityNegativeComponent_generator P))

end HilbertModularity.Hyperelliptic
