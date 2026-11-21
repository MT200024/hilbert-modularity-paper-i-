/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.GoodReductionModels
public import HilbertModularity.Geometry.GroupScheme.PrimeGoodReductionInertia

/-! # Uniform good reduction for the selected plus Jacobian

The finite exceptional set is chosen for the actual Jacobian before any
coefficient prime, splitting field, or RM label is chosen.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- Actual local models for the same selected fibre exist outside one finite
set. This applies the standard spreading input [src_stacks_spreading] to the
selected plus Jacobian, without any extra geometric premise. -/
theorem exists_primePlusFiber_goodReductionModels :
    ∃ bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p))),
      bad.Finite ∧ ∀ P, P ∉ bad →
        ∃ (B : CommGrp (Over (Spec (CommRingCat.of
            (P.valuationSubringAtPrime (realCyclotomicField p)))))),
          IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
            Nonempty (primePlusFiber p hp ξ ≅
              localGenericFiber (realCyclotomicField p) P B) := by
  let : Smooth (primePlusFamily p hp).X.hom :=
    SmoothOfRelativeDimension.smooth
      (Module.finrank ℚ (realCyclotomicField p)) _
  unfold primePlusFiber parameterFiber
  exact exists_goodReductionModels_outside_finite (realCyclotomicField p) _

/-- The actual bad-reduction primes of the selected Jacobian. This set is
independent of coefficient primes and contains no prime with a good model. -/
def primePlusFiberBadPrimes :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p))) :=
  {P | ¬ ∃ (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField p)))))),
    IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
      Nonempty (primePlusFiber p hp ξ ≅ localGenericFiber (realCyclotomicField p) P B)}

/-- The actual bad set is contained in any exceptional set furnished by
spreading out, and hence is finite. -/
theorem primePlusFiberBadPrimes_finite : (primePlusFiberBadPrimes p hp ξ).Finite := by
  classical
  obtain ⟨bad, hfinite, hgood⟩ := exists_primePlusFiber_goodReductionModels p hp ξ
  apply hfinite.subset
  intro P hP
  by_contra h
  exact hP (hgood P h)

/-- A prime outside the actual bad set has a good model of the same Jacobian. -/
theorem exists_primePlusFiber_goodReductionModel
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ primePlusFiberBadPrimes p hp ξ) :
    ∃ (B : CommGrp (Over (Spec (CommRingCat.of
        (P.valuationSubringAtPrime (realCyclotomicField p)))))),
      IsProper B.X.hom ∧ Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
        Nonempty (primePlusFiber p hp ξ ≅
          localGenericFiber (realCyclotomicField p) P B) := by
  classical
  exact not_not.mp hP

/-- Every supplied good-reduction model excludes its prime from the system's
bad set; there is no auxiliary enlargement of the geometric exceptions. -/
theorem primePlusFiber_not_mem_badPrimes_of_goodReduction
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField p))))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (e : primePlusFiber p hp ξ ≅ localGenericFiber (realCyclotomicField p) P B) :
    P ∉ primePlusFiberBadPrimes p hp ξ := by
  intro hP
  exact hP ⟨B, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩

/-- Every fixed-labelled cohomological factor is unramified outside the same
finite geometric set and its own coefficient characteristic. -/
theorem primePlusFiber_labelled_dual_unramified
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (hP : P ∉ primePlusFiberBadPrimes p hp ξ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓP : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L)
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (hg : g ∈ Q.inertia (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))) :
    (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      σ).toRepresentation.dual g = 1 := by
  let hm := exists_primePlusFiber_goodReductionModel p hp ξ P hP
  let B := hm.choose
  let : IsProper B.X.hom := hm.choose_spec.1
  let : Smooth B.X.hom := hm.choose_spec.2.1
  let : GeometricallyConnected B.X.hom := hm.choose_spec.2.2.1
  let e := hm.choose_spec.2.2.2.some
  have hi := primePlusFiber_labelled_dual_inertia_eq_one p hp ξ P B e Q ℓ hℓP L hL σ g hg
  unfold endomorphismLabelledTate at hi ⊢
  exact hi

end HilbertModularity.Hypergeometric
