/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeFiberDeterminant
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricResidual
public import HilbertModularity.Geometry.TateModule.FiniteGeneration
public import HilbertModularity.Geometry.TateModule.GoodReductionIsomorphism

/-! # Compatible Frobenius polynomials of the selected plus Jacobian

The fixed RM action and auxiliary-prime rank belong to the same selected
plus fibre. At a good-reduction model, the integral coefficient projector
and Newton identity yield the polynomial of
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The whole Tate module of the selected fibre is finite dimensional at every
auxiliary prime, using finite surjective multiplication on that same fibre. -/
instance primePlusFiber_rationalTate_finite (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.Finite ℚ_[ℓ]
      (rationalTate (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ) := by
  change Module.Finite ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]]
    integralTate (realCyclotomicField p) (primePlusFiber p hp ξ).X ℓ)
  infer_instance

/-- The selected integral action has a two-dimensional factor at every label
and auxiliary prime; neither dimension nor a labelled basis is a premise. -/
theorem finrank_primePlusFiberLabelledTate
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    Module.finrank L
      (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toSubmodule = 2 := by
  have h := finrank_primePlusFiberTateFactor p hp ℓ L hL σ
    (realCyclotomicField p) (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
  unfold primePlusFiberTateFactor endomorphismLabelledTate at h
  unfold endomorphismLabelledTate primePlusFiberRealMultiplication primePlusFiber parameterFiber
  with_reducible exact h

/-- Each labelled factor of the selected fibre is finite dimensional. -/
instance primePlusFiberLabelledTate_finite
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    Module.Finite L
      (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toSubmodule := by
  let : Module.Free L
      (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toSubmodule := by
    with_reducible
      exact Module.Free.of_divisionRing L
        (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
          ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
          σ).toSubmodule
  exact Module.finite_of_finrank_eq_succ
    (finrank_primePlusFiberLabelledTate p hp ξ ℓ L hL σ)

/-- At every good-reduction prime of the selected plus Jacobian, one algebraic
polynomial computes geometric Frobenius on its fixed-labelled cohomological
factor for every auxiliary prime away from the residue characteristic.

The good-reduction hypothesis is an actual smooth proper connected group model
and an isomorphism of its generic fibre with the selected Jacobian. The model's
RM action, all finite-dimensionality instances and the rank-two basis are
constructed in the proof. This is the polynomial assertion of
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`]. -/
theorem exists_primePlusFiber_labelled_dual_frobeniusPolynomial
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField p))))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (e : primePlusFiber p hp ξ ≅ localGenericFiber (realCyclotomicField p) P B)
    (E : Type) [Field E] [CharZero E] [Algebra ℚ E]
    (hE : ∀ x : realCyclotomicField p,
      ((minpoly ℚ x).map (algebraMap ℚ E)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] E) :
    ∃ R : Polynomial E,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : (ℓ : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal),
        letI : Fact ℓ.Prime := ⟨hℓ⟩
        ∀ (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
          [IsScalarTower ℚ ℚ_[ℓ] L]
          (hL : ∀ x : realCyclotomicField p,
            ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
          (j : E →ₐ[ℚ] L),
          ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
            ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
            (j.comp σ)).toRepresentation.dual
              (NumberField.arithmeticFrobenius (realCyclotomicField p)
                (AlgebraicClosure (realCyclotomicField p)) P.asIdeal Q)⁻¹).charpoly =
            R.map j.toRingHom := by
  classical
  have h := exists_labelled_dual_frobeniusPolynomial_of_goodReduction
    (realCyclotomicField p) P B (primePlusFiber p hp ξ) e
    (realCyclotomicField p) (primePlusFiberRealMultiplication p hp ξ) E hE σ
  obtain ⟨R, hR⟩ := h
  refine ⟨R, ?_⟩
  intro Q _ _ ℓ hℓ hℓP
  let : Fact ℓ.Prime := ⟨hℓ⟩
  intro L _ _ _ _ _ hL j
  let : Module.Free L
      (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        (j.comp σ)).toSubmodule := by
    with_reducible
      exact Module.Free.of_divisionRing L
        (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
          ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
          (j.comp σ)).toSubmodule
  let basis := Module.finBasisOfFinrankEq L _
    (finrank_primePlusFiberLabelledTate p hp ξ ℓ L hL (j.comp σ))
  unfold endomorphismLabelledTate at basis ⊢
  exact hR Q ℓ hℓ hℓP inferInstance L hL j basis

end HilbertModularity.Hypergeometric
