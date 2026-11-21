/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.GoodReductionCoefficientTrace

/-! # A common labelled Frobenius polynomial

An integral basis of the RM field gives algebraic endomorphisms of the same
model. Their rational traces, followed by the fixed coefficient projector and
the rank-two Newton identity, give one polynomial before the auxiliary prime
is chosen. This is the argument of [TripathiGoswamiRevised,
Lemma `labelled-RM-compat`].
-/

public section
noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

/-- The labelled cohomological dual has one algebraic Frobenius polynomial at
good reduction. The RM action is supplied on the actual generic fibre and extended uniquely
to the same model by the Néron property. The rank-two
basis retains the dimension hypothesis on the chosen coefficient factor.
The polynomial is chosen before the Frobenius lift, auxiliary prime, scalar
extension or embedding of the common coefficient field. -/
theorem exists_goodReduction_labelled_dual_frobeniusPolynomial
    (K : Type u) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (F : Type*) [Field F] [NumberField F] (ψ : 𝓞 F →+* End (localGenericFiber K P B))
    (E : Type*) [Field E] [CharZero E] [Algebra ℚ E]
    (hE : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ E)).Splits)
    (σ : F →ₐ[ℚ] E) :
    ∃ R : Polynomial E,
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
        (p : ℕ) (hp : p.Prime) (_ : (p : 𝓞 K) ∉ P.asIdeal),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K (localGenericFiber K P B).X p))
          (L : Type*) [Field L] [CharZero L] [Algebra ℚ_[p] L] [Algebra ℚ L]
          [IsScalarTower ℚ ℚ_[p] L]
          (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
          (j : E →ₐ[ℚ] L)
          (basis : Module.Basis (Fin 2) L
            (labelledTateSubrepresentation K (localGenericFiber K P B).X p F L hL
              (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) (extendLocalGenericAction K P B ψ))
              (fiberPointsAction_realized K (AlgebraicClosure K) B (localGenericPoint K P)
                (𝓞 F) (extendLocalGenericAction K P B ψ)) (j.comp σ)).toSubmodule),
          letI := Module.Finite.of_basis basis
          letI := Module.Free.of_basis basis
          letI := Module.Finite.of_basis basis.dualBasis
          letI : Module.Free L
            (Module.Dual L (labelledTateSubrepresentation K (localGenericFiber K P B).X p F L hL
              (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) (extendLocalGenericAction K P B ψ))
              (fiberPointsAction_realized K (AlgebraicClosure K) B (localGenericPoint K P)
                (𝓞 F) (extendLocalGenericAction K P B ψ)) (j.comp σ)).toSubmodule) := Module.Free.of_divisionRing _ _
          ((labelledTateSubrepresentation K (localGenericFiber K P B).X p F L hL
            (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) (extendLocalGenericAction K P B ψ))
            (fiberPointsAction_realized K (AlgebraicClosure K) B (localGenericPoint K P)
              (𝓞 F) (extendLocalGenericAction K P B ψ)) (j.comp σ)).toRepresentation.dual
                (NumberField.arithmeticFrobenius K (AlgebraicClosure K) P.asIdeal Q)⁻¹).charpoly =
            R.map j.toRingHom := by
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  have htr (i : J) (n : ℕ) := exists_goodReduction_integralCoefficient_powerTrace
    K P B F (extendLocalGenericAction K P B ψ) (NumberField.RingOfIntegers.basis F i) n
  choose t ht using htr
  let b := (NumberField.integralBasis F).baseChange E
  let c := b.repr (embeddingIdempotent ℚ F E hE σ)
  let s₁ : E := ∑ i, c i * algebraMap ℚ E (t i 1)
  let s₂ : E := ∑ i, c i * algebraMap ℚ E (t i 2)
  refine ⟨Polynomial.X ^ 2 - Polynomial.C s₁ * Polynomial.X +
    Polynomial.C ((s₁ ^ 2 - s₂) / 2), ?_⟩
  intro Q _ _ p hp hpP
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite L _ _ _ _ _ hL j basis
  let := hfinite
  apply charpoly_dual_labelledTateSubrepresentation_inv_eq_map_of_basis
    K (localGenericFiber K P B).X p F L hL
    (fiberPointsAction K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) (extendLocalGenericAction K P B ψ))
    (fiberPointsAction_realized K (AlgebraicClosure K) B (localGenericPoint K P) (𝓞 F) (extendLocalGenericAction K P B ψ))
    (NumberField.integralBasis F) hE σ j _ basis
    (fun i => algebraMap ℚ E (t i 1)) (fun i => algebraMap ℚ E (t i 2))
  · intro i
    simpa only [NumberField.integralBasis_apply, AlgHom.commutes] using
      ht i 1 Q p hp hpP hfinite L
  · intro i
    simpa only [NumberField.integralBasis_apply, AlgHom.commutes] using
      ht i 2 Q p hp hpP hfinite L

end AlgebraicGeometry.GroupScheme
