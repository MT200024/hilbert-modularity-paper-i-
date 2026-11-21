/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCompatibleTwist
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesSphericalComparison

/-! # Spherical modularity of the selected plus Jacobian system

The selected labelled Tate action, its cohomological dual and the common
Frobenius polynomials refer to the same Jacobian. This applies the checked local
comparison in [TripathiGoswamiRevised, Theorem `thm:prime` and Lemma
`promotion`]. The Skinner--Wiles checklist and the identification of its chosen
covariant coordinates remain explicit; local polynomial compatibility is proved.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain NumberField
open scoped ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme HilbertModularForms

/-- A Skinner--Wiles checklist for the selected covariant Tate factor produces
one eigenform for every good polynomial of its finite-character-twisted system.
The coefficient embedding and RM label are fixed before the good prime. No
compatible system or local Frobenius identity is supplied as a premise. -/
theorem exists_primePlus_sphericalEigenform_of_skinnerWiles
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (A : Type) [Field A] [NumberField A]
    (hA : ∀ a : realCyclotomicField p, ((minpoly ℚ a).map (algebraMap ℚ A)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] A)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField p) A)
    (E : Type) [NontriviallyNormedField E] [CompleteSpace E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p] [Algebra ℚ E] [IsScalarTower ℚ ℚ_[p] E]
    (hE : ∀ a : realCyclotomicField p, ((minpoly ℚ a).map (algebraMap ℚ E)).Splits)
    (j : A →ₐ[ℚ] E)
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (e : ρ.Equiv ((endomorphismLabelledTate (realCyclotomicField p)
      (primePlusFiber p hp ξ) p (realCyclotomicField p) E hE
      (primePlusFiberRealMultiplication p hp ξ) (j.comp σ)).toRepresentation))
    (L : Type*) [Field L] [NumberField L] [Algebra (realCyclotomicField p) L]
    (H : SkinnerWilesWeightTwoInput p ρ L) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level : FiniteLevel (realCyclotomicField p))
        (μ : AdditiveQuotientMeasure (realCyclotomicField p))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        ψ.complexEmbedding = B.val.toRingHom ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        ∀ q, q ∉ ((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).bad →
          ∃ hψ : q ∉ ψ.form.bad,
            (((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ).polynomial q).map i =
              ψ.heckePolynomial q hψ := by
  let ν := (Units.map j.toRingHom.toMonoidHom).comp χ.toMonoidHom
  let τ := primePlusCohomologicalAction p hp ξ p E hE (j.comp σ)
  let edual : ρ.dual.Equiv τ := by
    have eT := primePlusCohomologicalActionEquiv p hp ξ p E hE (j.comp σ)
    let T := (endomorphismLabelledTate (realCyclotomicField p)
      (primePlusFiber p hp ξ) p (realCyclotomicField p) E hE
      (primePlusFiberRealMultiplication p hp ξ) (j.comp σ)).toRepresentation
    have he : ρ.dual.Equiv T.dual := by
      refine .mk e.toLinearEquiv.symm.dualMap ?_
      intro g
      ext φ w
      change φ (ρ g⁻¹ (e.symm w)) = φ (e.symm (T g⁻¹ w))
      exact congrArg φ (e.symm.toIntertwiningMap.isIntertwining T ρ g⁻¹ w).symm
    exact he.trans eT.symm
  apply exists_sphericalEigenform_of_skinnerWiles_finiteComparison p ρ L H χ j.toRingHom
    ((primePlusCompatibleSystem p hp ξ A hA σ).characterTwist χ)
    (τ.characterTwist ν)
    ⟨(Representation.characterTwistTensorEquiv ρ.dual ν).trans (edual.characterTwist ν)⟩
  intro q hq P _ hP hpP Q _ _
  subst P
  exact primePlusCohomologicalAction_twist_compatible_charpoly
    p hp ξ A hA σ χ q hq Q p hpP E hE j

end HilbertModularity.Hypergeometric
