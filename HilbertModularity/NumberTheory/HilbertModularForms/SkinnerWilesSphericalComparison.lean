/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesFiniteComparison
public import HilbertModularity.NumberTheory.HilbertModularForms.SphericalEigenformComparison

/-! # From the Skinner--Wiles checklist to all good Hecke polynomials

Apply the covariant modularity input, absorb the finite comparison character,
extend the original compatible system to the resulting coefficient field, and
choose one spherical eigenform before the good prime. This combines the
manuscript arguments of [TripathiGoswamiRevised, Theorem `thm:prime`
and the final proof of `thm:intro-main`]. The actual geometric comparison and
Skinner--Wiles hypotheses remain explicit application inputs.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace HilbertModularity.HilbertModularForms

universe u

variable {F : Type*} [Field F] [NumberField F]

/-- One cuspidal weight-two eigenform realizes the original system's Hecke
polynomials at every good prime, after finite coefficient enlargement. The
finite character and the system use a common algebraic field with specified
local embedding; no equality with the modular form's initial field is needed.
The local action is compared to the character tensor the covariant dual.
This is a deduction from the checklist and comparison, not a new literature
input and not the assertion that the selected manuscript family meets them. -/
theorem exists_sphericalEigenform_of_skinnerWiles_finiteComparison
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    {A : Type*} [Field A] [NumberField A]
    (χ : FiniteAlgebraicGaloisCharacter F A) (k : A →+* E)
    (S : NumberFieldCompatibleSystem F A)
    {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (σ : Representation E (AbsoluteGalois F) V)
    (hcomparison : Nonempty (((Representation.ofCharacter
      ((Units.map k.toMonoidHom).comp χ.toMonoidHom)).tprod ρ.dual).Equiv σ))
    (hlocal : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map k) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F)
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        ψ.complexEmbedding = B.val.toRingHom ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (Set.range ψ.form.central_character).Finite ∧
        ∀ q, q ∉ S.bad →
          ∃ hψ : q ∉ ψ.form.bad,
            (S.polynomial q).map i = ψ.heckePolynomial q hψ := by
  obtain ⟨level, μ, C, hC, hN, φ, r, iA, hiA, hb, hc, _, ⟨e⟩⟩ :=
    exists_eigenform_of_skinnerWiles_finiteComparison_withAnalyticData
      p ρ L H χ k σ hcomparison
  let : NumberField.IsTotallyReal F := H.totally_real
  have hlocal' : ∀ q, q ∉ S.bad →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal → (p : 𝓞 F) ∉ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        (σ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
          (S.polynomial q).map (r.coefficientEmbedding.comp iA) := by
    simpa only [hiA] using hlocal
  obtain ⟨B, hB, i, level', ψ, _, hψ, _, hb', hc', _, hg⟩ :=
    r.exists_sphericalEigenform_of_mapped_localComparison hb hc S iA σ e hlocal'
  exact ⟨B, hB, i.comp iA, level', μ, ψ, hψ, hb', hc', hg⟩

end HilbertModularity.HilbertModularForms
