/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWiles
public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteTwistAnalyticProperties
public import HilbertModularity.NumberTheory.HilbertModularForms.CovariantHeckeTwistComparison

/-! # Automorphy after a finite cohomological comparison

This is the chosen-prime deduction in [TripathiGoswami, `thm:prime`, final proof paragraph]: apply Skinner--Wiles to the covariant action, retain its dual
cohomological realization, and absorb the finite comparison character by
twisting the actual eigenform. The form and character coefficient fields
need not coincide. Comparison at other coefficient places remains separate.
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel

namespace HilbertModularity.HilbertModularForms

universe u

variable {F : Type*} [Field F] [NumberField F]

/-- A finite algebraic comparison with the dual of a representation satisfying
the Skinner--Wiles checklist yields an actual cuspidal weight-two eigenform
realizing the compared action. Its coefficient field also supports an all-place
compatible system; boundedness and finite central image are retained for
simultaneous spherical replacement. The supplied character coefficient field
embeds into the new field with its original local embedding. The comparison character is tensored with the dual, with
the geometric reciprocity convention of the finite-twist construction. -/
theorem exists_eigenform_of_skinnerWiles_finiteComparison_withAnalyticData
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    {B : Type*} [Field B] [NumberField B]
    (χ : FiniteAlgebraicGaloisCharacter F B) (k : B →+* E)
    {V : Type*} [AddCommGroup V] [Module E V]
    (σ : Representation E (AbsoluteGalois F) V)
    (hcomparison : Nonempty (((Representation.ofCharacter
      ((Units.map k.toMonoidHom).comp χ.toMonoidHom)).tprod ρ.dual).Equiv σ)) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (C : Type u)
      (hC : Field C),
      letI : Field C := hC
      ∃ hN : NumberField C,
        letI : NumberField C := hN
        ∃ ψ : AlgebraicGoodPrimeEigenform level μ C,
          ∃ (r : CohomologicalRealization ψ p E) (i : B →+* C),
            r.coefficientEmbedding.comp i = k ∧
            (∃ D : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ D) ∧
            (Set.range ψ.form.central_character).Finite ∧
            Nonempty (EigenformCompatibleSystem ψ) ∧ Nonempty (σ.Equiv r.action) := by
  obtain ⟨level, μ, A, hA, hN, φ, r, hb, hz, ⟨e⟩⟩ :=
    skinnerWiles_weightTwoEigenform_withAnalyticData p ρ L H
  let : NumberField.IsTotallyReal F := H.totally_real
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
  obtain ⟨c, a, s, ψ, r', _, _, _, _, _, hcoeff, hb', hz', hsys, ⟨etwist⟩⟩ :=
    r.exists_finiteTwist_compatibleSystem χ k hb hz
  let ν := (Units.map k.toMonoidHom).comp χ.toMonoidHom
  let etensor := (Representation.characterTwistTensorEquiv ρ.dual ν).trans
    ((e.characterTwist ν).trans (Representation.characterTwistTensorEquiv r.action ν).symm)
  refine ⟨s.level, μ, coefficientCompositum r.coefficientEmbedding k,
    inferInstance, inferInstance, ψ, r',
    coefficientCompositum.right r.coefficientEmbedding k, ?_, hb', hz', hsys,
    ⟨hcomparison.some.symm.trans (etensor.trans etwist)⟩⟩
  rw [hcoeff]
  exact coefficientCompositum.val_comp_right r.coefficientEmbedding k

/-- A finite algebraic comparison with the dual of a representation satisfying
the Skinner--Wiles checklist yields an actual cuspidal weight-two eigenform
realizing the compared action. Its coefficient field also supports an all-place
compatible system. The comparison character is tensored with the dual, with
the geometric reciprocity convention of the finite-twist construction. -/
theorem exists_eigenform_of_skinnerWiles_finiteComparison
    (p : ℕ) [Fact p.Prime]
    {E : Type u} [NormedField E] [ValuativeRel E]
    [NormedAlgebra ℚ_[p] E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L]
    (H : SkinnerWilesWeightTwoInput p ρ L)
    {B : Type*} [Field B] [NumberField B]
    (χ : FiniteAlgebraicGaloisCharacter F B) (k : B →+* E)
    {V : Type*} [AddCommGroup V] [Module E V]
    (σ : Representation E (AbsoluteGalois F) V)
    (hcomparison : Nonempty (((Representation.ofCharacter
      ((Units.map k.toMonoidHom).comp χ.toMonoidHom)).tprod ρ.dual).Equiv σ)) :
    ∃ (level : FiniteLevel F) (μ : AdditiveQuotientMeasure F) (C : Type u)
      (hC : Field C),
      letI : Field C := hC
      ∃ hN : NumberField C,
        letI : NumberField C := hN
        ∃ ψ : AlgebraicGoodPrimeEigenform level μ C,
          ∃ r : CohomologicalRealization ψ p E,
            Nonempty (EigenformCompatibleSystem ψ) ∧ Nonempty (σ.Equiv r.action) := by
  obtain ⟨level, μ, C, hC, hN, ψ, r, _, _, _, _, hsys, he⟩ :=
    exists_eigenform_of_skinnerWiles_finiteComparison_withAnalyticData p ρ L H χ k σ
      hcomparison
  exact ⟨level, μ, C, hC, hN, ψ, r, hsys, he⟩

end HilbertModularity.HilbertModularForms
