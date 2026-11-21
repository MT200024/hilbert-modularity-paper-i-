/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization
public import HilbertModularity.NumberTheory.TeichmullerCharacter
public import HilbertModularity.NumberTheory.CyclotomicCharacter
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RepresentationTheory.Irreducible

/-! # The residually reducible Skinner--Wiles input

The data below retain the integral residual representation, the field cut out
by the ratio of its two characters, and an adapted local basis at every prime
above `p`. This is the covariant convention of [SkinnerWiles, §4.5, Theorem A].
-/

public noncomputable section

open NumberField IsDedekindDomain
open scoped ValuativeRel
open ValuativeRel

namespace HilbertModularity.HilbertModularForms

section General

variable {F : Type*} [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [ValuativeRel E]

/-- An integral lattice in a rank-two covariant representation, together with
its two residual semisimplification characters. Equality of trace and
determinant at every group element records the semisimplification rather than
an arbitrary splitting of the residual representation. -/
structure SkinnerWilesResidualData
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)) where
  integralAction : Representation (𝒪[E]) (AbsoluteGalois F) (Fin 2 → 𝒪[E])
  integral_spec : ∀ g i j,
    ((integralAction g (Pi.single j 1) i : 𝒪[E]) : E) =
      ρ g (Pi.single j 1) i
  chi₁ : AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ
  chi₂ : AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ
  residual_trace : ∀ g,
    (Ideal.Quotient.mk (𝓂[E])
      (LinearMap.trace (𝒪[E]) (Fin 2 → 𝒪[E]) (integralAction g))) =
        (chi₁ g : 𝒪[E] ⧸ 𝓂[E]) + (chi₂ g : 𝒪[E] ⧸ 𝓂[E])
  residual_det : ∀ g,
    (Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g))) =
        (chi₁ g : 𝒪[E] ⧸ 𝓂[E]) * (chi₂ g : 𝒪[E] ⧸ 𝓂[E])

/-- The ratio of the residual characters in Theorem A. -/
def residualRatio {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) :
    AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ :=
  { toFun := fun g => D.chi₁ g * (D.chi₂ g)⁻¹
    map_one' := by simp
    map_mul' := by
      intro g h
      simp only [map_mul, mul_inv_rev]
      apply Units.ext
      simp [mul_comm, mul_left_comm, mul_assoc] }

omit [NumberField F] in
@[simp]
theorem residualRatio_apply
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) (g : AbsoluteGalois F) :
    residualRatio D g = D.chi₁ g * (D.chi₂ g)⁻¹ := (rfl)

/-- A finite extension cut out exactly by the residual ratio. Its embedding
in the chosen algebraic closure identifies the kernel of the ratio with the
subgroup fixing this field, so abelianity concerns the actual ratio field. -/
structure SkinnerWilesRatioField
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ)
    (L : Type*) [Field L] [NumberField L] [Algebra F L] where
  embedding : L →ₐ[F] AlgebraicClosure F
  galois_over_rat : IsGalois ℚ L
  abelian_over_rat : ∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ
  cuts_out_ratio : ∀ g : AbsoluteGalois F,
    residualRatio D g = 1 ↔
      ∀ x : L, g (embedding x) = embedding x

/-- The actual decomposition subgroup of a prime of the algebraic closure:
an automorphism lies in it exactly when it preserves ideal membership. This
form uses the available Galois action on algebraic integers directly. -/
def primeDecompositionGroup
    (Q : Ideal (𝓞 (AlgebraicClosure F))) : Subgroup (AbsoluteGalois F) where
  carrier := {g | ∀ x : 𝓞 (AlgebraicClosure F), x ∈ Q ↔ g • x ∈ Q}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro g h hg hh x
    simpa only [mul_smul] using (hh x).trans (hg (h • x))
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    simpa only [smul_smul, mul_inv_cancel, one_smul] using h.symm

omit [NumberField F] in
/-- Membership in the decomposition group is preservation of the chosen
prime's ideal membership under the Galois action. -/
theorem mem_primeDecompositionGroup_iff
    (Q : Ideal (𝓞 (AlgebraicClosure F))) (g : AbsoluteGalois F) :
    g ∈ primeDecompositionGroup Q ↔
      ∀ x : 𝓞 (AlgebraicClosure F), x ∈ Q ↔ g • x ∈ Q := (Iff.rfl)

omit [NumberField F] in
/-- Every inertia element preserves its prime. Thus the inertia condition on
the local ordinary character below ranges over the whole inertia group. -/
theorem inertia_mem_primeDecompositionGroup
    (Q : Ideal (𝓞 (AlgebraicClosure F)))
    (g : AbsoluteGalois F)
    (hg : g ∈ Q.inertia (AbsoluteGalois F)) :
    g ∈ primeDecompositionGroup Q := by
  have hmem (u : AbsoluteGalois F)
      (hu : u ∈ Q.inertia (AbsoluteGalois F))
      (x : 𝓞 (AlgebraicClosure F)) (hx : x ∈ Q) : u • x ∈ Q := by
    change (∀ y : 𝓞 (AlgebraicClosure F), u • y - y ∈ Q) at hu
    simpa only [sub_add_cancel] using Q.add_mem (hu x) hx
  intro x
  constructor
  · exact hmem g hg x
  · intro hx
    have h := hmem g⁻¹ (inv_mem hg) (g • x) hx
    simpa only [smul_smul, inv_mul_cancel, one_smul] using h

section WeightTwo

variable [NormedField E] [NormedAlgebra ℚ_[p] E]
  [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [CharP (𝒪[E] ⧸ 𝓂[E]) p]

/-- The local ordinary shape of a covariant representation at a chosen prime
of the algebraic closure. The matrix is written in an adapted basis. Its
lower-right character is the Teichmüller lift of `chi₂` times a normalized
character with pro-`p` image and finite inertia image, exactly as in
[SkinnerWiles, §4.5, Theorem A]. -/
structure SkinnerWilesOrdinaryAt
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] where
  basis : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E)
  psi₁ : primeDecompositionGroup Q →* 𝒪[E]ˣ
  psi₂ : primeDecompositionGroup Q →* 𝒪[E]ˣ
  psi₂_continuous : Continuous psi₂
  psi₂_reduction : ∀ g,
    Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E]) (psi₂ g) = 1
  psi₂_pro_p : ∀ {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : psi₂.range →* H), Continuous f → IsPGroup p f.range
  psi₂_finite_inertia :
    Set.Finite {u : 𝒪[E]ˣ | ∃ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F) ∧ psi₂ g = u}
  lower_left_zero : ∀ g : primeDecompositionGroup Q,
    basis (ρ (g : AbsoluteGalois F) (basis.symm (Pi.single 0 1))) 1 = 0
  upper_left : ∀ g : primeDecompositionGroup Q,
    basis (ρ (g : AbsoluteGalois F) (basis.symm (Pi.single 0 1))) 0 =
      ((psi₁ g : 𝒪[E]) : E) *
        ((IsNonarchimedeanLocalField.teichmullerCharacter E p
          (D.chi₁.comp (primeDecompositionGroup Q).subtype) g :
          𝒪[E]) : E)
  lower_right : ∀ g : primeDecompositionGroup Q,
    basis (ρ (g : AbsoluteGalois F) (basis.symm (Pi.single 1 1))) 1 =
      ((psi₂ g : 𝒪[E]) : E) *
        ((IsNonarchimedeanLocalField.teichmullerCharacter E p
          (D.chi₂.comp (primeDecompositionGroup Q).subtype) g :
          𝒪[E]) : E)

end WeightTwo
end General

section WeightTwoInput

variable {F : Type*} [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [NormedField E] [ValuativeRel E]
variable [Algebra ℚ_[p] E] [ContinuousSMul ℚ_[p] E]
  [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [CharP (𝒪[E] ⧸ 𝓂[E]) p]

/-- The full weight-two specialization of the hypotheses of
[SkinnerWiles, §4.5, Theorem A]. `ρ` is covariant. The residual trace and
determinant are in `SkinnerWilesResidualData`; the actual ratio extension is
`SkinnerWilesRatioField`. The oddness predicate ranges over every genuine
complex conjugation, specified by an embedding of the algebraic closure in
`ℂ`. Its determinant uses the chosen continuous `ℚ_[p]`-algebra map into the
coefficient field; a norm inequality for that algebra map is not part of
these input data. -/
structure SkinnerWilesWeightTwoInput
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (L : Type*) [Field L] [NumberField L] [Algebra F L] where
  p_odd : Odd p
  totally_real : NumberField.IsTotallyReal F
  galois_over_rat : IsGalois ℚ F
  abelian_over_rat : ∀ σ τ : F ≃ₐ[ℚ] F, σ * τ = τ * σ
  continuous : ∀ i j : Fin 2,
    Continuous (fun g : AbsoluteGalois F => ρ g (Pi.single j 1) i)
  absolutely_irreducible :
    (Representation.baseChange (AlgebraicClosure E) ρ).IsIrreducible
  ramified : Set (HeightOneSpectrum (𝓞 F))
  ramified_finite : ramified.Finite
  unramified : ∀ q, q ∉ ramified →
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
    ∀ g : AbsoluteGalois F, g ∈ Q.inertia (AbsoluteGalois F) → ρ g = 1
  residual : SkinnerWilesResidualData ρ
  ratio_field : SkinnerWilesRatioField residual L
  ratio_odd : ∀ c : AbsoluteGalois F,
    (∃ ι : AlgebraicClosure F →+* ℂ,
      ∀ x : AlgebraicClosure F, ι (c x) = star (ι x)) →
    ((residualRatio residual c : 𝒪[E] ⧸ 𝓂[E]) = -1)
  local_ordinary : ∀ (P : Ideal (𝓞 F)) [P.IsMaximal],
    (p : 𝓞 F) ∈ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
    SkinnerWilesOrdinaryAt p ρ residual Q
  ratio_distinguished : ∀ (P : Ideal (𝓞 F)) [P.IsMaximal],
    (p : 𝓞 F) ∈ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
    ∃ g : primeDecompositionGroup Q,
      residualRatio residual (g : AbsoluteGalois F) ≠ 1
  finite_det_character : AbsoluteGalois F →* Eˣ
  finite_det_range : (Set.range finite_det_character).Finite
  determinant : ∀ g : AbsoluteGalois F,
    LinearMap.det (ρ g) =
      (finite_det_character g : E) *
        (Field.cyclotomicCharacterWithCoefficients F p E g : E)

end WeightTwoInput

end HilbertModularity.HilbertModularForms
