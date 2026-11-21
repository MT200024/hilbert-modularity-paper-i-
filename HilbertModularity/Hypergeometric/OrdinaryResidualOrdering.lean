/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesInput
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Ordering the residual characters of an ordinary quotient

Equality of the trace characters fixes one ordering on the entire decomposition
group. This supplies the residual ordering step in
[TripathiGoswamiRevised, Proposition `SW-checklist`], independently of the
special quotient character at a cubic cusp.
-/

public noncomputable section

namespace MonoidHom

/-- Dedekind independence makes a sum of two multiplicative characters
identify the unordered pair globally. Characteristic two is excluded because
two copies of any character would otherwise have zero sum. -/
theorem eq_and_eq_or_eq_and_eq_of_add_eq_add
    {G K : Type*} [MulOneClass G] [Field K]
    {a b c d : G →* K} (h2 : (2 : K) ≠ 0)
    (h : ∀ g, a g + b g = c g + d g) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hs : Finsupp.single a (1 : K) + Finsupp.single b 1 =
      Finsupp.single c 1 + Finsupp.single d 1 := by
    apply (linearIndependent_monoidHom G K).finsuppLinearCombination_injective
    simp only [map_add, Finsupp.linearCombination_single, one_smul]
    ext g
    exact h g
  have ha : a = c ∨ a = d := by
    by_contra hn
    push Not at hn
    have hx := congrArg (fun f : (G →* K) →₀ K => f a) hs
    by_cases hab : b = a
    · simp [hab, Ne.symm hn.1, Ne.symm hn.2] at hx
      exact h2 (by simpa only [one_add_one_eq_two] using hx)
    · simp [hab, Ne.symm hn.1, Ne.symm hn.2] at hx
  rcases ha with rfl | rfl
  · exact Or.inl ⟨rfl, MonoidHom.ext fun g => add_left_cancel (h g)⟩
  · exact Or.inr ⟨rfl, MonoidHom.ext fun g => by
      have hg := h g
      rw [add_comm (c g) (a g)] at hg
      exact add_left_cancel hg⟩

end MonoidHom

namespace HilbertModularity.HilbertModularForms

open scoped NumberField ValuativeRel

attribute [local instance] Ideal.Quotient.field

/-- An integral ordinary pair whose field trace is the trace of the given
representation has the same residual characters, in one of the two global
orders. The basis or lattice used for the ordinary pair need not be the
integral basis stored in `D`. -/
theorem SkinnerWilesResidualData.localCharacters_eq_or_swap_of_trace
    {F E G : Type*} [Field F] [NumberField F] [Field E] [ValuativeRel E]
    [Group G]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ)
    (φ : G →* AbsoluteGalois F) (χ₁ χ₂ : G →* 𝒪[E]ˣ)
    (h2 : (2 : 𝒪[E] ⧸ 𝓂[E]) ≠ 0)
    (htrace : ∀ g, LinearMap.trace E (Fin 2 → E) (ρ (φ g)) =
      ((χ₁ g : 𝒪[E]) : E) + ((χ₂ g : 𝒪[E]) : E)) :
    let red := Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom
    (red.comp χ₁ = D.chi₁.comp φ ∧ red.comp χ₂ = D.chi₂.comp φ) ∨
      (red.comp χ₁ = D.chi₂.comp φ ∧ red.comp χ₂ = D.chi₁.comp φ) := by
  classical
  let red := Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom
  have hsum (g : G) :
      ((red.comp χ₁) g : 𝒪[E] ⧸ 𝓂[E]) + ((red.comp χ₂) g : 𝒪[E] ⧸ 𝓂[E]) =
      (D.chi₁ (φ g) : 𝒪[E] ⧸ 𝓂[E]) + (D.chi₂ (φ g) : 𝒪[E] ⧸ 𝓂[E]) := by
    have hint : LinearMap.trace 𝒪[E] (Fin 2 → 𝒪[E]) (D.integralAction (φ g)) =
        (χ₁ g : 𝒪[E]) + (χ₂ g : 𝒪[E]) := by
      apply Subtype.val_injective
      have ht := htrace g
      rw [LinearMap.trace_eq_matrix_trace E (Pi.basisFun E (Fin 2))] at ht
      rw [LinearMap.trace_eq_matrix_trace 𝒪[E] (Pi.basisFun 𝒪[E] (Fin 2))]
      simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two,
        LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr] at ht ⊢
      change ((D.integralAction (φ g) (Pi.single 0 1) 0 : 𝒪[E]) : E) +
        ((D.integralAction (φ g) (Pi.single 1 1) 1 : 𝒪[E]) : E) = _
      rw [D.integral_spec, D.integral_spec]
      exact ht
    rw [← D.residual_trace (φ g), hint, map_add]
    rfl
  have hs := MonoidHom.eq_and_eq_or_eq_and_eq_of_add_eq_add
    (G := G) (K := 𝒪[E] ⧸ 𝓂[E]) h2
    (a := (Units.coeHom (𝒪[E] ⧸ 𝓂[E])).comp (red.comp χ₁))
    (b := (Units.coeHom (𝒪[E] ⧸ 𝓂[E])).comp (red.comp χ₂))
    (c := (Units.coeHom (𝒪[E] ⧸ 𝓂[E])).comp (D.chi₁.comp φ))
    (d := (Units.coeHom (𝒪[E] ⧸ 𝓂[E])).comp (D.chi₂.comp φ)) (fun g => hsum g)
  have hinj : Function.Injective (fun f : G →* (𝒪[E] ⧸ 𝓂[E])ˣ =>
      (Units.coeHom (𝒪[E] ⧸ 𝓂[E])).comp f) := by
    intro f g hfg
    ext x
    exact congrArg (fun h : G →* (𝒪[E] ⧸ 𝓂[E]) => h x) hfg
  rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨hinj h₁, hinj h₂⟩
  · exact Or.inr ⟨hinj h₁, hinj h₂⟩

/-- The two integral diagonal characters in any ordinary basis reduce to
one fixed ordering of the given global residual characters on the whole
local group. No comparison of the two integral bases is required. -/
theorem SkinnerWilesResidualData.localCharacters_eq_or_swap
    {F E G : Type*} [Field F] [NumberField F] [Field E] [ValuativeRel E]
    [Group G]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ)
    (φ : G →* AbsoluteGalois F) (χ₁ χ₂ : G →* 𝒪[E]ˣ)
    (h2 : (2 : 𝒪[E] ⧸ 𝓂[E]) ≠ 0)
    (b : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
    (hupper : ∀ g, b (ρ (φ g) (b.symm (Pi.single 0 1))) 0 =
      ((χ₁ g : 𝒪[E]) : E))
    (hlower : ∀ g, b (ρ (φ g) (b.symm (Pi.single 1 1))) 1 =
      ((χ₂ g : 𝒪[E]) : E)) :
    let red := Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom
    (red.comp χ₁ = D.chi₁.comp φ ∧ red.comp χ₂ = D.chi₂.comp φ) ∨
      (red.comp χ₁ = D.chi₂.comp φ ∧ red.comp χ₂ = D.chi₁.comp φ) := by
  apply D.localCharacters_eq_or_swap_of_trace φ χ₁ χ₂ h2
  intro g
  rw [← LinearMap.trace_conj' (ρ (φ g)) b,
    LinearMap.trace_eq_matrix_trace E (Pi.basisFun E (Fin 2))]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hupper, hlower]

end HilbertModularity.HilbertModularForms
