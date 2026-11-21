/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.OrdinaryResidualOrdering
public import HilbertModularity.Hypergeometric.ModularityOrdinaryTransport
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementOrdering

/-! # The ordinary lifting row with a derived residual ordering

The ordinary basis and finite normalized inertia give the local Skinner–Wiles
row after ordering the actual global residual pair. The order is derived from
the trace, rather than supplied as a comparison of separately chosen lattices.
-/

public noncomputable section

open NumberField ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularForms

/-- An ordinary basis with integral diagonal characters and finite normalized
lower inertia supplies the local lifting row for the original residual datum
or its swap. Both choices retain the same integral action. This is the
residual-ordering deduction in [TripathiGoswamiRevised, Proposition
`SW-checklist`]; existence of the ordinary quotient remains a separate input. -/
theorem exists_skinnerWilesOrdinaryAt_of_integralCharacters
    (p : ℕ) [Fact p.Prime]
    {F E : Type*} [Field F] [NumberField F]
    [NormedField E] [ValuativeRel E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    (b : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
    (χ₁ χ₂ : primeDecompositionGroup Q →* 𝒪[E]ˣ)
    (hχ₂ : Continuous χ₂)
    (h2 : (2 : 𝒪[E] ⧸ 𝓂[E]) ≠ 0)
    (hzero : ∀ g : primeDecompositionGroup Q,
      b (ρ g (b.symm (Pi.single 0 1))) 1 = 0)
    (hupper : ∀ g : primeDecompositionGroup Q,
      b (ρ g (b.symm (Pi.single 0 1))) 0 = ((χ₁ g : 𝒪[E]) : E))
    (hlower : ∀ g : primeDecompositionGroup Q,
      b (ρ g (b.symm (Pi.single 1 1))) 1 = ((χ₂ g : 𝒪[E]) : E))
    (hfinite : Set.Finite {u : 𝒪[E]ˣ | ∃ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F) ∧
        IsNonarchimedeanLocalField.normalizedCharacter E p χ₂ g = u}) :
    ∃ D' : SkinnerWilesResidualData ρ,
      (D' = D ∨ D' = D.swap) ∧ Nonempty (SkinnerWilesOrdinaryAt p ρ D' Q) := by
  let red := Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom
  let δ₁ := red.comp χ₁
  let δ₂ := red.comp χ₂
  have hnorm (χ : primeDecompositionGroup Q →* 𝒪[E]ˣ)
      (g : primeDecompositionGroup Q) :
      ((IsNonarchimedeanLocalField.normalizedCharacter E p χ g : 𝒪[E]) : E) *
        ((IsNonarchimedeanLocalField.teichmullerCharacter E p (red.comp χ) g :
          𝒪[E]) : E) = ((χ g : 𝒪[E]) : E) := by
    have hu : IsNonarchimedeanLocalField.normalizedCharacter E p χ g *
        IsNonarchimedeanLocalField.teichmullerCharacter E p (red.comp χ) g = χ g := by
      change (χ g * (Ideal.teichmullerCharacter 𝓂[E] p (red.comp χ) g)⁻¹) *
        Ideal.teichmullerCharacter 𝓂[E] p (red.comp χ) g = χ g
      group
    exact congrArg (fun u : 𝒪[E]ˣ => ((u : 𝒪[E]) : E)) hu
  have hnormcont : Continuous (IsNonarchimedeanLocalField.normalizedCharacter E p χ₂) := by
    let : DiscreteTopology (𝒪[E] ⧸ 𝓂[E]) :=
      QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal 𝒪[E])
    exact Ideal.continuous_teichmullerNormalizedCharacter 𝓂[E] p χ₂ hχ₂
  have make (D' : SkinnerWilesResidualData ρ)
      (h₁ : δ₁ = D'.chi₁.comp (primeDecompositionGroup Q).subtype)
      (h₂ : δ₂ = D'.chi₂.comp (primeDecompositionGroup Q).subtype) :
      Nonempty (SkinnerWilesOrdinaryAt p ρ D' Q) := by
    refine ⟨skinnerWilesOrdinaryAt_of_localTransport p ρ D' Q
      (ρ.comp (primeDecompositionGroup Q).subtype) (MonoidHom.id _) continuous_id
      (fun _ => rfl) b δ₁ δ₂
      (fun g => congrArg (fun χ => χ g) h₁)
      (fun g => congrArg (fun χ => χ g) h₂)
      (IsNonarchimedeanLocalField.normalizedCharacter E p χ₁)
      (IsNonarchimedeanLocalField.normalizedCharacter E p χ₂)
      hnormcont (fun g => IsNonarchimedeanLocalField.reduction_normalizedCharacter E p χ₂ g)
      ((Q.inertia (AbsoluteGalois F)).comap (primeDecompositionGroup Q).subtype)
      (fun _ h => h) hfinite hzero ?_ ?_⟩
    · intro g
      exact (hupper g).trans (hnorm χ₁ g).symm
    · intro g
      exact (hlower g).trans (hnorm χ₂ g).symm
  rcases D.localCharacters_eq_or_swap (primeDecompositionGroup Q).subtype
    χ₁ χ₂ h2 b hupper hlower with h | h
  · exact ⟨D, Or.inl rfl, make D h.1 h.2⟩
  · refine ⟨D.swap, Or.inr rfl, make D.swap ?_ ?_⟩
    · simpa only [SkinnerWilesResidualData.swap_chi₁] using h.1
    · simpa only [SkinnerWilesResidualData.swap_chi₂] using h.2

end HilbertModularity.Hypergeometric
