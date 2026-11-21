/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesCharacterTwist
public import HilbertModularity.Geometry.GroupScheme.HypergeometricOrdinaryCharacters

/-! # Transport of an ordinary local representation to a decomposition group

An identified local action supplies the ordinary entry of the prime-level
lifting checklist.  The restriction homomorphism, equality of the two actions,
residual-character comparison, and inertia containment are stated explicitly.
-/

public section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open scoped ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.HilbertModularForms

/-- Transport a normalized ordinary basis from a local Galois group to the
decomposition group of a specified prime.  In applications, `φ` must be the
actual local-to-global restriction and `hρ` the comparison on the same Tate
lattice.  The image of global inertia must lie in `I`.  The pro-`p` condition
follows from reduction one for the normalized lower character, as in
[SkinnerWiles, §4.5, Theorem A]. -/
def skinnerWilesOrdinaryAt_of_localTransport
    (p : ℕ) [Fact p.Prime]
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    {G : Type*} [Group G] [TopologicalSpace G]
    (σ : Representation E G (Fin 2 → E))
    (φ : primeDecompositionGroup Q →* G) (hφ : Continuous φ)
    (hρ : ∀ g : primeDecompositionGroup Q,
      ρ (g : AbsoluteGalois F) = σ (φ g))
    (b : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
    (δ₁ δ₂ : G →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (hδ₁ : ∀ g : primeDecompositionGroup Q,
      δ₁ (φ g) = D.chi₁ (g : AbsoluteGalois F))
    (hδ₂ : ∀ g : primeDecompositionGroup Q,
      δ₂ (φ g) = D.chi₂ (g : AbsoluteGalois F))
    (ψ₁ ψ₂ : G →* 𝒪[E]ˣ)
    (hψ₂ : Continuous ψ₂)
    (hψ₂red : ∀ g : G,
      Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E]) (ψ₂ g) = 1)
    (I : Subgroup G)
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F) → φ g ∈ I)
    (hfinite : Set.Finite {u : 𝒪[E]ˣ | ∃ g : G, g ∈ I ∧ ψ₂ g = u})
    (hzero : ∀ g : G,
      b (σ g (b.symm (Pi.single 0 1))) 1 = 0)
    (hupper : ∀ g : G,
      b (σ g (b.symm (Pi.single 0 1))) 0 =
        ((ψ₁ g : 𝒪[E]) : E) *
          ((IsNonarchimedeanLocalField.teichmullerCharacter E p δ₁ g :
            𝒪[E]) : E))
    (hlower : ∀ g : G,
      b (σ g (b.symm (Pi.single 1 1))) 1 =
        ((ψ₂ g : 𝒪[E]) : E) *
          ((IsNonarchimedeanLocalField.teichmullerCharacter E p δ₂ g :
            𝒪[E]) : E)) :
    SkinnerWilesOrdinaryAt p ρ D Q := by
  let ψ₁' : primeDecompositionGroup Q →* 𝒪[E]ˣ := ψ₁.comp φ
  let ψ₂' : primeDecompositionGroup Q →* 𝒪[E]ˣ := ψ₂.comp φ
  have hχ₁ : δ₁.comp φ = D.chi₁.comp (primeDecompositionGroup Q).subtype := by
    exact MonoidHom.ext hδ₁
  have hχ₂ : δ₂.comp φ = D.chi₂.comp (primeDecompositionGroup Q).subtype := by
    exact MonoidHom.ext hδ₂
  refine
    { basis := b
      psi₁ := ψ₁'
      psi₂ := ψ₂'
      psi₂_continuous := hψ₂.comp hφ
      psi₂_reduction := by
        intro g
        exact hψ₂red (φ g)
      psi₂_pro_p := by
        intro H _ _ _ f hf
        exact isPGroup_range_principalCharacter p ψ₂'
          (fun g => hψ₂red (φ g)) f hf
      psi₂_finite_inertia := by
        apply hfinite.subset
        rintro u ⟨g, hg, rfl⟩
        exact ⟨φ g, hI g hg, rfl⟩
      lower_left_zero := by
        intro g
        rw [hρ g]
        exact hzero (φ g)
      upper_left := by
        intro g
        rw [hρ g]
        rw [← hχ₁]
        simpa only [ψ₁', MonoidHom.comp_apply,
          IsNonarchimedeanLocalField.teichmullerCharacter,
          Ideal.teichmullerCharacter] using hupper (φ g)
      lower_right := by
        intro g
        rw [hρ g]
        rw [← hχ₂]
        simpa only [ψ₂', MonoidHom.comp_apply,
          IsNonarchimedeanLocalField.teichmullerCharacter,
          Ideal.teichmullerCharacter] using hlower (φ g) }

/-- Multiplication by the Teichmüller lift restores an integral character from
its principal-unit normalization. -/
private theorem normalizedCharacter_mul_teichmuller
    (p : ℕ) [Fact p.Prime]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    {G : Type*} [Group G] (ψ : G →* 𝒪[E]ˣ) (g : G) :
    ((IsNonarchimedeanLocalField.normalizedCharacter E p ψ g : 𝒪[E]) : E) *
      ((IsNonarchimedeanLocalField.teichmullerCharacter E p
        ((Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp ψ) g :
        𝒪[E]) : E) = ((ψ g : 𝒪[E]) : E) := by
  have h : IsNonarchimedeanLocalField.normalizedCharacter E p ψ g *
      IsNonarchimedeanLocalField.teichmullerCharacter E p
        ((Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp ψ) g = ψ g := by
    change (ψ g *
      (Ideal.teichmullerCharacter 𝓂[E] p
        ((Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp ψ) g)⁻¹) *
      Ideal.teichmullerCharacter 𝓂[E] p
        ((Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp ψ) g = ψ g
    group
  exact congrArg (fun u : 𝒪[E]ˣ => ((u : 𝒪[E]) : E)) h

/-- A triangular local action with a full stable quotient-character lattice
gives the ordinary Skinner–Wiles input after identifying its action with the
specified global prime decomposition group. The residual comparisons refer to
the very same integral characters as the diagonal entries. -/
def skinnerWilesOrdinaryAt_of_characterLattice
    (p : ℕ) [Fact p.Prime]
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [NormedField E] [ValuativeRel E]
    [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (σ : Representation E G (Fin 2 → E))
    (φ : primeDecompositionGroup Q →* G) (hφ : Continuous φ)
    (hρ : ∀ g : primeDecompositionGroup Q,
      ρ (g : AbsoluteGalois F) = σ (φ g))
    (b : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
    (χ₁ χ₂ : G →* Eˣ) (hχ₁ : Continuous χ₁) (hχ₂ : Continuous χ₂)
    (S : Subrepresentation ((Representation.ofCharacter χ₂).restrictScalars 𝒪[E]))
    [Submodule.IsLattice E S.toSubmodule]
    (δ₁ : G →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (hδ₁ : δ₁ = (Units.map (Ideal.Quotient.mk 𝓂[E] :
      𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp
        (IsNonarchimedeanLocalField.integerCharacter E χ₁ hχ₁))
    (hδ₁global : ∀ g : primeDecompositionGroup Q,
      δ₁ (φ g) = D.chi₁ (g : AbsoluteGalois F))
    (hδ₂global : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp
        (Representation.determinantCharacter S.toRepresentation)) (φ g) =
          D.chi₂ (g : AbsoluteGalois F))
    (I : Subgroup G)
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F) → φ g ∈ I)
    (hχ₂finite : (Set.range ((IsNonarchimedeanLocalField.normalizedCharacterOfLattice
      E p χ₂ S).comp I.subtype)).Finite)
    (hzero : ∀ g : G, b (σ g (b.symm (Pi.single 0 1))) 1 = 0)
    (hupper : ∀ g : G, b (σ g (b.symm (Pi.single 0 1))) 0 = (χ₁ g : E))
    (hlower : ∀ g : G, b (σ g (b.symm (Pi.single 1 1))) 1 = (χ₂ g : E)) :
    SkinnerWilesOrdinaryAt p ρ D Q := by
  let ψ₁ := IsNonarchimedeanLocalField.normalizedCharacter E p
    (IsNonarchimedeanLocalField.integerCharacter E χ₁ hχ₁)
  let ψ₂ := IsNonarchimedeanLocalField.normalizedCharacter E p
    (Representation.determinantCharacter S.toRepresentation)
  have hψ₂cont : Continuous ψ₂ := by
    let : DiscreteTopology (𝒪[E] ⧸ 𝓂[E]) :=
      QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal 𝒪[E])
    exact Ideal.continuous_teichmullerNormalizedCharacter 𝓂[E] p
      (Representation.determinantCharacter S.toRepresentation)
      (IsNonarchimedeanLocalField.continuous_characterLattice E χ₂ S
        hχ₂)
  have hψ₂red (g : G) :
      Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E]) (ψ₂ g) = 1 :=
    IsNonarchimedeanLocalField.reduction_normalizedCharacter E p
      (Representation.determinantCharacter S.toRepresentation) g
  have hψ₂finite : Set.Finite {u : 𝒪[E]ˣ | ∃ g : G, g ∈ I ∧ ψ₂ g = u} := by
    have hmap := IsNonarchimedeanLocalField.map_normalizedCharacterOfLattice E p χ₂ S
    let f : 𝒪[E]ˣ → Eˣ := Units.map (algebraMap 𝒪[E] E : 𝒪[E] →* E)
    have hf : Function.Injective f := by
      intro a c hac
      apply Units.ext
      apply Subtype.ext
      exact congrArg (fun x : Eˣ => (x : E)) hac
    have hfin : (Set.range (ψ₂.comp I.subtype)).Finite := by
      apply Set.Finite.of_finite_image (f := f)
      · convert hχ₂finite using 1
        ext x
        simp only [Set.mem_image, Set.mem_range, MonoidHom.comp_apply]
        constructor
        · rintro ⟨u, ⟨g, rfl⟩, rfl⟩
          exact ⟨g, (congrArg (fun c : G →* Eˣ => c (g : G)) hmap).symm⟩
        · rintro ⟨g, rfl⟩
          exact ⟨ψ₂ (g : G), ⟨g, rfl⟩,
            congrArg (fun c : G →* Eˣ => c (g : G)) hmap⟩
      · intro a _ c _ hac
        exact hf hac
    apply hfin.subset
    rintro u ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  exact skinnerWilesOrdinaryAt_of_localTransport p ρ D Q σ φ hφ hρ b
    δ₁ ((Units.map (Ideal.Quotient.mk 𝓂[E] : 𝒪[E] →* 𝒪[E] ⧸ 𝓂[E])).comp
      (Representation.determinantCharacter S.toRepresentation)) hδ₁global hδ₂global
    ψ₁ ψ₂ hψ₂cont hψ₂red I hI hψ₂finite hzero
    (by
      intro g
      rw [hupper g]
      rw [hδ₁]
      rw [normalizedCharacter_mul_teichmuller p
        (IsNonarchimedeanLocalField.integerCharacter E χ₁ hχ₁) g]
      rfl)
    (by
      intro g
      rw [hlower g]
      rw [normalizedCharacter_mul_teichmuller p
        (Representation.determinantCharacter S.toRepresentation) g]
      exact congrArg (fun u : Eˣ => (u : E))
        (congrArg (fun f : G →* Eˣ => f g)
          (Representation.map_determinantCharacter_characterLattice χ₂ S)).symm)

end HilbertModularity.Hypergeometric
