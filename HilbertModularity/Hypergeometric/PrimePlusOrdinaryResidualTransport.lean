/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.OrdinaryResidualTransport
public import HilbertModularity.Hypergeometric.PrimeHypergeometricChecklist

/-! # Residual ordering for the selected ordinary quotient

The two residual comparisons in the selected Jacobian's ordinary checklist
follow from its actual diagonal characters. The local intertwiner and inertia
map remain explicit, with no restriction to a cubic cusp.
-/

public noncomputable section

open AlgebraicGeometry NumberField ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms IsNonarchimedeanLocalField

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  Ideal.Quotient.field

local instance ordinaryResidualCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

local instance ordinaryResidualLocalGalCompact (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p] (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- The actual selected ordinary quotient gives a local lifting row after
ordering the given global residual pair. Both residual-character comparison
premises of the earlier interface are derived. The chosen local arithmetic
intertwiner and inertia compatibility are retained exactly. -/
theorem PrimePlusNormalizedOrdinaryData.exists_skinnerWilesOrdinaryAt_of_equiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : Continuous φ)
    (e : (Fin 2 → RealPrimePowerCompletion p 0) ≃ₗ[RealPrimePowerCompletion p 0]
      (Fin 2 → RealPrimePowerCompletion p 0))
    (hρ : ∀ (g : primeDecompositionGroup Q)
      (v : Fin 2 → RealPrimePowerCompletion p 0),
      e (ρ (g : AbsoluteGalois (realCyclotomicField p)) v) =
        d.coordinateRepresentation p hp ξ (φ g) (e v))
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois (realCyclotomicField p)) ∈
        Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
        φ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) :
    ∃ D' : SkinnerWilesResidualData ρ,
      (D' = D ∨ D' = D.swap) ∧ Nonempty (SkinnerWilesOrdinaryAt p ρ D' Q) := by
  let E := RealPrimePowerCompletion p 0
  let := d.lattice_isLattice
  let χ₁ := integerCharacter E d.upperCharacter d.upper_continuous
  let χ₂ := Representation.determinantCharacter d.lattice.toRepresentation
  have hχ₁ (g : Gal(PadicAlgCl p/E)) : ((χ₁ g : 𝒪[E]) : E) =
      (d.upperCharacter g : E) := by
    rfl
  have hχ₂ (g : Gal(PadicAlgCl p/E)) : ((χ₂ g : 𝒪[E]) : E) =
      (d.lowerCharacter g : E) := by
    exact congrArg (fun χ : Gal(PadicAlgCl p/E) →* Eˣ => (χ g : E))
      (Representation.map_determinantCharacter_characterLattice d.lowerCharacter d.lattice)
  have hentry (g : primeDecompositionGroup Q) (i j : Fin 2) :
      e (ρ g (e.symm (Pi.single j 1))) i =
        LinearMap.toMatrix d.basis d.basis
          ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ (φ g)) i j := by
    rw [hρ, e.apply_symm_apply]
    dsimp [PrimePlusNormalizedOrdinaryData.coordinateRepresentation]
    simp only [LinearMap.toMatrix_apply]
    simp
  have h2 : (2 : 𝒪[E] ⧸ 𝓂[E]) ≠ 0 := by
    let : CharP (𝒪[E] ⧸ 𝓂[E]) p := inferInstanceAs (CharP 𝓀[E] p)
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (𝒪[E] ⧸ 𝓂[E]) p 2).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hupper (g : primeDecompositionGroup Q) :
      e (ρ g (e.symm (Pi.single 0 1))) 0 = ((χ₁ (φ g) : 𝒪[E]) : E) := by
    rw [hentry, d.upperTriangular, hχ₁]
    rfl
  have hlower (g : primeDecompositionGroup Q) :
      e (ρ g (e.symm (Pi.single 1 1))) 1 = ((χ₂ (φ g) : 𝒪[E]) : E) := by
    rw [hentry, d.upperTriangular, hχ₂]
    rfl
  have horder := D.localCharacters_eq_or_swap (primeDecompositionGroup Q).subtype
    (χ₁.comp φ) (χ₂.comp φ) h2 e hupper hlower
  have make (D' : SkinnerWilesResidualData ρ)
      (h₁ : (Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom).comp (χ₁.comp φ) =
        D'.chi₁.comp (primeDecompositionGroup Q).subtype)
      (h₂ : (Units.map (Ideal.Quotient.mk 𝓂[E]).toMonoidHom).comp (χ₂.comp φ) =
        D'.chi₂.comp (primeDecompositionGroup Q).subtype) :
      Nonempty (SkinnerWilesOrdinaryAt p ρ D' Q) := by
    refine ⟨d.skinnerWilesOrdinaryAt_of_equiv p hp ξ m hm ρ D' Q φ hφ e hρ ?_ ?_ hI⟩
    · intro g
      exact congrArg (fun χ => χ g) h₁
    · intro g
      exact congrArg (fun χ => χ g) h₂
  rcases horder with h | h
  · exact ⟨D, Or.inl rfl, make D h.1 h.2⟩
  · refine ⟨D.swap, Or.inr rfl, make D.swap ?_ ?_⟩
    · simpa only [SkinnerWilesResidualData.swap_chi₁] using h.1
    · simpa only [SkinnerWilesResidualData.swap_chi₂] using h.2

end HilbertModularity.Hypergeometric
