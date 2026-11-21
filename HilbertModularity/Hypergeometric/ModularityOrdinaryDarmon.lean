/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ModularityOrdinaryTransport

/-! # The chosen Darmon ordinary quotient in the lifting checklist

The actual local quotient supplies a triangular basis and an integral
quotient-character lattice. Comparisons with the global coefficient-labelled
representation and its residual lattice remain explicit arithmetic premises.
-/

public section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open scoped ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.HilbertModularForms HilbertModularity.Cyclotomic AlgebraicGeometry

attribute [local instance] realPrimePowerCompletionIntegerQuotientCharP
  realPrimePowerCompletionPadicAlgebra realPrimePowerCompletionPadicTower
  realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower
  darmonDecompositionConjugateRationalModule darmonDecompositionConjugateScalarTower

local instance realPrimePowerCompletionGalCompact (p k : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p k)) := by
  let : IsGalois (RealPrimePowerCompletion p k) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p k) (PadicAlgCl p)
  infer_instance

/-- The triangular basis, characters and quotient lattice of an actual
ordinary Darmon local representation. Finite inertia is imposed on the
normalized character of this very lattice. -/
structure DarmonNormalizedOrdinaryData
    (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))
    (ξ : ProjectiveLine.Parameter ℚ) (m : ℕ)
    (hm : m.Coprime (p ^ (k + 1))) where
  basis : Module.Basis (Fin 2) (RealPrimePowerCompletion p k)
    (darmonDecompositionScalarConjugate p k hN ξ m hm)
  upperCharacter : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →*
    (RealPrimePowerCompletion p k)ˣ
  lowerCharacter : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →*
    (RealPrimePowerCompletion p k)ˣ
  upperRight : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →
    RealPrimePowerCompletion p k
  upper_continuous : Continuous upperCharacter
  lower_continuous : Continuous lowerCharacter
  lower_zero_labelled_weights : ∀ τ, ∀ q : ℤ, q ≠ 0 →
    HodgeTate.labelledWeightSpace p
      (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
      (Representation.ofCharacter lowerCharacter) q τ = ⊥
  lattice : Subrepresentation ((Representation.ofCharacter lowerCharacter).restrictScalars
    𝒪[RealPrimePowerCompletion p k])
  lattice_isLattice : Submodule.IsLattice (RealPrimePowerCompletion p k)
    lattice.toSubmodule
  upperTriangular : ∀ g,
    LinearMap.toMatrix basis basis
      ((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ g) =
        !![(upperCharacter g : RealPrimePowerCompletion p k), upperRight g;
          0, (lowerCharacter g : RealPrimePowerCompletion p k)]
  finite_normalized_inertia :
    letI := lattice_isLattice
    (Set.range ((IsNonarchimedeanLocalField.normalizedCharacterOfLattice
      (RealPrimePowerCompletion p k) p lowerCharacter lattice).comp
        (PadicAlgCl.inertia p (RealPrimePowerCompletion p k)).subtype)).Finite

/-- The chosen-family weight-zero quotient produces concrete normalized
ordinary data; see [TripathiGoswamiRevised, Lemma `primeordinary`] and
[Caruso2019, Theorem 2.2.1]. -/
theorem DarmonOrdinaryQuotient.exists_normalizedOrdinaryData
    (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))
    (ξ : ProjectiveLine.Parameter ℚ) (m : ℕ)
    (hm : m.Coprime (p ^ (k + 1)))
    (W : DarmonOrdinaryQuotient p k hN ξ m hm) :
    Nonempty (DarmonNormalizedOrdinaryData p k hN ξ m hm) := by
  obtain ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, _, _, hzero, hmat, S, hS,
      _, _, _, _, hfinite⟩ :=
    W.exists_normalized_characters p k hN ξ m hm
  exact ⟨⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hzero, S, hS, hmat, hfinite⟩⟩

/-- Coordinate action of the actual chosen Darmon local representation in
its ordinary basis. -/
def DarmonNormalizedOrdinaryData.coordinateRepresentation
    {p k : ℕ} [Fact p.Prime] {hN : 3 ≤ p ^ (k + 1)}
    {ξ : ProjectiveLine.Parameter ℚ} {m : ℕ}
    {hm : m.Coprime (p ^ (k + 1))}
    (d : DarmonNormalizedOrdinaryData p k hN ξ m hm) :
    Representation (RealPrimePowerCompletion p k)
      (Gal(PadicAlgCl p/RealPrimePowerCompletion p k))
      (Fin 2 → RealPrimePowerCompletion p k) :=
  d.basis.equivFun.conjRingEquiv.toMonoidHom.comp
    (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ

/-- The chosen-family ordinary quotient supplies the local lifting input
once local restriction, same-lattice residual characters, and inertia have
been identified. See [TripathiGoswamiRevised, Proposition
`SW-checklist`] and [SkinnerWiles, §4.5, Theorem A]. -/
def DarmonNormalizedOrdinaryData.skinnerWilesOrdinaryAt
    (p k : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p k)]
    (hN : 3 ≤ p ^ (k + 1))
    (ξ : ProjectiveLine.Parameter ℚ) (m : ℕ)
    (hm : m.Coprime (p ^ (k + 1)))
    (d : DarmonNormalizedOrdinaryData p k hN ξ m hm)
    {F : Type*} [Field F] [NumberField F]
    (ρ : Representation (RealPrimePowerCompletion p k)
      (AbsoluteGalois F) (Fin 2 → RealPrimePowerCompletion p k))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal]
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p k))
    (hφ : Continuous φ)
    (hρ : ∀ g : primeDecompositionGroup Q,
      ρ (g : AbsoluteGalois F) = d.coordinateRepresentation (φ g))
    (hδ₁ : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p k] :
          𝒪[RealPrimePowerCompletion p k] →*
            𝒪[RealPrimePowerCompletion p k] ⧸ 𝓂[RealPrimePowerCompletion p k])).comp
        (IsNonarchimedeanLocalField.integerCharacter
          (RealPrimePowerCompletion p k) d.upperCharacter d.upper_continuous)) (φ g) =
        D.chi₁ (g : AbsoluteGalois F))
    (hδ₂ : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p k] :
          𝒪[RealPrimePowerCompletion p k] →*
            𝒪[RealPrimePowerCompletion p k] ⧸ 𝓂[RealPrimePowerCompletion p k])).comp
        (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
        D.chi₂ (g : AbsoluteGalois F))
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois F) ∈ Q.inertia (AbsoluteGalois F) →
        φ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p k)) :
    SkinnerWilesOrdinaryAt p ρ D Q := by
  letI : IsGalois (RealPrimePowerCompletion p k) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p k) (PadicAlgCl p)
  letI := d.lattice_isLattice
  let σ := d.coordinateRepresentation
  have hentry (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k))
      (i j : Fin 2) :
      σ g (Pi.single j 1) i =
        LinearMap.toMatrix d.basis d.basis
          ((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ g) i j := by
    change d.basis.equivFun
      ((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ g
        (d.basis.equivFun.symm (Pi.single j 1))) i = _
    simp only [LinearMap.toMatrix_apply]
    simp
  exact skinnerWilesOrdinaryAt_of_characterLattice p ρ D Q σ φ hφ hρ
    (LinearEquiv.refl _ _) d.upperCharacter d.lowerCharacter
    d.upper_continuous d.lower_continuous d.lattice
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p k] :
      𝒪[RealPrimePowerCompletion p k] →*
        𝒪[RealPrimePowerCompletion p k] ⧸ 𝓂[RealPrimePowerCompletion p k])).comp
      (IsNonarchimedeanLocalField.integerCharacter
        (RealPrimePowerCompletion p k) d.upperCharacter d.upper_continuous))
    rfl hδ₁ hδ₂ (PadicAlgCl.inertia p (RealPrimePowerCompletion p k))
    hI d.finite_normalized_inertia
    (by
      intro g
      change σ g (Pi.single 0 1) 1 = 0
      rw [hentry g 1 0, d.upperTriangular g]
      rfl)
    (by
      intro g
      change σ g (Pi.single 0 1) 0 = (d.upperCharacter g : RealPrimePowerCompletion p k)
      rw [hentry g 0 0, d.upperTriangular g]
      rfl)
    (by
      intro g
      change σ g (Pi.single 1 1) 1 = (d.lowerCharacter g : RealPrimePowerCompletion p k)
      rw [hentry g 1 1, d.upperTriangular g]
      rfl)

end HilbertModularity.Hypergeometric
