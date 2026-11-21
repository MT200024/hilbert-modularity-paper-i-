/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricOrdinary
public import HilbertModularity.NumberTheory.CyclotomicLocalField
public import HilbertModularity.NumberTheory.IntegralCharacter
public import HilbertModularity.RepresentationTheory.HodgeTateInertia

/-! # Normalized ordinary characters of the chosen Darmon representation

The actual weight-zero quotient supplies a continuous lower diagonal
character. Its genuine fixed periods span the entire rational restriction,
so the reviewed rank-one inertia input applies. The canonical integral
character then supplies its residual character and Teichmüller normalization.
We follow [TripathiGoswami, prime ordinary lemma] and
[Caruso2019, Theorem 2.2.1].
-/

@[expose] public noncomputable section
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic AlgebraicGeometry IsNonarchimedeanLocalField
open scoped ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower
  darmonDecompositionConjugateRationalModule darmonDecompositionConjugateScalarTower

variable (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))
  (ξ : ProjectiveLine.Parameter ℚ)

local instance realPrimePowerCompletionIntegerQuotientCharP :
    CharP (𝒪[RealPrimePowerCompletion p k] ⧸ 𝓂[RealPrimePowerCompletion p k]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p k] p)

/-- A deeply ordinary chosen fibre has an actual triangular basis whose lower
character has all labelled weights zero and whose residual Teichmüller
normalization has profinite pro-p image and finite actual inertia. -/
theorem DarmonOrdinaryQuotient.exists_normalized_characters
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) (W : DarmonOrdinaryQuotient p k hN ξ m hm) :
    ∃ (b : Module.Basis (Fin 2) (RealPrimePowerCompletion p k)
        (darmonDecompositionScalarConjugate p k hN ξ m hm))
      (χ₁ χ₂ : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →*
        (RealPrimePowerCompletion p k)ˣ)
      (a : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) → RealPrimePowerCompletion p k),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ W.kernel ∧
      Nonempty (((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ.quotient
        W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).Equiv
          (Representation.ofCharacter χ₂)) ∧
      (∀ τ, ∀ q : ℤ, q ≠ 0 → HodgeTate.labelledWeightSpace p
        (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
        (Representation.ofCharacter χ₂) q τ = ⊥) ∧
      (∀ g, LinearMap.toMatrix b b ((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ g) =
        !![(χ₁ g : RealPrimePowerCompletion p k), a g; 0, (χ₂ g : RealPrimePowerCompletion p k)]) ∧
      ∃ S : Subrepresentation ((Representation.ofCharacter χ₂).restrictScalars
          𝒪[RealPrimePowerCompletion p k]),
        ∃ hS : Submodule.IsLattice (RealPrimePowerCompletion p k) S.toSubmodule,
        letI := hS
        Continuous (normalizedCharacterOfLattice (RealPrimePowerCompletion p k) p χ₂ S) ∧
        CompactSpace (normalizedCharacterOfLattice (RealPrimePowerCompletion p k) p χ₂ S).range ∧
        TotallyDisconnectedSpace
          (normalizedCharacterOfLattice (RealPrimePowerCompletion p k) p χ₂ S).range ∧
        (∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H]
          (f : (normalizedCharacterOfLattice (RealPrimePowerCompletion p k) p χ₂ S).range →* H),
          Continuous f → IsPGroup p f.range) ∧
        (Set.range ((normalizedCharacterOfLattice (RealPrimePowerCompletion p k) p χ₂ S).comp
          (PadicAlgCl.inertia p (RealPrimePowerCompletion p k)).subtype)).Finite := by
  obtain ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, hw, hp, hmat⟩ :=
    DarmonOrdinaryQuotient.exists_continuous_characters_upperTriangular p k hN ξ m hm W
  refine ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, hw, hmat, ?_⟩
  let := Valued.toNontriviallyNormedField (RealPrimePowerCompletion p k) (WithZero (Multiplicative ℤ))
  have hi := HodgeTate.finite_inertia_of_character_zeroWeightSpan p
    (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) χ₂ hχ₂ hp
  let : IsGalois (RealPrimePowerCompletion p k) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p] (RealPrimePowerCompletion p k) (PadicAlgCl p)
  exact exists_lattice_normalized_character (RealPrimePowerCompletion p k) p χ₂ hχ₂
    (PadicAlgCl.inertia p (RealPrimePowerCompletion p k)) hi

end HilbertModularity.Hypergeometric
