/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PadicInertia
public import HilbertModularity.RepresentationTheory.HodgeTate
public import HilbertModularity.RepresentationTheory.CharacterComparison

/-! # Finite inertia of weight-zero character periods

We follow [Caruso2019, Theorem 2.2.1]. The assertion is the rank-one
coefficient-field specialization of the theorem that a continuous finite-dimensional
Qp representation with spanning fixed Cp periods has finite inertia.
-/

@[expose] public noncomputable section
namespace HodgeTate

/-- A continuous finite-coefficient character whose actual fixed periods span
the completed tensor has finite image on actual valuation-residue inertia. -/
theorem finite_inertia_of_character_zeroWeightSpan
    (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (E : Type) [NontriviallyNormedField E] [CompleteSpace E]
    [Algebra ℚ_[p] E] [ContinuousSMul ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (χ : Gal(PadicAlgCl p/K) →* Eˣ) (hχ : Continuous χ)
    (hperiods : HodgeTate.zeroWeightSpan
      (ι := (AlgEquiv.restrictScalarsHom ℚ_[p] :
        Gal(PadicAlgCl p/K) →* Gal(PadicAlgCl p/ℚ_[p])))
      ((Representation.ofCharacter χ).restrictScalars ℚ_[p]) = ⊤) :
    (Set.range (χ.comp (PadicAlgCl.inertia p K).subtype)).Finite := by
  sorry

/-- A quotient character inherits finite inertia from the spanning fixed periods
of the actual quotient representation, using its given intertwining equivalence. -/
theorem finite_inertia_of_quotient_zeroWeightSpan
    (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (E : Type) [NontriviallyNormedField E] [CompleteSpace E]
    [Algebra ℚ_[p] E] [ContinuousSMul ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    {V : Type*} [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
    [IsScalarTower ℚ_[p] E V]
    (ρ : Representation E Gal(PadicAlgCl p/K) V) (S : Subrepresentation ρ)
    (χ : Gal(PadicAlgCl p/K) →* Eˣ) (hχ : Continuous χ)
    (e : (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
      (Representation.ofCharacter χ))
    (hperiods : zeroWeightSpan
      (ι := (AlgEquiv.restrictScalarsHom ℚ_[p] :
        Gal(PadicAlgCl p/K) →* Gal(PadicAlgCl p/ℚ_[p])))
      ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤) :
    (Set.range (χ.comp (PadicAlgCl.inertia p K).subtype)).Finite := by
  apply finite_inertia_of_character_zeroWeightSpan p K E χ hχ
  exact (zeroWeightSpan_eq_top_iff (e.restrictScalars ℚ_[p])).mp hperiods

end HodgeTate
