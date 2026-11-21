/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.LabelledHodgeTate
public import HilbertModularity.RepresentationTheory.CyclotomicCoefficients

/-! # Coefficient conjugation and labelled weight-zero quotients

Scalar conjugation transports actual stable quotients and their period spaces.
The all-labelled weight-zero condition is unchanged, as required by the
local coefficient labels in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E G : Type*} [Field K] [Field E] [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
  [FiniteDimensional ℚ_[p] K] [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
  [Group G] (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  (σ : E ≃ₐ[ℚ_[p]] E) (A : Rep E G)
  [Module ℚ_[p] A] [IsScalarTower ℚ_[p] E A]
  [Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv A)]
  [IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv A)]

/-- All local labels have only weight zero before coefficient conjugation exactly when they do after. -/
theorem scalarConjugate_all_labelled_weights_zero_iff :
    (∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK A.ρ q τ = ⊥) ↔
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (Rep.scalarConjugate σ.toRingEquiv A).ρ q τ = ⊥ :=
  (all_labelled_weights_zero_iff p ι hK A.ρ).trans
    ((scalarConjugate_nonzero_weightSpace_eq_bot_iff (p := p) (ι := ι) σ A).trans
      (all_labelled_weights_zero_iff p ι hK (Rep.scalarConjugate σ.toRingEquiv A).ρ).symm)

/-- Coefficient conjugation preserves actual rank-one quotients with every nonzero labelled period
space zero, without a comparison-map premise. -/
theorem scalarConjugate_exists_quotient_labelled_weights_zero_iff :
    (∃ S : Subrepresentation A.ρ, Module.finrank E (A ⧸ S.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (A.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥) ↔
    ∃ T : Subrepresentation (Rep.scalarConjugate σ.toRingEquiv A).ρ,
      Module.finrank E (Rep.scalarConjugate σ.toRingEquiv A ⧸ T.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        ((Rep.scalarConjugate σ.toRingEquiv A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule) q τ = ⊥ := by
  rw [exists_quotient_labelled_weights_zero_iff, exists_quotient_labelled_weights_zero_iff]
  constructor
  · rintro ⟨S, hdim, hweights⟩
    refine ⟨Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv A S, ?_, ?_⟩
    · exact (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv A S).trans hdim
    · intro q hq
      exact (weightSpace_eq_bot_iff
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S) q).mp (hweights q hq)
  · rintro ⟨T, hdim, hweights⟩
    obtain ⟨S, rfl⟩ := (Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv A).surjective T
    refine ⟨S, ?_, ?_⟩
    · exact (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv A S).symm.trans hdim
    · intro q hq
      exact (weightSpace_eq_bot_iff
        (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ A S) q).mpr (hweights q hq)

end HodgeTate

namespace HodgeTate

open HilbertModularity.Cyclotomic

variable (p k m : ℕ) [Fact p.Prime] (hm : m.Coprime (p ^ (k + 1)))
  {K G : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]] [Group G]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  (A : Rep (RealPrimePowerCompletion p k) G)
  [Module ℚ_[p] A] [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) A]
  [Module ℚ_[p] (Rep.localCoefficientConjugate p k m hm A)]
  [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
    (Rep.localCoefficientConjugate p k m hm A)]

/-- The actual ramified cyclotomic coefficient label preserves the all-labelled ordinary quotient
criterion and leaves the local acting group unchanged. -/
theorem localCoefficientConjugate_exists_quotient_labelled_weights_zero_iff :
    (∃ S : Subrepresentation A.ρ,
      Module.finrank (RealPrimePowerCompletion p k) (A ⧸ S.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        (A.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥) ↔
    ∃ T : Subrepresentation (Rep.localCoefficientConjugate p k m hm A).ρ,
      Module.finrank (RealPrimePowerCompletion p k)
        (Rep.localCoefficientConjugate p k m hm A ⧸ T.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        ((Rep.localCoefficientConjugate p k m hm A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule) q τ = ⊥ := by
  let : Module ℚ_[p] (Rep.scalarConjugate
      (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv A) :=
    inferInstanceAs (Module ℚ_[p] (Rep.localCoefficientConjugate p k m hm A))
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) (Rep.scalarConjugate
      (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv A) :=
    inferInstanceAs (IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
      (Rep.localCoefficientConjugate p k m hm A))
  exact scalarConjugate_exists_quotient_labelled_weights_zero_iff p ι hK
    (realPrimePowerCompletionAutomorphism p k m hm) A

variable [Module ℚ_[p] (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A)]
  [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
    (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A)]

/-- For the constructed prime-power completion automorphisms, all coprime coefficient labels
have a rank-one all-labelled weight-zero quotient exactly when label one does. -/
theorem localCoefficientConjugate_weight_zero_quotient_independent :
    (∃ T : Subrepresentation (Rep.localCoefficientConjugate p k m hm A).ρ,
      Module.finrank (RealPrimePowerCompletion p k)
        (Rep.localCoefficientConjugate p k m hm A ⧸ T.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        ((Rep.localCoefficientConjugate p k m hm A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule) q τ = ⊥) ↔
    ∃ T : Subrepresentation (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A).ρ,
      Module.finrank (RealPrimePowerCompletion p k)
        (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A ⧸ T.toSubmodule) = 1 ∧
      ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
        ((Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule) q τ = ⊥ :=
  (localCoefficientConjugate_exists_quotient_labelled_weights_zero_iff p k m hm ι hK A).symm.trans
    (localCoefficientConjugate_exists_quotient_labelled_weights_zero_iff p k 1
      (Nat.coprime_one_left _) ι hK A)

end HodgeTate
