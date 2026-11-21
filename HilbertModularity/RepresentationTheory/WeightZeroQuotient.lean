/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.LabelledConjugation
public import Mathlib.Algebra.Exact.Basic

/-! # Rank-one Hodge–Tate quotients of weight zero

A witness consists of an actual stable kernel and properties of its canonical
quotient. The quotient has dimension one, its actual Hodge–Tate comparison is
bijective, and its nonzero-weight period spaces vanish. Thus `Nonempty` of this
witness type expresses the ordinary quotient condition in [TripathiGoswami].
The labelled formulation uses every embedding of the local base field; no
condition on the divisibility of the specialization parameter is imposed.
-/

@[expose] public noncomputable section

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E G V : Type*} [Field K] [Field E] [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
  [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
  [Group G] [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
  [IsScalarTower ℚ_[p] E V]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)

/-- An actual stable quotient of dimension one with bijective Hodge–Tate comparison
and only weight zero. Its stable kernel supplies the canonical short exact sequence. -/
structure WeightZeroQuotient (ρ : Representation E G V) where
  /-- The kernel of the quotient representation. -/
  kernel : Subrepresentation ρ
  /-- The quotient has dimension one over the coefficient field. -/
  finrank_eq_one : Module.finrank E (V ⧸ kernel.toSubmodule) = 1
  /-- The actual period comparison for the quotient is bijective. -/
  comparison_bijective : Function.Bijective (comparison p ι hK
    ((ρ.quotient kernel.toSubmodule kernel.apply_mem_toSubmodule).restrictScalars ℚ_[p]))
  /-- Every nonzero cyclotomic weight space of the quotient vanishes. -/
  weights_zero : ∀ q : ℤ, q ≠ 0 → weightSpace p ι
    ((ρ.quotient kernel.toSubmodule kernel.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥

/-- Inclusion and quotient form the actual short exact sequence carried by a witness. -/
theorem WeightZeroQuotient.shortExact {ρ : Representation E G V}
    (W : WeightZeroQuotient p ι hK ρ) :
    Function.Injective W.kernel.toSubmodule.subtype ∧
      Function.Exact W.kernel.toSubmodule.subtype W.kernel.toSubmodule.mkQ ∧
      Function.Surjective W.kernel.toSubmodule.mkQ :=
  ⟨Subtype.val_injective, LinearMap.exact_subtype_mkQ W.kernel.toSubmodule,
    W.kernel.toSubmodule.mkQ_surjective⟩

/-- Unpacking a quotient witness gives precisely the existential comparison criterion. -/
theorem nonempty_weightZeroQuotient_iff (ρ : Representation E G V) :
    Nonempty (WeightZeroQuotient p ι hK ρ) ↔
      ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
        Function.Bijective (comparison p ι hK
          ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
        ∀ q : ℤ, q ≠ 0 → weightSpace p ι
          ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.kernel, W.finrank_eq_one, W.comparison_bijective, W.weights_zero⟩
  · rintro ⟨S, hdim, hcomp, hweights⟩
    exact ⟨⟨S, hdim, hcomp, hweights⟩⟩

/-- A quotient witness is equivalent to dimension one and weight zero at every
actual local-field label, with the genuine Hodge–Tate comparison retained. -/
theorem nonempty_weightZeroQuotient_iff_labelled [FiniteDimensional ℚ_[p] K]
    (ρ : Representation E G V) :
    Nonempty (WeightZeroQuotient p ι hK ρ) ↔
      ∃ S : Subrepresentation ρ, Module.finrank E (V ⧸ S.toSubmodule) = 1 ∧
        Function.Bijective (comparison p ι hK
          ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
        ∀ τ, ∀ q : ℤ, q ≠ 0 → labelledWeightSpace p ι hK
          (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥ :=
  (nonempty_weightZeroQuotient_iff p ι hK ρ).trans
    (exists_labelled_weight_zero_quotient_iff p ι hK ρ).symm

/-- The fixed periods of a weight-zero quotient span its actual completed period tensor. -/
theorem WeightZeroQuotient.zeroWeightSpan_eq_top {ρ : Representation E G V}
    (W : WeightZeroQuotient p ι hK ρ) :
    zeroWeightSpan (ι := ι)
      ((ρ.quotient W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤ :=
  zeroWeightSpan_eq_top_of_surjective_comparison p ι hK _
    W.comparison_bijective.2 W.weights_zero

section CoefficientConjugation

variable (σ : E ≃ₐ[ℚ_[p]] E) (A : Rep E G)
  [Module ℚ_[p] A] [IsScalarTower ℚ_[p] E A]
  [Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv A)]
  [IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv A)]

/-- Conjugating coefficients preserves the existence of a genuine weight-zero quotient. -/
theorem nonempty_weightZeroQuotient_scalarConjugate_iff :
    Nonempty (WeightZeroQuotient p ι hK A.ρ) ↔
      Nonempty (WeightZeroQuotient p ι hK (Rep.scalarConjugate σ.toRingEquiv A).ρ) := by
  rw [nonempty_weightZeroQuotient_iff, nonempty_weightZeroQuotient_iff]
  exact scalarConjugate_exists_weight_zero_quotient_iff p ι hK σ A

end CoefficientConjugation

section CyclotomicCoefficients

open HilbertModularity.Cyclotomic

variable (k m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
  (A : Rep (RealPrimePowerCompletion p k) G)
  [Module ℚ_[p] A] [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) A]
  [Module ℚ_[p] (Rep.localCoefficientConjugate p k m hm A)]
  [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
    (Rep.localCoefficientConjugate p k m hm A)]

/-- The actual cyclotomic completion automorphism preserves weight-zero quotient witnesses. -/
theorem nonempty_weightZeroQuotient_localCoefficientConjugate_iff :
    Nonempty (WeightZeroQuotient p ι hK A.ρ) ↔
      Nonempty (WeightZeroQuotient p ι hK (Rep.localCoefficientConjugate p k m hm A).ρ) := by
  let : Module ℚ_[p] (Rep.scalarConjugate
      (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv A) :=
    inferInstanceAs (Module ℚ_[p] (Rep.localCoefficientConjugate p k m hm A))
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) (Rep.scalarConjugate
      (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv A) :=
    inferInstanceAs (IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
      (Rep.localCoefficientConjugate p k m hm A))
  exact nonempty_weightZeroQuotient_scalarConjugate_iff p ι hK
    (realPrimePowerCompletionAutomorphism p k m hm) A

variable [Module ℚ_[p] (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A)]
  [IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
    (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A)]

/-- A coprime local coefficient label has a genuine ordinary quotient exactly when label one does. -/
theorem nonempty_weightZeroQuotient_localCoefficientConjugate_independent :
    Nonempty (WeightZeroQuotient p ι hK (Rep.localCoefficientConjugate p k m hm A).ρ) ↔
      Nonempty (WeightZeroQuotient p ι hK
        (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _) A).ρ) :=
  (nonempty_weightZeroQuotient_localCoefficientConjugate_iff p ι hK k m hm A).symm.trans
    (nonempty_weightZeroQuotient_localCoefficientConjugate_iff p ι hK k 1
      (Nat.coprime_one_left _) A)

end CyclotomicCoefficients

end HodgeTate
