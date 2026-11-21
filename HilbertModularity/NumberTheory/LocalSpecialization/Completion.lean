/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization

/-! # Local specialization in the adic completion

The local valuation ring maps canonically and locally into the integers of its
adic completion. Its residue-field map is injective, so equality of completed
residual values reflects equality of the original algebraic specializations.
This is the coefficient-completion bridge used in
[TripathiGoswami, determinant rigidity].
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] (P : HeightOneSpectrum R)

/-- Embed the local valuation ring into the integer ring of its adic completion. -/
def completionIntegralMap : P.valuationSubringAtPrime K →+* P.adicCompletionIntegers K :=
  ((algebraMap K (P.adicCompletion K)).comp (P.valuationSubringAtPrime K).subtype).codRestrict
    (P.adicCompletionIntegers K).toSubring (by
      intro x
      change Valued.v (algebraMap K (P.adicCompletion K) (x : K)) ≤ 1
      rw [show algebraMap K (P.adicCompletion K) (x : K) = ((x : K) : P.adicCompletion K) from rfl,
        adicCompletion.valued_coe]
      change (x : K) ∈ (P.valuation K).valuationSubring
      rw [← P.valuationSubringAtPrime_eq_valuationSubring]
      exact x.property)

@[simp]
theorem completionIntegralMap_coe (x : P.valuationSubringAtPrime K) :
    (completionIntegralMap P x : P.adicCompletion K) = algebraMap K (P.adicCompletion K) (x : K) := rfl

/-- The completion embedding preserves and reflects units of the local valuation ring. -/
theorem isUnit_completionIntegralMap_iff (x : P.valuationSubringAtPrime K) :
    IsUnit (completionIntegralMap P x) ↔ IsUnit x := by
  rw [adicCompletionIntegers.isUnit_iff_valued_eq_one,
    P.localIntegers.isUnit_iff_valuation_eq_one]
  change Valued.v ((x : K) : P.adicCompletion K) = 1 ↔ P.valuation K (x : K) = 1
  rw [adicCompletion.valued_coe]

instance completionIntegralMap_isLocalHom : IsLocalHom (completionIntegralMap (K := K) P) :=
  ⟨fun x => (isUnit_completionIntegralMap_iff P x).mp⟩

/-- The canonical map from the algebraic residue field to the residue field of the completion integers. -/
def completionResidueMap : R ⧸ P.asIdeal →+* IsLocalRing.ResidueField (P.adicCompletionIntegers K) :=
  (IsLocalRing.ResidueField.map (completionIntegralMap (K := K) P)).comp
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (P.valuationSubringAtPrime K)).toRingHom

/-- Passing to the completion does not identify distinct algebraic residue classes. -/
theorem completionResidueMap_injective : Function.Injective (completionResidueMap (K := K) P) :=
  (IsLocalRing.ResidueField.map (completionIntegralMap (K := K) P)).injective.comp
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (P.valuationSubringAtPrime K)).injective

/-- Specialization of an algebraic element agrees with its residue in the adic completion. -/
theorem completionResidueMap_specialization (x : K) (hx : P.valuation K x ≤ 1) :
    completionResidueMap P (P.specialization x hx) =
      IsLocalRing.residue (P.adicCompletionIntegers K)
        (completionIntegralMap P (P.localElement x hx)) := by
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (P.valuationSubringAtPrime K)
  change IsLocalRing.ResidueField.map (completionIntegralMap P)
    (e (e.symm (IsLocalRing.residue (P.valuationSubringAtPrime K) (P.localElement x hx)))) = _
  exact (congrArg (IsLocalRing.ResidueField.map (completionIntegralMap P))
    (e.apply_symm_apply (IsLocalRing.residue (P.valuationSubringAtPrime K) (P.localElement x hx)))).trans
      (IsLocalRing.ResidueField.map_residue (completionIntegralMap P) (P.localElement x hx))

/-- Residue one in the actual completion reflects residue one of the original algebraic element. -/
theorem completion_residue_eq_one_iff (x : K) (hx : P.valuation K x ≤ 1) :
    IsLocalRing.residue (P.adicCompletionIntegers K)
        (completionIntegralMap P (P.localElement x hx)) = 1 ↔
      P.specialization x hx = 1 := by
  rw [← completionResidueMap_specialization, ← map_one (completionResidueMap (K := K) P)]
  exact (completionResidueMap_injective (K := K) P).eq_iff

end IsDedekindDomain.HeightOneSpectrum
