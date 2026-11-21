/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicCompletion
public import Mathlib.NumberTheory.Padics.LocalField

/-! # The native local-field structure of the completed coefficient field

The valuation and topology are those of the existing number-field completion.
Finite dimensionality over `Q_p` gives local compactness without changing the
normalization of its norm, as required for the integral characters in
[TripathiGoswami, prime ordinary lemma].
-/

@[expose] public noncomputable section
open IsDedekindDomain
open scoped NumberField WithZero ValuativeRel

namespace NumberField
variable (K : Type*) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The valuative relation on a number-field completion is its native adic valuation. -/
instance adicCompletionValuativeRel : ValuativeRel (w.adicCompletion K) :=
  .ofValuation (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)

/-- The native valuation is compatible with the induced valuative relation. -/
instance adicCompletionValuationCompatible :
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- The valuative topology is exactly the already defined completion topology. -/
instance adicCompletionIsValuativeTopology : IsValuativeTopology (w.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)
    (fun {s} => Valued.is_topological_valuation s)

/-- The native completion valuation is nontrivial. -/
instance adicCompletionValuativeRelIsNontrivial : ValuativeRel.IsNontrivial (w.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).mpr inferInstance

variable (p : ℕ) [Fact p.Prime] [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]

include p in
/-- The native completion above `p` is locally compact by its finite-dimensional `Q_p` topology. -/
theorem locallyCompactSpace_padicCompletion : LocallyCompactSpace (w.adicCompletion K) :=
  LocallyCompactSpace.of_finiteDimensional_of_complete ℚ_[p] (w.adicCompletion K)

include p in
/-- A completion above `p` is an actual nonarchimedean local field with its native valuation. -/
theorem isNonarchimedeanLocalField_padicCompletion : IsNonarchimedeanLocalField (w.adicCompletion K) := by
  let := locallyCompactSpace_padicCompletion K w p
  exact ⟨⟩

omit [Fact p.Prime] in
/-- The rational prime lies strictly inside the native valuation's maximal ideal. -/
theorem valuation_p_lt_one_padicCompletion :
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) p < 1 := by
  have hp : (p : 𝓞 K) ∈ w.asIdeal := by
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver w.asIdeal (Ideal.span {(p : ℤ)}) (p : ℤ)).mp
        (Ideal.subset_span (Set.mem_singleton _))
  have h := w.valuedAdicCompletion_eq_valuation (K := K) (p : 𝓞 K)
  simp only [map_natCast] at h
  rw [h]
  simpa only [map_natCast] using (w.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).mpr hp

/-- The actual residue field of a completion above `p` has characteristic `p`. -/
theorem adicCompletionResidueCharP : CharP 𝓀[w.adicCompletion K] p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast (IsLocalRing.residue 𝒪[w.adicCompletion K]),
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ValuativeRel.valuation (w.adicCompletion K) (p : w.adicCompletion K) < 1
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion K))
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).lt_one_iff_lt_one.mpr
      (valuation_p_lt_one_padicCompletion K w p)

end NumberField

namespace HilbertModularity.Cyclotomic
variable (p k : ℕ) [Fact p.Prime]

/-- The actual completed real multiplication field is a nonarchimedean local field. -/
instance realPrimePowerCompletionIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField (RealPrimePowerCompletion p k) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (realCyclotomicField (p ^ (k + 1))) (realPrimeAbovePrimePower p k) p

/-- The finite residue field of the actual coefficient completion has characteristic `p`. -/
instance realPrimePowerCompletionResidueCharP : CharP 𝓀[RealPrimePowerCompletion p k] p :=
  NumberField.adicCompletionResidueCharP
    (realCyclotomicField (p ^ (k + 1))) (realPrimeAbovePrimePower p k) p

end HilbertModularity.Cyclotomic
