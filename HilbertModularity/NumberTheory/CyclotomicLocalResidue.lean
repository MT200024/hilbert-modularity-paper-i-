/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.AdicCompletionResidue

/-! # The actual cyclotomic coefficient residue field

The unique prime at a prime-power conductor has residue field `ZMod p`, both
before and after completion. The comparison is induced by the native integer
embedding, as required for the RM reductions in [TripathiGoswami].
-/

@[expose] public noncomputable section
open scoped NumberField ValuativeRel
namespace HilbertModularity.Cyclotomic
variable (p k : ℕ) [Fact p.Prime]

/-- The full prime-power cyclotomic residue has exactly `p` elements. -/
theorem card_quotient_primeAbovePrimePower :
    Nat.card (𝓞 (cyclotomicField (p ^ (k + 1))) ⧸ (primeAbovePrimePower p k).asIdeal) = p :=
  IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p k (root_isPrimitiveRoot (p ^ (k + 1)))

/-- The full prime-power cyclotomic residue is canonically the prime field. -/
def cyclotomicPrimePowerResidueEquiv :
    (𝓞 (cyclotomicField (p ^ (k + 1))) ⧸ (primeAbovePrimePower p k).asIdeal) ≃+* ZMod p :=
  letI := Fintype.ofFinite
    (𝓞 (cyclotomicField (p ^ (k + 1))) ⧸ (primeAbovePrimePower p k).asIdeal)
  (ZMod.ringEquivOfPrime _ (Fact.out : p.Prime)
    (by rw [← Nat.card_eq_fintype_card]; exact card_quotient_primeAbovePrimePower p k)).symm

/-- Global real prime-power multiplication integers reduce through the full cyclotomic prime. -/
def realPrimePowerReduction : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* ZMod p :=
  (cyclotomicPrimePowerResidueEquiv p k).toRingHom.comp
    ((Ideal.Quotient.mk (primeAbovePrimePower p k).asIdeal).comp
      (NumberField.RingOfIntegers.mapRingHom
        (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom))

/-- The reduction kernel is the actual prime used to define the coefficient completion. -/
theorem realPrimePowerReduction_eq_zero_iff (a : 𝓞 (realCyclotomicField (p ^ (k + 1)))) :
    realPrimePowerReduction p k a = 0 ↔ a ∈ (realPrimeAbovePrimePower p k).asIdeal := by
  change cyclotomicPrimePowerResidueEquiv p k
    ((Ideal.Quotient.mk (primeAbovePrimePower p k).asIdeal)
      (NumberField.RingOfIntegers.mapRingHom
        (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom a)) = 0 ↔ _
  rw [map_eq_zero_iff _ (cyclotomicPrimePowerResidueEquiv p k).injective,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- Every prime-field residue is represented by a rational integer. -/
theorem realPrimePowerReduction_surjective : Function.Surjective (realPrimePowerReduction p k) := by
  intro a
  exact ⟨(a.val : 𝓞 (realCyclotomicField (p ^ (k + 1)))), by simp⟩

/-- The actual real coefficient prime has residue field `ZMod p`. -/
def realPrimePowerResidueEquiv :
    (𝓞 (realCyclotomicField (p ^ (k + 1))) ⧸ (realPrimeAbovePrimePower p k).asIdeal) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq (show (realPrimeAbovePrimePower p k).asIdeal =
      RingHom.ker (realPrimePowerReduction p k) by
    ext a
    exact (realPrimePowerReduction_eq_zero_iff p k a).symm)).trans
      ((realPrimePowerReduction p k).quotientKerEquivOfSurjective
        (realPrimePowerReduction_surjective p k))

/-- The actual native completed coefficient residue is the prime field. -/
def realPrimePowerCompletionResidueEquiv : 𝓀[RealPrimePowerCompletion p k] ≃+* ZMod p :=
  (NumberField.adicCompletionResidueEquiv
    (realCyclotomicField (p ^ (k + 1))) (realPrimeAbovePrimePower p k)).symm.trans
      (realPrimePowerResidueEquiv p k)

/-- Completion and reduction commute on actual global multiplication integers. -/
@[simp] theorem realPrimePowerCompletionResidueEquiv_globalInteger
    (a : 𝓞 (realCyclotomicField (p ^ (k + 1)))) :
    realPrimePowerCompletionResidueEquiv p k
      (NumberField.adicCompletionResidueMap
        (realCyclotomicField (p ^ (k + 1))) (realPrimeAbovePrimePower p k) a) =
      realPrimePowerReduction p k a := by
  unfold realPrimePowerCompletionResidueEquiv
  rw [RingEquiv.trans_apply, ← NumberField.adicCompletionResidueEquiv_mk,
    RingEquiv.symm_apply_apply]
  rfl

/-- The native residue field of the completed coefficient field has exactly `p` elements. -/
theorem card_realPrimePowerCompletionResidue : Nat.card 𝓀[RealPrimePowerCompletion p k] = p := by
  rw [Nat.card_congr (realPrimePowerCompletionResidueEquiv p k).toEquiv, Nat.card_zmod]

/-- The original prime-conductor completion has the same canonical prime-field residue. -/
def realCompletionResidueEquiv : 𝓀[RealCompletion p] ≃+* ZMod p :=
  (NumberField.adicCompletionResidueEquiv
    (realCyclotomicField p) (realPrimeAboveConductor p)).symm.trans
      (realCyclotomicResidueEquiv p)

/-- Native completion reduction agrees with the existing prime-conductor RM reduction. -/
@[simp] theorem realCompletionResidueEquiv_globalInteger
    (a : 𝓞 (realCyclotomicField p)) :
    realCompletionResidueEquiv p
      (NumberField.adicCompletionResidueMap (realCyclotomicField p) (realPrimeAboveConductor p) a) =
      realCyclotomicReduction p a := by
  unfold realCompletionResidueEquiv
  rw [RingEquiv.trans_apply, ← NumberField.adicCompletionResidueEquiv_mk,
    RingEquiv.symm_apply_apply]
  rfl

/-- The scaled roots retain their actual square residues in the native completed coefficient field. -/
theorem realCompletionResidueEquiv_scaledRoot (j : ℕ) :
    realCompletionResidueEquiv p
      (NumberField.adicCompletionResidueMap (realCyclotomicField p) (realPrimeAboveConductor p)
        (realScaledRootInteger p j)) = (j : ZMod p) ^ 2 := by
  rw [realCompletionResidueEquiv_globalInteger, realCyclotomicReduction_realScaledRootInteger]

end HilbertModularity.Cyclotomic
