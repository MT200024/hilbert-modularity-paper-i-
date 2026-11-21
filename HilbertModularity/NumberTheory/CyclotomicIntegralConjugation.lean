/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicLocalResidue
public import HilbertModularity.NumberTheory.LocalFieldMorphisms

/-! # Integral coefficient conjugation at the ramified prime

The actual local coefficient automorphisms preserve the native integer ring.
Their action on its residue field is trivial because that field is `ZMod p`.
This concerns the coefficient ring, and asserts no integral Tate idempotent
decomposition; see [TripathiGoswami, ramified scalar label].
-/

@[expose] public noncomputable section
open scoped NumberField ValuativeRel
namespace HilbertModularity.Cyclotomic
variable (p k m : ℕ) [Fact p.Prime] (hm : m.Coprime (p ^ (k + 1)))

/-- The actual coefficient label acts on the native completed integer ring. -/
def realPrimePowerCompletionIntegerAutomorphism :
    𝒪[RealPrimePowerCompletion p k] ≃+* 𝒪[RealPrimePowerCompletion p k] :=
  IsNonarchimedeanLocalField.integerEquiv
    (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (continuous_realPrimePowerCompletionAutomorphism p k m hm)
    (realPrimePowerCompletionAutomorphism p k m hm).symm.toLinearMap.continuous_of_finiteDimensional

/-- Integral conjugation has precisely the original coefficient automorphism as its field map. -/
@[simp] theorem coe_realPrimePowerCompletionIntegerAutomorphism (a : 𝒪[RealPrimePowerCompletion p k]) :
    (realPrimePowerCompletionIntegerAutomorphism p k m hm a : RealPrimePowerCompletion p k) =
      realPrimePowerCompletionAutomorphism p k m hm (a : RealPrimePowerCompletion p k) := rfl

/-- Integral conjugation agrees with the actual global multiplication action before completion. -/
theorem realPrimePowerCompletionIntegerAutomorphism_globalInteger
    (a : 𝓞 (realCyclotomicField (p ^ (k + 1)))) :
    realPrimePowerCompletionIntegerAutomorphism p k m hm
      (NumberField.adicCompletionIntegerMap
        (realCyclotomicField (p ^ (k + 1))) (realPrimeAbovePrimePower p k) a) =
      NumberField.adicCompletionIntegerMap
        (realCyclotomicField (p ^ (k + 1))) (realPrimeAbovePrimePower p k)
        (NumberField.RingOfIntegers.mapRingHom
          (realPowerAutomorphism (p ^ (k + 1)) m hm).toRingHom a) := by
  apply Subtype.ext
  exact realPrimePowerCompletionAutomorphism_algebraMap p k m hm (a : realCyclotomicField (p ^ (k + 1)))

/-- The actual residue automorphism induced by the integral coefficient label. -/
def realPrimePowerCompletionResidueAutomorphism :
    𝓀[RealPrimePowerCompletion p k] ≃+* 𝓀[RealPrimePowerCompletion p k] :=
  IsLocalRing.ResidueField.mapEquiv (realPrimePowerCompletionIntegerAutomorphism p k m hm)

/-- Every actual local coefficient label acts trivially on the native prime-field residue. -/
theorem realPrimePowerCompletionResidueAutomorphism_eq_refl :
    realPrimePowerCompletionResidueAutomorphism p k m hm = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  let e := realPrimePowerCompletionResidueEquiv p k
  have hx : (((e x).val : ℕ) : 𝓀[RealPrimePowerCompletion p k]) = x := by
    apply e.injective
    simp only [map_natCast, ZMod.natCast_zmod_val]
  rw [← hx]
  simp only [map_natCast]

/-- Native reduction is unchanged by the actual integral coefficient conjugation. -/
theorem residue_realPrimePowerCompletionIntegerAutomorphism (a : 𝒪[RealPrimePowerCompletion p k]) :
    IsLocalRing.residue _ (realPrimePowerCompletionIntegerAutomorphism p k m hm a) =
      IsLocalRing.residue _ a := by
  have h := RingEquiv.congr_fun (realPrimePowerCompletionResidueAutomorphism_eq_refl p k m hm)
    (IsLocalRing.residue _ a)
  exact h

end HilbertModularity.Cyclotomic
