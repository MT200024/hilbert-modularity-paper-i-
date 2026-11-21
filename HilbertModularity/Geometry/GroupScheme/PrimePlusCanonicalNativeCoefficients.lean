/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusExtendedChecklist
public import HilbertModularity.NumberTheory.CyclotomicZeroCompletion

/-! # The fixed native real-multiplication coefficient map

The global integer ring and the native completion are compared through the
same field equivalence. In particular, the full RM label is retained, not
just the rational p-adic scalars.
-/

public noncomputable section

open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- Canonical completed integers in the exponent-zero native coefficient field. -/
def primePlusCanonicalNativeIntegerEquiv :
    AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) ≃+* 𝒪[RealPrimePowerCompletion p 0] :=
  (realPrimeGeneratorAdicIntegersEquiv p hp).trans
    (realPrimePowerZeroIntegerEquiv p).symm

/-- On every original RM integer, the native coefficient map is the inverse
of the specified conductor field equivalence. -/
theorem primePlusCanonicalNativeIntegerEquiv_global
    (a : 𝓞 (realCyclotomicField p)) :
    (primePlusCanonicalNativeIntegerEquiv p hp
      (algebraMap (𝓞 (realCyclotomicField p))
        (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) a) : RealPrimePowerCompletion p 0) =
      (realPrimePowerZeroCompletionEquiv p).symm
        (algebraMap (realCyclotomicField p) (RealCompletion p) a) := by
  apply (realPrimePowerZeroCompletionEquiv p).injective
  rw [AlgEquiv.apply_symm_apply]
  rw [← coe_realPrimePowerZeroIntegerEquiv]
  simp only [primePlusCanonicalNativeIntegerEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, realPrimeGeneratorAdicIntegersEquiv_algebraMap,
    NumberField.coe_adicCompletionIntegerMap]
  exact IsScalarTower.algebraMap_apply (𝓞 (realCyclotomicField p))
    (realCyclotomicField p) (RealCompletion p) a

/-- The residual equivalence induced by the same canonical integer-ring
comparison used for the native Tate coefficients. -/
def primePlusCanonicalNativeResidueEquiv :
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) := by
  let κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealCompletion p] ⧸ 𝓂[RealCompletion p]) :=
    (Ideal.quotEquivOfEq (span_realPrimeGenerator p (by omega))).trans
      ((realCyclotomicResidueEquiv p).trans (realCompletionResidueEquiv p).symm)
  let ι := realPrimePowerZeroIntegerEquiv p
  have hmax : 𝓂[RealCompletion p] =
      (𝓂[RealPrimePowerCompletion p 0]).map ι.toRingHom :=
    (IsLocalRing.map_ringEquiv_maximalIdeal ι).symm
  exact κ.trans ((𝓂[RealPrimePowerCompletion p 0]).quotientEquiv
    (𝓂[RealCompletion p]) ι hmax).symm

/-- The algebra structure uses that actual integer embedding. -/
@[instance_reducible] def primePlusCanonicalNativeAlgebra :
    Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0) :=
  ((𝒪[RealPrimePowerCompletion p 0]).subtype.comp
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).toAlgebra

/-- The canonical scalar structure is induced by the specified integer map. -/
theorem primePlusCanonicalNativeAlgebra_eq :
    primePlusCanonicalNativeAlgebra p hp =
      ((𝒪[RealPrimePowerCompletion p 0]).subtype.comp
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).toAlgebra := by
  exact (rfl)

/-- The canonical native field is the fraction field for this integer map. -/
theorem primePlusCanonicalNative_isFractionRing :
    letI := primePlusCanonicalNativeAlgebra p hp
    IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0) := by
  let := primePlusCanonicalNativeAlgebra p hp
  apply IsFractionRing.of_ringEquiv_left (primePlusCanonicalNativeIntegerEquiv p hp)
  intro x
  rfl

/-- The same native integer map preserves the original rational p-adic scalars. -/
theorem primePlusCanonicalNativeAlgebra_padic (z : ℤ_[p]) :
    letI := primePlusCanonicalNativeAlgebra p hp
    algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
      (TateModule.coefficientPrimeRingEquiv p (𝓞 (realCyclotomicField p))
        (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
        (realPrimeRamification_pos p (by omega))
        (span_realPrimeGenerator_pow p (by omega))
        (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) (z : ℚ_[p]) := by
  let := primePlusCanonicalNativeAlgebra p hp
  change (primePlusCanonicalNativeIntegerEquiv p hp _ : RealPrimePowerCompletion p 0) = _
  apply (realPrimePowerZeroCompletionEquiv p).injective
  rw [AlgEquiv.commutes, ← coe_realPrimePowerZeroIntegerEquiv]
  simp only [primePlusCanonicalNativeIntegerEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, realPrimeGeneratorAdicIntegersEquiv_padic]

private theorem coe_transport_realInteger
    (F G : IntermediateField ℚ Qbar) (h : F = G) (a : 𝓞 F) :
    ((Eq.mp (congrArg (fun E : IntermediateField ℚ Qbar => 𝓞 E) h) a : 𝓞 G) : G) =
      IntermediateField.equivOfEq h (a : F) := by
  cases h
  rfl

/-- The full real-multiplication coefficient diagram commutes. This rules
out an unrelated local coefficient automorphism in the Tate comparison. -/
theorem primePlusCanonicalNativeAlgebra_fullRM
    (a : 𝓞 (realCyclotomicField (p ^ (0 + 1)))) :
    letI := primePlusCanonicalNativeAlgebra p hp
    algebraMap (realCyclotomicField (p ^ (0 + 1)))
        (RealPrimePowerCompletion p 0) (a : realCyclotomicField (p ^ (0 + 1))) =
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
        (algebraMap (𝓞 (realCyclotomicField p))
          (AdicCompletion (Ideal.span {realPrimeGenerator p})
            (𝓞 (realCyclotomicField p)))
          (Eq.mp (congrArg (fun F : IntermediateField ℚ Qbar => 𝓞 F)
            (realCyclotomicField_primePower_zero p)) a)) := by
  let := primePlusCanonicalNativeAlgebra p hp
  change _ = (primePlusCanonicalNativeIntegerEquiv p hp _ : RealPrimePowerCompletion p 0)
  rw [primePlusCanonicalNativeIntegerEquiv_global]
  apply (realPrimePowerZeroCompletionEquiv p).injective
  rw [AlgEquiv.apply_symm_apply, realPrimePowerZeroCompletionEquiv_global,
    coe_transport_realInteger]

end HilbertModularity.Hypergeometric
