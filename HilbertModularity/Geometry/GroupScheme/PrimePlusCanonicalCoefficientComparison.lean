/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusCanonicalNativeComparison
public import HilbertModularity.Geometry.GroupScheme.PrimePlusNativeCoefficientExtension

/-! # Canonical selected Tate comparisons after a local coefficient embedding -/

public noncomputable section

open AlgebraicGeometry
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  {L : Type*} [Field L] [ValuativeRel L] [UniformSpace L]
  [IsUniformAddGroup L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[p] L]

/-- The completed RM integers map through the specified local coefficient
embedding into the target's actual valuation ring. -/
def primePlusExtendedNativeIntegerMap
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L) (hf : Continuous f) :
    AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[L] :=
  (IsNonarchimedeanLocalField.integerMap f.toRingHom hf).comp
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom

/-- The extended integer map is precisely restriction of the specified
field embedding after the canonical native integer equivalence. -/
theorem primePlusExtendedNativeIntegerMap_eq
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L) (hf : Continuous f) :
    primePlusExtendedNativeIntegerMap p hp f hf =
      (IsNonarchimedeanLocalField.integerMap f.toRingHom hf).comp
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom := (rfl)

/-- The target algebra structure is induced by that same integer map. -/
@[instance_reducible] def primePlusExtendedNativeAlgebra
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L) (hf : Continuous f) :
    Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) L :=
  ((𝒪[L]).subtype.comp (primePlusExtendedNativeIntegerMap p hp f hf)).toAlgebra

/-- The canonical comparison extends to the exact specified local
coefficient embedding. No enlarged-field comparison is assumed. -/
def primePlusCanonicalTateComparisonAt
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L) (hf : Continuous f) :
    letI := primePlusExtendedNativeAlgebra p hp f hf
    PrimePlusNativeTateComparison p hp ξ L
      (primePlusExtendedNativeIntegerMap p hp f hf) := by
  letI := primePlusCanonicalNativeAlgebra p hp
  letI := primePlusExtendedNativeAlgebra p hp f hf
  apply (primePlusCanonicalNativeTateComparison p hp ξ).extendCoefficients p hp ξ
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom f
    (fun _ => ?_) (primePlusExtendedNativeIntegerMap p hp f hf) (by exact (rfl))
  change (primePlusExtendedNativeIntegerMap p hp f hf _ : L) = _
  rw [primePlusCanonicalNativeAlgebra_eq]
  exact (rfl)

/-- The extended comparison retains its specified local coefficient map. -/
theorem primePlusCanonicalTateComparisonAt_localMap
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L) (hf : Continuous f) :
    letI := primePlusExtendedNativeAlgebra p hp f hf
    (primePlusCanonicalTateComparisonAt p hp ξ f hf).localMap = f := by
  let := primePlusCanonicalNativeAlgebra p hp
  let := primePlusExtendedNativeAlgebra p hp f hf
  simp only [primePlusCanonicalTateComparisonAt,
    PrimePlusNativeTateComparison.extendCoefficients_localMap,
    primePlusCanonicalNativeTateComparison_localMap, AlgHom.comp_id]

/-- The extended native action has the actual selected integral Tate
coordinates at the same coefficient embedding. -/
def primePlusCanonicalCoefficientCoordinateEquiv
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (f : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] L) (hf : Continuous f) :
    letI := primePlusExtendedNativeAlgebra p hp f hf
    letI : Algebra (RealPrimePowerCompletion p 0) L := f.toAlgebra
    ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange L).Equiv
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusExtendedNativeIntegerMap p hp f hf)) := by
  letI := primePlusExtendedNativeAlgebra p hp f hf
  letI : Algebra (RealPrimePowerCompletion p 0) L := f.toAlgebra
  let C := primePlusCanonicalTateComparisonAt p hp ξ f hf
  have hmap : C.localMap = f :=
    primePlusCanonicalTateComparisonAt_localMap p hp ξ f hf
  have e := C.coordinateEquiv p hp ξ (primePlusExtendedNativeIntegerMap p hp f hf)
  rw [hmap] at e
  exact e

end HilbertModularity.Hypergeometric
