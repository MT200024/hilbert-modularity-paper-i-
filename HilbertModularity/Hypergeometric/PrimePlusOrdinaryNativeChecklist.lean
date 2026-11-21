/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusUniformOrdinaryOrdering
public import HilbertModularity.Geometry.GroupScheme.PrimePlusCanonicalNativeComparison
import HilbertModularity.NumberTheory.ComplexConjugation

/-! # The canonical native checklist from an ordinary quotient

The native lifting input is constructed from the actual selected Jacobian's
weight-zero quotient and irreducibility. All coefficient maps, residual order,
local decomposition comparisons and complex conjugation are chosen internally.
-/

public noncomputable section

open AlgebraicGeometry NumberField ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra

local instance ordinaryNativeChecklistCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- The selected native ordinary quotient and irreducibility supply the full
weight-two lifting checklist, without a rational cubic-divisibility premise.
The same residual ordering works at every absolute prime above the conductor.
This proves the native assembly in [TripathiGoswamiRevised, Proposition
`SW-checklist`]; the chosen labelled global-family application remains separate. -/
def primePlusCanonicalOrdinarySkinnerWilesWeightTwoInput
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (W : PrimePlusOrdinaryQuotient p hp ξ 1 (Nat.coprime_one_left _))
    (hirred : (primePlusTateFieldCoordinateAction p hp ξ
      (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).IsIrreducible) :
    letI := primePlusCanonicalNativeAlgebra p hp
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom) (cyclotomicField p) := by
  letI := primePlusCanonicalNativeAlgebra p hp
  letI := primePlusCanonicalNative_isFractionRing p hp
  let β := (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
  let κ := primePlusCanonicalNativeResidueEquiv p hp
  let C := primePlusCanonicalNativeTateComparison p hp ξ
  let d := W.normalizedData p hp ξ 1 (Nat.coprime_one_left _)
  let D₀ := C.selectedResidualData p hp ξ β κ
  have hrows := exists_primePlus_uniformOrdinaryOrdering p hp ξ β C
    (primePlusCanonicalNativeTateComparison_localMap p hp ξ) d D₀
  let D := Classical.choose hrows
  have hordinary := (Classical.choose_spec hrows).2
  let hcomplex := NumberField.exists_complexConjugation (realCyclotomicField p)
  let ι := Classical.choose hcomplex
  let hcdata := Classical.choose_spec hcomplex
  let c := Classical.choose hcdata
  have hc : c ^ 2 = 1 := (Classical.choose_spec hcdata).1
  have hconj : ∀ x, ι (c x) = star (ι x) := (Classical.choose_spec hcdata).2
  apply skinnerWilesWeightTwoInput_of_primePlusNativeComparison p hp ξ
    (RealPrimePowerCompletion p 0) β κ C hirred ι c hc hconj D
  intro P _ hpP Q _ _
  have hP := realPrimeAboveConductor_eq_of_maximal_mem p hp P hpP
  letI : Q.LiesOver (realPrimeAboveConductor p).asIdeal := by
    rw [← hP]
    infer_instance
  exact Classical.choice (hordinary Q)

/-- A weight-zero quotient at any coprime coefficient label supplies the
same native lifting input. Coefficient conjugation preserves the ordinary
quotient condition; the output uses the canonical native label before the
separate global coefficient extension. -/
def primePlusCanonicalOrdinarySkinnerWilesWeightTwoInput_of_label
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm)
    (hirred : (primePlusTateFieldCoordinateAction p hp ξ
      (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).IsIrreducible) :
    letI := primePlusCanonicalNativeAlgebra p hp
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom) (cyclotomicField p) :=
  primePlusCanonicalOrdinarySkinnerWilesWeightTwoInput p hp ξ
    (Classical.choice ((nonempty_primePlusOrdinaryQuotient_iff p hp ξ m hm).mp ⟨W⟩))
    hirred

end HilbertModularity.Hypergeometric
