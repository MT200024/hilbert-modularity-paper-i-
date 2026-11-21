/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorIrreducibility
public import HilbertModularity.Hypergeometric.ChosenEulerSelectedPlusIrreducibility

/-! # Odd determinant of the chosen full-conductor coordinates

The canonical integral/rational Tate comparison fixes the determinant of the
selected plus-Jacobian action at a real-place involution. The coefficient map
is the specified exponent-labelled map to the full conductor completion.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

local instance fullConductorDeterminantLocalField (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- Some complex conjugation has determinant `-1` on the exact chosen
integral Tate coordinate action. This uses the canonical same-fibre Tate
comparison and its full real-multiplication coefficient map. See
[TripathiGoswamiRevised, Lemma `RMtorsion` and Lemma
`prime-absolute-irred`]. -/
theorem exists_chosenConductorPlusCoordinate_oddInvolution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    ∃ c : AbsoluteGalois (realCyclotomicField p),
      c ^ 2 = 1 ∧
        LinearMap.det (chosenConductorPlusCoordinateAction p hp m hm ξ c) = -1 := by
  let L := FullConductorCompletion p
  let f := chosenConductorNativeMap p m hm
  let hf : Continuous f := continuous_chosenConductorNativeMap p m hm
  let := primePlusExtendedNativeAlgebra p hp f hf
  let C := primePlusCanonicalTateComparisonAt p hp ξ f hf
  let β := primePlusExtendedNativeIntegerMap p hp f hf
  let := primePlusIntegralTateModule p hp ξ
  obtain ⟨ι, c, hc, hconj⟩ :=
    NumberField.exists_complexConjugation (realCyclotomicField p)
  have hTateDet (g : AbsoluteGalois (realCyclotomicField p)) :
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) L
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))) :=
    primePlusIntegralTate_det_of_nativeComparison p hp ξ L
      C.localMap C.actionEquiv C.integerCoefficients g
  have hcyclo :
      (Field.cyclotomicCharacter (realCyclotomicField p) p c : ℤ_[p]) = -1 :=
    cyclotomicCharacter.coe_eq_neg_one_of_complexConjugation
      p ι c.toRingEquiv hconj
  have hnative :
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L c) = -1 := by
    rw [hTateDet c, hcyclo]
    simp
  refine ⟨c, hc, ?_⟩
  rw [chosenConductorPlusCoordinateAction_eq p hp m hm ξ]
  exact ((primePlusTateFieldCoordinateEquiv p hp ξ β C.integralEmbedding).determinant_eq c).trans
    hnative

/-- Irreducibility over the full-conductor coefficient field becomes
absolute irreducibility by the chosen real-place involution. The determinant
is the canonical Tate determinant proved above. -/
theorem chosenConductorPlus_absoluteIrreducible_of_irreducible
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hirred : (chosenConductorPlusCoordinateAction p hp m hm ξ).IsIrreducible) :
    ((chosenConductorPlusCoordinateAction p hp m hm ξ).baseChange
      (AlgebraicClosure (FullConductorCompletion p))).IsIrreducible := by
  let L := FullConductorCompletion p
  let σ := chosenConductorPlusCoordinateAction p hp m hm ξ
  let : σ.IsIrreducible := hirred
  obtain ⟨c, hc, hdet⟩ :=
    exists_chosenConductorPlusCoordinate_oddInvolution p hp m hm ξ
  have htwoFp : (2 : cyclotomicField p) ≠ 0 := by
    exact (map_ne_zero (cyclotomicField p).val).mp (by norm_num)
  have htwo : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap (cyclotomicField p) L)).mpr htwoFp
  exact Representation.isIrreducible_baseChange_of_involution σ
    htwo c hc hdet

/-- At either rational cubic cusp, source-field irreducibility of the actual
chosen full-conductor coordinate action supplies the complete spectral
weight-two checklist. Absolute and native irreducibility are consequences,
using the canonical odd determinant and faithful scalar extension. -/
def chosenConductorCubicWeightTwoInput_spectral_of_irreducible
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (hirred : (chosenConductorPlusCoordinateAction p hp m hm
      (darmonRationalParameter p ξ₀)).IsIrreducible) := by
  have habs := chosenConductorPlus_absoluteIrreducible_of_irreducible
    p hp m hm (darmonRationalParameter p ξ₀) hirred
  rw [chosenConductorPlusCoordinateAction_eq_mapNative p hp m hm
    (darmonRationalParameter p ξ₀)] at habs
  exact chosenConductorCubicWeightTwoInput_spectral_of_fullAbsolute
    p hp m hm ξ₀ hξ hA hB hAB hdeep habs

end HilbertModularity.Hypergeometric
