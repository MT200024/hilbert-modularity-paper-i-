/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusCanonicalNativeComparison
public import HilbertModularity.Hypergeometric.PrimePlusCubicNativeChecklist

/-! # Canonical native residual and ordinary data at either cubic cusp -/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

local instance canonicalCubicResidueCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- Either rational cubic-cusp condition supplies the selected native
residual datum and all its local ordinary rows. The integral/rational Tate
comparison, coefficient map and residue equivalence are constructed here. -/
theorem exists_primePlusCanonicalCubicResidualOrdinaryData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    letI := primePlusCanonicalNativeAlgebra p hp
    let β := (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
    let κ := primePlusCanonicalNativeResidueEquiv p hp
    ∃ D : SkinnerWilesResidualData
        (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β),
      residualRatio D =
        (Units.map κ.toMonoidHom).comp
          (realPrimeResidualCyclotomicCharacter (realCyclotomicField p) p (by omega)) ∧
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
        (p : 𝓞 (realCyclotomicField p)) ∈ P →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
          [Q.IsMaximal] [Q.LiesOver P],
          Nonempty (SkinnerWilesOrdinaryAt p
            (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
            D Q) := by
  let := primePlusCanonicalNativeAlgebra p hp
  let := primePlusCanonicalNative_isFractionRing p hp
  exact exists_primePlusCubicNativeResidualOrdinaryData p hp ξ₀ hξ hA hB hAB hdeep
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
    (primePlusCanonicalNativeResidueEquiv p hp)
    (primePlusCanonicalNativeTateComparison p hp (darmonRationalParameter p ξ₀))
    (primePlusCanonicalNativeTateComparison_localMap p hp (darmonRationalParameter p ξ₀))

/-- The actual cubic-cusp native lifting input uses canonical coefficient
and residual maps. Irreducibility of the selected native action is the
remaining arithmetic hypothesis; all other checklist fields are derived. -/
def primePlusCanonicalCubicSkinnerWilesWeightTwoInput
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (hirred : (primePlusTateFieldCoordinateAction p hp
      (darmonRationalParameter p ξ₀)
      (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).IsIrreducible) :
    letI := primePlusCanonicalNativeAlgebra p hp
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀)
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom)
      (cyclotomicField p) := by
  letI := primePlusCanonicalNativeAlgebra p hp
  letI := primePlusCanonicalNative_isFractionRing p hp
  exact primePlusCubic_nativeSkinnerWilesWeightTwoInput p hp ξ₀ hξ hA hB hAB hdeep
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
    (primePlusCanonicalNativeResidueEquiv p hp)
    (primePlusCanonicalNativeTateComparison p hp (darmonRationalParameter p ξ₀))
    (primePlusCanonicalNativeTateComparison_localMap p hp (darmonRationalParameter p ξ₀))
    hirred

end HilbertModularity.Hypergeometric
