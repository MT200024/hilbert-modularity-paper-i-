/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementLocalSkinnerWiles
import HilbertModularity.NumberTheory.ComplexConjugation

/-! # Native Skinner–Wiles input at rational cubic cusps

The complementary Raynaud quotient uses the second constituent of the
swapped selected residual datum. The ratio remains the canonical quadratic
cyclotomic character because that character is its own inverse. Together
with the selected native comparison and irreducibility, the two actual local
rows yield the weight-two lifting input on the same plus-Jacobian Tate action.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

local instance primePlusCubicNativeResidueCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸
      𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- The swapped selected residual datum has the same exact cyclotomic
ratio as the native datum, not merely the same kernel. This is the global
ratio used for the complementary-cusp checklist after coefficient transport. -/
theorem PrimePlusNativeTateComparison.selectedResidualRatio_swap
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E])) :
    residualRatio (C.selectedResidualData p hp ξ β κ).swap =
      (Units.map κ.toMonoidHom).comp
        (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  let D := C.selectedResidualData p hp ξ β κ
  let ε := realPrimeResidualCyclotomicCharacter
    (realCyclotomicField p) p (by omega)
  have hratio := C.selectedResidualRatio p hp ξ β κ
  apply MonoidHom.ext
  intro g
  have hg : residualRatio D g = Units.map κ.toMonoidHom (ε g) := by
    exact congrArg (fun f : AbsoluteGalois (realCyclotomicField p) →*
      (𝒪[E] ⧸ 𝓂[E])ˣ => f g) hratio
  rw [D.residualRatio_swap g, hg]
  change (Units.map κ.toMonoidHom (ε g))⁻¹ =
    Units.map κ.toMonoidHom (ε g)
  rcases realPrimeResidualCharacter_eq_one_or_neg_one p (by omega) g with h | h
  · change ε g = 1 at h
    simp [h]
  · change ε g = -1 at h
    simp [h]

/-- Either rational cubic cusp determines the actual selected native
residual datum, ordered so the Raynaud weight-zero quotient is second. Its
ratio is the canonical quadratic cyclotomic character, and every prime
above `p` has the corresponding local ordinary row. No `NormedAlgebra`
structure on the native completion is used. -/
theorem exists_primePlusCubicNativeResidualOrdinaryData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)) :
    ∃ D : SkinnerWilesResidualData
        (primePlusTateFieldCoordinateAction p hp
          (darmonRationalParameter p ξ₀) β),
      residualRatio D =
        (Units.map κ.toMonoidHom).comp
          (realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega)) ∧
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
        (p : 𝓞 (realCyclotomicField p)) ∈ P →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
          [Q.IsMaximal] [Q.LiesOver P],
          Nonempty (SkinnerWilesOrdinaryAt p
            (primePlusTateFieldCoordinateAction p hp
              (darmonRationalParameter p ξ₀) β) D Q) := by
  let ξ := darmonRationalParameter p ξ₀
  let D₀ := C.selectedResidualData p hp ξ β κ
  rcases hdeep with hn | hc
  · refine ⟨D₀, C.selectedResidualRatio p hp ξ β κ, ?_⟩
    intro P _ hpP Q _ _
    exact primePlusRaynaudCubicNumerator_skinnerWilesOrdinaryAt p hp ξ₀
      hξ hA hB hAB hn β κ C hmap P hpP Q
  · refine ⟨D₀.swap, C.selectedResidualRatio_swap p hp ξ β κ, ?_⟩
    intro P _ hpP Q _ _
    exact primePlusRaynaudCubicDifference_skinnerWilesOrdinaryAt p hp ξ₀
      hξ hB hAB hc β κ C hmap P hpP Q

/-- [TripathiGoswamiRevised, Proposition `prime-deep-DO` and
Proposition `SW-checklist`] The actual numerator-deep selected plus Jacobian
supplies the complete native weight-two Skinner–Wiles input. Its local
ordinary conditions come from the Raynaud quotient; its determinant and
residual lattice come from the specified same-family native comparison.
The named literature inputs remain visible in those constructions. -/
noncomputable def primePlusCubicNumerator_nativeSkinnerWilesWeightTwoInput
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (hirred : (primePlusTateFieldCoordinateAction p hp
      (darmonRationalParameter p ξ₀) β).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
      (cyclotomicField p) := by
  let hcomplex := NumberField.exists_complexConjugation (realCyclotomicField p)
  let ι := Classical.choose hcomplex
  let hcomplex' := Classical.choose_spec hcomplex
  let c := Classical.choose hcomplex'
  have hc : c ^ 2 = 1 := (Classical.choose_spec hcomplex').1
  have hconj : ∀ x, ι (c x) = star (ι x) :=
    (Classical.choose_spec hcomplex').2
  let D := C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ
  apply skinnerWilesWeightTwoInput_of_primePlusNativeComparison
    p hp (darmonRationalParameter p ξ₀)
    (RealPrimePowerCompletion p 0) β κ C hirred ι c hc hconj D
  intro P _ hpP Q _ _
  exact Classical.choice <|
    primePlusRaynaudCubicNumerator_skinnerWilesOrdinaryAt p hp ξ₀
      hξ hA hB hAB hdeep β κ C hmap P hpP Q

/-- [TripathiGoswamiRevised, Proposition `prime-deep-DO` and
Proposition `SW-checklist`] The complementary-deep selected plus Jacobian
supplies the complete native weight-two input. Swapping the selected
residual ordering puts the transported Darmon–Mestre quadratic quotient in
the lower position, preserving the residual ratio field and oddness. -/
noncomputable def primePlusCubicDifference_nativeSkinnerWilesWeightTwoInput
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (hirred : (primePlusTateFieldCoordinateAction p hp
      (darmonRationalParameter p ξ₀) β).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
      (cyclotomicField p) := by
  let hcomplex := NumberField.exists_complexConjugation (realCyclotomicField p)
  let ι := Classical.choose hcomplex
  let hcomplex' := Classical.choose_spec hcomplex
  let c := Classical.choose hcomplex'
  have hc : c ^ 2 = 1 := (Classical.choose_spec hcomplex').1
  have hconj : ∀ x, ι (c x) = star (ι x) :=
    (Classical.choose_spec hcomplex').2
  let D := (C.selectedResidualData p hp
    (darmonRationalParameter p ξ₀) β κ).swap
  apply skinnerWilesWeightTwoInput_of_primePlusNativeComparison
    p hp (darmonRationalParameter p ξ₀)
    (RealPrimePowerCompletion p 0) β κ C hirred ι c hc hconj D
  intro P _ hpP Q _ _
  exact Classical.choice <|
    primePlusRaynaudCubicDifference_skinnerWilesOrdinaryAt p hp ξ₀
      hξ hB hAB hdeep β κ C hmap P hpP Q

/-- The rational cubic deep-cusp disjunction gives one native lifting input
on the actual selected plus-Jacobian Tate representation, with the residual
ordering chosen by the cusp. -/
noncomputable def primePlusCubic_nativeSkinnerWilesWeightTwoInput
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (hirred : (primePlusTateFieldCoordinateAction p hp
      (darmonRationalParameter p ξ₀) β).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
      (cyclotomicField p) := by
  classical
  by_cases hn : (p : ℤ) ^ 3 ∣ A
  · exact primePlusCubicNumerator_nativeSkinnerWilesWeightTwoInput
      p hp ξ₀ hξ hA hB hAB hn β κ C hmap hirred
  · have hc : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A) := hdeep.resolve_left hn
    exact primePlusCubicDifference_nativeSkinnerWilesWeightTwoInput
      p hp ξ₀ hξ hB hAB hc β κ C hmap hirred

end HilbertModularity.Hypergeometric
