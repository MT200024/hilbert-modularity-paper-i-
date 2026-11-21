/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ChosenEulerCanonicalModularity
public import HilbertModularity.Hypergeometric.PrimePlusConductorDeterminant
public import HilbertModularity.Hypergeometric.PrimePlusOrdinaryNativeChecklist
public import HilbertModularity.NumberTheory.CuspDepth

/-! # The deep-cusp lifting checklist with canonical normalized coefficients -/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic HilbertModularForms

variable (p : ℕ) [Fact p.Prime]

local instance : NormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNormedField p
local instance : NontriviallyNormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNontriviallyNormedField p
local instance : NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  fullConductorCanonicalNormedAlgebra p
local instance : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p
local instance : CharP (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) p :=
  NumberField.adicCompletionResidueCharP
    (cyclotomicField p) (primeAboveConductor p) p

attribute [local instance] realFieldAlgebra


attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

local instance : CharP (𝒪[RealPrimePowerCompletion p 0] ⧸
    𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- The actual native checklist extends through the fixed exponent-labelled
map to normalized full conductor coefficients with the original topology. -/
def chosenConductorWeightTwoInput_of_native
    (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom)
      (cyclotomicField p))
    (habs : (Representation.baseChange
      (AlgebraicClosure (FullConductorCompletion p))
      ((primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom)).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m hm ξ)
      (cyclotomicField p) := by
  let f := chosenConductorNativeMap p m hm
  have hf : Continuous f := continuous_chosenConductorNativeMap p m hm
  have hfp (x : ℚ_[p]) :
      f (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) x) =
        algebraMap ℚ_[p] (FullConductorCompletion p) x := f.commutes x
  let Hfull := SkinnerWilesWeightTwoInput.mapLocalCoefficients_withOrdinary
    p (cyclotomicField p) H f.toRingHom hf hfp
    (chosenConductorNativeIntegerResidueComparison p m hm) habs
  rw [chosenConductorPlusCoordinateAction_eq_mapNative p hp m hm ξ]
  exact Hfull

/-- A weight-zero quotient at the chosen coprime label supplies the
canonical normalized full-conductor checklist once coefficient-field
irreducibility is known. This is the general local-to-global route, before
specializing the ordinary quotient to a deep cusp. -/
def chosenConductorOrdinaryWeightTwoInput_of_irreducible
    (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (W : PrimePlusOrdinaryQuotient p hp ξ m (by simpa using hm))
    (hirred : (chosenConductorPlusCoordinateAction p hp m hm ξ).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m hm ξ) (cyclotomicField p) := by
  have habs := chosenConductorPlus_absoluteIrreducible_of_irreducible
    p hp m hm ξ hirred
  rw [chosenConductorPlusCoordinateAction_eq_mapNative] at habs
  have hnative := primePlusCanonicalNative_isIrreducible_of_chosenConductorAbsolute
    p hp m hm ξ habs
  letI := primePlusCanonicalNativeAlgebra p hp
  let H := primePlusCanonicalOrdinarySkinnerWilesWeightTwoInput_of_label
    p hp ξ m (by simpa using hm) W hnative
  exact chosenConductorWeightTwoInput_of_native p hp m hm ξ H habs

/-- At either rational cubic cusp, irreducibility over the actual conductor
field supplies the canonical normalized checklist. The odd involution proves
absolute irreducibility, and faithful scalar extension gives native irreducibility.
This is the remaining irreducibility-dependent application of
[TripathiGoswamiRevised, Proposition `SW-checklist`]. -/
def chosenConductorCubicWeightTwoInput_of_irreducible
    (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (hirred : (chosenConductorPlusCoordinateAction p hp m hm
      (darmonRationalParameter p ξ₀)).IsIrreducible) :
    SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m hm
        (darmonRationalParameter p ξ₀)) (cyclotomicField p) := by
  have habs := chosenConductorPlus_absoluteIrreducible_of_irreducible
    p hp m hm (darmonRationalParameter p ξ₀) hirred
  rw [chosenConductorPlusCoordinateAction_eq_mapNative] at habs
  have hnative := primePlusCanonicalNative_isIrreducible_of_chosenConductorAbsolute
    p hp m hm (darmonRationalParameter p ξ₀) habs
  letI := primePlusCanonicalNativeAlgebra p hp
  let H := primePlusCanonicalCubicSkinnerWilesWeightTwoInput
    p hp ξ₀ hξ hA hB hAB hdeep hnative
  exact chosenConductorWeightTwoInput_of_native p hp m hm
    (darmonRationalParameter p ξ₀) H habs

/-- Either cubic-cusp condition gives the finite-field Hecke identities once
the actual conductor action is irreducible. All lifting-checklist fields,
coefficient maps, covariant coordinates and finite characters are internal. -/
theorem finiteFieldHilbertModularAt_of_cubic_of_irreducible
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (hirred : (chosenConductorPlusCoordinateAction p hp m
      (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt)
      (darmonRationalParameter p ξ₀)).IsIrreducible) :
    FiniteFieldHilbertModularAt p m (darmonRationalParameter p ξ₀).val := by
  exact finiteFieldHilbertModularAt_of_chosenConductorChecklist p hp m hmPos hmLt
    (darmonRationalParameter p ξ₀)
    (chosenConductorCubicWeightTwoInput_of_irreducible p hp m _ ξ₀
      hξ hA hB hAB hdeep hirred)

/-- The manuscript's weight-zero quotient condition yields finite-field
modularity once coefficient-field irreducibility is supplied. -/
theorem finiteFieldHilbertModularAt_of_ordinary_of_irreducible
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (W : PrimePlusOrdinaryQuotient p hp ξ m
      (by simpa using (eulerExponent_coprime_of_prime p m
        (Fact.out : p.Prime) hmPos hmLt)))
    (hirred : (chosenConductorPlusCoordinateAction p hp m
      (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt)
      ξ).IsIrreducible) :
    FiniteFieldHilbertModularAt p m ξ.val := by
  exact finiteFieldHilbertModularAt_of_chosenConductorChecklist p hp m hmPos hmLt ξ
    (chosenConductorOrdinaryWeightTwoInput_of_irreducible p hp m _ ξ W hirred)

/-- The valuation formulation of the manuscript's deep-cusp region supplies
all reduced numerator/denominator data internally. Only actual coefficient-field
irreducibility remains to be supplied by the chosen Euler comparison. -/
theorem finiteFieldHilbertModularAt_of_deep_cusp_of_irreducible
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ)
    (hdeep : 3 ≤ padicValRat p ξ₀.val ∨ 3 ≤ padicValRat p (1 - ξ₀.val))
    (hirred : (chosenConductorPlusCoordinateAction p hp m
      (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt)
      (darmonRationalParameter p ξ₀)).IsIrreducible) :
    FiniteFieldHilbertModularAt p m (darmonRationalParameter p ξ₀).val := by
  have hξ : ξ₀.val = (ξ₀.val.num : ℚ) / ξ₀.val.den := (Rat.num_div_den ξ₀.val).symm
  have hA : ξ₀.val.num ≠ 0 := by
    intro h
    apply ξ₀.property.1
    rw [hξ, h]
    simp
  have hB : ξ₀.val.den ≠ 0 := Rat.den_ne_zero ξ₀.val
  have hAB : Int.gcd ξ₀.val.num ξ₀.val.den = 1 := ξ₀.val.reduced
  have hcubic : (p : ℤ) ^ 3 ∣ ξ₀.val.num ∨
      (p : ℤ) ^ 3 ∣ ((ξ₀.val.den : ℤ) - ξ₀.val.num) := by
    rcases hdeep with h | h
    · exact Or.inl ((Cusp.padicValRat_ge_three_iff hA hB hAB).mp (hξ ▸ h))
    · have hne : (ξ₀.val.num : ℚ) / ξ₀.val.den ≠ 1 := hξ ▸ ξ₀.property.2
      exact Or.inr ((Cusp.padicValRat_one_sub_ge_three_iff hB hAB hne).mp (hξ ▸ h))
  exact finiteFieldHilbertModularAt_of_cubic_of_irreducible p hp m hmPos hmLt
    ξ₀ hξ hA hB hAB hcubic hirred

/-- The cubic-cusp checklist gives all-place automorphy for the actual
chosen Euler system, conditional only on its conductor coordinate action's
coefficient-field irreducibility. The same eigenform works at every place. -/
theorem exists_chosenEuler_allPlaceEigenform_of_cubic_of_irreducible
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (hirred : (chosenConductorPlusCoordinateAction p hp m
      (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt)
      (darmonRationalParameter p ξ₀)).IsIrreducible) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (j : cyclotomicField p →+* B)
        (level : FiniteLevel (realCyclotomicField p))
        (μ : AdditiveQuotientMeasure (realCyclotomicField p))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        letI : Algebra (cyclotomicField p) B := j.toAlgebra
        ∃ T : EigenformCohomologicalActions ψ,
          ψ.complexEmbedding = B.val.toRingHom ∧
          (∃ b : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ b) ∧
          (Set.range ψ.form.central_character).Finite ∧
          (∀ q, q ∉ (chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt (darmonRationalParameter p ξ₀)).bad →
            ∃ hψ : q ∉ ψ.form.bad,
              ((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt (darmonRationalParameter p ξ₀)).polynomial q).map
                j = ψ.heckePolynomial q hψ) ∧
          ∀ v : HeightOneSpectrum (𝓞 B),
            Nonempty ((((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt (darmonRationalParameter p ξ₀)
              ).extendCoefficients (L := B)).action v).Equiv (T.action v)) := by
  exact exists_chosenEuler_allPlaceEigenform_of_chosenConductorChecklist
    p hp m hmPos hmLt (darmonRationalParameter p ξ₀)
    (chosenConductorCubicWeightTwoInput_of_irreducible p hp m _ ξ₀
      hξ hA hB hAB hdeep hirred)

end HilbertModularity.Hypergeometric
