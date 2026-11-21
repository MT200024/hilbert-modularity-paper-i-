/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorSpectralCoordinates
public import HilbertModularity.Hypergeometric.ChosenEulerFiniteFieldModularity

/-! # Finite-field modularity from the actual conductor checklist

The normalized conductor field and the fixed-label covariant coordinate
comparison are constructed internally. The remaining input is the lifting
checklist for the actual selected integral Tate action.
-/

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

/-- The actual selected conductor checklist yields the manuscript's
finite-field Hecke trace property. No coefficient field, coordinate
comparison or finite comparison character is supplied as a premise. -/
theorem finiteFieldHilbertModularAt_of_chosenConductorChecklist
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m
        (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt) ξ)
      (cyclotomicField p)) :
    FiniteFieldHilbertModularAt p m ξ.val := by
  let hm := eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt
  exact finiteFieldHilbertModularAt_of_skinnerWiles p m Fact.out hp hmPos hmLt
    (primeAboveConductor p) (FullConductorCompletion p)
    (algebraMap (cyclotomicField p) (FullConductorCompletion p)) (by ext x; rfl)
    ξ (chosenConductorPlusCoordinateAction p hp m hm ξ)
    (chosenConductorDarmonCoordinateEquiv_spectral p hp m hm ξ)
    (cyclotomicField p) H

/-- The same actual conductor checklist produces one eigenform and a
compatible identification at every coefficient place of the chosen Euler
system. The normalized field and covariant coordinates are internal. -/
theorem exists_chosenEuler_allPlaceEigenform_of_chosenConductorChecklist
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (H : SkinnerWilesWeightTwoInput p
      (chosenConductorPlusCoordinateAction p hp m
        (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt) ξ)
      (cyclotomicField p)) :
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
          (∀ q, q ∉ (chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ).bad →
            ∃ hψ : q ∉ ψ.form.bad,
              ((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ).polynomial q).map
                j = ψ.heckePolynomial q hψ) ∧
          ∀ v : HeightOneSpectrum (𝓞 B),
            Nonempty ((((chosenCommonEulerCompatibleSystem p m (Fact.out : p.Prime) hp hmPos hmLt ξ
              ).extendCoefficients (L := B)).action v).Equiv (T.action v)) := by
  let hm := eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt
  exact exists_chosenEuler_allPlaceEigenform_of_skinnerWiles p m Fact.out hp hmPos hmLt
    (primeAboveConductor p) (FullConductorCompletion p)
    (algebraMap (cyclotomicField p) (FullConductorCompletion p)) (by ext x; rfl)
    ξ (chosenConductorPlusCoordinateAction p hp m hm ξ)
    (chosenConductorDarmonCoordinateEquiv_spectral p hp m hm ξ)
    (cyclotomicField p) H


end HilbertModularity.Hypergeometric
