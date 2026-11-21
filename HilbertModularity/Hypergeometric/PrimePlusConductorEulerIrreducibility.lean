/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationSpecifiedPrimeComparison
public import HilbertModularity.RepresentationTheory.IrreducibilityReflection

public import HilbertModularity.Hypergeometric.ChosenEulerCanonicalModularity
public import HilbertModularity.Hypergeometric.ChosenEulerIrreducibility
public import HilbertModularity.NumberTheory.PrimeBelowComparison

/-! # Irreducibility of the actual selected conductor Tate coordinates

The chosen Euler specialization is irreducible at its specified coefficient
completion by the named GPRV input. The proved finite comparison character and
fixed-label Darmon equivalence then identify the same covariant plus-Jacobian
coordinate action, with no irreducibility or character supplied as a premise.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms

variable (p : ℕ) [Fact p.Prime]

local instance chosenEulerConductorNormedField : NormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNormedField p
local instance chosenEulerConductorNontriviallyNormedField : NontriviallyNormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNontriviallyNormedField p
local instance chosenEulerConductorNormedAlgebra : NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  fullConductorCanonicalNormedAlgebra p
local instance chosenEulerConductorCompleteSpace : CompleteSpace (FullConductorCompletion p) := inferInstance
local instance chosenEulerConductorLocalField : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

attribute [local instance] realFieldAlgebra

/-- The chosen full-conductor coordinate action of the selected plus Jacobian
is irreducible over its actual coefficient field for every nonsingular
prime-level specialization. The finite Euler comparison character is obtained
internally from the chosen family. See [TripathiGoswamiRevised, Lemma
`prime-absolute-irred`, proof paragraphs 1–2]. -/
theorem chosenConductorPlusCoordinate_isIrreducible
    (hp : 5 ≤ p) (m : ℕ) (hmPos : 0 < m) (hmLt : m < p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    (chosenConductorPlusCoordinateAction p hp m
      (eulerExponent_coprime_of_prime p m (Fact.out : p.Prime) hmPos hmLt) ξ).IsIrreducible := by
  let hN : p.Prime := Fact.out
  let hm := eulerExponent_coprime_of_prime p m hN hmPos hmLt
  let L := FullConductorCompletion p
  let ι : cyclotomicField p →+* L := algebraMap (cyclotomicField p) L
  let 𝒞 := chosenSmoothProperEulerFamily p m hN hp hmPos hmLt
  let R := chosenCommonRealEulerQuotientRealization p m 𝒞 hN hp hmPos hmLt
  have hι : coefficientEmbeddingAbovePrime p m hm
      (cyclotomicField p)
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
        (realCyclotomicNormalClosure_le_full p))
      (primeAboveConductor p) L (tau p 1) =
        ι ((root p) ^ m + (root p)⁻¹ ^ m) := by
    rw [coefficientEmbeddingAbovePrime_tau_one]
    have hvalue : IntermediateField.inclusion
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans
          (realCyclotomicNormalClosure_le_full p)) (tau p m) =
        (root p) ^ m + (root p)⁻¹ ^ m := by
      apply Subtype.ext
      rfl
    rw [hvalue]
    rfl
  have hEuler :
      let D := R.placeDescent p m 𝒞 p L ι
      (puncturedFiberArithmeticRepresentation (realCyclotomicField p) ξ
        D.localSystem).IsIrreducible := by
    let ρ := commonEulerCompletionAction p m 𝒞 R ξ (primeAboveConductor p)
    have hcoord : ρ.IsIrreducible :=
      chosenEulerConductorCompletion_isIrreducible
        p m hN hp hmPos hmLt ξ (primeAboveConductor p)
    have hbase : (ρ.baseChange L).IsIrreducible := by
      apply Representation.isIrreducible_equiv (Representation.baseChangePiEquiv (L := L) ρ).symm
      change (ρ.mapCoefficients (RingHom.id L)).IsIrreducible
      simpa only [Representation.mapCoefficients_id] using hcoord
    exact Representation.isIrreducible_equiv
      (commonEulerCompletionAction_baseChangeEquiv_at_prime p m 𝒞 R ξ p
        (primeAboveConductor p) L ι (by ext x; rfl)) hbase
  exact darmonLabelledTate_isIrreducible_of_selectedEuler
    p m hN hp hmPos hmLt (cyclotomicField p)
    (realCyclotomicNormalClosure_le_full p) (primeAboveConductor p) L
    𝒞 R ι hι ξ (chosenConductorPlusCoordinateAction p hp m hm ξ)
    (chosenConductorDarmonCoordinateEquiv_spectral p hp m hm ξ) hEuler

end HilbertModularity.Hypergeometric
