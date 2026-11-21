/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveChosenArithmeticComparison
public import HilbertModularity.NumberTheory.CyclotomicPrime

/-! # The chosen fifth-cyclotomic coefficient place

The full fifth-cyclotomic field itself is a common coefficient field for the
first real label. Its canonical prime above five and a compatible local
embedding satisfy the exact label equality required by the selected
Euler/Darmon comparison.
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

local instance canonicalCoefficientFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The full cyclotomic field contains the normal closure of its real
fifth-cyclotomic subfield. -/
theorem primeFive_normalClosure_le_cyclotomic :
    IntermediateField.normalClosure ℚ (realCyclotomicField 5) Qbar ≤
      cyclotomicField 5 :=
  IntermediateField.normalClosure_le_iff_of_normal.mpr (realCyclotomicField_le 5)

/-- The canonical completion embedding realizes the fixed first real label,
with the chosen exponent appearing once. -/
theorem primeFive_coefficientEmbeddingAbovePrime_tau
    (hN : Nat.Prime 5) (hmPos : 0 < 1) (hmN : 1 < 5)
    (L : Type) [Field L]
    [Algebra ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    (ι : cyclotomicField 5 →+* L)
    (hcoeff : (algebraMap ((primeAboveConductor 5).adicCompletion
      (cyclotomicField 5)) L).comp
        (algebraMap (cyclotomicField 5)
          ((primeAboveConductor 5).adicCompletion (cyclotomicField 5))) = ι) :
    coefficientEmbeddingAbovePrime 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      (cyclotomicField 5)
      ((IntermediateField.le_normalClosure (realCyclotomicField 5)).trans
        primeFive_normalClosure_le_cyclotomic)
      (primeAboveConductor 5) L (tau 5 1) =
        ι ((root 5) ^ 1 + (root 5)⁻¹ ^ 1) := by
  rw [coefficientEmbeddingAbovePrime_tau_one]
  have hvalue : IntermediateField.inclusion
      ((IntermediateField.le_normalClosure (realCyclotomicField 5)).trans
        primeFive_normalClosure_le_cyclotomic) (tau 5 1) =
        (root 5) ^ 1 + (root 5)⁻¹ ^ 1 := by
    apply Subtype.ext
    rfl
  rw [hvalue]
  exact congrArg (fun f : cyclotomicField 5 →+* L =>
    f ((root 5) ^ 1 + (root 5)⁻¹ ^ 1)) hcoeff

/-- With the actual full-cyclotomic coefficient field and its canonical
conductor prime, the chosen Euler/Darmon comparison yields a finite
character and the fixed-label arithmetic trace equality at the worked
parameter. No independent coefficient field or labelled trace is chosen. -/
theorem exists_primeFive_canonicalArithmeticTraceComparison
    (hN : Nat.Prime 5) (h5 : 5 ≤ 5) (hmPos : 0 < 1) (hmN : 1 < 5)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [ContinuousSMul ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [NormedAlgebra ℚ_[5] L] [FiniteDimensional ℚ_[5] L]
    [IsScalarTower ℚ_[5] ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ ((primeAboveConductor 5).adicCompletion (cyclotomicField 5)) L]
    [IsScalarTower ℚ ℚ_[5] L]
    (ι : cyclotomicField 5 →+* L)
    (hcoeff : (algebraMap ((primeAboveConductor 5).adicCompletion
      (cyclotomicField 5)) L).comp
        (algebraMap (cyclotomicField 5)
          ((primeAboveConductor 5).adicCompletion (cyclotomicField 5))) = ι) :
    let 𝒞 := chosenSmoothProperEulerFamily 5 1 hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization 5 1 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent 5 1 𝒞 5 L ι
    let F_RM := darmonCohomologicalFamily (realCyclotomicField 5)
      5 (le_trans (by decide : 3 ≤ 5) h5) 5 1
      (eulerExponent_coprime_of_prime 5 1 hN hmPos hmN)
      (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
      (primeAboveConductor 5) L
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ,
      Continuous ν ∧ (Set.range ν).Finite ∧
      ∀ g,
        (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
          primeFiveParameter D.localSystem).character g =
          (ν g : L) *
            (puncturedFiberArithmeticRepresentation (realCyclotomicField 5)
              primeFiveParameter F_RM).character g := by
  let : (primeAboveConductor 5).asIdeal.LiesOver (Ideal.span {(5 : ℤ)}) :=
    primeAboveConductor_liesOver 5
  exact exists_primeFive_chosenArithmeticTraceComparison hN h5 hmPos hmN
    (cyclotomicField 5) primeFive_normalClosure_le_cyclotomic
    (primeAboveConductor 5) L ι
    (primeFive_coefficientEmbeddingAbovePrime_tau hN hmPos hmN L ι hcoeff)


end HilbertModularity.Examples
