/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedGenericPolynomial
public import HilbertModularity.Examples.PrimeFiveGoodModelPolynomialTransport
public import HilbertModularity.Examples.PrimeFiveSelectedRMProduct
public import HilbertModularity.Examples.PrimeFivePolynomialBaseChange
public import HilbertModularity.LinearAlgebra.ReverseCharacteristicPolynomial

/-! # Full Frobenius polynomials of the original selected plus Jacobian

The generic fibre of each chosen good model is isomorphic to the original
Jacobian at `ξ=125`. The basis-level Tate isomorphism carries the counted
polynomial to that same Jacobian, before choosing any RM factor.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

attribute [local instance] Ideal.Quotient.field
local instance selectedFullFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A basis certificate for the full dual Tate polynomial of a specified
group scheme and Galois element. -/
def SelectedDualPolynomial
    (K : Type*) [Field K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (R : Polynomial ℚ_[5]) : Prop :=
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate K A.X 5)),
      (LinearMap.toMatrix b b ((tateRepresentation K A.X 5).dual g)).charpolyRev = R

/-- A chosen basis and its full polynomial certificate, tied to one
specified group scheme, scalar field and Galois element. -/
structure SelectedDualPolynomialData
    (K : Type*) [Field K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (R : Polynomial ℚ_[5]) where
  basis : Module.Basis (Fin 4) ℚ_[5]
    (Module.Dual ℚ_[5] (rationalTate K A.X 5))
  charpolyRev_eq :
    (LinearMap.toMatrix basis basis ((tateRepresentation K A.X 5).dual g)).charpolyRev = R

/-- Extract the certified full dual Tate basis without unfolding the
statement predicate in its consumers. -/
theorem SelectedDualPolynomial.exists_basis
    (K : Type*) [Field K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (R : Polynomial ℚ_[5]) (h : SelectedDualPolynomial K A g R) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate K A.X 5)),
      (LinearMap.toMatrix b b ((tateRepresentation K A.X 5).dual g)).charpolyRev = R := by
  exact h

/-- The full polynomial of the original dual Tate action persists after
extension to a field containing the chosen RM labels. -/
theorem SelectedDualPolynomial.exists_baseChange_basis
    (K : Type*) [Field K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    [FiniteDimensional ℚ_[5] (rationalTate K A.X 5)]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (R : Polynomial ℚ_[5]) (h : SelectedDualPolynomial K A g R)
    (L : Type*) [Field L] [Algebra ℚ_[5] L] :
    ∃ bL : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate K A.X 5)),
      (LinearMap.toMatrix bL bL
        (((tateRepresentation K A.X 5).baseChange L).dual g)).charpolyRev =
          R.map (algebraMap ℚ_[5] L) := by
  obtain ⟨b, hb⟩ := SelectedDualPolynomial.exists_basis K A g R h
  let ρ := tateRepresentation K A.X 5
  let e := Representation.dualBaseChangeEquiv L ρ
  let bL := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
  refine ⟨bL, ?_⟩
  have hbase := dualTate_charpolyRev_baseChange (L := L) ρ g b
  have hmap := congrArg (fun P : Polynomial ℚ_[5] =>
    P.map (algebraMap ℚ_[5] L)) hb
  exact hbase.trans hmap

/-- The displayed numerical coefficients remain literal after extending
from the conductor-adic field to the RM splitting field. -/
theorem primeFiveNumericalPolynomial11_baseChange
    (L : Type*) [Field L] [Algebra ℚ_[5] L] :
    (primeFiveNumericalPolynomial11 ℚ_[5]).map (algebraMap ℚ_[5] L) =
      primeFiveNumericalPolynomial11 L :=
  primeFiveNumericalPolynomial11_map (algebraMap ℚ_[5] L)

theorem primeFiveNumericalPolynomial41_baseChange
    (L : Type*) [Field L] [Algebra ℚ_[5] L] :
    (primeFiveNumericalPolynomial41 ℚ_[5]).map (algebraMap ℚ_[5] L) =
      primeFiveNumericalPolynomial41 L :=
  primeFiveNumericalPolynomial41_map (algebraMap ℚ_[5] L)

/-- Transport a counted model polynomial to any actually isomorphic
generic-fibre group scheme. -/
theorem selectedDualPolynomial_of_model
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    (e : A ≅ localGenericFiber K P B)
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (R : Polynomial ℚ_[5])
    (hmodel : ModelGenericPolynomial K P B Q R) :
    SelectedDualPolynomial K A
      (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q) R := by
  obtain ⟨bB, hbB⟩ := ModelGenericPolynomial.exists_basis K P B Q R hmodel
  obtain ⟨bA, hbA⟩ := exists_selectedDualTateBasis_of_goodModel
    K P B A e 5
    (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q) bB
  unfold SelectedDualPolynomial
  exact ⟨bA, hbA.trans hbB⟩

/-- The actual plus Jacobian at `ξ=125` has the counted full polynomial
at an eleven-prime good model. -/
theorem selectedFullPolynomial11
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    SelectedDualPolynomial (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)
      (primeFiveNumericalPolynomial11 ℚ_[5]) := by
  obtain ⟨e⟩ := W.genericIso
  exact selectedDualPolynomial_of_model (realCyclotomicField 5) P W.model
    (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
    e Q (primeFiveNumericalPolynomial11 ℚ_[5])
    (selectedGenericPolynomial11 P W hk Q h5P)

/-- Extract the actual selected Jacobian's eleven-prime basis certificate
before extending the coefficient field. -/
theorem selectedFullPolynomial11_exists_basis
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation (realCyclotomicField 5)
          (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).dual
          (NumberField.geometricFrobenius (realCyclotomicField 5)
            (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q))).charpolyRev =
        primeFiveNumericalPolynomial11 ℚ_[5] := by
  have h := selectedFullPolynomial11 P W hk Q h5P
  unfold SelectedDualPolynomial at h
  exact h

/-- Choose the actual selected Jacobian's eleven-prime full polynomial
certificate once, keeping its basis and proof in the same structure. -/
def selectedFullPolynomial11_data
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    SelectedDualPolynomialData (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)
      (primeFiveNumericalPolynomial11 ℚ_[5]) := by
  refine Classical.choice ?_
  obtain ⟨b, hb⟩ := selectedFullPolynomial11_exists_basis P W hk Q h5P
  exact ⟨⟨b, hb⟩⟩

/-- The eleven-prime numerical polynomial is intrinsic to the original
selected Jacobian's full dual Tate Frobenius, independently of a basis. -/
theorem selectedFullPolynomial11_intrinsic
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    ((tateRepresentation (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).dual
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)).charpolyRev =
      primeFiveNumericalPolynomial11 ℚ_[5] := by
  let D := selectedFullPolynomial11_data P W hk Q h5P
  have h := D.charpolyRev_eq
  rw [LinearMap.charpolyRev_toMatrix] at h
  exact h

/-- The corresponding forty-one-prime polynomial is on the very same
selected plus Jacobian, with a possibly different good model. -/
theorem selectedFullPolynomial41
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    SelectedDualPolynomial (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)
      (primeFiveNumericalPolynomial41 ℚ_[5]) := by
  obtain ⟨e⟩ := W.genericIso
  exact selectedDualPolynomial_of_model (realCyclotomicField 5) P W.model
    (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
    e Q (primeFiveNumericalPolynomial41 ℚ_[5])
    (selectedGenericPolynomial41 P W hk Q h5P)

/-- The forty-one-prime basis certificate belongs to the same selected
Jacobian and uses the original geometric Frobenius. -/
theorem selectedFullPolynomial41_exists_basis
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate (realCyclotomicField 5)
        (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation (realCyclotomicField 5)
          (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).dual
          (NumberField.geometricFrobenius (realCyclotomicField 5)
            (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q))).charpolyRev =
        primeFiveNumericalPolynomial41 ℚ_[5] := by
  have h := selectedFullPolynomial41 P W hk Q h5P
  unfold SelectedDualPolynomial at h
  exact h

/-- The actual selected forty-one-prime full polynomial certificate with
its basis and geometric-Frobenius proof packaged together. -/
def selectedFullPolynomial41_data
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    SelectedDualPolynomialData (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter)
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)
      (primeFiveNumericalPolynomial41 ℚ_[5]) := by
  refine Classical.choice ?_
  obtain ⟨b, hb⟩ := selectedFullPolynomial41_exists_basis P W hk Q h5P
  exact ⟨⟨b, hb⟩⟩

/-- The forty-one-prime full dual Tate polynomial is also independent
of its chosen basis. -/
theorem selectedFullPolynomial41_intrinsic
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    ((tateRepresentation (realCyclotomicField 5)
      (primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter).X 5).dual
      (NumberField.geometricFrobenius (realCyclotomicField 5)
        (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q)).charpolyRev =
      primeFiveNumericalPolynomial41 ℚ_[5] := by
  let D := selectedFullPolynomial41_data P W hk Q h5P
  have h := D.charpolyRev_eq
  rw [LinearMap.charpolyRev_toMatrix] at h
  exact h

end HilbertModularity.Examples
