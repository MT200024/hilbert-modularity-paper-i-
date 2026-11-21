/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFivePointedRawPolynomial

/-! # The counted polynomial on a selected good model's generic fibre

The point-count and good-reduction comparisons are composed while the
number field and the model remain abstract. The level-five model is inserted
only after their common residue-field structure has been fixed.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hyperelliptic GroupScheme

attribute [local instance] Ideal.Quotient.field
local instance selectedGenericFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The full cohomological Frobenius polynomial of the generic fibre of a
specified good model, in a basis of its original Tate module. -/
def ModelGenericPolynomial
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (R : Polynomial ℚ_[5]) : Prop :=
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate K (localGenericFiber K P B).X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation K (localGenericFiber K P B).X 5).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K)
            P.asIdeal Q))).charpolyRev = R

/-- Extract the model's transported basis without unfolding the statement
predicate in downstream applications. -/
theorem ModelGenericPolynomial.exists_basis
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (R : Polynomial ℚ_[5]) (h : ModelGenericPolynomial K P B Q R) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate K (localGenericFiber K P B).X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation K (localGenericFiber K P B).X 5).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K)
            P.asIdeal Q))).charpolyRev = R := by
  exact h

/-- Count the pointed special curve and transport its full cohomological
polynomial through the same good abelian model. -/
theorem modelGenericPolynomial11_of_pointed
    (K : Type*) [fieldK : Field K] [numberFieldK : NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [modelProper : IsProper B.X.hom] [modelSmooth : Smooth B.X.hom]
    [modelConnected : GeometricallyConnected B.X.hom]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [maxQ : Q.IsMaximal]
    [liesQ : Q.LiesOver P.asIdeal]
    [residueFinite : Fintype (𝓞 K ⧸ P.asIdeal)]
    (h5P : (5 : 𝓞 K) ∉ P.asIdeal)
    (hk : Fintype.card (𝓞 K ⧸ P.asIdeal) = 11)
    (point : Over.mk (𝟙 (Spec (CommRingCat.of (𝓞 K ⧸ P.asIdeal)))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial (𝓞 K ⧸ P.asIdeal)) 3
        (primeFivePolynomial_degree (𝓞 K ⧸ P.asIdeal))))
    (pointed : PointedCurveJacobian (𝓞 K ⧸ P.asIdeal)
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial (𝓞 K ⧸ P.asIdeal)) 3
        (primeFivePolynomial_degree (𝓞 K ⧸ P.asIdeal))))
      point (localSpecialFiber K P B)) :
    ModelGenericPolynomial K P B Q (primeFiveNumericalPolynomial11 ℚ_[5]) := by
  let k := 𝓞 K ⧸ P.asIdeal
  have hspecial := exists_primeFive_pointedJacobianPolynomial11_basis
    k hk (localSpecialFiber K P B) point pointed
  have h5P' : ((5 : ℕ) : 𝓞 K) ∉ P.asIdeal := by
    simpa only [Nat.cast_ofNat] using h5P
  unfold ModelGenericPolynomial
  with_reducible
    exact exists_goodReduction_genericFrobeniusPolynomial_of_special
      K P B Q 5 h5P' (primeFiveNumericalPolynomial11 ℚ_[5]) hspecial

/-- The actual selected Jacobian at `ξ=125` inherits the counted
eleven-prime generic polynomial from its own pointed special fibre. -/
theorem selectedGenericPolynomial11
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    ModelGenericPolynomial (realCyclotomicField 5) P W.model Q
      (primeFiveNumericalPolynomial11 ℚ_[5]) := by
  let : IsProper W.model.X.hom := W.proper
  let : Smooth W.model.X.hom := W.smooth
  let : GeometricallyConnected W.model.X.hom := W.connected
  exact modelGenericPolynomial11_of_pointed
    (realCyclotomicField 5) P W.model Q h5P hk
    W.specialPoint W.specialJacobian

/-- The same counted special Jacobian at the forty-one-prime transports
through its original selected good model. -/
theorem modelGenericPolynomial41_of_pointed
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal]
    [Q.LiesOver P.asIdeal]
    [Fintype (𝓞 K ⧸ P.asIdeal)]
    (h5P : (5 : 𝓞 K) ∉ P.asIdeal)
    (hk : Fintype.card (𝓞 K ⧸ P.asIdeal) = 41)
    (point : Over.mk (𝟙 (Spec (CommRingCat.of (𝓞 K ⧸ P.asIdeal)))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial (𝓞 K ⧸ P.asIdeal)) 3
        (primeFivePolynomial_degree (𝓞 K ⧸ P.asIdeal))))
    (pointed : PointedCurveJacobian (𝓞 K ⧸ P.asIdeal)
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial (𝓞 K ⧸ P.asIdeal)) 3
        (primeFivePolynomial_degree (𝓞 K ⧸ P.asIdeal))))
      point (localSpecialFiber K P B)) :
    ModelGenericPolynomial K P B Q (primeFiveNumericalPolynomial41 ℚ_[5]) := by
  let k := 𝓞 K ⧸ P.asIdeal
  have hspecial := exists_primeFive_pointedJacobianPolynomial41_basis
    k hk (localSpecialFiber K P B) point pointed
  have h5P' : ((5 : ℕ) : 𝓞 K) ∉ P.asIdeal := by
    simpa only [Nat.cast_ofNat] using h5P
  unfold ModelGenericPolynomial
  with_reducible
    exact exists_goodReduction_genericFrobeniusPolynomial_of_special
      K P B Q 5 h5P' (primeFiveNumericalPolynomial41 ℚ_[5]) hspecial

/-- The actual selected Jacobian at `ξ=125` inherits the forty-one-prime
generic polynomial from its own pointed special fibre. -/
theorem selectedGenericPolynomial41
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal) :
    ModelGenericPolynomial (realCyclotomicField 5) P W.model Q
      (primeFiveNumericalPolynomial41 ℚ_[5]) := by
  let : IsProper W.model.X.hom := W.proper
  let : Smooth W.model.X.hom := W.smooth
  let : GeometricallyConnected W.model.X.hom := W.connected
  exact modelGenericPolynomial41_of_pointed
    (realCyclotomicField 5) P W.model Q h5P hk
    W.specialPoint W.specialJacobian

end HilbertModularity.Examples
