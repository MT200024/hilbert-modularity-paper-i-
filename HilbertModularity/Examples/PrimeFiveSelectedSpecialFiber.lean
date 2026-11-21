/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedJacobian
public import HilbertModularity.Examples.PrimeFiveGoodReductionFrobenius

/-! # Frobenius on the selected level-five special Jacobian

The model below is the specialization of the single selected plus Jacobian.
Its special fibre is identified with the pointed Jacobian of the reduced
completed curve before applying the checked numerical point counts.
-/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Examples

open Hyperelliptic Hypergeometric _root_.HilbertModularity.Cyclotomic GroupScheme

attribute [local instance] Ideal.Quotient.field
local instance selectedPolynomialFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance selectedPolynomialSevenFact : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance selectedPolynomialElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance selectedPolynomialFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The actual special fibre of a chosen model over the local valuation ring. -/
def primeFiveSpecialFiber
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField 5)))))) :=
  localSpecialFiber (realCyclotomicField 5) P B

/-- The named special fibre is the standard pullback of this same model. -/
theorem primeFiveSpecialFiber_eq_localSpecialFiber
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (B : CommGrp (Over (Spec (CommRingCat.of
      (P.valuationSubringAtPrime (realCyclotomicField 5)))))) :
    primeFiveSpecialFiber P B = localSpecialFiber (realCyclotomicField 5) P B := (rfl)

/-- A good model of the actual selected plus Jacobian, including the
Abel–Jacobi identification of its special fibre. -/
structure PrimeFiveSelectedSpecialJacobian
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5))) where
  model : CommGrp (Over (Spec (CommRingCat.of
    (P.valuationSubringAtPrime (realCyclotomicField 5)))))
  proper : IsProper model.X.hom
  smooth : Smooth model.X.hom
  connected : GeometricallyConnected model.X.hom
  genericIso : Nonempty (primePlusFiber 5 (by decide) primeFiveParameter ≅
    localGenericFiber (realCyclotomicField 5) P model)
  specialPoint : Over.mk (𝟙 (Spec (CommRingCat.of
    (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)))) ⟶
    Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
      (primeFivePolynomial (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)) 3
      (primeFivePolynomial_degree (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)))
  specialJacobian : PointedCurveJacobian
    (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
    (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
      (primeFivePolynomial (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)) 3
      (primeFivePolynomial_degree (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal))))
    specialPoint (localSpecialFiber (realCyclotomicField 5) P model)

/-- Standard relative Jacobian geometry gives this data for the same selected
plus fibre, once its reduced branch polynomial is separable. -/
theorem exists_primeFiveSelectedSpecialJacobian
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (h2 : (2 : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal)
    (hsep : (primeFivePolynomial
      (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)).Separable) :
    Nonempty (PrimeFiveSelectedSpecialJacobian P) := by
  obtain ⟨B, hp, hs, hc, he, b, ⟨hJ⟩⟩ :=
    exists_primeFive_selectedSpecialJacobian P h2 hsep
  exact ⟨⟨B, hp, hs, hc, he, b, hJ⟩⟩

/-- The special fibre of the model of the single selected plus Jacobian. -/
def PrimeFiveSelectedSpecialJacobian.specialFiber
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P) :=
  primeFiveSpecialFiber P W.model

/-- Geometric Frobenius on its cohomological dual Tate space. -/
def PrimeFiveSelectedSpecialJacobian.geometricFrobeniusAction
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (W : PrimeFiveSelectedSpecialJacobian P) :=
  (tateRepresentation (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
    (primeFiveSpecialFiber P W.model).X 7).dual
    (AlgebraicGeometry.Hyperelliptic.finiteFieldGeometricFrobenius
      (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal))

/-- Apply standard good-reduction cohomology to this already selected model.
Its source is the general named Milne comparison, and the statement retains
the actual generic and special fibres of `W.model`. -/
theorem PrimeFiveSelectedSpecialJacobian.exists_genericFrobeniusBasis
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bₛ : Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
          (localSpecialFiber (realCyclotomicField 5) P W.model).X ℓ))) :
    ∃ bₙ : Module.Basis ι ℚ_[ℓ]
        (Module.Dual ℚ_[ℓ] (rationalTate (realCyclotomicField 5)
          (localGenericFiber (realCyclotomicField 5) P W.model).X ℓ)),
      (LinearMap.toMatrix bₙ bₙ
        ((tateRepresentation (realCyclotomicField 5)
          (localGenericFiber (realCyclotomicField 5) P W.model).X ℓ).dual
          (NumberField.geometricFrobenius (realCyclotomicField 5)
            (AlgebraicClosure (realCyclotomicField 5)) P.asIdeal Q))).charpolyRev =
        (LinearMap.toMatrix bₛ bₛ
          ((tateRepresentation (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
            (localSpecialFiber (realCyclotomicField 5) P W.model).X ℓ).dual
            (Hyperelliptic.finiteFieldGeometricFrobenius
              (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)))).charpolyRev := by
  let : IsProper W.model.X.hom := W.proper
  let : Smooth W.model.X.hom := W.smooth
  let : GeometricallyConnected W.model.X.hom := W.connected
  exact exists_goodReduction_dualTateFrobenius_basis
    (realCyclotomicField 5) P W.model Q ℓ hℓ bₛ

/-- Choose the generic cohomology basis transported from one basis on this
same selected model's special fibre. -/
def PrimeFiveSelectedSpecialJacobian.genericFrobeniusBasis
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField 5)))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)]
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField 5))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : 𝓞 (realCyclotomicField 5)) ∉ P.asIdeal)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bₛ : Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 (realCyclotomicField 5) ⧸ P.asIdeal)
          (localSpecialFiber (realCyclotomicField 5) P W.model).X ℓ))) :
    Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ] (rationalTate (realCyclotomicField 5)
        (localGenericFiber (realCyclotomicField 5) P W.model).X ℓ)) :=
  (W.exists_genericFrobeniusBasis P Q ℓ hℓ bₛ).choose

end HilbertModularity.Examples
