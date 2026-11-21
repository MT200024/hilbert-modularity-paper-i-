/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalCoordinates
public import HilbertModularity.Geometry.GroupScheme.HypergeometricFactors

/-! # The chosen Darmon fibre and the selected plus Tate factor

The prime-level choice of family and integral RM action is a single dependent
pair. Transporting that pair preserves the actual coefficient label and gives
the coordinate bridge required by the chosen Euler modularity application.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace AlgebraicGeometry.GroupScheme

/-- The geometric points action of an integral RM endomorphism specializes to
its action on the same group-scheme fibre. This packages the two equivalent
native Tate APIs without evaluating a particular family's chosen data. -/
def fiberLabelledTateEquivEndomorphism
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (A : CommGrp (Over S)) (x : Spec (CommRingCat.of K) ⟶ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (φ : 𝓞 F →+* End A)
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L) :
    ((labelledTateSubrepresentation K (fiber K A x).X ℓ F L hL
      (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
      (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) σ
      ).toRepresentation).Equiv
        ((endomorphismLabelledTate K (fiber K A x) ℓ F L hL
          ((fiberEndomorphismMap K A x).comp φ) σ).toRepresentation) := by
  unfold endomorphismLabelledTate
  exact Representation.Equiv.refl _

/-- Equality of the family together with its RM action transports the native
labelled Tate factor; the coefficient embedding is fixed. -/
def fiberLabelledTateEquivOfFamilyEq
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (x : Spec (CommRingCat.of K) ⟶ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L)
    (D D' : Σ A : CommGrp (Over S), 𝓞 F →+* End A) (h : D = D') :
    ((labelledTateSubrepresentation K (fiber K D.1 x).X ℓ F L hL
      (fiberPointsAction K (AlgebraicClosure K) D.1 x (𝓞 F) D.2)
      (fiberPointsAction_realized K (AlgebraicClosure K) D.1 x (𝓞 F) D.2) σ
      ).toRepresentation).Equiv
        ((endomorphismLabelledTate K (fiber K D'.1 x) ℓ F L hL
          ((fiberEndomorphismMap K D'.1 x).comp D'.2) σ).toRepresentation) := by
  subst D'
  exact fiberLabelledTateEquivEndomorphism K D.1 x ℓ F L D.2 hL σ

/-- An equality of dependent family/RM pairs preserves the labelled Tate
action before changing from the geometric-point API to the endomorphism API. -/
def fiberLabelledTateEquivOfFamilyEq_same
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (x : Spec (CommRingCat.of K) ⟶ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L)
    (D D' : Σ A : CommGrp (Over S), 𝓞 F →+* End A) (h : D = D') :
    ((labelledTateSubrepresentation K (fiber K D.1 x).X ℓ F L hL
      (fiberPointsAction K (AlgebraicClosure K) D.1 x (𝓞 F) D.2)
      (fiberPointsAction_realized K (AlgebraicClosure K) D.1 x (𝓞 F) D.2) σ
      ).toRepresentation).Equiv
      ((labelledTateSubrepresentation K (fiber K D'.1 x).X ℓ F L hL
        (fiberPointsAction K (AlgebraicClosure K) D'.1 x (𝓞 F) D'.2)
        (fiberPointsAction_realized K (AlgebraicClosure K) D'.1 x (𝓞 F) D'.2) σ
        ).toRepresentation) := by
  subst D'
  exact Representation.Equiv.refl _

/-- Native labelled Tate action of one dependent family/RM pair on a fibre.
Keeping the pair as one argument prevents a change of coefficient label while
transporting it. -/
def familyNativeLabelledTateFactor
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (x : Spec (CommRingCat.of K) ⟶ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L)
    (D : Σ A : CommGrp (Over S), 𝓞 F →+* End A) :=
  (endomorphismLabelledTate K (fiber K D.1 x) ℓ F L hL
    ((fiberEndomorphismMap K D.1 x).comp D.2) σ).toRepresentation

/-- The actual native factor respects equality of a whole family/RM pair. -/
def familyNativeLabelledTateFactorEquivOfFamilyEq
    (K : Type) [Field K] [CharZero K] {S : Scheme}
    (x : Spec (CommRingCat.of K) ⟶ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L)
    (D D' : Σ A : CommGrp (Over S), 𝓞 F →+* End A) (h : D = D') :
    (familyNativeLabelledTateFactor K x ℓ F L hL σ D).Equiv
      (familyNativeLabelledTateFactor K x ℓ F L hL σ D') := by
  subst D'
  exact Representation.Equiv.refl _


end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

/-- The chosen Darmon dependent family/RM pair and the selected plus pair
give the same native labelled Tate factor on the actual rational fibre. This
keeps the coefficient embedding fixed and does not invoke any extra source
claim about Tate actions. -/
def darmonPrimeNativeLabelledTateEquivPlus
    (p : ℕ) [Fact p.Prime] (h3 : 3 ≤ p) (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
      [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    (familyNativeLabelledTateFactor (realCyclotomicField p)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
      ℓ (realCyclotomicField p) L hL σ
      (darmonFamilyWithRealMultiplication p h3)).Equiv
    (familyNativeLabelledTateFactor (realCyclotomicField p)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
      ℓ (realCyclotomicField p) L hL σ
      ⟨primePlusFamily p hp, primePlusRealMultiplication p hp⟩) :=
  familyNativeLabelledTateFactorEquivOfFamilyEq
    (realCyclotomicField p)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    ℓ (realCyclotomicField p) L hL σ
    (darmonFamilyWithRealMultiplication p h3)
    ⟨primePlusFamily p hp, primePlusRealMultiplication p hp⟩
    (darmonFamilyWithRealMultiplication_eq_primePlus p h3 hp)

/-- Native labelled action of the chosen Darmon family on the actual fibre,
with the family and its integral RM action kept together. -/
def darmonPrimeNativeTateAction
    (p : ℕ) [Fact p.Prime] (h3 : 3 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
      [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :=
  familyNativeLabelledTateFactor (realCyclotomicField p)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    ℓ (realCyclotomicField p) L hL σ
    ⟨darmonFamily p h3, darmonRealMultiplication p h3⟩

/-- The actual chosen Darmon native action transports to the selected plus
native action through the equality of the full dependent family/RM pair. -/
def darmonPrimeNativeTateActionEquivPlus
    (p : ℕ) [Fact p.Prime] (h3 : 3 ≤ p) (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
      [IsScalarTower ℚ ℚ_[ℓ] L]
    (hL : ∀ a : realCyclotomicField p,
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField p →ₐ[ℚ] L) :
    (darmonPrimeNativeTateAction p h3 ξ ℓ L hL σ).Equiv
    (familyNativeLabelledTateFactor (realCyclotomicField p)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
      ℓ (realCyclotomicField p) L hL σ
      ⟨primePlusFamily p hp, primePlusRealMultiplication p hp⟩) := by
  have hpair :
      (⟨darmonFamily p h3, darmonRealMultiplication p h3⟩ :
        Σ A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))),
          𝓞 (realCyclotomicField p) →+* End A) =
        darmonFamilyWithRealMultiplication p h3 := by
    unfold darmonFamily darmonRealMultiplication
    exact Sigma.eta _
  exact (familyNativeLabelledTateFactorEquivOfFamilyEq
    (realCyclotomicField p)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    ℓ (realCyclotomicField p) L hL σ
    ⟨darmonFamily p h3, darmonRealMultiplication p h3⟩
    (darmonFamilyWithRealMultiplication p h3) hpair).trans
      (darmonPrimeNativeLabelledTateEquivPlus p h3 hp ξ ℓ L hL σ)

end HilbertModularity.Hypergeometric
