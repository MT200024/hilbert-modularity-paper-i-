/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeFiberDeterminant
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomology
public import HilbertModularity.Hypergeometric.FamilyComparison
public import HilbertModularity.RepresentationTheory.DualLattice

/-! # Determinants of the chosen prime Darmon family

The dependent equality of the selected family and its integral RM action
transports the polarized determinant with its original coefficient label.
Arithmetic specialization and contragredient duality then give the inverse
cyclotomic normalization of [TripathiGoswami, RMgeneral].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hN : 3 ≤ p) (hp : 5 ≤ p)
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [NormedField L] [NormedAlgebra ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ a : realCyclotomicField p,
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)
  (K : Type) [Field K] [CharZero K]
  (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p))

include hp

/-- The determinant retains both components of the chosen family/RM pair. -/
theorem darmonPrimeFiberLabelledTate_det
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det (A := L) (M := (endomorphismLabelledTate K (fiber K (darmonFamily p hN) x)
      ℓ (realCyclotomicField p) L hL
      ((fiberEndomorphismMap K (darmonFamily p hN) x).comp
        (darmonRealMultiplication p hN)) σ).toSubmodule)
      ((endomorphismLabelledTate K (fiber K (darmonFamily p hN) x)
      ℓ (realCyclotomicField p) L hL
      ((fiberEndomorphismMap K (darmonFamily p hN) x).comp
        (darmonRealMultiplication p hN)) σ).toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L) := by
  let P (D : Σ A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))),
      𝓞 (realCyclotomicField p) →+* End A) : Prop :=
    LinearMap.det (A := L) (M := (endomorphismLabelledTate K (fiber K D.1 x)
      ℓ (realCyclotomicField p) L hL
      ((fiberEndomorphismMap K D.1 x).comp D.2) σ).toSubmodule)
      ((endomorphismLabelledTate K (fiber K D.1 x)
      ℓ (realCyclotomicField p) L hL
      ((fiberEndomorphismMap K D.1 x).comp D.2) σ).toRepresentation g) =
      (Field.cyclotomicCharacterWithCoefficients K ℓ L g : L)
  have hs : P ⟨primePlusFamily p hp, primePlusRealMultiplication p hp⟩ := by
    dsimp only [P]
    have h := primePlusFiberTateFactor_det p hp ℓ L hL σ K x g
    unfold primePlusFiberTateFactor at h
    with_reducible exact h
  have hd : P (darmonFamilyWithRealMultiplication p hN) := by
    rw [darmonFamilyWithRealMultiplication_eq_primePlus p hN hp]
    exact hs
  dsimp only [P] at hd
  unfold darmonFamily darmonRealMultiplication
  with_reducible exact hd

section LabelledCompletion

variable (m : ℕ) (hm : m.Coprime p)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
  (C : Type) [NontriviallyNormedField C] [CompleteSpace C]
  [Algebra (w.adicCompletion E) C] [ContinuousSMul (w.adicCompletion E) C]
  [NormedAlgebra ℚ_[ℓ] C] [IsScalarTower ℚ_[ℓ] (w.adicCompletion E) C]
  [Algebra ℚ C] [IsScalarTower ℚ (w.adicCompletion E) C]
  [IsScalarTower ℚ ℚ_[ℓ] C]

omit [CompleteSpace C] in
/-- The actual arithmetic representation of the chosen prime Tate local system
has cyclotomic determinant at every nonsingular fibre. -/
theorem darmonPrimeLabelledTateFamily_det
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det ((darmonLabelledTateFamily K p hN ℓ m hm E hE w C
      ).arithmeticRepresentation x g) =
      (Field.cyclotomicCharacterWithCoefficients K ℓ C g : C) := by
  have h := darmonPrimeFiberLabelledTate_det p hN hp ℓ C
    (splits_minpoly_above_coefficientPrime p E w C hE)
    (coefficientEmbeddingAbovePrime p m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) w C)
    K x g
  unfold endomorphismLabelledTate at h
  exact (darmonLabelledTateFamily_arithmeticEquiv K p hN ℓ m hm E hE w C x
    ).determinant_eq g |>.trans h

/-- Cohomological duality inverts the actual cyclotomic determinant; it is
not absorbed into a finite-order comparison character. -/
theorem darmonPrimeCohomologicalFamily_det
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det ((darmonCohomologicalFamily K p hN ℓ m hm E hE w C
      ).arithmeticRepresentation x g) =
      ((Field.cyclotomicCharacterWithCoefficients K ℓ C g : C)⁻¹) := by
  have he := (darmonLabelledTateFamily K p hN ℓ m hm E hE w C
    ).cohDual_arithmeticRepresentation x
  change LinearMap.det ((darmonLabelledTateFamily K p hN ℓ m hm E hE w C
    ).cohDual.arithmeticRepresentation x g) = _
  rw [he]
  change LinearMap.det (((darmonLabelledTateFamily K p hN ℓ m hm E hE w C
    ).arithmeticRepresentation x g⁻¹).dualMap) = _
  rw [LinearMap.det_dualMap, darmonPrimeLabelledTateFamily_det p hN hp ℓ K x m hm E hE w C]
  simp only [map_inv, Units.val_inv_eq_inv_val]

end LabelledCompletion

end HilbertModularity.Hypergeometric
