/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedRMFactorization
public import HilbertModularity.Examples.PrimeFiveNativeRMBases
public import HilbertModularity.Examples.PrimeFiveSelectedRMDeterminant
public import HilbertModularity.Hypergeometric.PrimePlusFullPolynomialExtension

/-! # Numerical polynomials of the selected native RM factors

The point-count polynomial belongs to the actual selected plus Jacobian.
Its native RM projectors have determinant equal to the residue cardinality,
so the full polynomial is the product of their trace quadratics.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric GroupScheme

local instance selectedNumericalFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local notation "K₅" => realCyclotomicField 5
local notation "J₅" => primePlusFiber 5 selectedRMProductFiveLowerBound primeFiveParameter

/-- The two native cohomological factors of the selected Jacobian give the
counted genus-two polynomial at a real prime of residue cardinality eleven. -/
theorem primeFiveSelectedRM_numericFactors11
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (P : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 K₅ ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ P.asIdeal) = 11)
    (Q : Ideal (𝓞 (AlgebraicClosure K₅)))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 K₅) ∉ P.asIdeal)
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 0)).toSubmodule))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 1)).toSubmodule)) :
    let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
    let f₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual g
    let f₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual g
    quadraticTraceFactor (LinearMap.toMatrix b₀ b₀ f₀) 11 *
      quadraticTraceFactor (LinearMap.toMatrix b₁ b₁ f₁) 11 =
        primeFiveNumericalPolynomial11 L := by
  let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
  let : FiniteDimensional ℚ_[5] (rationalTate K₅ (J₅).X 5) := by
    infer_instance
  let bK := (selectedFullPolynomial11_data P W hk Q h5P).basis
  let b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate K₅ (J₅).X 5)) := by
    with_reducible
      exact (Algebra.TensorProduct.basis L bK).map
        (Representation.dualBaseChangeEquiv L
          (tateRepresentation K₅ (J₅).X 5)).toLinearEquiv
  have hfull := primeFive_fullDualPolynomial11_baseChange L P W hk Q h5P
  have hcard : (Nat.card (𝓞 K₅ ⧸ P.asIdeal) : L) = 11 := by
    simp only [Nat.card_eq_fintype_card, hk, Nat.cast_ofNat]
  have hdet : ∀ σ : K₅ →ₐ[ℚ] L,
      LinearMap.det ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual g) = (11 : L) := by
    intro σ
    have h5P' : ((5 : ℕ) : 𝓞 K₅) ∉ P.asIdeal := by
      simpa only [Nat.cast_ofNat] using h5P
    with_reducible
      exact (primePlusLabelledDual_det_geometricFrobenius
        5 selectedRMProductFiveLowerBound primeFiveParameter 5 L hL σ P Q h5P').trans hcard
  with_reducible
    exact primeFiveSelectedRM_factorization_of_intrinsic
      L hL labels g 11 (primeFiveNumericalPolynomial11 L)
      hfull hdet b b₀ b₁

/-- The two native cohomological factors of the selected Jacobian give the
counted genus-two polynomial at a real prime of residue cardinality forty-one. -/
theorem primeFiveSelectedRM_numericFactors41
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[5] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[5] L]
    (hL : ∀ a : K₅, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (labels : Fin 2 ≃ (K₅ →ₐ[ℚ] L))
    (P : HeightOneSpectrum (𝓞 K₅))
    (W : PrimeFiveSelectedSpecialJacobian P)
    [Fintype (𝓞 K₅ ⧸ P.asIdeal)]
    (hk : Fintype.card (𝓞 K₅ ⧸ P.asIdeal) = 41)
    (Q : Ideal (𝓞 (AlgebraicClosure K₅)))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (h5P : (5 : 𝓞 K₅) ∉ P.asIdeal)
    (b₀ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 0)).toSubmodule))
    (b₁ : Module.Basis (Fin 2) L
      (Module.Dual L (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) (labels 1)).toSubmodule)) :
    let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
    let f₀ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 0)).toRepresentation.dual g
    let f₁ := (endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
      (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
        primeFiveParameter) (labels 1)).toRepresentation.dual g
    quadraticTraceFactor (LinearMap.toMatrix b₀ b₀ f₀) 41 *
      quadraticTraceFactor (LinearMap.toMatrix b₁ b₁ f₁) 41 =
        primeFiveNumericalPolynomial41 L := by
  let g := NumberField.geometricFrobenius K₅ (AlgebraicClosure K₅) P.asIdeal Q
  let : FiniteDimensional ℚ_[5] (rationalTate K₅ (J₅).X 5) := by
    infer_instance
  let bK := (selectedFullPolynomial41_data P W hk Q h5P).basis
  let b : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate K₅ (J₅).X 5)) := by
    with_reducible
      exact (Algebra.TensorProduct.basis L bK).map
        (Representation.dualBaseChangeEquiv L
          (tateRepresentation K₅ (J₅).X 5)).toLinearEquiv
  have hfull := primeFive_fullDualPolynomial41_baseChange L P W hk Q h5P
  have hcard : (Nat.card (𝓞 K₅ ⧸ P.asIdeal) : L) = 41 := by
    simp only [Nat.card_eq_fintype_card, hk, Nat.cast_ofNat]
  have hdet : ∀ σ : K₅ →ₐ[ℚ] L,
      LinearMap.det ((endomorphismLabelledTate K₅ J₅ 5 K₅ L hL
        (primePlusFiberRealMultiplication 5 selectedRMProductFiveLowerBound
          primeFiveParameter) σ).toRepresentation.dual g) = (41 : L) := by
    intro σ
    have h5P' : ((5 : ℕ) : 𝓞 K₅) ∉ P.asIdeal := by
      simpa only [Nat.cast_ofNat] using h5P
    with_reducible
      exact (primePlusLabelledDual_det_geometricFrobenius
        5 selectedRMProductFiveLowerBound primeFiveParameter 5 L hL σ P Q h5P').trans hcard
  with_reducible
    exact primeFiveSelectedRM_factorization_of_intrinsic
      L hL labels g 41 (primeFiveNumericalPolynomial41 L)
      hfull hdet b b₀ b₁

end HilbertModularity.Examples
