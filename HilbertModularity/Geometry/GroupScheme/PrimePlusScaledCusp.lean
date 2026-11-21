/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusScaledJacobian
public import HilbertModularity.Geometry.GroupScheme.HypergeometricScalarConjugate
public import HilbertModularity.Geometry.ProjectiveInvolution
public import HilbertModularity.NumberTheory.RealCyclotomicPrime

/-! # Deep rational cusps on the selected scaled plus curve

The local parameter here is the one in the smooth generic curve whose pointed
Jacobian is the selected prime plus family. Its positive valuation is the
numerical input to the separate integral stable-model argument. -/

public noncomputable section

open CategoryTheory AlgebraicGeometry HilbertModularity.Cyclotomic
  HilbertModularity.Hyperelliptic

namespace HilbertModularity.Hypergeometric

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- [TripathiGoswami, proof of Proposition `prime-deep-DO`, scaled equation;
Appendix A] The parameter of the selected smooth scaled curve lies in the
maximal ideal exactly at rational `p`-adic depth at least three. The
normalization of `2 - τₚ(1)` is proved for the actual real cyclotomic prime. -/
theorem primePlusScaledParameter_lt_one_iff_depth_three
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ) :
    (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (((darmonRationalParameter p ξ).val : realCyclotomicField p) /
        (2 - tau p 1) ^ p) < 1 ↔ 3 ≤ padicValRat p ξ.val := by
  have hval : (darmonRationalParameter p ξ).val =
      (ξ.val : realCyclotomicField p) := by
    rw [darmonRationalParameter_val]
    exact (rfl)
  rw [hval]
  exact
    (valuation_scaled_parameter_lt_one_iff p hp
      (valuation_real_parameter p (by omega)) ξ.property.1)

/-- [TripathiGoswami, Proposition `prime-deep-DO`] The first printed
divisibility alternative is precisely positive depth for the parameter of
the selected smooth scaled plus curve. -/
theorem primePlusScaledParameter_lt_one_iff_cubic_numerator
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) :
    (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (((darmonRationalParameter p ξ).val : realCyclotomicField p) /
        (2 - tau p 1) ^ p) < 1 ↔ (p : ℤ) ^ 3 ∣ A := by
  rw [primePlusScaledParameter_lt_one_iff_depth_three p hp ξ, hξ]
  exact Cusp.padicValRat_ge_three_iff hA hB hAB

/-- [TripathiGoswami, Proposition `prime-deep-DO`] The complementary
cusp has positive scaled depth exactly when `p³` divides `B - A`. This is a
statement about the selected family at `1 - ξ`; it does not supply the Tate
intertwiner between the two fibres. -/
theorem primePlusComplementScaledParameter_lt_one_iff_cubic_difference
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) :
    (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (((darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ)).val :
          realCyclotomicField p) / (2 - tau p 1) ^ p) < 1 ↔
        (p : ℤ) ^ 3 ∣ ((B : ℤ) - A) := by
  rw [primePlusScaledParameter_lt_one_iff_depth_three p hp
    (ProjectiveLine.complementParameter ℚ ξ), ProjectiveLine.complementParameter_val, hξ]
  exact Cusp.padicValRat_one_sub_ge_three_iff hB hAB (by simpa [← hξ] using ξ.property.2)

/-- [TripathiGoswami, proof of Proposition `prime-deep-DO`] At a rational
depth-three cusp, the *same selected plus Jacobian* is the pointed Jacobian
of the scaled smooth generic curve, and its scaled parameter has positive
local order. The integral stable-model and Picard comparison are separate. -/
theorem exists_primePlusScaledJacobian_at_cubic_numerator
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A) :
    Nonempty (Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          ((darmonRationalParameter p ξ).val / (2 - tau p 1) ^ p)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          ((darmonRationalParameter p ξ).val / (2 - tau p 1) ^ p))) b
        (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p)
            (darmonRationalParameter p ξ)))) ∧
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        ((darmonRationalParameter p ξ).val / (2 - tau p 1) ^ p) < 1 := by
  obtain ⟨b, hb⟩ := primePlusRealScaledFiberJacobian p hp (darmonRationalParameter p ξ)
  exact ⟨⟨b, hb⟩,
    (primePlusScaledParameter_lt_one_iff_cubic_numerator p hp ξ hξ hA hB hAB).2 hdeep⟩

/-- [TripathiGoswami, proof of Proposition `prime-deep-DO`] At the
complementary rational cusp, the selected plus Jacobian at `1 - ξ` is the
pointed Jacobian of its scaled smooth generic curve and the scaled parameter
has positive local order. The comparison with the fibre at `ξ` requires the
separate Tate intertwiner. -/
theorem exists_primePlusComplementScaledJacobian_at_cubic_difference
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    Nonempty (Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          ((darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ)).val /
            (2 - tau p 1) ^ p)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
          ((darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ)).val /
            (2 - tau p 1) ^ p))) b
        (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p)
            (darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ))))) ∧
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        ((darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ)).val /
          (2 - tau p 1) ^ p) < 1 := by
  obtain ⟨b, hb⟩ := primePlusRealScaledFiberJacobian p hp
    (darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ))
  exact ⟨⟨b, hb⟩,
    (primePlusComplementScaledParameter_lt_one_iff_cubic_difference
      p hp ξ hξ hB hAB).2 hdeep⟩

end HilbertModularity.Hypergeometric
