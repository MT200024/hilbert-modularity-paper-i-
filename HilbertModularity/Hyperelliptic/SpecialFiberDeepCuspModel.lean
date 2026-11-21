/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberGenericPlusModel
public import HilbertModularity.Geometry.GroupScheme.PrimePlusScaledCusp

/-! # Deep-cusp instances of the selected scaled stable model

The cubic numerator and cubic difference alternatives place the *actual*
selected plus fibre into the canonical local scaled model. The model's
special and generic properties are supplied by `PrimePlusScaledStableModelData`.
-/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic

namespace HilbertModularity.Hyperelliptic

/-- [TripathiGoswami, proof of Proposition `prime-deep-DO`]
The cubic numerator condition constructs the actual local scaled model of
the selected plus fibre. Its generic Jacobian and split nodal special fibre
are supplied together, with the coefficient parameter kept equal to the
printed scaling `ξ/(2-τₚ(1))^p`. -/
def PrimePlusScaledStableModelData.of_cubicNumerator (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ)
    {A : ℤ} {B : ℕ} (hξ : ξ.val = (A : ℚ) / B)
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A) :
    PrimePlusScaledStableModelData p hp
      (Hypergeometric.darmonRationalParameter p ξ) :=
  PrimePlusScaledStableModelData.of_positiveValuation p hp _
    ((Hypergeometric.primePlusScaledParameter_lt_one_iff_cubic_numerator
      p hp ξ hξ hA hB hAB).2 hdeep)

/-- [TripathiGoswami, proof of Proposition `prime-deep-DO`]
The complementary cubic-difference condition constructs the corresponding
local model at `1-ξ`, with its own selected plus Jacobian. The Tate
intertwiner between the two fibres is a separate arithmetic comparison. -/
def PrimePlusScaledStableModelData.of_cubicDifference (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter ℚ)
    {A : ℤ} {B : ℕ} (hξ : ξ.val = (A : ℚ) / B)
    (hB : B ≠ 0) (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) :
    PrimePlusScaledStableModelData p hp
      (Hypergeometric.darmonRationalParameter p
        (ProjectiveLine.complementParameter ℚ ξ)) :=
  PrimePlusScaledStableModelData.of_positiveValuation p hp _
    ((Hypergeometric.primePlusComplementScaledParameter_lt_one_iff_cubic_difference
      p hp ξ hξ hB hAB).2 hdeep)

end HilbertModularity.Hyperelliptic
