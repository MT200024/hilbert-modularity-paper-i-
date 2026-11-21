/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementTate
public import HilbertModularity.Geometry.GroupScheme.PrimePlusRaynaudStableApplication

/-! # The complementary deep cusp on the original plus Jacobian

The scaled stable model at `1-ξ` gives the ordinary quotient there. The
Darmon--Mestre correspondence carries it to the selected fibre at `ξ`
through the explicit quadratic cyclotomic Tate comparison. This applies the
same native RM label after one global relabelling; no separate fibrewise
character or quotient is chosen.
-/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- The manuscript's `p³` complementary-cusp branch on the *original*
selected plus Jacobian. The named Darmon--Mestre/Tate literature interface
is the sole new conditional input beyond the already checked stable-model
and Raynaud calculation. -/
theorem nonempty_primePlusOrdinaryQuotient_at_cubic_difference_original
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp
      (darmonRationalParameter p ξ₀) m hm) := by
  let ξ := darmonRationalParameter p ξ₀
  obtain ⟨e⟩ := nonempty_primePlusComplementNativeTateComparison p hp ξ
  exact nonempty_primePlusOrdinaryQuotient_at_deep_cusp p hp ξ₀
    hξ hA hB hAB (primePlusComplementQuadraticCharacter p hp)
    (primePlusComplementQuadraticCharacter_continuous p hp)
    (primePlusComplementQuadraticCharacter_isOfFinOrder p hp)
    e (Or.inr hdeep) m hm

/-- Both rational `p³` alternatives now use actual selected plus fibres;
the zero cusp is the existing scaled-model application and the one cusp is
the fixed Darmon--Mestre quadratic comparison proved above. -/
theorem nonempty_primePlusOrdinaryQuotient_at_cubic_cusps_original
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp
      (darmonRationalParameter p ξ₀) m hm) := by
  rcases hdeep with hzero | hone
  · exact nonempty_primePlusOrdinaryQuotient_at_cubic_numerator p hp ξ₀
      hξ hA hB hAB hzero m hm
  · exact nonempty_primePlusOrdinaryQuotient_at_cubic_difference_original p hp ξ₀
      hξ hA hB hAB hone m hm

end HilbertModularity.Hypergeometric
