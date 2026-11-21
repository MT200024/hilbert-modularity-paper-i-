/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricFactors
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricRanks
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientRank

/-! # Rank of each selected plus-family Tate factor

The selected pointed plus Jacobian has completed Tate rank two. The
coefficient-completion comparison transfers this rank to every actual
arithmetic coefficient label of that same Jacobian.
See [DarmonFibres, Section 3, Example 3 and Propositions 3.2 and 3.4] and
[TripathiGoswami, coefficient-label lemma].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- Every exponent-one prime-power coefficient-labelled Tate factor of the
selected plus Jacobian has rank two on each arithmetic fibre. The exponent-one
real cyclotomic field equals the prime real cyclotomic field, as proved in
`PrimeHypergeometricRanks`. -/
theorem finrank_primePlusPrimePowerLabelledTateSummand_at (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p))
    (L : Type) [NontriviallyNormedField L]
    [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField (p ^ (0 + 1)),
      ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField (p ^ (0 + 1)) →ₐ[ℚ] L) :
    Module.finrank L (labelledTateSummand K
      (fiber K (primePlusFamily p hp) x).X p (realCyclotomicField (p ^ (0 + 1))) L hL
      (fiberPointsAction K (AlgebraicClosure K) (primePlusFamily p hp) x
        (𝓞 (realCyclotomicField (p ^ (0 + 1))))
        (primePlusPrimePowerRealMultiplication p hp))
      σ) = 2 := by
  let : NeZero p := ⟨by omega⟩
  have h := GroupScheme.finrank_labelledTateSummand_eq_localCoefficientTateRep_of_embedding
    p 0 L K (primePlusFamily p hp) x (primePlusPrimePowerRealMultiplication p hp)
    hL σ
  exact h.trans (finrank_primePlusLocalTateRep_at p hp K x)

end HilbertModularity.Hypergeometric
