/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalCoordinates
public import HilbertModularity.Geometry.GroupScheme.PrimeDarmonLocalSystemComparison
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomology

/-! # Cohomological coordinates for the same chosen Darmon and plus family

Equality of the chosen prime Darmon and selected plus Tate local systems
survives continuous dualization. Their arithmetic fibres therefore share
the two-coordinate selected plus cohomological action at the fixed label.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic

theorem three_le_of_five_le {p : ℕ} (hp : 5 ≤ p) : 3 ≤ p :=
  le_trans (by decide : 3 ≤ 5) hp

/-- The actual Darmon cohomological fibre is the selected plus
cohomological coordinate action at the same exponent label. -/
def darmonPrimeCohomologicalEquivPlus
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (m : ℕ) (hm : m.Coprime p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L] :
    ((darmonCohomologicalFamily (realCyclotomicField p) p
      (three_le_of_five_le hp) p m hm E hE w L).arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
      (primePlusCohomologicalAction p hp ξ p L
        (splits_minpoly_above_coefficientPrime p E w L hE)
        (coefficientEmbeddingAbovePrime p m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE)
          w L)) := by
  let hL := splits_minpoly_above_coefficientPrime p E w L hE
  let τ := coefficientEmbeddingAbovePrime p m hm E
    ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) w L
  let x := ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ
  have hTate := darmonLabelledTateFamily_eq_primePlus p (three_le_of_five_le hp) hp
    (realCyclotomicField p) m hm E hE w L
  have hCoh :
      darmonCohomologicalFamily (realCyclotomicField p) p (three_le_of_five_le hp) p m hm
        E hE w L = primePlusCohomologicalFamily p hp p L hL τ := by
    change (darmonLabelledTateFamily (realCyclotomicField p) p (three_le_of_five_le hp)
      p m hm E hE w L).cohDual = _
    rw [hTate]
    exact (primePlusCohomologicalFamily_eq_labelledTateDual
      p hp m hm E hE w L).symm
  exact (arithmeticLocalSystemEquivOfEq (realCyclotomicField p) L
    _ _ hCoh x).trans
      (primePlusCohomologicalFamilyArithmeticEquivAction p hp ξ p L hL τ)

end HilbertModularity.Hypergeometric
