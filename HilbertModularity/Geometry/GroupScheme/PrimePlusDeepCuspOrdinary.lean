/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusScaledCusp
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricCuspOrdinary

/-! # The deep-cusp deduction for the selected prime plus Jacobian

The corrected scaled equation detects the two rational deep cusps. The
period-to-graph comparison and the complementary-cusp Tate intertwiner are
explicit geometric inputs on the same selected family. This module makes the
resulting ordinary-quotient deduction without identifying either input with
the ordinary conclusion.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower
  primePlusDecompositionRationalModule primePlusDecompositionScalarTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- The arithmetic data needed from the regularized Picard/period sequence of
the actual selected plus Jacobian. The period quotient and its graph map
must refer to the same fibre; its equivariance includes the completed RM
action. The period map, rank, and fixed-node action still require a geometric
construction. See [SGA7I, Exposé IX, §§8.2 and 12.3] and
[TripathiGoswami, proof of Proposition `prime-deep-DO`]. -/
structure PrimePlusGraphPeriodData
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) where
  nodeAction : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
    Equiv.Perm (Fin (((p - 1) / 2) + 1))
  fixedNodes : ∀ g i, nodeAction g i = i
  periodSubrepresentation :
    Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ
  periodToGraph :
    (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      periodSubrepresentation.toSubmodule
      periodSubrepresentation.apply_mem_toSubmodule).restrictScalars ℚ_[p]).IntertwiningMap
        (Graph.twoComponentHomologyRepresentation ℚ_[p] ((p - 1) / 2) nodeAction)
  surjective : Function.Surjective periodToGraph
  periodRank : Module.finrank ℚ_[p]
    ((primePlusDecompositionRepresentation p hp ξ) ⧸
      periodSubrepresentation.toSubmodule) = (p - 1) / 2

/-- The actual selected Jacobian has the manuscript's ordinary quotient once
its regularized Picard/period comparison supplies the stated data. -/
theorem PrimePlusGraphPeriodData.ordinary
    {ξ : ProjectiveLine.Parameter (realCyclotomicField p)}
    (D : PrimePlusGraphPeriodData p hp ξ) (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) :=
  nonempty_primePlusOrdinaryQuotient_of_surjectiveGraphMap p hp ξ
    D.nodeAction D.fixedNodes D.periodSubrepresentation D.periodToGraph
    D.surjective D.periodRank m hm

/-- Rational complement commutes with the actual embedding into the selected
real cyclotomic coefficient field. -/
theorem darmonRationalParameter_complement
    (ξ : ProjectiveLine.Parameter ℚ) :
    darmonRationalParameter p (ProjectiveLine.complementParameter ℚ ξ) =
      ProjectiveLine.complementParameter (realCyclotomicField p)
        (darmonRationalParameter p ξ) := by
  apply Subtype.ext
  simp [darmonRationalParameter_val, ProjectiveLine.complementParameter_val,
    map_sub]

/-- The first deep-cusp branch of [TripathiGoswami, Proposition
`prime-deep-DO`]. The hypothesis constructs the period comparison for the
same selected Jacobian when its corrected scaled parameter is integral of
positive order. The proposition's cubic numerator supplies that order. -/
theorem nonempty_primePlusOrdinaryQuotient_of_cubic_numerator
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (hdeep : (p : ℤ) ^ 3 ∣ A) (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp (darmonRationalParameter p ξ) m hm) := by
  have hscaled := (primePlusScaledParameter_lt_one_iff_cubic_numerator
    p hp ξ hξ hA hB hAB).2 hdeep
  obtain ⟨D⟩ := hgraph ξ hscaled
  exact D.ordinary p hp m hm

/-- The complementary deep-cusp branch of [TripathiGoswami,
Proposition `prime-deep-DO`]. The selected-fibre finite twist and local Tate
intertwiner are separate inputs; the parameter involution alone does not
construct them. -/
theorem nonempty_primePlusOrdinaryQuotient_of_cubic_difference
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp (darmonRationalParameter p ξ)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A)) (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp (darmonRationalParameter p ξ) m hm) := by
  let η := ProjectiveLine.complementParameter ℚ ξ
  have hscaled := (primePlusComplementScaledParameter_lt_one_iff_cubic_difference
    p hp ξ hξ hB hAB).2 hdeep
  obtain ⟨D⟩ := hgraph η hscaled
  have hbase : Nonempty (PrimePlusOrdinaryQuotient p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p)
        (darmonRationalParameter p ξ)) 1 (Nat.coprime_one_left _)) := by
    rw [← darmonRationalParameter_complement p ξ]
    exact D.ordinary p hp 1 (Nat.coprime_one_left _)
  exact nonempty_primePlusOrdinaryQuotient_of_complement_twist p hp
    (darmonRationalParameter p ξ) χ hχ horder e m hm hbase

/-- The two cubic divisibility alternatives imply the ordinary quotient for
the selected plus Jacobian, conditional on the same-fibre geometric graph
comparison and the local complementary-cusp intertwiner. This is the
arithmetic part of [TripathiGoswami, Proposition `prime-deep-DO`]. -/
theorem nonempty_primePlusOrdinaryQuotient_of_deep_cusp
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp (darmonRationalParameter p ξ)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp (darmonRationalParameter p ξ) m hm) := by
  rcases hdeep with hzero | hone
  · exact nonempty_primePlusOrdinaryQuotient_of_cubic_numerator p hp ξ
      hξ hA hB hAB hgraph hzero m hm
  · exact nonempty_primePlusOrdinaryQuotient_of_cubic_difference p hp ξ
      hξ hB hAB hgraph χ hχ horder e hone m hm

/-- The deep-cusp quotient gives the normalized upper-triangular local data
of the same selected Jacobian. In particular the quotient character has
finite normalized inertia, as required in the local ordinary checklist.
The geometric and complementary-cusp inputs are exactly those of the
preceding theorem; see [TripathiGoswami, Proposition `prime-deep-DO`]. -/
theorem nonempty_primePlusNormalizedOrdinaryData_of_deep_cusp
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp (darmonRationalParameter p ξ)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusNormalizedOrdinaryData p hp (darmonRationalParameter p ξ) m hm) := by
  obtain ⟨W⟩ := nonempty_primePlusOrdinaryQuotient_of_deep_cusp p hp ξ
    hξ hA hB hAB hgraph χ hχ horder e hdeep m hm
  exact W.exists_normalizedOrdinaryData p hp (darmonRationalParameter p ξ) m hm

/-- A selected normalized local basis for the same plus Jacobian at a deep
rational cusp. The choice makes subsequent comparison hypotheses refer to one
specific basis and integral lattice; the existence proof is the preceding
manuscript deduction. -/
noncomputable def primePlusNormalizedOrdinaryData_of_deep_cusp
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp (darmonRationalParameter p ξ)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    PrimePlusNormalizedOrdinaryData p hp (darmonRationalParameter p ξ) m hm :=
  Classical.choice <| nonempty_primePlusNormalizedOrdinaryData_of_deep_cusp
    p hp ξ hξ hA hB hAB hgraph χ hχ horder e hdeep m hm

end HilbertModularity.Hypergeometric
