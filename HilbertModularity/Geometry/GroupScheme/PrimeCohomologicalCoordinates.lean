/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem.Coordinates
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.EndomorphismDual
public import HilbertModularity.Geometry.GroupScheme.PrimeLabelledCompatibility
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricFactors

/-! # Continuous coordinates for the selected cohomological factor

The action is the arithmetic fibre of the actual selected plus-Jacobian family,
with its fixed RM label and contragredient convention. Rank two is derived from
the same family's Tate factor, rather than supplied as an additional premise.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
  (ℓ : ℕ) [Fact ℓ.Prime]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[ℓ] L]
  (hL : ∀ a : realCyclotomicField p,
    ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
  (σ : realCyclotomicField p →ₐ[ℚ] L)

/-- The actual continuous cohomological family at the specified coefficient label. -/
def primePlusCohomologicalFamily :
    Scheme.EtaleLocalSystem (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p)) L :=
  labelledCohomologicalTateEtaleLocalSystem (realCyclotomicField p)
    (primePlusFamily p hp) ℓ L (realCyclotomicField p)
    (primePlusRealMultiplication p hp) hL σ

/-- The arithmetic fibre identifies with the native fixed-label dual Tate action. -/
def primePlusCohomologicalFamilyArithmeticEquiv :
    ((primePlusCohomologicalFamily p hp ℓ L hL σ).arithmeticRepresentation
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
    ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      σ).toRepresentation.dual) := by
  unfold primePlusCohomologicalFamily primePlusFiber primePlusFiberRealMultiplication
    parameterFiber
  with_reducible
    exact endomorphismLabelledCohomologicalArithmeticEquiv
      (realCyclotomicField p) (primePlusFamily p hp) ℓ L (realCyclotomicField p)
      (primePlusRealMultiplication p hp) hL
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) σ

/-- The actual cohomological fibre has dimension two at every fixed RM label. -/
theorem finrank_primePlusCohomologicalFamily :
    Module.finrank L ((primePlusCohomologicalFamily p hp ℓ L hL σ).toFunctor.obj
      (Scheme.etaleFiberPoint (realCyclotomicField p) _
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))) = 2 := by
  have e := primePlusCohomologicalFamilyArithmeticEquiv p hp ξ ℓ L hL σ
  refine e.toLinearEquiv.finrank_eq.trans ?_
  exact (Subspace.dual_finrank_eq (K := L) (V :=
    (endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
      ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
      σ).toSubmodule)).trans (finrank_primePlusFiberLabelledTate p hp ξ ℓ L hL σ)

/-- The selected labelled cohomological action in two continuous coordinates. -/
def primePlusCohomologicalAction :
    Representation L (AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) (Fin 2 → L) :=
  (primePlusCohomologicalFamily p hp ℓ L hL σ).arithmeticRepresentationOfFinrankEq
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) 2
    (finrank_primePlusCohomologicalFamily p hp ξ ℓ L hL σ)

/-- The two-coordinate action is equivariantly the original dual Tate factor. -/
def primePlusCohomologicalActionEquiv :
    (primePlusCohomologicalAction p hp ξ ℓ L hL σ).Equiv
      ((endomorphismLabelledTate (realCyclotomicField p) (primePlusFiber p hp ξ)
        ℓ (realCyclotomicField p) L hL (primePlusFiberRealMultiplication p hp ξ)
        σ).toRepresentation.dual) :=
  ((primePlusCohomologicalFamily p hp ℓ L hL σ).arithmeticEquivOfFinrankEq
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) 2
    (finrank_primePlusCohomologicalFamily p hp ξ ℓ L hL σ)).symm.trans
      (primePlusCohomologicalFamilyArithmeticEquiv p hp ξ ℓ L hL σ)

/-- Coordinate choice on the arithmetic fibre of the selected cohomological
family, before identifying its native dual Tate model. -/
def primePlusCohomologicalFamilyArithmeticEquivAction :
    ((primePlusCohomologicalFamily p hp ℓ L hL σ).arithmeticRepresentation
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
      (primePlusCohomologicalAction p hp ξ ℓ L hL σ) :=
  (primePlusCohomologicalFamily p hp ℓ L hL σ).arithmeticEquivOfFinrankEq
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) 2
    (finrank_primePlusCohomologicalFamily p hp ξ ℓ L hL σ)

/-- Continuity of every matrix entry comes from the actual local-system topology. -/
theorem continuous_primePlusCohomologicalAction_entry (i j : Fin 2) :
    Continuous (fun g => primePlusCohomologicalAction p hp ξ ℓ L hL σ g (Pi.single j 1) i) :=
  (primePlusCohomologicalFamily p hp ℓ L hL σ).continuous_arithmeticRepresentationOfFinrankEq_entry
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) 2
    (finrank_primePlusCohomologicalFamily p hp ξ ℓ L hL σ) i j

end HilbertModularity.Hypergeometric

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme

/-- At a chosen coefficient prime, the plus cohomological family is the dual
of its exponent-labelled Tate family. The coefficient embedding is the same
map on both sides. -/
theorem primePlusCohomologicalFamily_eq_labelledTateDual
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L] :
    primePlusCohomologicalFamily p hp p L
      (splits_minpoly_above_coefficientPrime p E w L hE)
      (coefficientEmbeddingAbovePrime p m hm E
        ((IntermediateField.le_normalClosure (realCyclotomicField p)).trans hE) w L) =
      (primePlusLabelledTateFamily p hp (realCyclotomicField p) m hm E hE w L).cohDual := by
  unfold primePlusCohomologicalFamily
    GroupScheme.labelledCohomologicalTateEtaleLocalSystem
  rw [primePlusLabelledTateFamily_eq_labelled]
  rfl

end HilbertModularity.Hypergeometric
