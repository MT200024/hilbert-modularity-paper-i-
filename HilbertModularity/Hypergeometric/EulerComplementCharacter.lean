/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ChosenEulerComplement
public import HilbertModularity.Hypergeometric.QuadraticCoefficientDescent
public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter
public import HilbertModularity.RepresentationTheory.FiniteCharacterRamification

/-! # A rational algebraic complement character for the selected Euler fibres

A quadratic comparison takes rational sign values. Its one algebraic character
is chosen before all parameters, and recovers the comparison under the original
coefficient map without extending or relabelling that coefficient field.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

variable (N m p : ℕ) [NeZero N] [Fact p.Prime]
  (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion (cyclotomicField N)) L]
  [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField N)) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]

/-- A single rational-valued finite algebraic character compares every pair
of complementary fibres of the actual effective Euler realization. The
coefficient prime and field are fixed before the character; this theorem does
not yet assert that the same selected character works at other coefficient places. -/
theorem exists_algebraic_character_chosenEffectiveEuler_complement :
    let K := realCyclotomicField N
    ∃ χ : FiniteAlgebraicGaloisCharacter K ℚ,
      χ.toMonoidHom ^ 2 = 1 ∧
      ∀ ξ : ProjectiveLine.Parameter K,
        Nonempty (((Representation.ofCharacter
          ((Units.map (algebraMap ℚ L).toMonoidHom).comp χ.toMonoidHom)).tprod
          (chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L
            (coprimeEulerCoefficientMap N w L) ξ)).Equiv
              (chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L
                (coprimeEulerCoefficientMap N w L)
                (ProjectiveLine.complementParameter K ξ))) := by
  let K := realCyclotomicField N
  obtain ⟨ν, hνc, hνsq, _, hall⟩ :=
    exists_quadratic_character_chosenEffectiveEuler_complement N m p h3 hmPos hmN hcop w L
  let η := ν.quadraticRealization hνsq ℚ
  have hηsq : η ^ 2 = 1 := ν.quadraticRealization_sq hνsq ℚ
  have hηfin : (Set.range η).Finite := ν.quadraticRealization_finite_range hνsq ℚ
  have hηlc : IsLocallyConstant η := ν.quadraticRealization_isLocallyConstant hνsq hνc ℚ
  have hη : (Units.map (algebraMap ℚ L).toMonoidHom).comp η = ν :=
    (ν.map_quadraticRealization hνsq (algebraMap ℚ L)).trans
      (ν.quadraticRealization_self hνsq)
  obtain ⟨bad, hbad, hunram⟩ :=
    finiteCharacter_unramifiedOutsideFinite η hηlc.continuous hηfin
  let χ : FiniteAlgebraicGaloisCharacter K ℚ := {
    toMonoidHom := η
    finite_range := hηfin
    local_continuous := fun v => by
      change Continuous (fun g => algebraMap ℚ (v.adicCompletion ℚ) (η g : ℚ))
      exact (hηlc.comp (fun z : ℚˣ => algebraMap ℚ (v.adicCompletion ℚ) (z : ℚ))).continuous
    bad := bad
    bad_finite := hbad
    unramified := hunram }
  refine ⟨χ, hηsq, ?_⟩
  intro ξ
  change Nonempty (((Representation.ofCharacter
    ((Units.map (algebraMap ℚ L).toMonoidHom).comp η)).tprod _).Equiv _)
  rw [hη]
  exact hall ξ

end HilbertModularity.Hypergeometric
