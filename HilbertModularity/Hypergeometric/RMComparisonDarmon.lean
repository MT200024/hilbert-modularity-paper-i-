/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonSpecialization
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomology

/-! # The uniform comparison with the chosen Darmon family

The RM local system in this comparison is the continuous cohomological dual of
the single scheme chosen by Darmon's construction. Its arithmetic fibres are
identified with the same labelled dual Tate factors by
`darmonCohomologicalFamilyArithmeticEquiv`. The effective hypergeometric
local system and its geometric comparison are separate inputs. -/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- A comparison at one rational fibre of the actual dual Darmon family and
one effective arithmetic local system propagates with the identical character
to every rational nonsingular fibre. This is the specialization deduction in
[TripathiGoswamiRevised, Theorem RMgeneral]. The generic geometric
equivalence and finite order of the character are separate prerequisites. -/
def darmonComparisonAllFibers
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ν : (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) →* Lˣ)
    (h : ((Representation.ofCharacter
      (ν.comp (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀))).tprod
        (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
          (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L))).Equiv
      (puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff)) :
    ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
      Representation.Equiv ((Representation.ofCharacter ν).tprod
        (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
          (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)))
        (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ F_eff) :=
  puncturedComparisonAllFibers (realCyclotomicField N) ξ₀
    (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)
    F_eff ν h

/-- The comparison at every fibre uses the cohomological dual of the
coefficient-labelled Tate factor of the single chosen Darmon scheme. The
labelled dual is kept explicit, so this cannot silently replace the
cohomological factor by the covariant Tate factor. -/
def darmonLabelledComparisonAllFibers
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ν : (AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) →* Lˣ)
    (h : ((Representation.ofCharacter
      (ν.comp (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀))).tprod
        (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
          (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L))).Equiv
      (puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Representation.Equiv ((Representation.ofCharacter ν).tprod
      (GroupScheme.labelledDualTateFactor (realCyclotomicField N)
        (GroupScheme.fiber (realCyclotomicField N) (darmonFamily N hN)
          (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ)).X p
        (realCyclotomicField N) L (splits_minpoly_above_coefficientPrime N E w L hE)
        (GroupScheme.fiberPointsAction (realCyclotomicField N)
          (AlgebraicClosure (realCyclotomicField N)) (darmonFamily N hN)
          (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ)
          (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
        (GroupScheme.fiberPointsAction_realized (realCyclotomicField N)
          (AlgebraicClosure (realCyclotomicField N)) (darmonFamily N hN)
          (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ)
          (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)))
      (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ F_eff) :=
  (Representation.characterTensorEquivCongr ν
    (darmonCohomologicalFamilyArithmeticEquiv (realCyclotomicField N)
      N hN p m hm E hE w L
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ)).symm).trans
    (darmonComparisonAllFibers N hN p m hm E hE w L ξ₀ F_eff ν h ξ)

end HilbertModularity.Hypergeometric
