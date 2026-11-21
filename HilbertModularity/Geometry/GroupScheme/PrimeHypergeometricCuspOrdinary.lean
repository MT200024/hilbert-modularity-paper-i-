/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricOrdinary
public import HilbertModularity.RepresentationTheory.FiniteCharacterTwist
public import HilbertModularity.RepresentationTheory.Quotient
public import HilbertModularity.Geometry.ProjectiveInvolution

/-! # Ordinary quotients at the complementary cusp

The manuscript transfers the deep-cusp quotient from `t = 0` to `t = 1`
using its parameter involution and a finite-order arithmetic twist. The
comparison between the *selected plus Jacobian fibres* is an explicit input:
pullback base change alone does not identify a family with its pullback.
-/

public noncomputable section

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E G V W : Type*} [Field K] [Field E] [Algebra ℚ_[p] K]
  [Algebra ℚ_[p] E] [Algebra K ℂ_[p]] [IsScalarTower ℚ_[p] K ℂ_[p]]
  [Group G] [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
  [IsScalarTower ℚ_[p] E V] [AddCommGroup W] [Module E W]
  [Module ℚ_[p] W] [IsScalarTower ℚ_[p] E W]
  (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hK : ∀ (g : G) (a : K), PadicComplex.galoisEquiv p (ι g)
    (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a)
  {ρ : Representation E G V} {τ : Representation E G W}

/-- A coefficient-linear intertwiner transports an actual rank-one quotient,
its canonical Hodge--Tate comparison, and every nonzero-weight period space. -/
theorem nonempty_weightZeroQuotient_equiv_iff (e : ρ.Equiv τ) :
    Nonempty (WeightZeroQuotient p ι hK ρ) ↔
      Nonempty (WeightZeroQuotient p ι hK τ) := by
  rw [nonempty_weightZeroQuotient_iff, nonempty_weightZeroQuotient_iff]
  constructor
  · rintro ⟨S, hdim, hcomp, hweights⟩
    let T := e.subrepresentationOrderIso S
    let eqv := (e.quotientCongr S).restrictScalars ℚ_[p]
    refine ⟨T, ?_, ?_, ?_⟩
    · exact (e.quotientCongr S).toLinearEquiv.finrank_eq.symm.trans hdim
    · exact (comparison_bijective_iff p ι hK eqv).mp hcomp
    · intro q hq
      exact (weightSpace_eq_bot_iff (ι := ι) eqv q).mp (hweights q hq)
  · rintro ⟨T, hdim, hcomp, hweights⟩
    obtain ⟨S, rfl⟩ := e.subrepresentationOrderIso.surjective T
    let eqv := (e.quotientCongr S).restrictScalars ℚ_[p]
    refine ⟨S, ?_, ?_, ?_⟩
    · exact (e.quotientCongr S).toLinearEquiv.finrank_eq.trans hdim
    · exact (comparison_bijective_iff p ι hK eqv).mpr hcomp
    · intro q hq
      exact (weightSpace_eq_bot_iff (ι := ι) eqv q).mpr (hweights q hq)

end HodgeTate

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The manuscript's `t = 1` ordinary transfer for the selected plus Jacobian.
The intertwiner is the precise arithmetic comparison required by
[TripathiGoswamiRevised, Lemma `involution` and Proposition `prime-deep-DO`].
Its construction from the geometric involution and the chosen RM descent is
still unsupplied. The finite-order twist and coefficient-label deductions are
proved here; no ordinary quotient is assumed at `ξ`. -/
theorem nonempty_primePlusOrdinaryQuotient_of_complement_twist
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p) ξ)).ρ).Equiv
      (primePlusDecompositionRepresentation p hp ξ).ρ))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (hordinary : Nonempty (PrimePlusOrdinaryQuotient p hp
      (ProjectiveLine.complementParameter (realCyclotomicField p) ξ) 1
      (Nat.coprime_one_left _))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let η := ProjectiveLine.complementParameter (realCyclotomicField p) ξ
  let ρ := (primePlusDecompositionRepresentation p hp η).ρ
  let τ := (primePlusDecompositionRepresentation p hp ξ).ρ
  let : Module ℚ_[p] (primePlusDecompositionRepresentation p hp η) :=
    primePlusDecompositionRationalModule p hp η
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (primePlusDecompositionRepresentation p hp η) :=
    primePlusDecompositionScalarTower p hp η
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p 0 1 (Nat.coprime_one_left _)
        (primePlusDecompositionRepresentation p hp η)) :=
    primePlusConjugateRationalModule p hp η 1 (Nat.coprime_one_left _)
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (Rep.localCoefficientConjugate p 0 1 (Nat.coprime_one_left _)
        (primePlusDecompositionRepresentation p hp η)) :=
    primePlusConjugateScalarTower p hp η 1 (Nat.coprime_one_left _)
  let : Module ℚ_[p] (primePlusDecompositionRepresentation p hp ξ) :=
    primePlusDecompositionRationalModule p hp ξ
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (primePlusDecompositionRepresentation p hp ξ) :=
    primePlusDecompositionScalarTower p hp ξ
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p 0 m hm
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateRationalModule p hp ξ m hm
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (Rep.localCoefficientConjugate p 0 m hm
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateScalarTower p hp ξ m hm
  have hη : Nonempty (HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0) ρ) :=
    (HodgeTate.nonempty_weightZeroQuotient_localCoefficientConjugate_iff p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0) 0 1
      (Nat.coprime_one_left _) (primePlusDecompositionRepresentation p hp η)).mpr
      hordinary
  have htwisted : Nonempty (HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0)
      ((Representation.ofCharacter χ).tprod ρ)) :=
    (HodgeTate.nonempty_weightZeroQuotient_iff p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0) _).mpr
      ((HodgeTate.finiteCharacterTensor_exists_weight_zero_quotient_iff p
        ρ χ hχ horder).mpr
        ((HodgeTate.nonempty_weightZeroQuotient_iff p
          (realPrimePowerLocalPeriodAction p 0)
          (realPrimePowerLocalPeriodAction_fixes p 0) ρ).mp hη))
  have hξ : Nonempty (HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0) τ) :=
    (HodgeTate.nonempty_weightZeroQuotient_equiv_iff p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0) e).mp htwisted
  exact (HodgeTate.nonempty_weightZeroQuotient_localCoefficientConjugate_iff p
    (realPrimePowerLocalPeriodAction p 0)
    (realPrimePowerLocalPeriodAction_fixes p 0) 0 m hm
    (primePlusDecompositionRepresentation p hp ξ)).mp hξ

end HilbertModularity.Hypergeometric
