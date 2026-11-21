/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusSelectedChecklist
import HilbertModularity.RepresentationTheory.ScalarConjugationInvariants

/-! # Applying the native Tate determinant to the selected checklist

The comparison data below identify two realizations of the same selected
plus-Jacobian Tate action. They replace an assumed determinant equation in
the selected Skinner--Wiles checklist with the already proved native exact
determinant. The completion and action comparison itself remains open.
-/

public noncomputable section

open scoped NumberField ValuativeRel
open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms
  IsNonarchimedeanLocalField

attribute [local instance] HilbertModularity.Cyclotomic.realFieldAlgebra
  realPrimePowerCompletionPadicAlgebra realPrimePowerCompletionPadicTower

/-- Coefficient and operator comparison for the two completed realizations
of the SAME selected plus Jacobian. The equivalence intertwines all Galois
operators, while `integerCoefficients` fixes the native `ℤ_[p]` normalization.
These are construction obligations, not determinant or modularity premises. -/
structure PrimePlusNativeTateComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E]) where
  localMap : RealPrimePowerCompletion p 0 →ₐ[ℚ_[p]] E
  actionEquiv :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra (RealPrimePowerCompletion p 0) E := localMap.toAlgebra
    ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange E).Equiv
      ((primePlusIntegralTateRepresentation p hp ξ).baseChange E)
  integerCoefficients : ∀ z : ℤ_[p],
    algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E
      (TateModule.coefficientPrimeRingEquiv p
        (𝓞 (realCyclotomicField p))
        (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
        (realPrimeRamification_pos p (by omega))
        (span_realPrimeGenerator_pow p (by omega))
          (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
      algebraMap ℚ_[p] E (z : ℚ_[p])
  integralEmbedding :
    (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))) E) =
      ((𝒪[E]).subtype.comp β).toAlgebra

/-- The selected canonical-prime torsion and the comparison's transported
determinant determine one residual datum on the same integral Tate basis. -/
noncomputable def PrimePlusNativeTateComparison.selectedResidualData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E])) :
    SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β) :=
  primePlusNativeComparedTateResidualData p hp ξ β κ
    C.localMap C.actionEquiv C.integerCoefficients

/-- The fixed selected torsion line orders the native residual characters
with the trivial character in the second, ordinary-quotient position. -/
theorem PrimePlusNativeTateComparison.selectedResidualData_chi₂_eq_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E])) :
    (C.selectedResidualData p hp ξ β κ).chi₂ = 1 := by
  unfold PrimePlusNativeTateComparison.selectedResidualData
  exact primePlusNativeComparedTateResidualData_chi₂_eq_one
    p hp ξ β κ C.localMap C.actionEquiv C.integerCoefficients

/-- The selected native residual datum and a Raynaud ordinary basis with
trivial lower character have identical lower residual characters on any
specified decomposition map. Both sides use their actual integral lattices. -/
theorem PrimePlusNativeTateComparison.lowerResidual_eq_of_lowerOne
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (hlower : d.lowerCharacter = 1)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (g : primeDecompositionGroup Q) :
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
    (C.selectedResidualData p hp ξ β κ).chi₂
      (g : AbsoluteGalois (realCyclotomicField p)) := by
  calc
    _ = 1 := congrArg (fun f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0])ˣ => f (φ g))
      (d.reducedLowerCharacter_eq_one p hp ξ hlower)
    _ = _ := (congrArg
      (fun f : AbsoluteGalois (realCyclotomicField p) →*
        (𝒪[RealPrimePowerCompletion p 0] ⧸
          𝓂[RealPrimePowerCompletion p 0])ˣ => f (g : AbsoluteGalois _))
      (C.selectedResidualData_chi₂_eq_one p hp ξ β κ)).symm

/-- The selected global field-coordinate action has the native exact
cyclotomic determinant. This identifies the determinant of the same lattice
used to construct its residual datum. -/
theorem PrimePlusNativeTateComparison.selectedFieldCoordinate_det
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (g : AbsoluteGalois (realCyclotomicField p)) :
    LinearMap.det (primePlusTateFieldCoordinateAction p hp ξ β g) =
      algebraMap ℚ_[p] E
        ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]) := by
  let := primePlusIntegralTateModule p hp ξ
  let z : ℤ_[p] := Field.cyclotomicCharacter (realCyclotomicField p) p g
  calc
    LinearMap.det (primePlusTateFieldCoordinateAction p hp ξ β g) =
        LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) :=
      (primePlusTateFieldCoordinateEquiv p hp ξ β C.integralEmbedding).det_eq g |>.symm
    _ = algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) :=
      primePlusIntegralTate_det_of_nativeComparison p hp ξ E
        C.localMap C.actionEquiv C.integerCoefficients g
    _ = algebraMap ℚ_[p] E (z : ℚ_[p]) := C.integerCoefficients z

/-- The selected residual character ratio is the canonical-prime reduction
of the cyclotomic character. The fixed torsion point and native determinant
are taken on the same integral Tate lattice. -/
theorem PrimePlusNativeTateComparison.selectedResidualRatio
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E])) :
    residualRatio (C.selectedResidualData p hp ξ β κ) =
      (Units.map κ.toMonoidHom).comp
        (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  unfold PrimePlusNativeTateComparison.selectedResidualData
  exact primePlusNativeComparedTate_residualRatio p hp ξ β κ
    C.localMap C.actionEquiv C.integerCoefficients

/-- The native determinant, actual selected integral Tate basis, canonical
prime residual matrix, finite ramification, and real-place sign supply the
global Skinner--Wiles rows. Irreducibility and ordinary local comparisons
remain visible for the selected representation. See
[TripathiGoswamiRevised, Proposition `SW-checklist`]. -/
noncomputable def skinnerWilesWeightTwoInput_of_primePlusNativeComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [NormedField E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [ContinuousSMul ℚ_[p] E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (hirred : (primePlusTateFieldCoordinateAction p hp ξ β).IsIrreducible)
    (ι : AlgebraicClosure (realCyclotomicField p) →+* ℂ)
    (c : AbsoluteGalois (realCyclotomicField p)) (hc : c ^ 2 = 1)
    (hconj : ∀ x, ι (c x) = star (ι x))
    (D : SkinnerWilesResidualData (primePlusTateFieldCoordinateAction p hp ξ β))
    (hordinary : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      SkinnerWilesOrdinaryAt p
        (primePlusTateFieldCoordinateAction p hp ξ β) D Q) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ β) (cyclotomicField p) := by
  have hdet := primePlusIntegralTate_det_of_nativeComparison p hp ξ E
    C.localMap C.actionEquiv C.integerCoefficients
  exact skinnerWilesWeightTwoInput_of_primePlusSelectedTate p hp ξ E β
    C.integralEmbedding κ hdet C.integerCoefficients hirred ι c hc hconj
    D hordinary

/-- The native determinant and selected fixed torsion point provide the
actual residual datum for the selected plus Jacobian's checklist. The
remaining local condition refers to that very datum; it is not an arbitrary
independently chosen residual representation. -/
noncomputable def skinnerWilesWeightTwoInput_of_primePlusNativeResidualData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [NormedField E] [ValuativeRel E] [Algebra ℚ_[p] E]
    [ContinuousSMul ℚ_[p] E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (C : PrimePlusNativeTateComparison p hp ξ E β)
    (hirred : (primePlusTateFieldCoordinateAction p hp ξ β).IsIrreducible)
    (ι : AlgebraicClosure (realCyclotomicField p) →+* ℂ)
    (c : AbsoluteGalois (realCyclotomicField p)) (hc : c ^ 2 = 1)
    (hconj : ∀ x, ι (c x) = star (ι x))
    (hordinary : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      SkinnerWilesOrdinaryAt p
        (primePlusTateFieldCoordinateAction p hp ξ β)
        (C.selectedResidualData p hp ξ β κ) Q) :
    SkinnerWilesWeightTwoInput p
      (primePlusTateFieldCoordinateAction p hp ξ β) (cyclotomicField p) :=
  skinnerWilesWeightTwoInput_of_primePlusNativeComparison p hp ξ E β κ C
    hirred ι c hc hconj (C.selectedResidualData p hp ξ β κ) hordinary

end HilbertModularity.Hypergeometric
