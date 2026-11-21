/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudResidualOrdering
public import HilbertModularity.Hypergeometric.PrimePlusLocalDecomposition
import HilbertModularity.NumberTheory.CyclotomicEmbeddings
import HilbertModularity.RepresentationTheory.SpecifiedFiniteTwistQuotient

/-! # The native local ordinary row at a deep zero cusp

The label-one coefficient automorphism is the identity, so the native local
Tate action can be compared linearly with the chosen Raynaud ordinary basis.
The selected upper and lower residual rows are proved separately in
`PrimePlusRaynaudResidualOrdering`.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusDecompositionRationalModule
  primePlusDecompositionScalarTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

private theorem cyclotomicPowerAutomorphism_one_eq_refl
    (N : ℕ) [NeZero N] :
    powerAutomorphism N 1 (Nat.coprime_one_left N) = AlgEquiv.refl := by
  have h : (powerAutomorphism N 1 (Nat.coprime_one_left N)).toAlgHom =
      (AlgEquiv.refl : cyclotomicField N ≃ₐ[ℚ] cyclotomicField N).toAlgHom := by
    apply ((root_isPrimitiveRoot N).powerBasis ℚ).algHom_ext
    simp
  apply AlgEquiv.ext
  intro x
  exact AlgHom.congr_fun h x

private theorem realPowerAutomorphism_one_eq_refl
    (N : ℕ) [NeZero N] :
    realPowerAutomorphism N 1 (Nat.coprime_one_left N) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change (powerAutomorphism N 1 (Nat.coprime_one_left N)
      (IntermediateField.inclusion (realCyclotomicField_le N) x) : Qbar) = (x : Qbar)
  rw [cyclotomicPowerAutomorphism_one_eq_refl N]
  rfl

/-- The first local RM coefficient label is literally the identity on the
chosen completion. The proof uses the pinned mathlib
`Algebra.TensorProduct.congr_refl` through the completion tensor model. -/
theorem realPrimePowerCompletionAutomorphism_one_eq_refl
    (p : ℕ) [Fact p.Prime] :
    realPrimePowerCompletionAutomorphism p 0 1
      (Nat.coprime_one_left _) = AlgEquiv.refl := by
  unfold realPrimePowerCompletionAutomorphism
  rw [realPowerAutomorphism_one_eq_refl]
  unfold NumberField.padicCompletionAutomorphism
  rw [Algebra.TensorProduct.congr_refl]
  apply AlgEquiv.ext
  intro x
  simp

private def scalarConjugateReflRepEquiv
    {F G : Type*} [Field F] [Group G] (V : Rep F G) :
    V.ρ.Equiv (Rep.scalarConjugate (RingEquiv.refl F) V).ρ := by
  let e := Rep.scalarConjugateEquiv (RingEquiv.refl F) V
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro v
  exact Rep.scalarConjugateEquiv_apply_action (RingEquiv.refl F) V g v

/-- At label one, coefficient conjugation leaves the same selected local
Tate representation. The equivalence is the genuine scalar-conjugation map
with identity coefficient automorphism. -/
def primePlusLabelOneDecompositionEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    (primePlusDecompositionRepresentation p hp ξ).ρ.Equiv
      (primePlusDecompositionScalarConjugate p hp ξ 1
        (Nat.coprime_one_left _)).ρ := by
  let V := primePlusDecompositionRepresentation p hp ξ
  have hσ : (realPrimePowerCompletionAutomorphism p 0 1
      (Nat.coprime_one_left _)).toRingEquiv =
        RingEquiv.refl (RealPrimePowerCompletion p 0) :=
    congrArg AlgEquiv.toRingEquiv (realPrimePowerCompletionAutomorphism_one_eq_refl p)
  change V.ρ.Equiv
    (Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p 0 1
      (Nat.coprime_one_left _)).toRingEquiv V).ρ
  rw [hσ]
  exact scalarConjugateReflRepEquiv V

/-- A specified native quotient with character `χ` gives one label-one
normalized ordinary basis with that same lower character. -/
theorem exists_primePlusLabelOneNormalizedData_with_character
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ)
    (W : HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0)
      (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hact : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionRepresentation p hp ξ) ⧸
        W.kernel.toSubmodule),
      (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v =
          (χ g : RealPrimePowerCompletion p 0) • v) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp ξ 1
        (Nat.coprime_one_left _),
      d.lowerCharacter = χ := by
  obtain ⟨W₁, h₁⟩ := HodgeTate.exists_weightZeroQuotient_equiv_with_character p
    (realPrimePowerLocalPeriodAction p 0)
    (realPrimePowerLocalPeriodAction_fixes p 0)
    (primePlusLabelOneDecompositionEquiv p hp ξ) χ W hact
  change PrimePlusOrdinaryQuotient p hp ξ 1 (Nat.coprime_one_left _) at W₁
  let d := W₁.normalizedData p hp ξ 1 (Nat.coprime_one_left _)
  refine ⟨d, d.lowerCharacter_eq_of_sourceQuotient_character p hp ξ χ ?_⟩
  have hsource : d.sourceQuotient = W₁ :=
    W₁.normalizedData_sourceQuotient p hp ξ 1 (Nat.coprime_one_left _)
  rw [hsource]
  exact h₁

/-- An operator comparison whose coefficient map is the identity identifies
the selected global Tate coordinates with their native local realization.
The identity requirement pins the same RM label; it is supplied by the
canonical native comparison, not by the ordinary quotient. -/
def primePlusNativeComparisonLocalEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)) :
    (primePlusTateFieldCoordinateAction p hp ξ β).Equiv
      (primePlusLocalTateRepresentation p hp ξ).ρ := by
  have e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0)
        (RealPrimePowerCompletion p 0) :=
          (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
        (RealPrimePowerCompletion p 0)).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (RealPrimePowerCompletion p 0)) := by
    rw [← hmap]
    exact C.actionEquiv
  exact primePlusTateFieldCoordinateNativeEquiv p hp ξ β
    C.integralEmbedding e

private def representationActionLinearEquiv
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (s : G) : V ≃ₗ[F] V where
  toFun := ρ s
  invFun := ρ s⁻¹
  left_inv v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' v w := map_add (ρ s) v w
  map_smul' a v := map_smul (ρ s) a v

private theorem representationEquiv_conjugatedIntertwines
    {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (ρ : Representation F G V) (τ : Representation F G W)
    (E : ρ.Equiv τ) (σ g : G) (v : V) :
    E (ρ σ (ρ g v)) = τ (σ * g * σ⁻¹) (E (ρ σ v)) := by
  have hconj : ρ (σ * g * σ⁻¹) (ρ σ v) = ρ σ (ρ g v) := by
    calc
      _ = ρ ((σ * g * σ⁻¹) * σ) v := by
        simp only [map_mul, Module.End.mul_apply]
      _ = ρ (σ * g) v := by
        congr 1
        group
      _ = _ := by rw [map_mul, Module.End.mul_apply]
  have h := LinearMap.congr_fun
    (E.toIntertwiningMap.isIntertwining' (σ * g * σ⁻¹)) (ρ σ v)
  change E (ρ (σ * g * σ⁻¹) (ρ σ v)) =
    τ (σ * g * σ⁻¹) (E (ρ σ v)) at h
  exact (congrArg E hconj.symm).trans h

def conjugatedRepresentationCoordinateEquiv
    {F G H V W U : Type*} [Field F] [Group G] [Group H]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    (ρ : Representation F G V) (τ : Representation F G W)
    (r : H →* G) (η : Representation F H U)
    (E : ρ.Equiv τ) (B : Representation.Equiv (τ.comp r) η) (σ : G) :
    V ≃ₗ[F] U :=
  (representationActionLinearEquiv ρ σ).trans
    (E.toLinearEquiv.trans B.toLinearEquiv)

theorem conjugatedRepresentationCoordinateEquiv_intertwines
    {F G H J V W U : Type*} [Field F] [Group G] [Group H] [Monoid J]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    (ρ : Representation F G V) (τ : Representation F G W)
    (r : H →* G) (η : Representation F H U)
    (E : ρ.Equiv τ) (B : Representation.Equiv (τ.comp r) η)
    (ι : J →* G) (δ : J →* H) (σ : G)
    (hδ : ∀ g, r (δ g) = σ * ι g * σ⁻¹)
    (g : J) (v : V) :
    let e := conjugatedRepresentationCoordinateEquiv ρ τ r η E B σ
    e (ρ (ι g) v) = η (δ g) (e v) := by
  have hE := representationEquiv_conjugatedIntertwines ρ τ E σ (ι g) v
  rw [← hδ g] at hE
  have hB := LinearMap.congr_fun
    (B.toIntertwiningMap.isIntertwining' (δ g)) (E (ρ σ v))
  change B (τ (r (δ g)) (E (ρ σ v))) =
    η (δ g) (B (E (ρ σ v))) at hB
  change B (E (ρ σ (ρ (ι g) v))) =
    η (δ g) (B (E (ρ σ v)))
  exact (congrArg B hE).trans hB

/-- The label-one Raynaud basis is an equivariant coordinate system for the
actual selected local Tate representation. -/
def primePlusLabelOneRaynaudCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ 1
      (Nat.coprime_one_left _)) :
    (primePlusDecompositionRepresentation p hp ξ).ρ.Equiv
      (d.coordinateRepresentation p hp ξ) :=
  (primePlusLabelOneDecompositionEquiv p hp ξ).trans
    (d.coordinateEquiv p hp ξ)

/-- Native global coordinates, transported across the chosen algebraic-prime
conjugation and the label-one ordinary basis. This is a linear equivalence
on the same completed RM field. -/
def primePlusRaynaudLabelOneLocalEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ 1
      (Nat.coprime_one_left _))
    (σ : AbsoluteGalois (realCyclotomicField p)) :
    (Fin 2 → RealPrimePowerCompletion p 0) ≃ₗ[RealPrimePowerCompletion p 0]
      (Fin 2 → RealPrimePowerCompletion p 0) :=
  conjugatedRepresentationCoordinateEquiv
    (primePlusTateFieldCoordinateAction p hp ξ β)
    (primePlusLocalTateRepresentation p hp ξ).ρ
    (primePlusLocalGaloisRestriction p)
    (d.coordinateRepresentation p hp ξ)
    (primePlusNativeComparisonLocalEquiv p hp ξ β C hmap)
    (primePlusLabelOneRaynaudCoordinateEquiv p hp ξ d) σ

/-- The selected coordinate change is exactly the generic conjugated
representation equivalence with the actual native and Raynaud factors. -/
theorem primePlusRaynaudLabelOneLocalEquiv_eq_generic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ 1
      (Nat.coprime_one_left _))
    (σ : AbsoluteGalois (realCyclotomicField p)) :
    primePlusRaynaudLabelOneLocalEquiv p hp ξ β C hmap d σ =
      conjugatedRepresentationCoordinateEquiv
        (primePlusTateFieldCoordinateAction p hp ξ β)
        (primePlusLocalTateRepresentation p hp ξ).ρ
        (primePlusLocalGaloisRestriction p)
        (d.coordinateRepresentation p hp ξ)
        (primePlusNativeComparisonLocalEquiv p hp ξ β C hmap)
        (primePlusLabelOneRaynaudCoordinateEquiv p hp ξ d) σ := (rfl)


end HilbertModularity.Hypergeometric
