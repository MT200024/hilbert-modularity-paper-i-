/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EffectiveEulerDarmonComparison
public import HilbertModularity.Hypergeometric.PrimePlusConductorSpectralCoordinates
public import HilbertModularity.Hypergeometric.PrimePlusConductorWeightTwo
public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist
public import HilbertModularity.Geometry.GroupScheme.PrimePlusCanonicalNativeComparison
public import HilbertModularity.NumberTheory.HilbertModularForms.IntegralFiniteCharacter
public import HilbertModularity.RepresentationTheory.IntegralCharacterTwist
public import HilbertModularity.RepresentationTheory.DualLattice
public import HilbertModularity.RepresentationTheory.DualSubquotient

/-! # Residual factors of the chosen effective Euler action

The integral coordinates below belong to the same selected plus Jacobian as
the arithmetic Euler comparison. Its dual lattice and the finite comparison
character will be transported to the actual chosen Euler fibre.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel TensorProduct

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularForms

attribute [local instance] Ideal.Quotient.field

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (m : ℕ) (hm : m.Coprime p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local instance chosenResidualNormedField : NormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNormedField p
local instance chosenResidualNontriviallyNormedField :
    NontriviallyNormedField (FullConductorCompletion p) :=
  fullConductorCanonicalNontriviallyNormedField p
local instance chosenResidualNormedAlgebra :
    NormedAlgebra ℚ_[p] (FullConductorCompletion p) :=
  fullConductorCanonicalNormedAlgebra p
local instance chosenResidualCompleteSpace : CompleteSpace (FullConductorCompletion p) :=
  inferInstance
local instance chosenResidualLocalField :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- The exponent-labelled map on the actual completed real-multiplication
integers, with codomain the conductor completion's valuation integers. -/
def chosenConductorPlusIntegralCoefficientMap :
    AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[FullConductorCompletion p] :=
  primePlusExtendedNativeIntegerMap p hp
    (chosenConductorNativeMap p m hm)
    (continuous_chosenConductorNativeMap p m hm)

/-- The selected plus Jacobian's integral rank-two action in the same Tate
basis used by its conductor-field coordinate action. -/
def chosenConductorPlusIntegralAction :
    Representation (𝒪[FullConductorCompletion p])
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → 𝒪[FullConductorCompletion p]) :=
  primePlusIntegralTateCoordinateAction p hp ξ
    (chosenConductorPlusIntegralCoefficientMap p hp m hm)

/-- The selected Jacobian's canonical native residual datum, before applying
the exponent-labelled conductor coefficient map. -/
def chosenPrimePlusNativeResidualData :
    letI := primePlusCanonicalNativeAlgebra p hp
    SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom) := by
  letI := primePlusCanonicalNativeAlgebra p hp
  letI := primePlusCanonicalNative_isFractionRing p hp
  exact (primePlusCanonicalNativeTateComparison p hp ξ).selectedResidualData p hp ξ
    (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
    (primePlusCanonicalNativeResidueEquiv p hp)

/-- The selected plus action has residual characters on this exact integral
coordinate lattice, for every nonsingular fibre and every exponent label. -/
def chosenConductorPlusMappedResidualData :
    letI := primePlusCanonicalNativeAlgebra p hp
    SkinnerWilesResidualData
      ((primePlusTateFieldCoordinateAction p hp ξ
        (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom).mapCoefficients
          (chosenConductorNativeMap p m hm).toRingHom) := by
  letI := primePlusCanonicalNativeAlgebra p hp
  exact SkinnerWilesResidualData.mapLocalCoefficients
    (chosenPrimePlusNativeResidualData p hp ξ)
    (chosenConductorNativeMap p m hm).toRingHom
    (chosenConductorNativeIntegerResidueComparison p m hm)

/-- The mapped datum lives on the exact exponent-labelled coordinate action. -/
def chosenConductorPlusResidualData :
    SkinnerWilesResidualData (chosenConductorPlusCoordinateAction p hp m hm ξ) :=
  (chosenConductorPlusCoordinateAction_eq_mapNative p hp m hm ξ).symm ▸
    chosenConductorPlusMappedResidualData p hp m hm ξ

/-- The mod-`p` cyclotomic character in the residue field of the chosen
conductor coefficient place, using the actual exponent-labelled integer map. -/
def chosenConductorResidualCyclotomicCharacter :
    AbsoluteGalois (realCyclotomicField p) →*
      (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p])ˣ :=
  (Units.map (chosenConductorNativeIntegerResidueComparison p m hm).residueMap.toMonoidHom).comp
    ((Units.map (primePlusCanonicalNativeResidueEquiv p hp).toMonoidHom).comp
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega)))

private theorem residualData_chi₂_transportAction
    {E : Type*} [Field E] [ValuativeRel E]
    {ρ σ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) (h : ρ = σ) :
    (h ▸ D).chi₂ = D.chi₂ := by
  cases h
  rfl

/-- The native residual datum retains the fixed canonical-prime torsion
line in the second character position. -/
theorem chosenPrimePlusNativeResidualData_chi₂_eq_one :
    letI := primePlusCanonicalNativeAlgebra p hp
    (chosenPrimePlusNativeResidualData p hp ξ).chi₂ = 1 := by
  let := primePlusCanonicalNativeAlgebra p hp
  let := primePlusCanonicalNative_isFractionRing p hp
  exact (primePlusCanonicalNativeTateComparison p hp ξ).selectedResidualData_chi₂_eq_one
    p hp ξ (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
    (primePlusCanonicalNativeResidueEquiv p hp)

/-- The mapped residual datum has the same fixed-character ordering. -/
theorem chosenConductorPlusMappedResidualData_chi₂_eq_one :
    letI := primePlusCanonicalNativeAlgebra p hp
    (chosenConductorPlusMappedResidualData p hp m hm ξ).chi₂ = 1 := by
  let := primePlusCanonicalNativeAlgebra p hp
  let D := chosenPrimePlusNativeResidualData p hp ξ
  let f := (chosenConductorNativeMap p m hm).toRingHom
  let B := chosenConductorNativeIntegerResidueComparison p m hm
  have hnative : D.chi₂ = 1 :=
    chosenPrimePlusNativeResidualData_chi₂_eq_one p hp ξ
  calc
    (chosenConductorPlusMappedResidualData p hp m hm ξ).chi₂ =
        (SkinnerWilesResidualData.mapLocalCoefficients D f B).chi₂ := (rfl)
    _ = (Units.map B.residueMap.toMonoidHom).comp D.chi₂ :=
      SkinnerWilesResidualData.mapLocalCoefficients_chi₂ D f B
    _ = 1 := by rw [hnative]; simp

/-- The selected integral residual datum keeps its fixed torsion line in the
second character position after the actual exponent-labelled map. -/
theorem chosenConductorPlusResidualData_chi₂_eq_one :
    (chosenConductorPlusResidualData p hp m hm ξ).chi₂ = 1 := by
  let := primePlusCanonicalNativeAlgebra p hp
  rw [chosenConductorPlusResidualData,
    residualData_chi₂_transportAction p]
  exact chosenConductorPlusMappedResidualData_chi₂_eq_one p hp m hm ξ

/-- The native residual ratio is the reduction of the actual cyclotomic
character at the canonical real coefficient prime. -/
theorem chosenPrimePlusNativeResidualData_ratio :
    letI := primePlusCanonicalNativeAlgebra p hp
    residualRatio (chosenPrimePlusNativeResidualData p hp ξ) =
      (Units.map (primePlusCanonicalNativeResidueEquiv p hp).toMonoidHom).comp
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p
          (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) hp))) := by
  let := primePlusCanonicalNativeAlgebra p hp
  let := primePlusCanonicalNative_isFractionRing p hp
  exact (primePlusCanonicalNativeTateComparison p hp ξ).selectedResidualRatio
    p hp ξ (primePlusCanonicalNativeIntegerEquiv p hp).toRingHom
    (primePlusCanonicalNativeResidueEquiv p hp)

/-- The exponent-labelled coefficient map carries the native cyclotomic
ratio to the chosen conductor residue field. -/
theorem chosenConductorPlusMappedResidualData_ratio :
    letI := primePlusCanonicalNativeAlgebra p hp
    residualRatio (chosenConductorPlusMappedResidualData p hp m hm ξ) =
      chosenConductorResidualCyclotomicCharacter p hp m hm := by
  let := primePlusCanonicalNativeAlgebra p hp
  let D := chosenPrimePlusNativeResidualData p hp ξ
  let f := (chosenConductorNativeMap p m hm).toRingHom
  let B := chosenConductorNativeIntegerResidueComparison p m hm
  have hnative : residualRatio D =
      (Units.map (primePlusCanonicalNativeResidueEquiv p hp).toMonoidHom).comp
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p
          (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) hp))) :=
    chosenPrimePlusNativeResidualData_ratio p hp ξ
  apply MonoidHom.ext
  intro g
  calc
    residualRatio (chosenConductorPlusMappedResidualData p hp m hm ξ) g =
        Units.map B.residueMap.toMonoidHom (residualRatio D g) :=
      SkinnerWilesResidualData.residualRatio_mapLocalCoefficients D f B g
    _ = chosenConductorResidualCyclotomicCharacter p hp m hm g := by
      rw [hnative]
      rfl

/-- The selected residual ratio is precisely the cyclotomic character under
the same residue embedding used by the exponent-labelled integral action. -/
theorem chosenConductorPlusResidualData_ratio :
    residualRatio (chosenConductorPlusResidualData p hp m hm ξ) =
      chosenConductorResidualCyclotomicCharacter p hp m hm := by
  let := primePlusCanonicalNativeAlgebra p hp
  rw [chosenConductorPlusResidualData,
    SkinnerWilesResidualData.residualRatio_transportAction]
  exact chosenConductorPlusMappedResidualData_ratio p hp m hm ξ

/-- The residual datum's integral action is literally the selected Jacobian's
chosen Tate basis action, transported through the exponent-labelled integers. -/
theorem chosenConductorPlusResidualData_integralAction_eq :
    (chosenConductorPlusResidualData p hp m hm ξ).integralAction =
      chosenConductorPlusIntegralAction p hp m hm ξ := by
  let D := chosenConductorPlusResidualData p hp m hm ξ
  let β := chosenConductorPlusIntegralCoefficientMap p hp m hm
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrixAlgEquiv'.injective
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  have hcoord : chosenConductorPlusCoordinateAction p hp m hm ξ =
      primePlusTateFieldCoordinateAction p hp ξ β := by
    exact chosenConductorPlusCoordinateAction_eq p hp m hm ξ
  have h : ((D.integralAction g (Pi.single j 1) i : 𝒪[FullConductorCompletion p]) :
        FullConductorCompletion p) =
      ((chosenConductorPlusIntegralAction p hp m hm ξ g
        (Pi.single j 1) i : 𝒪[FullConductorCompletion p]) :
          FullConductorCompletion p) := by
    calc
      _ = chosenConductorPlusCoordinateAction p hp m hm ξ g (Pi.single j 1) i :=
        D.integral_spec g i j
      _ = primePlusTateFieldCoordinateAction p hp ξ β g (Pi.single j 1) i := by
        rw [hcoord]
      _ = _ :=
        (primePlusTateFieldCoordinateAction_integral_coeff p hp ξ β g i j).symm
  simpa only [LinearMap.toMatrixAlgEquiv'_apply] using h

/-- Rationalizing the selected integral Tate basis gives exactly the named
conductor-coordinate action, rather than an independently chosen model. -/
theorem chosenConductorPlusIntegralAction_mapCoefficients :
    letI : Algebra 𝒪[FullConductorCompletion p] (FullConductorCompletion p) :=
      (𝒪[FullConductorCompletion p]).subtype.toAlgebra
    (chosenConductorPlusIntegralAction p hp m hm ξ).mapCoefficients
      (algebraMap 𝒪[FullConductorCompletion p] (FullConductorCompletion p)) =
        chosenConductorPlusCoordinateAction p hp m hm ξ := by
  let : Algebra 𝒪[FullConductorCompletion p] (FullConductorCompletion p) :=
    (𝒪[FullConductorCompletion p]).subtype.toAlgebra
  let D := chosenConductorPlusResidualData p hp m hm ξ
  have hi : D.integralAction = chosenConductorPlusIntegralAction p hp m hm ξ :=
    chosenConductorPlusResidualData_integralAction_eq p hp m hm ξ
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrixAlgEquiv'.injective
  apply Matrix.ext
  intro i j
  have h := D.integral_spec g i j
  rw [hi] at h
  have hcoe (x : 𝒪[FullConductorCompletion p]) :
      algebraMap 𝒪[FullConductorCompletion p] (FullConductorCompletion p) x =
        (x : FullConductorCompletion p) := (rfl)
  simpa only [LinearMap.toMatrixAlgEquiv'_apply,
    Representation.mapCoefficients_apply_single, hcoe] using h

/-- Reduction of the actual selected plus Jacobian's integral conductor
coordinate action. This is an action on the actual residue-field module. -/
@[expose] def chosenConductorPlusReducedAction :
    letI := Ideal.Quotient.field (𝓂[FullConductorCompletion p])
    Representation (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p])
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → 𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) := by
  letI := Ideal.Quotient.field (𝓂[FullConductorCompletion p])
  exact (chosenConductorPlusIntegralAction p hp m hm ξ).mapCoefficients
    (Ideal.Quotient.mk (𝓂[FullConductorCompletion p]))

/-- In the actual selected full-conductor lattice the two covariant
residual characters are the reduced cyclotomic character and one. -/
theorem chosenConductorPlusResidualData_chi₁_eq_cyclotomic :
    (chosenConductorPlusResidualData p hp m hm ξ).chi₁ =
      chosenConductorResidualCyclotomicCharacter p hp m hm := by
  let D := chosenConductorPlusResidualData p hp m hm ξ
  have h₂ : D.chi₂ = 1 := chosenConductorPlusResidualData_chi₂_eq_one p hp m hm ξ
  have hr : residualRatio D = chosenConductorResidualCyclotomicCharacter p hp m hm :=
    chosenConductorPlusResidualData_ratio p hp m hm ξ
  apply MonoidHom.ext
  intro g
  have h := congrArg (fun f => f g) hr
  simpa only [residualRatio_apply, h₂, MonoidHom.one_apply, inv_one, mul_one] using h

/-- The selected reduced integral coordinates have exactly the mod-`p`
cyclotomic determinant, with the exponent label fixed throughout. -/
theorem chosenConductorPlusReduced_det
    (g : AbsoluteGalois (realCyclotomicField p)) :
    LinearMap.det (chosenConductorPlusReducedAction p hp m hm ξ g) =
      (chosenConductorResidualCyclotomicCharacter p hp m hm g :
        𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) := by
  let D := chosenConductorPlusResidualData p hp m hm ξ
  have hi : D.integralAction = chosenConductorPlusIntegralAction p hp m hm ξ :=
    chosenConductorPlusResidualData_integralAction_eq p hp m hm ξ
  have h₁ : D.chi₁ = chosenConductorResidualCyclotomicCharacter p hp m hm :=
    chosenConductorPlusResidualData_chi₁_eq_cyclotomic p hp m hm ξ
  have h₂ : D.chi₂ = 1 := chosenConductorPlusResidualData_chi₂_eq_one p hp m hm ξ
  rw [chosenConductorPlusReducedAction,
    Representation.det_mapCoefficients_commRing, ← hi, D.residual_det]
  simp only [h₁, h₂, MonoidHom.one_apply, Units.val_one, mul_one]

/-- The actual reduced integral Tate coordinates contain the specialization
of the selected Jacobian's nonzero rational canonical-prime torsion point. -/
theorem exists_chosenConductorPlusReduced_fixed :
    let k := 𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]
    ∃ v : Fin 2 → k, v ≠ 0 ∧
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        chosenConductorPlusReducedAction p hp m hm ξ g v = v := by
  let k := 𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]
  let β := chosenConductorPlusIntegralCoefficientMap p hp m hm
  let κ := fullConductorAdicResidueEquiv p hp
  let ρ₀ := chosenConductorPlusIntegralAction p hp m hm ξ
  let := primePlusIntegralTateModule p hp ξ
  let := primePlusKernelModule p hp ξ
  let := (AdicCompletion.evalOneₐ
    (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
  let b := primePlusKernelBasisOfResidualTate p hp ξ
    (primePlusResidualTateBasis p hp ξ)
  have hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      (LinearMap.toMatrix b b (primePlusKernelRepresentation p hp ξ g)).map
        κ.toRingHom =
      (LinearMap.toMatrix' (ρ₀ g)).map (Ideal.Quotient.mk (𝓂[FullConductorCompletion p])) := by
    intro g
    simpa only [ρ₀, chosenConductorPlusIntegralAction,
      primePlusIntegralTateCoordinateAction_apply] using
      (primePlusIntegralCoordinateAction_kernelMatrix p hp ξ β κ g)
  obtain ⟨v, hv, hfix⟩ :=
    exists_primePlusKernel_fixed_in_residualCoordinates p hp ξ ρ₀ κ b hmat
  refine ⟨v, hv, ?_⟩
  intro g
  have hmatrix : LinearMap.toMatrix' (chosenConductorPlusReducedAction p hp m hm ξ g) =
      (LinearMap.toMatrix' (ρ₀ g)).map (Ideal.Quotient.mk (𝓂[FullConductorCompletion p])) := by
    exact Representation.toMatrix_mapCoefficients
      (Ideal.Quotient.mk (𝓂[FullConductorCompletion p])) ρ₀ g
  rw [← LinearMap.toMatrix'_mulVec]
  rw [hmatrix]
  exact hfix g

/-- The actual nonzero fixed vector on the selected reduced integral Tate
coordinates, chosen once from the canonical-prime torsion point. -/
def chosenConductorPlusReducedFixedVector :
    Fin 2 → 𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p] :=
  Classical.choose (exists_chosenConductorPlusReduced_fixed p hp m hm ξ)

theorem chosenConductorPlusReducedFixedVector_ne_zero :
    chosenConductorPlusReducedFixedVector p hp m hm ξ ≠ 0 :=
  (Classical.choose_spec (exists_chosenConductorPlusReduced_fixed p hp m hm ξ)).1

theorem chosenConductorPlusReducedFixedVector_fixed
    (g : AbsoluteGalois (realCyclotomicField p)) :
    chosenConductorPlusReducedAction p hp m hm ξ g
      (chosenConductorPlusReducedFixedVector p hp m hm ξ) =
        chosenConductorPlusReducedFixedVector p hp m hm ξ :=
  (Classical.choose_spec (exists_chosenConductorPlusReduced_fixed p hp m hm ξ)).2 g

/-- The actual conductor residue field, relabelled by its canonical prime
field equivalence. No coefficient embedding or Galois action is changed. -/
def chosenConductorResidueEquivZMod :
    (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) ≃+* ZMod p :=
  (fullConductorAdicResidueEquiv p hp).symm.trans
    (realPrimeResidueEquiv p
      (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) hp)))

/-- The selected plus lattice's reduction, transported only along the
canonical residue-field equivalence to `ZMod p`. -/
def chosenConductorPlusReducedActionZMod :
    Representation (ZMod p) (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → ZMod p) :=
  (chosenConductorPlusReducedAction p hp m hm ξ).mapCoefficients
    (chosenConductorResidueEquivZMod p hp).toRingHom

/-- The same reduced cyclotomic character with values in `ZMod p`. -/
def chosenConductorResidualCyclotomicZMod :
    AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ :=
  (Units.map (chosenConductorResidueEquivZMod p hp).toMonoidHom).comp
    (chosenConductorResidualCyclotomicCharacter p hp m hm)

/-- Relabelling the selected fixed torsion point by the canonical residue
equivalence gives a nonzero fixed vector over `ZMod p`. -/
theorem exists_chosenConductorPlusReducedZMod_fixed :
    ∃ v : Fin 2 → ZMod p, v ≠ 0 ∧
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        chosenConductorPlusReducedActionZMod p hp m hm ξ g v = v := by
  let κ := chosenConductorResidueEquivZMod p hp
  let v := chosenConductorPlusReducedFixedVector p hp m hm ξ
  have hv : v ≠ 0 := chosenConductorPlusReducedFixedVector_ne_zero p hp m hm ξ
  have hfix := chosenConductorPlusReducedFixedVector_fixed p hp m hm ξ
  refine ⟨fun i => κ (v i), ?_, ?_⟩
  · intro hzero
    apply hv
    funext i
    apply κ.injective
    have hi := congrFun hzero i
    simpa only [Pi.zero_apply, map_zero] using hi
  · intro g
    let : Algebra (𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p])
        (ZMod p) := κ.toRingHom.toAlgebra
    have he := Representation.mapCoefficients_apply_map κ.toRingHom
      (chosenConductorPlusReducedAction p hp m hm ξ) g v
    have hvfix : chosenConductorPlusReducedAction p hp m hm ξ g v = v := hfix g
    simpa only [chosenConductorPlusReducedActionZMod, κ, hvfix,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using he

/-- A fixed vector in the actual selected Tate reduction over `ZMod p`. -/
def chosenConductorPlusReducedFixedVectorZMod : Fin 2 → ZMod p :=
  Classical.choose (exists_chosenConductorPlusReducedZMod_fixed p hp m hm ξ)

theorem chosenConductorPlusReducedFixedVectorZMod_ne_zero :
    chosenConductorPlusReducedFixedVectorZMod p hp m hm ξ ≠ 0 :=
  (Classical.choose_spec (exists_chosenConductorPlusReducedZMod_fixed p hp m hm ξ)).1

theorem chosenConductorPlusReducedFixedVectorZMod_fixed
    (g : AbsoluteGalois (realCyclotomicField p)) :
    chosenConductorPlusReducedActionZMod p hp m hm ξ g
      (chosenConductorPlusReducedFixedVectorZMod p hp m hm ξ) =
        chosenConductorPlusReducedFixedVectorZMod p hp m hm ξ :=
  (Classical.choose_spec (exists_chosenConductorPlusReducedZMod_fixed p hp m hm ξ)).2 g

/-- The relabelled reduction retains exactly the cyclotomic determinant. -/
theorem chosenConductorPlusReducedZMod_det
    (g : AbsoluteGalois (realCyclotomicField p)) :
    LinearMap.det (chosenConductorPlusReducedActionZMod p hp m hm ξ g) =
      (chosenConductorResidualCyclotomicZMod p hp m hm g : ZMod p) := by
  let κ := chosenConductorResidueEquivZMod p hp
  rw [chosenConductorPlusReducedActionZMod,
    Representation.det_mapCoefficients_commRing,
    chosenConductorPlusReduced_det p hp m hm ξ g]
  rfl

/-- The selected cohomological flag is the annihilator of the fixed line
inside the dual of the actual relabelled Tate reduction. -/
def chosenConductorPlusCohomologicalResidualFlagZMod :
    Subrepresentation (chosenConductorPlusReducedActionZMod p hp m hm ξ).dual :=
  ((chosenConductorPlusReducedActionZMod p hp m hm ξ).fixedLine
    (chosenConductorPlusReducedFixedVectorZMod p hp m hm ξ)
    (chosenConductorPlusReducedFixedVectorZMod_fixed p hp m hm ξ)).dualAnnihilator

/-- The selected cohomological residual line has inverse cyclotomic action. -/
theorem chosenConductorPlusCohomologicalResidualFlagZMod_character :
    Nonempty ((chosenConductorPlusCohomologicalResidualFlagZMod p hp m hm ξ).toRepresentation.Equiv
      (Representation.ofCharacter
        (chosenConductorResidualCyclotomicZMod p hp m hm)⁻¹)) := by
  let ρ := chosenConductorPlusReducedActionZMod p hp m hm ξ
  let v := chosenConductorPlusReducedFixedVectorZMod p hp m hm ξ
  let hfix := chosenConductorPlusReducedFixedVectorZMod_fixed p hp m hm ξ
  let S := ρ.fixedLine v hfix
  have hv : v ≠ 0 := chosenConductorPlusReducedFixedVectorZMod_ne_zero p hp m hm ξ
  have hdim : Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 := by simp
  let b := Module.finBasisOfFinrankEq (ZMod p) S.toSubmodule
    (ρ.finrank_fixedLine v hfix hv)
  let c := Module.finBasisOfFinrankEq (ZMod p) ((Fin 2 → ZMod p) ⧸ S.toSubmodule)
    (ρ.finrank_quotient_fixedLine v hfix hv hdim)
  have hdet : ρ.determinantCharacter =
      chosenConductorResidualCyclotomicZMod p hp m hm := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    exact chosenConductorPlusReducedZMod_det p hp m hm ξ g
  have e := S.dualAnnihilatorCharacterEquiv ρ.determinantCharacter
    (ρ.quotientFixedLineEquiv v hfix b c)
  rw [hdet] at e
  exact ⟨e⟩

/-- The quotient by that cohomological residual line is the trivial
character; together with the line theorem this is `1 ⊕ ε̄⁻¹`. -/
theorem chosenConductorPlusCohomologicalResidualFlagZMod_quotient :
    let ρ := chosenConductorPlusReducedActionZMod p hp m hm ξ
    let T := chosenConductorPlusCohomologicalResidualFlagZMod p hp m hm ξ
    Nonempty ((ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule).Equiv
      (Representation.ofCharacter
        (1 : AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ))) := by
  let ρ := chosenConductorPlusReducedActionZMod p hp m hm ξ
  let v := chosenConductorPlusReducedFixedVectorZMod p hp m hm ξ
  let hfix := chosenConductorPlusReducedFixedVectorZMod_fixed p hp m hm ξ
  let S := ρ.fixedLine v hfix
  have hv : v ≠ 0 := chosenConductorPlusReducedFixedVectorZMod_ne_zero p hp m hm ξ
  let b := Module.finBasisOfFinrankEq (ZMod p) S.toSubmodule
    (ρ.finrank_fixedLine v hfix hv)
  let e := S.quotientDualAnnihilatorCharacterEquiv
    (1 : AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ)
    (ρ.fixedLineEquiv v hfix b)
  have hone : (1 : AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ)⁻¹ = 1 := by
    ext g
    simp
  rw [hone] at e
  exact ⟨e⟩

/-- The selected cohomological reduction, after the canonical residue-field
relabeling, has the two actual irreducible factors one and inverse cyclotomic.
The source is the constructed fixed torsion line and exact determinant. -/
theorem exists_chosenConductorPlusCohomologicalResidualZMod_factors :
    let ρ := chosenConductorPlusReducedActionZMod p hp m hm ξ
    let ε := chosenConductorResidualCyclotomicZMod p hp m hm
    ∃ T : Subrepresentation ρ.dual,
      Nonempty ((T.toRepresentation.prod
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (1 : AbsoluteGalois
            (realCyclotomicField p) →* (ZMod p)ˣ)).prod
            (Representation.ofCharacter (ε⁻¹)))) := by
  let ρ := chosenConductorPlusReducedActionZMod p hp m hm ξ
  let ε := chosenConductorResidualCyclotomicZMod p hp m hm
  obtain ⟨v, hv, hfix⟩ := exists_chosenConductorPlusReducedZMod_fixed p hp m hm ξ
  have hdim : Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 := by simp
  have hdet : ρ.determinantCharacter = ε := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    exact chosenConductorPlusReducedZMod_det p hp m hm ξ g
  obtain ⟨T, _, _, _, _, _, he⟩ := ρ.exists_dual_fixedLine_factors hdim v hv hfix
  rw [hdet] at he
  exact ⟨T, he⟩

/-- The chosen effective Euler fibre is the finite-character twist of the
dual of this same selected plus Jacobian's conductor-coordinate action.
The comparison character and intertwiner are constructed from the actual
Euler and Darmon families, not supplied as hypotheses. -/
theorem exists_chosenEffectiveEuler_finiteTwistDualPlus
    (hmPos : 0 < m) (hmLt : m < p) :
    let L := FullConductorCompletion p
    ∃ ν : AbsoluteGalois (realCyclotomicField p) →* Lˣ,
      (Set.range ν).Finite ∧
      Nonempty (((chosenConductorPlusCoordinateAction p hp m hm ξ).dual.characterTwist ν).Equiv
        (chosenEffectiveEulerAction p m p (by omega) hmPos hmLt hm L
          (coprimeEulerCoefficientMap p (primeAboveConductor p) L) ξ)) := by
  let L := FullConductorCompletion p
  let C := chosenConductorPlusCoordinateAction p hp m hm ξ
  let T := darmonLabelledTateFamily (realCyclotomicField p) p (by omega) p m hm
    (cyclotomicField p) (realCyclotomicNormalClosure_le_full_of_neZero p)
    (primeAboveConductor p) L
  let D := darmonCohomologicalFamily (realCyclotomicField p) p (by omega) p m hm
    (cyclotomicField p) (realCyclotomicNormalClosure_le_full_of_neZero p)
    (primeAboveConductor p) L
  have eT : C.Equiv (T.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
    exact chosenConductorDarmonCoordinateEquiv_spectral p hp m hm ξ
  have eD : C.dual.Equiv (puncturedFiberArithmeticRepresentation
      (realCyclotomicField p) ξ D) := by
    change C.dual.Equiv (T.cohDual.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))
    rw [T.cohDual_arithmeticRepresentation]
    exact HilbertModularity.representationDualEquiv eT
  obtain ⟨ν, _, hνfin, χ, hχ, hground, hcomparison⟩ :=
    exists_algebraic_character_comparing_chosenEffectiveEuler
      p m p (by omega) hmPos hmLt hm (primeAboveConductor p) L
  let e := Classical.choice (hcomparison ξ)
  have e' : ((Representation.ofCharacter ν).tprod
      (puncturedFiberArithmeticRepresentation (realCyclotomicField p) ξ D)).Equiv
      (chosenEffectiveEulerAction p m p (by omega) hmPos hmLt hm L
        (coprimeEulerCoefficientMap p (primeAboveConductor p) L) ξ) := by
    simpa only [hχ] using e
  exact ⟨ν, hνfin,
    ⟨((Representation.characterTwistTensorEquiv C.dual ν).symm.trans
      (Representation.characterTensorEquivCongr ν eD)).trans e'⟩⟩

/-- One finite comparison character obtained from the actual selected
Euler–Darmon arithmetic comparison at this specialization. -/
def chosenEffectiveEulerResidualCharacter
    (hmPos : 0 < m) (hmLt : m < p) :
    AbsoluteGalois (realCyclotomicField p) →* (FullConductorCompletion p)ˣ :=
  Classical.choose
    (exists_chosenEffectiveEuler_finiteTwistDualPlus p hp m hm ξ hmPos hmLt)

theorem chosenEffectiveEulerResidualCharacter_finite
    (hmPos : 0 < m) (hmLt : m < p) :
    (Set.range (chosenEffectiveEulerResidualCharacter p hp m hm ξ hmPos hmLt)).Finite :=
  (Classical.choose_spec
    (exists_chosenEffectiveEuler_finiteTwistDualPlus p hp m hm ξ hmPos hmLt)).1

/-- The fixed character and the same selected plus Jacobian give the
arithmetic intertwiner for the actual effective Euler fibre. -/
def chosenEffectiveEulerResidualComparisonEquiv
    (hmPos : 0 < m) (hmLt : m < p) :
    ((chosenConductorPlusCoordinateAction p hp m hm ξ).dual.characterTwist
      (chosenEffectiveEulerResidualCharacter p hp m hm ξ hmPos hmLt)).Equiv
      (chosenEffectiveEulerAction p m p (by omega) hmPos hmLt hm
        (FullConductorCompletion p)
        (coprimeEulerCoefficientMap p (primeAboveConductor p)
          (FullConductorCompletion p)) ξ) :=
  Classical.choice
    (Classical.choose_spec
      (exists_chosenEffectiveEuler_finiteTwistDualPlus p hp m hm ξ hmPos hmLt)).2

/-- A finite character has integral unit values in the conductor valuation
ring, giving the actual scalar action on the selected dual Tate lattice. -/
def chosenEffectiveEulerIntegralCharacter
    (hmPos : 0 < m) (hmLt : m < p) :
    AbsoluteGalois (realCyclotomicField p) →*
      𝒪[FullConductorCompletion p]ˣ :=
  finiteCharacterIntegralLift
    (chosenEffectiveEulerResidualCharacter p hp m hm ξ hmPos hmLt)
    (chosenEffectiveEulerResidualCharacter_finite p hp m hm ξ hmPos hmLt)

/-- The stable rank-two integral model transported to the chosen effective
Euler action: dual of the selected plus Tate coordinates, then one integral
finite-character twist. -/
def chosenEffectiveEulerIntegralAction
    (hmPos : 0 < m) (hmLt : m < p) :
    Representation (𝒪[FullConductorCompletion p])
      (AbsoluteGalois (realCyclotomicField p))
      (Module.Dual (𝒪[FullConductorCompletion p])
        (Fin 2 → 𝒪[FullConductorCompletion p])) :=
  ((chosenConductorPlusIntegralAction p hp m hm ξ).dual).integralCharacterTwist
    (chosenEffectiveEulerIntegralCharacter p hp m hm ξ hmPos hmLt)

/-- Reduction of the conductor valuation integers followed by the fixed
canonical residue-field equivalence. -/
def chosenEulerResidueCoefficientMap :
    𝒪[FullConductorCompletion p] →+* ZMod p :=
  (chosenConductorResidueEquivZMod p hp).toRingHom.comp
    (Ideal.Quotient.mk (𝓂[FullConductorCompletion p]))

/-- The finite comparison character reduced on the same integral Euler
lattice and expressed in the canonical `ZMod p` residue field. -/
def chosenEffectiveEulerResidualCharacterZMod
    (hmPos : 0 < m) (hmLt : m < p) :
    AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ :=
  (Units.map (chosenEulerResidueCoefficientMap p hp).toMonoidHom).comp
    (chosenEffectiveEulerIntegralCharacter p hp m hm ξ hmPos hmLt)

/-- Reduction of the actual selected Euler integral model. Its carrier is
the scalar reduction of that free rank-two lattice, not a replacement copy
of the desired residual character sum. -/
def chosenEffectiveEulerIntegralReductionZMod
    (hmPos : 0 < m) (hmLt : m < p) :
    let L := FullConductorCompletion p
    letI : Algebra 𝒪[L] (ZMod p) :=
      (chosenEulerResidueCoefficientMap p hp).toAlgebra
    Representation (ZMod p) (AbsoluteGalois (realCyclotomicField p))
      ((ZMod p) ⊗[𝒪[L]] Module.Dual 𝒪[L] (Fin 2 → 𝒪[L])) := by
  letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
    (chosenEulerResidueCoefficientMap p hp).toAlgebra
  exact (chosenEffectiveEulerIntegralAction p hp m hm ξ hmPos hmLt).baseChange (ZMod p)

/-- The coefficient map used by the actual Euler lattice reduces the
selected plus Tate matrices first modulo the conductor maximal ideal and
then through the canonical residue equivalence. -/
theorem chosenConductorPlusIntegralAction_residueZMod :
    letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
      (chosenEulerResidueCoefficientMap p hp).toAlgebra
    (chosenConductorPlusIntegralAction p hp m hm ξ).mapCoefficients
      (algebraMap 𝒪[FullConductorCompletion p] (ZMod p)) =
        chosenConductorPlusReducedActionZMod p hp m hm ξ := by
  let : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
    (chosenEulerResidueCoefficientMap p hp).toAlgebra
  change (chosenConductorPlusIntegralAction p hp m hm ξ).mapCoefficients
      (chosenEulerResidueCoefficientMap p hp) =
    ((chosenConductorPlusIntegralAction p hp m hm ξ).mapCoefficients
      (Ideal.Quotient.mk (𝓂[FullConductorCompletion p]))).mapCoefficients
        (chosenConductorResidueEquivZMod p hp).toRingHom
  rw [Representation.mapCoefficients_comp]
  rfl

/-- The reduction of the constructed Euler lattice is exactly the finite
character twist of the reduced dual Tate action of the same selected plus
Jacobian. This is an equivariant comparison of actual reduced modules. -/
def chosenEffectiveEulerIntegralReductionZMod_equiv
    (hmPos : 0 < m) (hmLt : m < p) :
    letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
      (chosenEulerResidueCoefficientMap p hp).toAlgebra
    (chosenEffectiveEulerIntegralReductionZMod p hp m hm ξ hmPos hmLt).Equiv
      ((chosenConductorPlusReducedActionZMod p hp m hm ξ).dual.characterTwist
        (chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt)) := by
  letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
    (chosenEulerResidueCoefficientMap p hp).toAlgebra
  let ρ₀ := chosenConductorPlusIntegralAction p hp m hm ξ
  let u := chosenEffectiveEulerIntegralCharacter p hp m hm ξ hmPos hmLt
  let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
  have hu : ((Units.map (algebraMap 𝒪[FullConductorCompletion p] (ZMod p)).toMonoidHom
      ).comp u) = θ := by
    rfl
  have eTwist : (chosenEffectiveEulerIntegralReductionZMod p hp m hm ξ hmPos hmLt).Equiv
      ((ρ₀.dual.baseChange (ZMod p)).characterTwist θ) := by
    change ((ρ₀.dual.integralCharacterTwist u).baseChange (ZMod p)).Equiv
      ((ρ₀.dual.baseChange (ZMod p)).characterTwist θ)
    have e := Representation.integralCharacterTwistBaseChangeEquiv (ZMod p) ρ₀.dual u
    rw [hu] at e
    exact e
  let eDual := Representation.dualBaseChangeEquiv (ZMod p) ρ₀
  have eBase : (ρ₀.baseChange (ZMod p)).Equiv
      (chosenConductorPlusReducedActionZMod p hp m hm ξ) := by
    have e := Representation.baseChangeIntegralCoordinatesEquiv (K := ZMod p) ρ₀
    rw [chosenConductorPlusIntegralAction_residueZMod p hp m hm ξ] at e
    exact e
  let eCDual := HilbertModularity.representationDualEquiv eBase
  exact eTwist.trans ((characterTwistEquiv eDual θ).trans
    (characterTwistEquiv eCDual θ))

/-- Standard character-twist transport of the two proved factors on the
selected cohomological reduction. The selected Euler flag below is then the
pullback of this actual twisted flag. -/
private theorem exists_chosenEffectiveEulerTwistedResidualFactors
    (hmPos : 0 < m) (hmLt : m < p) :
    let σ := (chosenConductorPlusReducedActionZMod p hp m hm ξ).dual
    let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
    let ε := chosenConductorResidualCyclotomicZMod p hp m hm
    ∃ T : Subrepresentation (σ.characterTwist θ),
      Nonempty ((T.toRepresentation.prod
        ((σ.characterTwist θ).quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter θ).prod
            (Representation.ofCharacter (θ * ε⁻¹)))) := by
  let σ := (chosenConductorPlusReducedActionZMod p hp m hm ξ).dual
  let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
  let ε := chosenConductorResidualCyclotomicZMod p hp m hm
  have hcoh := exists_chosenConductorPlusCohomologicalResidualZMod_factors p hp m hm ξ
  obtain ⟨T, ⟨eT⟩⟩ := exists_characterTwist_factors σ θ
    (1 : AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ)
    ε⁻¹ hcoh
  refine ⟨T, ⟨?_⟩⟩
  have hθ : θ * (1 : AbsoluteGalois (realCyclotomicField p) →* (ZMod p)ˣ) = θ :=
    mul_one θ
  rw [hθ] at eT
  exact eT

/-- The actual residual Euler flag is the pullback of the selected
cohomological factors after their finite integral twist. -/
def chosenEffectiveEulerResidualFlag
    (hmPos : 0 < m) (hmLt : m < p) :
    letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
      (chosenEulerResidueCoefficientMap p hp).toAlgebra
    Subrepresentation (chosenEffectiveEulerIntegralReductionZMod p hp m hm ξ hmPos hmLt) := by
  letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
    (chosenEulerResidueCoefficientMap p hp).toAlgebra
  let e := chosenEffectiveEulerIntegralReductionZMod_equiv p hp m hm ξ hmPos hmLt
  exact e.symm.subrepresentationOrderIso
    (Classical.choose (exists_chosenEffectiveEulerTwistedResidualFactors
      p hp m hm ξ hmPos hmLt))

/-- The actual reduced Euler lattice has the two residual constituents
`θ` and `θ ε̄⁻¹` in its semisimple associated graded. The one `θ` is the
reduction of the finite integral comparison character above. -/
theorem chosenEffectiveEulerResidualFlag_factors
    (hmPos : 0 < m) (hmLt : m < p) :
    letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
      (chosenEulerResidueCoefficientMap p hp).toAlgebra
    let ρ := chosenEffectiveEulerIntegralReductionZMod p hp m hm ξ hmPos hmLt
    let S := chosenEffectiveEulerResidualFlag p hp m hm ξ hmPos hmLt
    let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
    let ε := chosenConductorResidualCyclotomicZMod p hp m hm
    Nonempty ((S.toRepresentation.prod
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
        ((Representation.ofCharacter θ).prod
          (Representation.ofCharacter (θ * ε⁻¹)))) := by
  let : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
    (chosenEulerResidueCoefficientMap p hp).toAlgebra
  let e := chosenEffectiveEulerIntegralReductionZMod_equiv p hp m hm ξ hmPos hmLt
  let h := exists_chosenEffectiveEulerTwistedResidualFactors p hp m hm ξ hmPos hmLt
  let T := Classical.choose h
  let eT := Classical.choice (Classical.choose_spec h)
  let eS := e.symm.associatedGradedCongr T
  exact ⟨eS.symm.trans eT⟩

/-- The residual comparison character still has finite image after
reduction, with one character used for both constituents. -/
theorem chosenEffectiveEulerResidualCharacterZMod_finite
    (hmPos : 0 < m) (hmLt : m < p) :
    (Set.range (chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt)).Finite :=
  Set.toFinite _

/-- The quotient of the two displayed effective residual characters is
exactly the reduced cyclotomic character in this ordering. -/
theorem chosenEffectiveEulerResidualFactors_ratio
    (hmPos : 0 < m) (hmLt : m < p) :
    let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
    let ε := chosenConductorResidualCyclotomicZMod p hp m hm
    θ * (θ * ε⁻¹)⁻¹ = ε := by
  let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
  let ε := chosenConductorResidualCyclotomicZMod p hp m hm
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_comm, mul_left_comm]

/-- Injective residue maps leave the kernel of the reduced cyclotomic
character unchanged. Thus the effective residual ratio cuts out the same
cyclotomic extension as the selected plus Jacobian's canonical-prime kernel. -/
theorem chosenConductorResidualCyclotomicZMod_eq_one_iff
    (g : AbsoluteGalois (realCyclotomicField p)) :
    chosenConductorResidualCyclotomicZMod p hp m hm g = 1 ↔
      AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega) g = 1 := by
  let κ := chosenConductorResidueEquivZMod p hp
  let κ₀ := primePlusCanonicalNativeResidueEquiv p hp
  let B := chosenConductorNativeIntegerResidueComparison p m hm
  let ε := AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
    (realCyclotomicField p) p (by omega)
  have hκ : Function.Injective (Units.map κ.toMonoidHom) := by
    intro a b hab
    apply Units.ext
    apply κ.injective
    exact congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hab
  have hκ₀ : Function.Injective (Units.map κ₀.toMonoidHom) := by
    intro a b hab
    apply Units.ext
    apply κ₀.injective
    exact congrArg (fun u : (𝒪[RealPrimePowerCompletion p 0] ⧸
      𝓂[RealPrimePowerCompletion p 0])ˣ =>
        (u : 𝒪[RealPrimePowerCompletion p 0] ⧸
          𝓂[RealPrimePowerCompletion p 0])) hab
  constructor
  · intro h
    change Units.map κ.toMonoidHom
      (Units.map B.residueMap.toMonoidHom (Units.map κ₀.toMonoidHom (ε g))) = 1 at h
    have h₁ : Units.map B.residueMap.toMonoidHom
        (Units.map κ₀.toMonoidHom (ε g)) = 1 := hκ (by simpa using h)
    have h₂ : Units.map κ₀.toMonoidHom (ε g) = 1 :=
      (B.unitsMap_injective (chosenConductorNativeMap p m hm).toRingHom)
        (by simpa using h₁)
    exact hκ₀ (by simpa using h₂)
  · intro h
    change Units.map κ.toMonoidHom
      (Units.map B.residueMap.toMonoidHom (Units.map κ₀.toMonoidHom (ε g))) = 1
    rw [h]
    simp

/-- The kernel field of the actual effective residual ratio is the real
base field with one primitive conductor root adjoined, hence the full
prime cyclotomic extension over the real base. -/
theorem chosenEffectiveEulerResidualRatio_fixedField
    (ζ : AlgebraicClosure (realCyclotomicField p))
    (hζ : IsPrimitiveRoot ζ p) :
    IntermediateField.fixedField
      (chosenConductorResidualCyclotomicZMod p hp m hm).ker =
        IntermediateField.adjoin (realCyclotomicField p) {ζ} := by
  have hker : (chosenConductorResidualCyclotomicZMod p hp m hm).ker =
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega)).ker := by
    ext g
    exact chosenConductorResidualCyclotomicZMod_eq_one_iff p hp m hm g
  rw [hker]
  exact fixedField_realPrimeResidualCharacter p (by omega) ζ hζ

/-- The integral carrier is finite free of rank two; twisting changes only
its action, not the underlying selected dual Tate lattice. -/
theorem chosenEffectiveEulerIntegralCarrier_free :
    Module.Free (𝒪[FullConductorCompletion p])
      (Module.Dual (𝒪[FullConductorCompletion p])
        (Fin 2 → 𝒪[FullConductorCompletion p])) := by
  infer_instance

theorem chosenEffectiveEulerIntegralCarrier_rank_two :
    Module.finrank (𝒪[FullConductorCompletion p])
      (Module.Dual (𝒪[FullConductorCompletion p])
        (Fin 2 → 𝒪[FullConductorCompletion p])) = 2 := by
  exact Module.finrank_eq_card_basis
    ((Pi.basisFun (𝒪[FullConductorCompletion p]) (Fin 2)).dualBasis)

/-- Rationalizing the constructed finite integral twist gives precisely the
actual chosen effective Euler fibre, with the same exponent and conductor
coefficient embedding. -/
def chosenEffectiveEulerIntegralRationalEquiv
    (hmPos : 0 < m) (hmLt : m < p) :
    let L := FullConductorCompletion p
    letI : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
    ((chosenEffectiveEulerIntegralAction p hp m hm ξ hmPos hmLt).baseChange L).Equiv
      (chosenEffectiveEulerAction p m p (by omega) hmPos hmLt hm L
        (coprimeEulerCoefficientMap p (primeAboveConductor p) L) ξ) := by
  let L := FullConductorCompletion p
  letI : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
  let ρ₀ := chosenConductorPlusIntegralAction p hp m hm ξ
  let C := chosenConductorPlusCoordinateAction p hp m hm ξ
  let ν := chosenEffectiveEulerResidualCharacter p hp m hm ξ hmPos hmLt
  let u := chosenEffectiveEulerIntegralCharacter p hp m hm ξ hmPos hmLt
  have hufield : ((Units.map (algebraMap 𝒪[L] L).toMonoidHom).comp u) = ν := by
    apply MonoidHom.ext
    intro g
    exact finiteCharacterIntegralLift_toField ν
      (chosenEffectiveEulerResidualCharacter_finite p hp m hm ξ hmPos hmLt) g
  have eTwist : ((chosenEffectiveEulerIntegralAction p hp m hm ξ hmPos hmLt).baseChange L).Equiv
      ((ρ₀.dual.baseChange L).characterTwist ν) := by
    change ((ρ₀.dual.integralCharacterTwist u).baseChange L).Equiv
      ((ρ₀.dual.baseChange L).characterTwist ν)
    have e := Representation.integralCharacterTwistBaseChangeEquiv L ρ₀.dual u
    rw [hufield] at e
    exact e
  let eDual := Representation.dualBaseChangeEquiv L ρ₀
  have eBase : (ρ₀.baseChange L).Equiv C := by
    have e := Representation.baseChangeIntegralCoordinatesEquiv (K := L) ρ₀
    rw [chosenConductorPlusIntegralAction_mapCoefficients p hp m hm ξ] at e
    exact e
  let eCDual := HilbertModularity.representationDualEquiv eBase
  let ePlus := chosenEffectiveEulerResidualComparisonEquiv p hp m hm ξ hmPos hmLt
  exact eTwist.trans
    ((characterTwistEquiv eDual ν).trans
      ((characterTwistEquiv eCDual ν).trans ePlus))

/-- The transported image of the integral dual-twist model is a stable
submodule of the actual chosen effective Euler fibre. -/
def chosenEffectiveEulerStableLattice
    (hmPos : 0 < m) (hmLt : m < p) :=
  let L := FullConductorCompletion p
  letI : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
  letI : Module.Finite 𝒪[L] (Module.Dual 𝒪[L] (Fin 2 → 𝒪[L])) :=
    Module.Finite.of_basis ((Pi.basisFun 𝒪[L] (Fin 2)).dualBasis)
  Representation.transportedIntegralLattice
    (chosenEffectiveEulerIntegralAction p hp m hm ξ hmPos hmLt)
    (chosenEffectiveEulerIntegralRationalEquiv p hp m hm ξ hmPos hmLt)

/-- The embedded stable lattice is finite and spans the full actual Euler
coefficient-space fibre. Its integral source has rank two. -/
theorem chosenEffectiveEulerStableLattice_isLattice
    (hmPos : 0 < m) (hmLt : m < p) :
    let L := FullConductorCompletion p
    letI : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
    letI : Module.Finite 𝒪[L] (Module.Dual 𝒪[L] (Fin 2 → 𝒪[L])) :=
      Module.Finite.of_basis ((Pi.basisFun 𝒪[L] (Fin 2)).dualBasis)
    let 𝒞 := chosenCoprimeEulerFamily p m (by omega) hmPos hmLt hm
    let R := chosenCoprimeRawEulerRealization p m (by omega) hmPos hmLt hm
    let V : Type := (((R.placeDescent p m 𝒞 p L
      (coprimeEulerCoefficientMap p (primeAboveConductor p) L)).localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))).toModuleCat)
    letI : Module 𝒪[L] V := Module.compHom V (algebraMap 𝒪[L] L)
    @Submodule.IsLattice 𝒪[L] _ L _ _ V _ _ _
      (IsScalarTower.of_algebraMap_smul (fun _ _ => rfl))
      (IsScalarTower.of_algebraMap_smul (fun _ _ => rfl))
      (chosenEffectiveEulerStableLattice p hp m hm ξ hmPos hmLt).toSubmodule := by
  let L := FullConductorCompletion p
  let : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
  let : Module.Finite 𝒪[L] (Module.Dual 𝒪[L] (Fin 2 → 𝒪[L])) :=
    Module.Finite.of_basis ((Pi.basisFun 𝒪[L] (Fin 2)).dualBasis)
  let 𝒞 := chosenCoprimeEulerFamily p m (by omega) hmPos hmLt hm
  let R := chosenCoprimeRawEulerRealization p m (by omega) hmPos hmLt hm
  let V : Type := (((R.placeDescent p m 𝒞 p L
    (coprimeEulerCoefficientMap p (primeAboveConductor p) L)).localSystem.toFunctor.obj
      (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))).toModuleCat)
  let : Module 𝒪[L] V := Module.compHom V (algebraMap 𝒪[L] L)
  exact Representation.transportedIntegralLattice_isLattice
    (chosenEffectiveEulerIntegralAction p hp m hm ξ hmPos hmLt)
    (chosenEffectiveEulerIntegralRationalEquiv p hp m hm ξ hmPos hmLt)

/-- Every finite free stable integral model of the same actual chosen effective
Euler fibre has associated graded equivalent to the displayed direct sum.
The selected model and rational comparison above are proved; only generic
Serre lattice independence is admitted as literature. Neither this theorem
nor the selected associated-graded equivalence labels the invariant line. -/
theorem chosenEffectiveEulerResidual_semisimplification_of_integralModel
    (hmPos : 0 < m) (hmLt : m < p)
    {M : Type*} [AddCommGroup M]
    [Module 𝒪[FullConductorCompletion p] M]
    [Module.Free 𝒪[FullConductorCompletion p] M]
    [Module.Finite 𝒪[FullConductorCompletion p] M]
    (ρ' : Representation 𝒪[FullConductorCompletion p]
      (AbsoluteGalois (realCyclotomicField p)) M)
    (e' : let L := FullConductorCompletion p
      letI : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
      (ρ'.baseChange L).Equiv
        (chosenEffectiveEulerAction p m p (by omega) hmPos hmLt hm L
          (coprimeEulerCoefficientMap p (primeAboveConductor p) L) ξ)) :
    letI : Algebra 𝒪[FullConductorCompletion p] (ZMod p) :=
      (chosenEulerResidueCoefficientMap p hp).toAlgebra
    let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
    let ε := chosenConductorResidualCyclotomicZMod p hp m hm
    ∃ T : Subrepresentation (ρ'.baseChange (ZMod p)),
      Nonempty ((T.toRepresentation.prod
        ((ρ'.baseChange (ZMod p)).quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter θ).prod
            (Representation.ofCharacter (θ * ε⁻¹)))) := by
  let L := FullConductorCompletion p
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let oldFrac : IsFractionRing 𝒪[L] L := inferInstance
  have hAlg : (inferInstance : Algebra 𝒪[L] L) = (𝒪[L]).subtype.toAlgebra := by
    rfl
  let : Algebra 𝒪[L] L := (𝒪[L]).subtype.toAlgebra
  let : IsFractionRing 𝒪[L] L := by
    cases hAlg
    exact oldFrac
  let : Algebra 𝒪[L] (ZMod p) := (chosenEulerResidueCoefficientMap p hp).toAlgebra
  let ρ₀ := chosenEffectiveEulerIntegralAction p hp m hm ξ hmPos hmLt
  let e₀ := chosenEffectiveEulerIntegralRationalEquiv p hp m hm ξ hmPos hmLt
  let θ := chosenEffectiveEulerResidualCharacterZMod p hp m hm ξ hmPos hmLt
  let ε := chosenConductorResidualCyclotomicZMod p hp m hm
  let : Module.Finite 𝒪[L] (Module.Dual 𝒪[L] (Fin 2 → 𝒪[L])) :=
    Module.Finite.of_basis ((Pi.basisFun 𝒪[L] (Fin 2)).dualBasis)
  have h₀ : ∃ S : Subrepresentation (ρ₀.baseChange (ZMod p)),
      Nonempty ((S.toRepresentation.prod
        ((ρ₀.baseChange (ZMod p)).quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter θ).prod
            (Representation.ofCharacter (θ * ε⁻¹)))) := by
    exact ⟨chosenEffectiveEulerResidualFlag p hp m hm ξ hmPos hmLt,
      chosenEffectiveEulerResidualFlag_factors p hp m hm ξ hmPos hmLt⟩
  exact Representation.residualSemisimplification_independent_of_freeLattice ρ₀ ρ'
    (e₀.trans e'.symm) θ (θ * ε⁻¹) h₀

end HilbertModularity.Hypergeometric
