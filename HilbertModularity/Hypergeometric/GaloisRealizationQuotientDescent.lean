/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientComponent
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientTransfer

/-! # One quotient motive and its labelled realizations

The common quotient is geometric data over the real parameter line.  At each
coefficient place, [GPRV, Theorem 9.2 and Proposition 9.5] take the labelled
component of its degree-one cohomology and compare its cyclotomic base change
with the fixed-character Euler summand.  Keeping the common quotient outside
the place data ensures that the specializations are not independent choices.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

universe u

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)

/-- A realization of the same geometric quotient at one coefficient place.
The comparison is with the previously defined proper Euler projector, via
the real descended local system; no trace value is included in this data. -/
structure RealEulerQuotientPlace (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [Field L] [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L) where
  descent : ProperEulerRealDescent N m ℓ L ι 𝒞
  /-- Cohomological pullback and transfer for the specialization of this
  same geometric quotient map. The real generator must be obtained from
  these maps and the actual proper deck action. -/
  geometricTransfer : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
    GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L
  action : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
    RealCyclotomicQuotientAction N m 𝒞 𝒬 ξ ℓ L
  /-- Cohomology base change for this quotient fibre, using the chosen
  algebraic closures of the real and cyclotomic fields. -/
  baseChange : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
    GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L ≃ₗ[L]
      GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L
  /-- Restriction through the two closure identifications is compatible with
  the base change of this same quotient fibre. -/
  baseChange_galois : ∀
      (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
      (g : Qbar ≃ₐ[cyclotomicField N] Qbar)
      (v : GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L),
    baseChange ξ
        (geometricRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L
          (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g)) v) =
      geometricCyclotomicRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L
        (cyclotomicEulerClosureGaloisHom N g) (baseChange ξ v)
  /-- [GPRV, Theorem 9.2, proof, equation (76), pp.40–41]: every real
  cyclotomic correspondence on this quotient uses the transfer and deck
  operator of the same geometric quotient map.  The case `k = m` is the
  base-curve generator under the proved affine exponent change
  `EulerCover.geometricExponentCohomologyEquiv_deck`: its deck operator is
  `Dₘ(ζ^m)`, corresponding to `D₁(ζ)` on the base curve. -/
  action_generator : ∀
      (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
      (k : ℕ)
      (v : GeometricRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L),
    baseChange ξ ((action ξ).endomorphism (tau N k) v) =
      (geometricTransfer ξ).generator N m 𝒞 𝒬 ξ
        ((cyclotomicDeckGenerator N) ^ k) (baseChange ξ v)
  componentComparison : ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
    ((action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) ≃ₗ[L]
      (descent.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ)))
  /-- [GPRV, Theorem 9.2 and Proposition 9.5, pp.40–41]: the quotient
  motive over the real field gives the same arithmetic Galois action as its
  chosen descended local system, also on elements outside the cyclotomic
  subgroup.  The restricted case below follows independently from projected
  pullback naturality; this field records the full descent supplied by the
  cited quotient construction. -/
  componentComparison_galois : ∀
      (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
      (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
        AlgebraicClosure (realCyclotomicField N))
      (v : (action ξ).component N m 𝒞 𝒬 ξ ℓ L ι),
    componentComparison ξ
        ⟨geometricRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L g v.1,
          (action ξ).component_stable N m 𝒞 𝒬 ξ ℓ L ι g v⟩ =
      (descent.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)) g (componentComparison ξ v)
  /-- [GPRV, Theorem 9.2 and Proposition 9.5, pp.40–41]: the chosen
  comparison with the fixed `χ₀` cohomology is the projector applied to
  pullback along this same quotient map.  This connects the geometric
  transfer to the previously chosen descended local system.  Projection is
  necessary: the unprojected pullback is reflection invariant and generally
  has both the `χ₀` and inverse-character parts. -/
  componentComparison_pullback : ∀
      (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
      (v : (action ξ).component N m 𝒞 𝒬 ξ ℓ L ι),
    ((descent.properComparison ξ) (componentComparison ξ v)).1 =
      geometricProperEulerFixedPrimitiveProjector N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
        ((geometricTransfer ξ).pullback (baseChange ξ v.1))

/-- The quotient/component comparison intertwines Galois after restriction
from the cyclotomic field. This is forced by its projected pullback description,
the base-change and pullback naturality, and the proper Euler comparison. The
proper comparison supplies no statement for arbitrary real-field Galois
elements, so the assertion is intentionally restricted to this subgroup. -/
theorem RealEulerQuotientPlace.componentComparison_intertwines_restricted
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type u) [Field L]
    [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (g : Qbar ≃ₐ[cyclotomicField N] Qbar)
    (v : (R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :
    R.componentComparison ξ
        ⟨geometricRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L
            (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g)) v.1,
          (R.action ξ).component_stable N m 𝒞 𝒬 ξ ℓ L ι
            (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g)) v⟩ =
      (R.descent.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ))
          (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g))
          (R.componentComparison ξ v) := by
  let P := R.geometricTransfer ξ
  let E := geometricProperEulerFixedPrimitiveProjector N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
  let G := geometricProperEulerGaloisRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L
    (cyclotomicEulerClosureGaloisHom N g)
  apply (R.descent.properComparison ξ).injective
  apply Subtype.val_injective
  calc
    _ = E (P.pullback (R.baseChange ξ
          (geometricRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L
            (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g)) v.1))) :=
      R.componentComparison_pullback ξ _
    _ = E (P.pullback
          (geometricCyclotomicRealEulerQuotientGaloisRepresentation
            N m 𝒞 𝒬 ξ ℓ L (cyclotomicEulerClosureGaloisHom N g)
              (R.baseChange ξ v.1))) := by
      rw [R.baseChange_galois ξ g v.1]
    _ = E (G (P.pullback (R.baseChange ξ v.1))) := by
      rw [P.pullback_galois]
    _ = G (E (P.pullback (R.baseChange ξ v.1))) := by
      exact congrArg (fun f : Module.End L _ => f (P.pullback (R.baseChange ξ v.1)))
        (geometricProperEulerFixedPrimitiveProjector_comm_galois N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
          (cyclotomicEulerClosureGaloisHom N g))
    _ = G (((R.descent.properComparison ξ) (R.componentComparison ξ v)).1) := by
      rw [R.componentComparison_pullback ξ v]
    _ = _ := by
      simpa only [properPrimitiveQbarGaloisRepresentation_apply,
        properPrimitiveGaloisRepresentation_val,
        MonoidHom.comp_apply] using congrArg Subtype.val
          (R.descent.properComparison_intertwines ξ g (R.componentComparison ξ v)).symm

/-- The labelled real-field generator acts on the cyclotomic base change by
the fixed coefficient label.  The action is the deck/transfer action from
`action_generator`, not an independent endomorphism. -/
theorem RealEulerQuotientPlace.generator_on_component
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type u) [Field L]
    [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (v : (R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :
    (R.geometricTransfer ξ).generator N m 𝒞 𝒬 ξ
        (cyclotomicDeckGenerator N) (R.baseChange ξ v.1) =
      ι ((root N) + (root N)⁻¹) • R.baseChange ξ v.1 := by
  calc
    _ = R.baseChange ξ ((R.action ξ).endomorphism (tau N 1) v.1) :=
      (by simpa using (R.action_generator ξ 1 v.1).symm)
    _ = R.baseChange ξ
        ((realCyclotomicQuotientLabel N L ι (tau N 1)) • v.1) := by
      rw [(R.action ξ).component_spec N m 𝒞 𝒬 ξ ℓ L ι v (tau N 1)]
    _ = ι ((root N) + (root N)⁻¹) • R.baseChange ξ v.1 := by
      rw [map_smul, realCyclotomicQuotientLabel_tau]
      simp

/-- The base-family generator transported to the exponent-`m` curve uses
`Dₘ(ζ^m)`.  The fixed `χ₀` component therefore has the single powered label
`ι(ζ^m + ζ⁻ᵐ)`, as in revised Definition 2.3.  The exponent appears once in
the deck operator and is not also applied to the projector character. -/
theorem RealEulerQuotientPlace.base_generator_on_component
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type u) [Field L]
    [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (v : (R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :
    (R.geometricTransfer ξ).generator N m 𝒞 𝒬 ξ
        ((cyclotomicDeckGenerator N) ^ m) (R.baseChange ξ v.1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m) • R.baseChange ξ v.1 := by
  calc
    _ = R.baseChange ξ ((R.action ξ).endomorphism (tau N m) v.1) :=
      (R.action_generator ξ m v.1).symm
    _ = R.baseChange ξ
        ((realCyclotomicQuotientLabel N L ι (tau N m)) • v.1) := by
      rw [(R.action ξ).component_spec N m 𝒞 𝒬 ξ ℓ L ι v (tau N m)]
    _ = ι ((root N) ^ m + (root N)⁻¹ ^ m) • R.baseChange ξ v.1 := by
      rw [map_smul, realCyclotomicQuotientLabel_tau]

/-- Pullback of the labelled quotient component is an eigenspace for the
sum of the actual deck action and its inverse on the exponent-`m` curve.
This is the cohomological content of the real label in [GPRV, (76)]. -/
theorem RealEulerQuotientPlace.deck_sum_on_component
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type u) [Field L]
    [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (v : (R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :
    let P := R.geometricTransfer ξ
    let w := R.baseChange ξ v.1
    geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L
        (cyclotomicDeckGenerator N) (P.pullback w) +
      geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L
        (cyclotomicDeckGenerator N)⁻¹ (P.pullback w) =
      ι ((root N) + (root N)⁻¹) • P.pullback w := by
  dsimp only
  calc
    _ = (R.geometricTransfer ξ).pullback
        ((R.geometricTransfer ξ).generator N m 𝒞 𝒬 ξ
          (cyclotomicDeckGenerator N) (R.baseChange ξ v.1)) :=
        ((R.geometricTransfer ξ).pullback_generator N m 𝒞 𝒬 ξ
          (cyclotomicDeckGenerator N) (R.baseChange ξ v.1)).symm
    _ = (R.geometricTransfer ξ).pullback
        (ι ((root N) + (root N)⁻¹) • R.baseChange ξ v.1) := by
      rw [R.generator_on_component N m 𝒞 𝒬 ℓ L ι ξ v]
    _ = ι ((root N) + (root N)⁻¹) •
        (R.geometricTransfer ξ).pullback (R.baseChange ξ v.1) := by
      rw [map_smul]

/-- The corresponding identity for the base-family deck generator.  The
affine exponent equivalence identifies `D₁(ζ)` with `Dₘ(ζ^m)`, so this is
the form used by the labelled Frobenius dictionary. -/
theorem RealEulerQuotientPlace.base_deck_sum_on_component
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type u) [Field L]
    [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (v : (R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :
    let P := R.geometricTransfer ξ
    let w := R.baseChange ξ v.1
    geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L
        ((cyclotomicDeckGenerator N) ^ m) (P.pullback w) +
      geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L
        ((cyclotomicDeckGenerator N) ^ m)⁻¹ (P.pullback w) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m) • P.pullback w := by
  dsimp only
  calc
    _ = (R.geometricTransfer ξ).pullback
        ((R.geometricTransfer ξ).generator N m 𝒞 𝒬 ξ
          ((cyclotomicDeckGenerator N) ^ m) (R.baseChange ξ v.1)) :=
        ((R.geometricTransfer ξ).pullback_generator N m 𝒞 𝒬 ξ
          ((cyclotomicDeckGenerator N) ^ m) (R.baseChange ξ v.1)).symm
    _ = (R.geometricTransfer ξ).pullback
        (ι ((root N) ^ m + (root N)⁻¹ ^ m) • R.baseChange ξ v.1) := by
      rw [R.base_generator_on_component N m 𝒞 𝒬 ℓ L ι ξ v]
    _ = ι ((root N) ^ m + (root N)⁻¹ ^ m) •
        (R.geometricTransfer ξ).pullback (R.baseChange ξ v.1) := by
      rw [map_smul]

/-- The same base-family deck sum acts with its labelled scalar after the
actual quotient pullback is projected to the fixed `χ₀` summand and
identified with the chosen descended fibre.  The projector commutes with
deck operators because the cyclic deck group is abelian. -/
theorem RealEulerQuotientPlace.base_deck_sum_on_compared_component
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type u) [Field L]
    [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (v : (R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :
    let ρ := geometricProperEulerCoefficientDeckRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L
    let u := ((R.descent.properComparison ξ) (R.componentComparison ξ v)).1
    ρ ((cyclotomicDeckGenerator N) ^ m) u +
      ρ ((cyclotomicDeckGenerator N) ^ m)⁻¹ u =
      ι ((root N) ^ m + (root N)⁻¹ ^ m) • u := by
  dsimp only
  let ρ := geometricProperEulerCoefficientDeckRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L
  let P := geometricProperEulerFixedPrimitiveProjector N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
  let x := (R.geometricTransfer ξ).pullback (R.baseChange ξ v.1)
  have hcomparison :
      ((R.descent.properComparison ξ) (R.componentComparison ξ v)).1 = P x :=
    R.componentComparison_pullback ξ v
  have hraw := R.base_deck_sum_on_component N m 𝒞 𝒬 ℓ L ι ξ v
  dsimp only at hraw
  have hcomm (ζ : rootsOfUnity N (cyclotomicField N)) (w) :
      P (ρ ζ w) = ρ ζ (P w) := by
    exact congrArg (fun f : Module.End L _ => f w)
      (geometricProperEulerFixedPrimitiveProjector_comm_deck N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι ζ)
  rw [hcomparison]
  calc
    ρ ((cyclotomicDeckGenerator N) ^ m) (P x) +
        ρ ((cyclotomicDeckGenerator N) ^ m)⁻¹ (P x) =
      P (ρ ((cyclotomicDeckGenerator N) ^ m) x) +
        P (ρ ((cyclotomicDeckGenerator N) ^ m)⁻¹ x) := by
          rw [hcomm, hcomm]
    _ = P (ρ ((cyclotomicDeckGenerator N) ^ m) x +
        ρ ((cyclotomicDeckGenerator N) ^ m)⁻¹ x) := (map_add P _ _).symm
    _ = P (ι ((root N) ^ m + (root N)⁻¹ ^ m) • x) :=
      congrArg P hraw
    _ = ι ((root N) ^ m + (root N)⁻¹ ^ m) • P x := map_smul P _ _

/-- The labelled component, rather than the entire quotient cohomology, has
rank two.  This follows from the comparison with the descended local system. -/
theorem RealEulerQuotientPlace.component_finrank (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [Field L] [TopologicalSpace L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (P : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Module.finrank L ((P.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) = 2 := by
  rw [(P.componentComparison ξ).finrank_eq]
  exact P.descent.rank_two ξ

/-- The actual quotient is selected once before any coefficient place.  Each
place realization in this structure refers to its fibre cohomology. -/
structure CommonRealEulerQuotientRealization where
  quotient : SmoothProperRealEulerQuotient N m 𝒞
  atPlace : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
      [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
      [FiniteDimensional ℚ_[ℓ] L]
      (ι : cyclotomicField N →+* L),
    RealEulerQuotientPlace N m 𝒞 quotient ℓ L ι
  /-- Rational degree-one cohomology of this one quotient commutes with a
  finite extension of its `ℓ`-adic coefficient field.  The resulting
  equivariance is for the full real-field Galois group.  The two labels are
  required to agree under the specified scalar map; neither the quotient nor
  its descended arithmetic action is chosen anew after extension. -/
  coefficientBaseChange : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (L₀ L : Type u)
      [NontriviallyNormedField L₀] [CompleteSpace L₀]
      [Algebra ℚ_[ℓ] L₀] [ContinuousSMul ℚ_[ℓ] L₀]
      [FiniteDimensional ℚ_[ℓ] L₀]
      [NontriviallyNormedField L] [CompleteSpace L]
      [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
      [FiniteDimensional ℚ_[ℓ] L]
      [Algebra L₀ L] [IsScalarTower ℚ_[ℓ] L₀ L]
      (ι₀ : cyclotomicField N →+* L₀)
      (ι : cyclotomicField N →+* L)
      (_hι : (algebraMap L₀ L).comp ι₀ = ι)
      (ξ : ProjectiveLine.Parameter (realCyclotomicField N)),
    (((atPlace ℓ L₀ ι₀).descent.localSystem.arithmeticRepresentation
      (ProjectiveLine.puncturedPoint _ ξ)).baseChange L).Equiv
      ((atPlace ℓ L ι).descent.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ))

/-- Project the chosen common quotient realization to its descent at a
coefficient place.  This is the descent attached to the same quotient at
every place, rather than a fresh use of the per-place existence theorem. -/
def CommonRealEulerQuotientRealization.placeDescent
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L) :
    ProperEulerRealDescent N m ℓ L ι 𝒞 :=
  (R.atPlace ℓ L ι).descent

/-- The selected place descent is the descent field of that very same
quotient realization. -/
@[simp] theorem CommonRealEulerQuotientRealization.placeDescent_eq_atPlace
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L) :
    R.placeDescent N m 𝒞 ℓ L ι = (R.atPlace ℓ L ι).descent := (rfl)

/-- [GPRV, Theorem 9.2 and Proposition 9.5, pp. 40–41], in the coprime
symmetric case.  Their involution quotient is formed over `K_N` before
choosing a coefficient place; the real cyclotomic action on its H¹ has a
rank-two labelled component, and pullback to the Euler curve identifies that
component with the fixed `χ₀` summand. The source condition `(Irr)` follows
from `symmetricParameters_irreducible` and [GPRV, Lemma 8.5, p. 30].
This is the RAW cohomological
realization and chosen descent, not an assumption about Frobenius traces,
modularity, or an arithmetic RM comparison.  The `coefficientBaseChange`
field includes the standard rational `ℓ`-adic scalar extension of this same
quotient's H¹ and its labelled correspondence.  Its source correspondence
combines [src_milne_lec, Theorem 20.4, pp. 127–128] for proper smooth
cohomology with [proetale2015, Lemma 6.7.17, printed p. 57] for
finite-coefficient pushforward/tensor compatibility, and [proetale2015,
Definition 6.8.1 and Lemma 6.8.2, printed pp. 58–59; Proposition 6.8.4(3),
p. 59; Proposition 6.8.14 and Remark 6.8.15, pp. 61–62] for finite local
coefficient extension and functorial
sheaves.  GPRV does not state the entire Lean record verbatim.  This
strengthens the previously used joint-choice interface: the equivalence is
required at the same quotient and label for every real-field Galois element,
not just for its cyclotomic subgroup. -/
theorem exists_commonRealEulerQuotientRealization_of_coprime
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N) :
    Nonempty (CommonRealEulerQuotientRealization N m 𝒞) := by
  sorry

/-- At odd conductor the raw quotient is effective because κ_N is trivial
[GPRV, Definition 8.8 and paragraph after Lemma 9.3, p. 40]. -/
theorem exists_commonRealEulerQuotientRealization_of_odd_coprime
    (h3 : 3 ≤ N) (_hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N) :
    Nonempty (CommonRealEulerQuotientRealization N m 𝒞) :=
  exists_commonRealEulerQuotientRealization_of_coprime N m 𝒞 h3 hm hmN hcop

/-- The established prime joint-choice interface follows from the same
odd coprime quotient realization input. -/
theorem exists_commonRealEulerQuotientRealization
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    Nonempty (CommonRealEulerQuotientRealization N m 𝒞) := by
  have hOdd : Odd N := hN.odd_of_ne_two (by omega)
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact exists_commonRealEulerQuotientRealization_of_odd_coprime
    N m 𝒞 (le_trans (by decide : 3 ≤ 5) h5) hOdd hm hmN hcop

/-- Select one odd coprime quotient and all its coefficient realizations. -/
def chosenCommonRealEulerQuotientRealization_of_odd_coprime
    (h3 : 3 ≤ N) (hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N) :
    CommonRealEulerQuotientRealization N m 𝒞 :=
  Classical.choice (exists_commonRealEulerQuotientRealization_of_odd_coprime
    N m 𝒞 h3 hOdd hm hmN hcop)

/-- Select the geometric quotient and its place realizations as one object. -/
def chosenCommonRealEulerQuotientRealization
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    CommonRealEulerQuotientRealization N m 𝒞 :=
  Classical.choice (exists_commonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN)

end HilbertModularity.Hypergeometric
