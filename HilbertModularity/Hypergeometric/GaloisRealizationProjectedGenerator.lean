/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFibreExponentChange
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientTransfer

/-! # The fixed-character projection of the selected quotient generator

The real-cyclotomic generator is built using pullback and transfer for the
same selected quotient map.  Only after pulling it back to the proper Euler
cover do we apply the fixed `χ₀` deck projector.  The resulting scalar is
the labelled one of [GPRV, equation (76)] and
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open AlgebraicGeometry HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
  (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

/-- The actual quotient generator acts on its pullback's fixed-character
projection by the sum of the two coefficient values of the inverse deck
roots.  No character projector on the quotient is assumed. -/
theorem GeometricEulerQuotientTransfer.projected_pullback_generator
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (ζ : rootsOfUnity N (cyclotomicField N))
    (v : GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :
    let E := geometricProperEulerFixedPrimitiveProjector N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
    E (P.pullback (P.generator N m 𝒞 𝒬 ξ ζ v)) =
      ι (((ζ : (cyclotomicField N)ˣ) : cyclotomicField N) +
        (((ζ⁻¹ : rootsOfUnity N (cyclotomicField N)) :
          (cyclotomicField N)ˣ) : cyclotomicField N)) • E (P.pullback v) := by
  dsimp only
  let E := geometricProperEulerFixedPrimitiveProjector N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
  let D := geometricProperEulerCoefficientDeckRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L
  let w := P.pullback v
  have hcomm (η : rootsOfUnity N (cyclotomicField N)) :
      E (D η w) = D η (E w) := by
    exact congrArg (fun f : Module.End L _ => f w)
      (geometricProperEulerFixedPrimitiveProjector_comm_deck N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι η)
  have heigen (η : rootsOfUnity N (cyclotomicField N)) :
      D η (E w) =
        ι ((η : (cyclotomicField N)ˣ) : cyclotomicField N) • E w :=
    geometricProperEulerFixedPrimitiveProjector_eigen N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι η w
  change E (P.pullback (P.generator N m 𝒞 𝒬 ξ ζ v)) = _
  rw [P.pullback_generator N m 𝒞 𝒬 ξ ζ v, map_add,
    hcomm ζ, hcomm ζ⁻¹, heigen ζ, heigen ζ⁻¹, map_add, add_smul]

/-- The base-family generator uses the `m`th power on the actual proper
deck action.  The fixed projector is still `χ₀`, so `m` occurs only once
in the resulting real-cyclotomic coefficient. -/
theorem GeometricEulerQuotientTransfer.projected_base_generator
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (v : GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :
    let E := geometricProperEulerFixedPrimitiveProjector N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
    E (P.pullback (P.generator N m 𝒞 𝒬 ξ
      ((cyclotomicDeckGenerator N) ^ m) v)) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m) • E (P.pullback v) := by
  simpa only [Subgroup.coe_pow, Subgroup.coe_inv,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, cyclotomicDeckGenerator_coe,
    inv_pow] using
    P.projected_pullback_generator N m 𝒞 𝒬 ξ ℓ L ι
      ((cyclotomicDeckGenerator N) ^ m) v

end HilbertModularity.Hypergeometric
