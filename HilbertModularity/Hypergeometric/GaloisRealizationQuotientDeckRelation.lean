/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFibreDeckRelation
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientTransfer

/-! # The selected Euler reflection and deck action on cohomology

The affine relation from [GPRV, Proposition 9.5, equation (76)] is carried to
the chosen proper fibre, its geometric base change, and its actual degree-one
cohomology.  The selected fibre chart must be dominant; this is kept visible
until it is established for the chosen completion.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

/-- The geometric reflection conjugates the base change of the same selected
deck map to its inverse.  The three displayed geometric hypotheses concern
the selected proper fibre, not a freely chosen representation. -/
theorem geometricProperEulerQuotientReflection_deck
    (hmPos : 1 ≤ m) (hmN : m < N) (hcop : m.Coprime N)
    [IsReduced (smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    [(smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).IsSeparated]
    [IsDominant (smoothProperEulerFibreChartInclusion N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    (ζ : rootsOfUnity N (cyclotomicField N)) :
    (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
        (geometricProperEulerDeckIso N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ζ).hom =
      (geometricProperEulerDeckIso N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ζ⁻¹).hom ≫
        (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom := by
  let e := geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ
  let d := geometricProperEulerDeckIso N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ
  let di := geometricProperEulerDeckIso N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ⁻¹
  let S := (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)).hom
  let D := (smoothProperEulerFibreDeckAction N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ).unop.hom
  let Di := (smoothProperEulerFibreDeckAction N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ⁻¹).unop.hom
  have hSD : S ≫ D = Di ≫ S :=
    smoothProperEulerFibreReflection_deck N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) 𝒬 hmPos hmN hcop ζ
  change e.hom ≫ d.hom = di.hom ≫ e.hom
  apply pullback.hom_ext
  · dsimp only [e, d, di]
    rw [Category.assoc, geometricProperEulerDeckIso_fst]
    rw [geometricProperEulerQuotientReflectionIso_fst]
    rw [Category.assoc, geometricProperEulerQuotientReflectionIso_fst,
      geometricProperEulerDeckIso_fst]
  · dsimp only [e, d, di]
    rw [Category.assoc, geometricProperEulerDeckIso_snd]
    rw [← Category.assoc, geometricProperEulerQuotientReflectionIso_snd]
    conv_rhs =>
      rw [Category.assoc, geometricProperEulerQuotientReflectionIso_snd]
      rw [← Category.assoc, geometricProperEulerDeckIso_snd]
    simpa only [S, D, Di, Category.assoc] using
      congrArg (fun f => pullback.snd
        (GroupScheme.fieldPoint (cyclotomicField N)
          (AlgebraicClosure (cyclotomicField N))).hom
        (smoothProperEulerFibreStructureMap N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ)) ≫ f) hSD

/-- The relation between the selected reflection and deck maps acts on the
actual integral degree-one cohomology of the same geometric fibre. -/
theorem geometricProperEulerQuotientReflection_deck_cohomology
    (hmPos : 1 ≤ m) (hmN : m < N) (hcop : m.Coprime N)
    [IsReduced (smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    [(smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).IsSeparated]
    [IsDominant (smoothProperEulerFibreChartInclusion N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (ζ : rootsOfUnity N (cyclotomicField N))
    (x : (geometricSmoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).EllAdicCohomology ℓ 1) :
    Scheme.ellAdicCohomologyEquiv
      (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ) ℓ 1
        (Scheme.ellAdicCohomologyEquiv
          (geometricProperEulerDeckIso N m 𝒞
            (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
            (one_sub_realEulerParameter_isUnit N ξ) ζ) ℓ 1 x) =
      Scheme.ellAdicCohomologyEquiv
        (geometricProperEulerDeckIso N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ζ⁻¹) ℓ 1
        (Scheme.ellAdicCohomologyEquiv
          (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ) ℓ 1 x) := by
  let s := geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ
  let d := geometricProperEulerDeckIso N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ
  let di := geometricProperEulerDeckIso N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ⁻¹
  have h : s ≪≫ d = di ≪≫ s := by
    apply Iso.ext
    exact geometricProperEulerQuotientReflection_deck N m 𝒞 𝒬 ξ
      hmPos hmN hcop ζ
  change Scheme.ellAdicCohomologyEquiv s ℓ 1
    (Scheme.ellAdicCohomologyEquiv d ℓ 1 x) =
      Scheme.ellAdicCohomologyEquiv di ℓ 1
        (Scheme.ellAdicCohomologyEquiv s ℓ 1 x)
  calc
    Scheme.ellAdicCohomologyEquiv s ℓ 1
        (Scheme.ellAdicCohomologyEquiv d ℓ 1 x) =
      Scheme.ellAdicCohomologyEquiv (s ≪≫ d) ℓ 1 x :=
        (Scheme.ellAdicCohomologyEquiv_trans ℓ s d 1 x).symm
    _ = Scheme.ellAdicCohomologyEquiv (di ≪≫ s) ℓ 1 x := by rw [h]
    _ = Scheme.ellAdicCohomologyEquiv di ℓ 1
        (Scheme.ellAdicCohomologyEquiv s ℓ 1 x) :=
          Scheme.ellAdicCohomologyEquiv_trans ℓ di s 1 x

/-- The same selected maps satisfy the relation after both coefficient
extensions.  This supplies the deck field of the quotient transfer package. -/
theorem geometricProperEulerQuotientReflection_deck_coefficient
    (hmPos : 1 ≤ m) (hmN : m < N) (hcop : m.Coprime N)
    [IsReduced (smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    [(smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).IsSeparated]
    [IsDominant (smoothProperEulerFibreChartInclusion N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ζ : rootsOfUnity N (cyclotomicField N))
    (v : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
      (geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ v) =
    geometricProperEulerCoefficientDeckRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ⁻¹
        (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v) := by
  let H := (geometricSmoothProperEulerFibre N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)).ellAdicCohomologyAutRepresentation ℓ 1
  let s := MulOpposite.op (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ)
  let d := MulOpposite.op (geometricProperEulerDeckIso N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ)
  let di := MulOpposite.op (geometricProperEulerDeckIso N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ζ⁻¹)
  have hint : (H s).comp (H d) = (H di).comp (H s) := by
    ext x
    exact geometricProperEulerQuotientReflection_deck_cohomology
      N m 𝒞 𝒬 ξ hmPos hmN hcop ℓ ζ x
  have hq := congrArg (fun f => LinearMap.baseChange ℚ_[ℓ] f) hint
  have hL := congrArg (fun f => LinearMap.baseChange L f) hq
  rw [geometricProperEulerCoefficientReflection_eq,
    geometricProperEulerCoefficientDeckRepresentation_eq,
    geometricProperEulerCoefficientDeckRepresentation_eq]
  change ((LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] (H s))).comp
      (LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] (H d)))) v =
    ((LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] (H di))).comp
      (LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] (H s)))) v
  simpa only [LinearMap.baseChange_comp] using congrArg (fun f => f v) hL

/-- Build transfer for the actual selected quotient with its deck relation
derived from the affine reflection.  Only invariant-H¹ comparison and the
displayed geometric fibre hypotheses remain.  In the prime case this is full
quotient H¹; composite level still requires projection to the new part. -/
def GeometricEulerQuotientTransfer.ofInvariantPullback
    (hmPos : 1 ≤ m) (hmN : m < N) (hcop : m.Coprime N)
    [IsReduced (smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    [(smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).IsSeparated]
    [IsDominant (smoothProperEulerFibreChartInclusion N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (hbij : Function.Bijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L)) :
    GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L :=
  GeometricEulerQuotientTransfer.ofInvariantPullbackWithDeckRelation
    N m 𝒞 𝒬 ξ ℓ L hbij
      (geometricProperEulerQuotientReflection_deck_coefficient
        N m 𝒞 𝒬 ξ hmPos hmN hcop ℓ L)

end HilbertModularity.Hypergeometric
