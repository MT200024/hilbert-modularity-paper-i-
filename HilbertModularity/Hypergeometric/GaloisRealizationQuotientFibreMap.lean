/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientCohomology
public import HilbertModularity.Hypergeometric.GaloisDescent

/-! # The Euler cover map on a quotient fibre

The cover morphism in `SmoothProperRealEulerQuotient` is chosen before the
coefficient place.  Here it is specialized to a cyclotomic parameter.  Both
fibres and the resulting map are actual schemes over the cyclotomic field.
The cohomological pullback and transfer require a further comparison input.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)

/-- The base change of the one real quotient family to the cyclotomic
parameter line.  The cover map `𝒬.coverToQuotient` lands in this scheme. -/
abbrev cyclotomicRealEulerQuotientFamily : Scheme :=
  pullback 𝒬.projection
    (puncturedCoefficientMap (realEulerCoefficientInclusion N))

/-- The fibre of the base-changed quotient family at the same cyclotomic
parameter as the exponent-`m` Euler curve. -/
@[expose] def cyclotomicRealEulerQuotientFibre
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) : Scheme :=
  pullback (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N)))
    (EulerCover.puncturedParameterPoint
      (cyclotomicField N) (cyclotomicField N)
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))

/-- The specialized map from the actual proper Euler fibre to the actual
base-changed quotient fibre.  It is induced by the family map, not chosen
afresh at a coefficient place. -/
@[expose] def smoothProperEulerFibreToRealQuotient
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    smoothProperEulerFibre N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ⟶
      cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ :=
  pullback.lift
    (pullback.fst 𝒞.projection
      (EulerCover.puncturedParameterPoint
        (cyclotomicField N) (cyclotomicField N)
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ)) ≫ 𝒬.coverToQuotient)
    (pullback.snd 𝒞.projection
      (EulerCover.puncturedParameterPoint
        (cyclotomicField N) (cyclotomicField N)
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ))) (by
      calc
        _ = pullback.fst 𝒞.projection _ ≫
            (𝒬.coverToQuotient ≫ pullback.snd _ _) := Category.assoc _ _ _
        _ = pullback.fst 𝒞.projection _ ≫ 𝒞.projection := by
          rw [𝒬.coverToQuotient_overBase]
        _ = pullback.snd 𝒞.projection _ ≫ _ := pullback.condition)

/-- The specialized quotient map remembers the chosen family quotient map. -/
@[simp] theorem smoothProperEulerFibreToRealQuotient_fst
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ ≫
      pullback.fst
        (pullback.snd 𝒬.projection
          (puncturedCoefficientMap (realEulerCoefficientInclusion N)))
        (EulerCover.puncturedParameterPoint
          (cyclotomicField N) (cyclotomicField N)
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ)) =
      pullback.fst 𝒞.projection
        (EulerCover.puncturedParameterPoint
          (cyclotomicField N) (cyclotomicField N)
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ)) ≫ 𝒬.coverToQuotient := by
  exact pullback.lift_fst _ _ _

/-- The fibre quotient map fixes the cyclotomic parameter point. -/
@[simp] theorem smoothProperEulerFibreToRealQuotient_snd
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ ≫
      pullback.snd _ _ =
      smoothProperEulerFibreStructureMap N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) := by
  exact pullback.lift_snd _ _ _

/-- A specialized proper-family automorphism fixes the parameter-point
projection. -/
theorem smoothProperEulerFibreAutomorphism_snd
    (ι : Aut (Over.mk 𝒞.projection))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    (smoothProperEulerFibreAutomorphism N m 𝒞 ι
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ)).hom ≫
      smoothProperEulerFibreStructureMap N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) =
      smoothProperEulerFibreStructureMap N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) := by
  exact ((Over.pullback (EulerCover.puncturedParameterPoint
    (cyclotomicField N) (cyclotomicField N)
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ))).map ι.hom).w

/-- The quotient map of the specialized Euler fibre is invariant under the
same reflection that defines the common quotient family. -/
theorem smoothProperEulerFibreToRealQuotient_invariant
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ)).hom ≫
      smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ =
    smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ := by
  let p := EulerCover.puncturedParameterPoint
    (cyclotomicField N) (cyclotomicField N)
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)
  let a := (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)).hom
  let q := smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ
  let c : smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ⟶ 𝒞.curve :=
    pullback.fst 𝒞.projection p
  let d : cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ ⟶
      cyclotomicRealEulerQuotientFamily N m 𝒞 𝒬 := pullback.fst
    (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N))) p
  let e : cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ ⟶
      Spec (CommRingCat.of (cyclotomicField N)) := pullback.snd
    (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N))) p
  let s := smoothProperEulerFibreStructureMap N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)
  have hq : q ≫ d = c ≫ 𝒬.coverToQuotient :=
    smoothProperEulerFibreToRealQuotient_fst N m 𝒞 𝒬 ξ
  have hqs : q ≫ e = s :=
    smoothProperEulerFibreToRealQuotient_snd N m 𝒞 𝒬 ξ
  have ha : a ≫ c = c ≫ 𝒬.involution.hom.left :=
    smoothProperEulerFibreAutomorphism_fst N m 𝒞 𝒬.involution
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)
  have has : a ≫ s = s :=
    smoothProperEulerFibreAutomorphism_snd N m 𝒞 𝒬.involution ξ
  have hcv : (𝒬.involution.hom).left ≫ 𝒬.coverToQuotient =
      𝒬.coverToQuotient := 𝒬.coverToQuotient_invariant
  have hc : (a ≫ c) ≫ 𝒬.coverToQuotient =
      c ≫ 𝒬.coverToQuotient := by
    rw [ha]
    exact (Category.assoc c (𝒬.involution.hom).left
      𝒬.coverToQuotient).trans (congrArg (fun f => c ≫ f) hcv)
  apply pullback.hom_ext
  · change (a ≫ q) ≫ d = q ≫ d
    have h1 : (a ≫ q) ≫ d = a ≫ (c ≫ 𝒬.coverToQuotient) := by
      rw [Category.assoc, hq]
    have h2 : a ≫ (c ≫ 𝒬.coverToQuotient) =
        c ≫ 𝒬.coverToQuotient := by
      rw [← Category.assoc]
      exact hc
    exact h1.trans (h2.trans hq.symm)
  · change (a ≫ q) ≫ e = q ≫ e
    calc
      (a ≫ q) ≫ e = a ≫ (q ≫ e) := Category.assoc _ _ _
      _ = a ≫ s := congrArg (fun f => a ≫ f) hqs
      _ = s := has
      _ = q ≫ e := hqs.symm

/-- The structure map of the cyclotomic base change of the real quotient
fibre.  It has the same ground field as the exponent-`m` Euler fibre. -/
@[expose] def cyclotomicRealEulerQuotientFibreStructureMap
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ ⟶
      Spec (CommRingCat.of (cyclotomicField N)) :=
  pullback.snd _ _

/-- The selected real quotient remains proper after the cyclotomic
coefficient change and specialization to a parameter. -/
theorem cyclotomicRealEulerQuotientFibre_isProper
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    IsProper (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ) := by
  let : IsProper 𝒬.projection := 𝒬.isProper
  have : IsProper (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N))) := inferInstance
  change IsProper (pullback.snd
    (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N)))
    (EulerCover.puncturedParameterPoint
      (cyclotomicField N) (cyclotomicField N)
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)))
  infer_instance

/-- The selected real quotient remains smooth under the same two base
changes. -/
theorem cyclotomicRealEulerQuotientFibre_isSmooth
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Smooth (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ) := by
  let : Smooth 𝒬.projection := 𝒬.isSmooth
  have : Smooth (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N))) := inferInstance
  change Smooth (pullback.snd
    (pullback.snd 𝒬.projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N)))
    (EulerCover.puncturedParameterPoint
      (cyclotomicField N) (cyclotomicField N)
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)))
  infer_instance

/-- The quotient map is a morphism over the cyclotomic ground field. -/
@[simp] theorem smoothProperEulerFibreToRealQuotient_overField
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ ≫
      cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ =
    smoothProperEulerFibreStructureMap N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) :=
  smoothProperEulerFibreToRealQuotient_snd N m 𝒞 𝒬 ξ

/-- The geometric quotient fibre is formed by base changing the specialized
quotient to the algebraic closure of its cyclotomic ground field. -/
abbrev geometricCyclotomicRealEulerQuotientFibre
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) : Scheme :=
  pullback
    (GroupScheme.fieldPoint (cyclotomicField N)
      (AlgebraicClosure (cyclotomicField N))).hom
    (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ)

/-- Base change of the actual quotient map, before choosing a coefficient
field or a cohomology theory. -/
def geometricProperEulerFibreToRealQuotient
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    geometricSmoothProperEulerFibre N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ⟶
      geometricCyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ :=
  pullback.lift
    (pullback.fst _ _)
    (pullback.snd _ _ ≫ smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ) (by
      rw [Category.assoc,
        smoothProperEulerFibreToRealQuotient_overField]
      exact pullback.condition)

/-- The geometric quotient map fixes the algebraic-closure projection. -/
@[simp] theorem geometricProperEulerFibreToRealQuotient_fst
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The geometric quotient map has the original specialized quotient map
as its cyclotomic-fibre projection. -/
@[simp] theorem geometricProperEulerFibreToRealQuotient_snd
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ :=
  pullback.lift_snd _ _ _

end HilbertModularity.Hypergeometric
