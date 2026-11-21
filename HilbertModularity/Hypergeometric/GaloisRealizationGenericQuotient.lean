/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationGenericFibre
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotient

/-! # The selected real quotient over the Euler generic parameter

The maps in this module are base changes of the one chosen quotient family
and its reflection; they retain the original exponent and coefficient label.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)

/-- The selected real quotient family pulled back to the same cyclotomic
generic parameter. -/
@[expose] def genericSmoothProperRealEulerQuotientFibre : Scheme :=
  pullback 𝒬.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N) ≫
      puncturedCoefficientMap (realEulerCoefficientInclusion N))

/-- Its structure map over the cyclotomic parameter function field. -/
def genericSmoothProperRealEulerQuotientFibreStructureMap :
    genericSmoothProperRealEulerQuotientFibre N m 𝒞 𝒬 ⟶
      Spec (CommRingCat.of (EulerGenericParameterField N)) :=
  pullback.snd _ _

/-- The selected real quotient has a proper generic cyclotomic fibre. -/
theorem genericSmoothProperRealEulerQuotientFibre_isProper :
    IsProper (genericSmoothProperRealEulerQuotientFibreStructureMap N m 𝒞 𝒬) := by
  let : IsProper 𝒬.projection := 𝒬.isProper
  change IsProper (pullback.snd 𝒬.projection _)
  infer_instance

/-- The selected real quotient has a smooth generic cyclotomic fibre. -/
theorem genericSmoothProperRealEulerQuotientFibre_isSmooth :
    Smooth (genericSmoothProperRealEulerQuotientFibreStructureMap N m 𝒞 𝒬) := by
  let : Smooth 𝒬.projection := 𝒬.isSmooth
  change Smooth (pullback.snd 𝒬.projection _)
  infer_instance

/-- The generic cover map is induced by the original selected family map. -/
def genericSmoothProperEulerToRealQuotient :
    genericSmoothProperEulerFibre N m 𝒞 ⟶
      genericSmoothProperRealEulerQuotientFibre N m 𝒞 𝒬 :=
  pullback.lift
    (pullback.fst 𝒞.projection
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ≫
        𝒬.coverToQuotient ≫
        pullback.fst 𝒬.projection
          (puncturedCoefficientMap (realEulerCoefficientInclusion N)))
    (pullback.snd 𝒞.projection
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N))) (by
      dsimp [genericSmoothProperEulerFibre,
        genericSmoothProperRealEulerQuotientFibre]
      calc
        _ = pullback.fst 𝒞.projection _ ≫
              (𝒬.coverToQuotient ≫ pullback.snd _ _) ≫
                puncturedCoefficientMap (realEulerCoefficientInclusion N) := by
                  simp only [Category.assoc]
                  rw [pullback.condition]
        _ = (pullback.fst 𝒞.projection _ ≫ 𝒞.projection) ≫
              puncturedCoefficientMap (realEulerCoefficientInclusion N) := by
                rw [← Category.assoc, 𝒬.coverToQuotient_overBase]
        _ = (pullback.snd 𝒞.projection _ ≫
              ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ≫
                puncturedCoefficientMap (realEulerCoefficientInclusion N) := by
                  rw [pullback.condition]
        _ = pullback.snd 𝒞.projection _ ≫ _ := Category.assoc _ _ _)

/-- First projection of the generic map, retaining the one selected family
quotient morphism. -/
@[simp] theorem genericSmoothProperEulerToRealQuotient_fst :
    genericSmoothProperEulerToRealQuotient N m 𝒞 𝒬 ≫
      pullback.fst 𝒬.projection
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N) ≫
          puncturedCoefficientMap (realEulerCoefficientInclusion N)) =
    pullback.fst 𝒞.projection
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ≫
      𝒬.coverToQuotient ≫
        pullback.fst 𝒬.projection
          (puncturedCoefficientMap (realEulerCoefficientInclusion N)) := by
  exact pullback.lift_fst _ _ _

/-- The generic quotient map is a morphism over the same function field. -/
@[simp] theorem genericSmoothProperEulerToRealQuotient_overBase :
    genericSmoothProperEulerToRealQuotient N m 𝒞 𝒬 ≫
      genericSmoothProperRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 =
        genericSmoothProperEulerFibreStructureMap N m 𝒞 := by
  unfold genericSmoothProperEulerToRealQuotient
    genericSmoothProperRealEulerQuotientFibreStructureMap
  rw [genericSmoothProperEulerFibreStructureMap_eq]
  exact pullback.lift_snd _ _ _

/-- The family reflection acts on the selected generic Euler fibre.  It is
obtained by base change of the same automorphism used in the quotient family. -/
def genericSmoothProperEulerReflection :
    Aut (genericSmoothProperEulerFibre N m 𝒞) :=
  (Over.pullback
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ⋙
    Over.forget (Spec (CommRingCat.of (EulerGenericParameterField N)))).mapIso 𝒬.involution

/-- The generic reflection is the base change of the selected family
reflection on the proper Euler curve. -/
theorem genericSmoothProperEulerReflection_fst :
    (genericSmoothProperEulerReflection N m 𝒞 𝒬).hom ≫
      pullback.fst 𝒞.projection
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) =
    pullback.fst 𝒞.projection
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ≫
      𝒬.involution.hom.left := by
  dsimp [genericSmoothProperEulerFibre]
  change ((Over.pullback
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N))).map
        𝒬.involution.hom).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ 𝒬.involution.hom.left
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- The generic reflection fixes the function-field coordinate. -/
theorem genericSmoothProperEulerReflection_snd :
    (genericSmoothProperEulerReflection N m 𝒞 𝒬).hom ≫
      genericSmoothProperEulerFibreStructureMap N m 𝒞 =
    genericSmoothProperEulerFibreStructureMap N m 𝒞 := by
  unfold genericSmoothProperEulerReflection
  rw [genericSmoothProperEulerFibreStructureMap_eq]
  exact ((Over.pullback
    (ProjectiveLine.puncturedRationalPoint
      (Cyclotomic.cyclotomicField N))).map 𝒬.involution.hom).w

/-- The generic reflection remains an involution because it is the base
change of the one selected family reflection. -/
theorem genericSmoothProperEulerReflection_sq :
    (genericSmoothProperEulerReflection N m 𝒞 𝒬).hom ≫
      (genericSmoothProperEulerReflection N m 𝒞 𝒬).hom = 𝟙 _ := by
  let F := Over.pullback
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ⋙
    Over.forget (Spec (CommRingCat.of (EulerGenericParameterField N)))
  have h := congrArg Iso.hom 𝒬.involution_sq
  change 𝒬.involution.hom ≫ 𝒬.involution.hom = 𝟙 _ at h
  change F.map 𝒬.involution.hom ≫ F.map 𝒬.involution.hom = 𝟙 _
  calc
    _ = F.map (𝒬.involution.hom ≫ 𝒬.involution.hom) :=
      (F.map_comp _ _).symm
    _ = F.map (𝟙 _) := congrArg F.map h
    _ = 𝟙 _ := F.map_id _

/-- The selected generic quotient map is invariant under its actual family
reflection.  This is a base-change identity, independent of any assertion
that the generic quotient has finite orbit fibres. -/
theorem genericSmoothProperEulerToRealQuotient_invariant :
    (genericSmoothProperEulerReflection N m 𝒞 𝒬).hom ≫
      genericSmoothProperEulerToRealQuotient N m 𝒞 𝒬 =
    genericSmoothProperEulerToRealQuotient N m 𝒞 𝒬 := by
  let a := (genericSmoothProperEulerReflection N m 𝒞 𝒬).hom
  let q := genericSmoothProperEulerToRealQuotient N m 𝒞 𝒬
  let c : genericSmoothProperEulerFibre N m 𝒞 ⟶ 𝒞.curve := pullback.fst 𝒞.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N))
  let d := pullback.fst 𝒬.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N) ≫
      puncturedCoefficientMap (realEulerCoefficientInclusion N))
  let e := pullback.snd 𝒬.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N) ≫
      puncturedCoefficientMap (realEulerCoefficientInclusion N))
  have hq : q ≫ d = c ≫ 𝒬.coverToQuotient ≫
      pullback.fst 𝒬.projection
        (puncturedCoefficientMap (realEulerCoefficientInclusion N)) :=
    genericSmoothProperEulerToRealQuotient_fst N m 𝒞 𝒬
  have hqs : q ≫ e = genericSmoothProperEulerFibreStructureMap N m 𝒞 :=
    genericSmoothProperEulerToRealQuotient_overBase N m 𝒞 𝒬
  have ha : a ≫ c = c ≫ 𝒬.involution.hom.left :=
    genericSmoothProperEulerReflection_fst N m 𝒞 𝒬
  have has : a ≫ genericSmoothProperEulerFibreStructureMap N m 𝒞 =
      genericSmoothProperEulerFibreStructureMap N m 𝒞 :=
    genericSmoothProperEulerReflection_snd N m 𝒞 𝒬
  have hc : a ≫ (c ≫ 𝒬.coverToQuotient) = c ≫ 𝒬.coverToQuotient := by
    calc
      _ = (a ≫ c) ≫ 𝒬.coverToQuotient := (Category.assoc _ _ _).symm
      _ = (c ≫ 𝒬.involution.hom.left) ≫ 𝒬.coverToQuotient := by rw [ha]
      _ = c ≫ (𝒬.involution.hom.left ≫ 𝒬.coverToQuotient) := Category.assoc _ _ _
      _ = c ≫ 𝒬.coverToQuotient := by rw [𝒬.coverToQuotient_invariant]
  apply pullback.hom_ext
  · change (a ≫ q) ≫ d = q ≫ d
    calc
      (a ≫ q) ≫ d = a ≫ (q ≫ d) := Category.assoc _ _ _
      _ = a ≫ (c ≫ (𝒬.coverToQuotient ≫
            pullback.fst 𝒬.projection
              (puncturedCoefficientMap (realEulerCoefficientInclusion N)))) := by
          rw [hq]
      _ = (a ≫ (c ≫ 𝒬.coverToQuotient)) ≫
            pullback.fst 𝒬.projection
              (puncturedCoefficientMap (realEulerCoefficientInclusion N)) := by
          simp only [Category.assoc]
      _ = (c ≫ 𝒬.coverToQuotient) ≫
            pullback.fst 𝒬.projection
              (puncturedCoefficientMap (realEulerCoefficientInclusion N)) := by rw [hc]
      _ = q ≫ d := by rw [hq]; simp only [Category.assoc]
  · change (a ≫ q) ≫ e = q ≫ e
    calc
      (a ≫ q) ≫ e = a ≫ (q ≫ e) := Category.assoc _ _ _
      _ = a ≫ genericSmoothProperEulerFibreStructureMap N m 𝒞 := by rw [hqs]
      _ = genericSmoothProperEulerFibreStructureMap N m 𝒞 := has
      _ = q ≫ e := hqs.symm

end HilbertModularity.Hypergeometric
