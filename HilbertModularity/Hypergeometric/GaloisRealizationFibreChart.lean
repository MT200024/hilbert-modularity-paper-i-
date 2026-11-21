/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFamily
public import HilbertModularity.Hypergeometric.GaloisRealizationChartScheme

/-! # The affine Euler chart in a smooth proper fibre

The affine Euler scheme at a parameter is the fibre of the affine family.
Composing this fibre comparison with the chosen open immersion into the proper
family gives the actual chart map needed to compare the two reflections.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N]

private theorem affineSpecialization_overBase
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    EulerCover.affineFamilySpecialization
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t ≫
      EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m =
    EulerCover.structureMap N m t ≫
      EulerCover.puncturedParameterPoint
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        t ht h1t := by
  have h :
      pullback.fst
          (EulerCover.puncturedParameterPoint
            (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t)
          (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m) ≫
        EulerCover.puncturedParameterPoint
          (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t =
      pullback.snd
          (EulerCover.puncturedParameterPoint
            (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t)
          (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m) ≫
        EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m :=
    pullback.condition
  have h' := congrArg
    (fun f =>
      (EulerCover.affineFamilyFibreIso
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t).hom ≫ f) h
  simpa only [← Category.assoc,
    EulerCover.affineFamilyFibreIso_fst,
    EulerCover.affineFamilyFibreIso_snd] using h'.symm

/-- The branch-open affine Euler chart in the fibre of a smooth proper Euler
family. It is obtained from the actual family open immersion, not an unrelated
choice of affine model. -/
def smoothProperEulerFibreChartInclusion (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    EulerCover.affineScheme N m t ⟶
      smoothProperEulerFibre N m 𝒞 t ht h1t :=
  pullback.lift
    (EulerCover.affineFamilySpecialization
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
      N m t ht h1t ≫ 𝒞.affineInclusion)
    (EulerCover.structureMap N m t) (by
      rw [Category.assoc, 𝒞.affineInclusion_overBase]
      exact affineSpecialization_overBase N m t ht h1t)

/-- Projection of a proper Euler fibre to its ambient proper family. -/
@[expose] def smoothProperEulerFibreToCurve (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    smoothProperEulerFibre N m 𝒞 t ht h1t ⟶ 𝒞.curve :=
  pullback.fst _ _

@[simp] theorem smoothProperEulerFibreChartInclusion_fst
    (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t ≫
      smoothProperEulerFibreToCurve N m 𝒞 t ht h1t =
      EulerCover.affineFamilySpecialization
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t ≫ 𝒞.affineInclusion := by
  exact pullback.lift_fst _ _ _

@[simp] theorem smoothProperEulerFibreChartInclusion_snd
    (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t ≫
      smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t =
      EulerCover.structureMap N m t := by
  exact pullback.lift_snd _ _ _

/-- Specialization of a proper-family automorphism to a parameter fibre. -/
@[expose] def smoothProperEulerFibreAutomorphism (𝒞 : SmoothProperEulerFamily N m)
    (ι : Aut (Over.mk 𝒞.projection))
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    Aut (smoothProperEulerFibre N m 𝒞 t ht h1t) :=
  (Over.pullback (EulerCover.puncturedParameterPoint
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
      t ht h1t) ⋙
    Over.forget (Spec (CommRingCat.of (Cyclotomic.cyclotomicField N)))).mapIso ι

/-- The fibre automorphism is the base change of its family map. -/
theorem smoothProperEulerFibreAutomorphism_fst (𝒞 : SmoothProperEulerFamily N m)
    (ι : Aut (Over.mk 𝒞.projection))
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) :
    (smoothProperEulerFibreAutomorphism N m 𝒞 ι t ht h1t).hom ≫
      smoothProperEulerFibreToCurve N m 𝒞 t ht h1t =
    smoothProperEulerFibreToCurve N m 𝒞 t ht h1t ≫ ι.hom.left := by
  change ((Over.pullback (EulerCover.puncturedParameterPoint
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
      t ht h1t)).map ι.hom).left ≫
      pullback.fst 𝒞.projection
        (EulerCover.puncturedParameterPoint
          (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
          t ht h1t) =
    pullback.fst 𝒞.projection
      (EulerCover.puncturedParameterPoint
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        t ht h1t) ≫ ι.hom.left
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

end HilbertModularity.Hypergeometric
