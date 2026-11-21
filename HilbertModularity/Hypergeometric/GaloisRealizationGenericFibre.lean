/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFamily
public import HilbertModularity.Geometry.ProjectiveLine.RationalCoordinate
public import HilbertModularity.Hypergeometric.EulerCover.Integrality

/-! # The generic fibre of the selected Euler family

The generic parameter is the function field of the actual punctured cyclotomic
line. Base change preserves the selected family's smoothness, properness and
open chart. The chart is geometrically integral for coprime exponents, using
the explicit Euler equation of [GPRV, Definition 8.2].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric

theorem rationalParameter_isUnit (K : Type*) [Field K] :
    IsUnit (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) := by
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne
      Polynomial.X_ne_zero

theorem one_sub_rationalParameter_isUnit (K : Type*) [Field K] :
    IsUnit (1 - algebraMap (Polynomial K) (RatFunc K) Polynomial.X) := by
  apply isUnit_iff_ne_zero.mpr
  have h : (1 : Polynomial K) - Polynomial.X ≠ 0 := by
    intro heq
    have heq' := congrArg (Polynomial.eval (0 : K)) heq
    simp at heq'
  simpa only [map_sub, map_one, map_zero] using
    (IsFractionRing.injective (Polynomial K) (RatFunc K)).ne h

/-- The rational-coordinate point is the evaluation point used by the actual
Euler-family specialization, at its transcendental parameter. -/
theorem puncturedRationalPoint_eq_eulerParameterPoint (K : Type*) [Field K] :
    ProjectiveLine.puncturedRationalPoint K =
      EulerCover.puncturedParameterPoint K (RatFunc K)
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
        (rationalParameter_isUnit K) (one_sub_rationalParameter_isUnit K) := by
  have hh : ProjectiveLine.puncturedCoordinatesToRatFunc K =
      EulerCover.parameterEval K
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
        (rationalParameter_isUnit K) (one_sub_rationalParameter_isUnit K) := by
    apply IsLocalization.ringHom_ext
      (M := Submonoid.powers ((Polynomial.X : Polynomial K) * (Polynomial.X - 1)))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, EulerCover.parameterEval_algebraMap,
        ProjectiveLine.puncturedCoordinatesToRatFunc_algebraMap,
        Polynomial.eval₂_C]
      rfl
    · simp only [RingHom.comp_apply, EulerCover.parameterEval_algebraMap,
        ProjectiveLine.puncturedCoordinatesToRatFunc_algebraMap,
        Polynomial.eval₂_X]
  unfold ProjectiveLine.puncturedRationalPoint EulerCover.puncturedParameterPoint
  rw [hh]

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)

/-- Function field of the actual punctured cyclotomic parameter line. -/
abbrev EulerGenericParameterField :=
  RatFunc (Cyclotomic.cyclotomicField N)

omit [NeZero N] in
/-- A nonzero exponent below a prime denominator is coprime to that denominator.
This discharges the exact hypothesis of the affine Euler integrality theorem. -/
theorem eulerExponent_coprime_of_prime (hN : N.Prime)
    (hmPos : 0 < m) (hmN : m < N) : m.Coprime N := by
  apply Nat.Coprime.symm
  apply hN.coprime_iff_not_dvd.mpr
  intro h
  have hle := Nat.le_of_dvd hmPos h
  omega

/-- The generic fibre of the selected smooth proper exponent-`m` Euler family. -/
@[expose] def genericSmoothProperEulerFibre : Scheme :=
  pullback 𝒞.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N))

/-- Its structure map to the function field of the parameter line. -/
def genericSmoothProperEulerFibreStructureMap :
    genericSmoothProperEulerFibre N m 𝒞 ⟶
      Spec (CommRingCat.of (EulerGenericParameterField N)) :=
  pullback.snd _ _

/-- The chosen generic-fibre structure map is the second projection of its
defining base change. -/
@[simp] theorem genericSmoothProperEulerFibreStructureMap_eq :
    genericSmoothProperEulerFibreStructureMap N m 𝒞 =
      pullback.snd 𝒞.projection
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) :=
  (rfl)

/-- The generic fibre of the *actual* affine Euler family, with its inherited
parameter map.  This is the branch-open chart of the selected proper fibre. -/
@[expose] def genericAffineEulerFibre : Scheme :=
  pullback
    (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m)
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N))

/-- The affine generic chart enters the selected proper generic fibre by
base change of the chosen family open immersion. -/
def genericAffineEulerFibreInclusion :
    genericAffineEulerFibre N m ⟶ genericSmoothProperEulerFibre N m 𝒞 :=
  pullback.lift
    (pullback.fst
      (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m)
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ≫
        𝒞.affineInclusion)
    (pullback.snd
      (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m)
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N))) (by
      dsimp [genericAffineEulerFibre, genericSmoothProperEulerFibre]
      rw [Category.assoc, 𝒞.affineInclusion_overBase]
      exact pullback.condition)

/-- The affine generic chart retains the original family open immersion. -/
@[simp] theorem genericAffineEulerFibreInclusion_fst :
    genericAffineEulerFibreInclusion N m 𝒞 ≫
      pullback.fst 𝒞.projection
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) =
      pullback.fst
        (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m)
        (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) ≫
          𝒞.affineInclusion := by
  exact pullback.lift_fst _ _ _

/-- The affine chart and proper fibre have the same generic parameter. -/
@[simp] theorem genericAffineEulerFibreInclusion_snd :
    genericAffineEulerFibreInclusion N m 𝒞 ≫
      genericSmoothProperEulerFibreStructureMap N m 𝒞 =
    pullback.snd
      (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m)
      (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)) := by
  exact pullback.lift_snd _ _ _

/-- The actual affine Euler chart remains an open subcurve after passage to
the generic parameter. -/
theorem genericAffineEulerFibreInclusion_isOpenImmersion :
    IsOpenImmersion (genericAffineEulerFibreInclusion N m 𝒞) := by
  let b := ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)
  let f := EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m
  let i := 𝒞.affineInclusion
  have e₁ : f ≫ (𝟙 _) = i ≫ 𝒞.projection := by
    simpa only [f, i, Category.comp_id] using 𝒞.affineInclusion_overBase.symm
  have e₂ : b ≫ (𝟙 _) = (𝟙 _) ≫ b := by simp
  let j := pullback.map f b 𝒞.projection b i (𝟙 _) (𝟙 _) e₁ e₂
  have hj : j = genericAffineEulerFibreInclusion N m 𝒞 := by
    apply pullback.hom_ext
    · rfl
    · rfl
  have : IsOpenImmersion i := 𝒞.affineInclusion_isOpenImmersion
  have : IsOpenImmersion
      (𝟙 (Spec (CommRingCat.of (EulerGenericParameterField N)))) := inferInstance
  have : Mono (𝟙 (ProjectiveLine.punctured (Cyclotomic.cyclotomicField N))) := inferInstance
  have : IsOpenImmersion j :=
    Scheme.pullback_map_isOpenImmersion f b 𝒞.projection b i (𝟙 _) (𝟙 _) e₁ e₂
  exact hj ▸ (inferInstance : IsOpenImmersion j)

/-- The generic affine chart is the specialization of the *actual* Euler
family at the transcendental parameter.  The family-fibre comparison is
written in the opposite pullback order, hence the symmetry isomorphism. -/
def genericAffineEulerFibreIso :
    EulerCover.affineScheme N m
      (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
        (EulerGenericParameterField N) Polynomial.X) ≅
      genericAffineEulerFibre N m :=
  (EulerCover.affineFamilyFibreIso
    (Cyclotomic.cyclotomicField N) (EulerGenericParameterField N)
    N m _ (rationalParameter_isUnit _) (one_sub_rationalParameter_isUnit _)) ≪≫
    (pullbackSymmetry _ _).symm ≪≫
      eqToIso (by
        unfold genericAffineEulerFibre
        exact congrArg (fun g : Spec (CommRingCat.of (EulerGenericParameterField N)) ⟶
            ProjectiveLine.punctured (Cyclotomic.cyclotomicField N) =>
          pullback (EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m) g)
          (puncturedRationalPoint_eq_eulerParameterPoint
            (Cyclotomic.cyclotomicField N)).symm)

/-- The actual Euler chart over the generic parameter is integral for
coprime exponents in the manuscript range. -/
theorem genericEulerAffineScheme_isIntegral_of_coprime
    (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N) :
    IsIntegral (EulerCover.affineScheme N m
      (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
        (EulerGenericParameterField N) Polynomial.X)) := by
  let : IsDomain (EulerCover.CoverRing N m
      (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
        (EulerGenericParameterField N) Polynomial.X)) :=
    EulerCover.coverRing_isDomain N m _ (NeZero.ne N) hmPos hmN hcop
  change IsIntegral (Spec (CommRingCat.of (EulerCover.CoverRing N m _)))
  infer_instance

/-- Prime-denominator specialization of generic affine integrality. -/
theorem genericEulerAffineScheme_isIntegral (hN : N.Prime)
    (hmPos : 0 < m) (hmN : m < N) :
    IsIntegral (EulerCover.affineScheme N m
      (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
        (EulerGenericParameterField N) Polynomial.X)) := by
  exact genericEulerAffineScheme_isIntegral_of_coprime N m hmPos hmN
    (eulerExponent_coprime_of_prime N m hN hmPos hmN)

/-- The coordinate ring of the actual generic Euler chart stays a domain
after every extension of its parameter function field. This uses the selected
chart's equation, without identifying an unrelated curve with the fibre. -/
theorem genericEulerAffineCoverRing_scalarExtension_isDomain_of_coprime
    (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (E : Type*) [Field E] [Algebra (EulerGenericParameterField N) E] :
    IsDomain (E ⊗[EulerGenericParameterField N]
      EulerCover.CoverRing N m
        (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
          (EulerGenericParameterField N) Polynomial.X)) := by
  exact EulerCover.coverRing_scalarExtension_isDomain N m _ (NeZero.ne N)
    hmPos hmN hcop E

/-- Prime-denominator specialization of the scalar-extension domain theorem. -/
theorem genericEulerAffineCoverRing_scalarExtension_isDomain
    (hN : N.Prime) (hmPos : 0 < m) (hmN : m < N)
    (E : Type*) [Field E] [Algebra (EulerGenericParameterField N) E] :
    IsDomain (E ⊗[EulerGenericParameterField N]
      EulerCover.CoverRing N m
        (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
          (EulerGenericParameterField N) Polynomial.X)) := by
  exact genericEulerAffineCoverRing_scalarExtension_isDomain_of_coprime N m
    hmPos hmN (eulerExponent_coprime_of_prime N m hN hmPos hmN) E

/-- The branch-open chart of the selected generic proper Euler fibre is
integral, by the actual family-fibre comparison. -/
theorem genericAffineEulerFibre_isIntegral_of_coprime
    (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N) :
    IsIntegral (genericAffineEulerFibre N m) := by
  let : IsIntegral (EulerCover.affineScheme N m
      (algebraMap (Polynomial (Cyclotomic.cyclotomicField N))
        (EulerGenericParameterField N) Polynomial.X)) :=
    genericEulerAffineScheme_isIntegral_of_coprime N m hmPos hmN hcop
  exact IsIntegral.of_isIso (genericAffineEulerFibreIso N m).hom

/-- Prime-denominator specialization for the branch-open generic fibre. -/
theorem genericAffineEulerFibre_isIntegral (hN : N.Prime)
    (hmPos : 0 < m) (hmN : m < N) :
    IsIntegral (genericAffineEulerFibre N m) := by
  exact genericAffineEulerFibre_isIntegral_of_coprime N m hmPos hmN
    (eulerExponent_coprime_of_prime N m hN hmPos hmN)

/-- Properness survives passage from the chosen family to its generic fibre. -/
theorem genericSmoothProperEulerFibre_isProper :
    IsProper (genericSmoothProperEulerFibreStructureMap N m 𝒞) := by
  let : IsProper 𝒞.projection := 𝒞.isProper
  change IsProper (pullback.snd 𝒞.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)))
  infer_instance

/-- Smoothness survives passage from the chosen family to its generic fibre. -/
theorem genericSmoothProperEulerFibre_isSmooth :
    Smooth (genericSmoothProperEulerFibreStructureMap N m 𝒞) := by
  let : Smooth 𝒞.projection := 𝒞.isSmooth
  change Smooth (pullback.snd 𝒞.projection
    (ProjectiveLine.puncturedRationalPoint (Cyclotomic.cyclotomicField N)))
  infer_instance

end HilbertModularity.Hypergeometric
