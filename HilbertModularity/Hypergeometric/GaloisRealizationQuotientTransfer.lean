/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientFibreMap
public import HilbertModularity.Hypergeometric.GaloisRealizationProper
public import HilbertModularity.Hypergeometric.GaloisRealizationMorphismPullback

/-! # Pullback and transfer for the geometric Euler quotient

The quotient map is the specialization of the one geometric quotient family.
The cohomological maps below are attached to that map, rather than chosen
independently with each Galois representation.  [GPRV, Proposition 9.5 and
proof of Theorem 9.2, equation (76)] give the reflection/deck relation used
to construct the real cyclotomic action.  The degree-two pullback/transfer
identities are the standard cohomological quotient comparison in this case.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HilbertModularity.Cyclotomic
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric

/-- The chosen primitive deck transformation is the root defining the actual
cyclotomic field.  It is the deck operator used in [GPRV, equation (76)]. -/
def cyclotomicDeckGenerator (N : ℕ) [NeZero N] :
    rootsOfUnity N (cyclotomicField N) :=
  (Cyclotomic.root_isPrimitiveRoot N).toRootsOfUnity

@[simp] theorem cyclotomicDeckGenerator_coe (N : ℕ) [NeZero N] :
    ((cyclotomicDeckGenerator N : (cyclotomicField N)ˣ) : cyclotomicField N) =
      root N := by
  exact (Cyclotomic.root_isPrimitiveRoot N).val_toRootsOfUnity_coe

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

/-- Cohomology of the base change of the chosen real quotient fibre to the
cyclotomic algebraic closure.  This uses the actual specialized quotient
scheme and precedes any choice of coefficient label. -/
abbrev GeometricCyclotomicRealEulerQuotientCohomology
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] : Type _ :=
  L ⊗[ℚ_[ℓ]]
    (geometricCyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ).RationalEllAdicCohomology ℓ 1

/-- Arithmetic Galois on the cyclotomic base change of the same quotient
fibre.  This is the action to which restriction from the real field must
compare. -/
def geometricCyclotomicRealEulerQuotientGaloisRepresentation
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    Representation L
      (AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
        AlgebraicClosure (cyclotomicField N))
      (GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :=
  Representation.baseChange L
    (Representation.baseChange ℚ_[ℓ]
      (Scheme.ellAdicCohomologyGaloisRepresentation
        (cyclotomicField N)
        (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ) ℓ 1))

/-- The reflection on the proper geometric Euler fibre is the base change of
the chosen quotient involution, which restricts to the explicit affine chart
reflection. -/
def geometricProperEulerQuotientReflectionIso :
    geometricSmoothProperEulerFibre N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ≅
      geometricSmoothProperEulerFibre N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) :=
  Scheme.baseChangedIso
    (smoothProperEulerFibreStructureMap N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))
    (GroupScheme.fieldPoint (cyclotomicField N)
      (AlgebraicClosure (cyclotomicField N))).hom
    (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))
    (smoothProperEulerFibreAutomorphism_snd N m 𝒞 𝒬.involution ξ)

/-- The geometric reflection fixes the algebraic-closure coordinate of the
selected proper Euler fibre. -/
theorem geometricProperEulerQuotientReflectionIso_fst :
    (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
        pullback.fst
          (GroupScheme.fieldPoint (cyclotomicField N)
            (AlgebraicClosure (cyclotomicField N))).hom
          (smoothProperEulerFibreStructureMap N m 𝒞
            (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
            (one_sub_realEulerParameter_isUnit N ξ)) =
      pullback.fst _ _ :=
  Scheme.baseChangedIso_fst _ _ _ _

/-- The second projection of the geometric reflection is the involution on
the same selected proper fibre. -/
theorem geometricProperEulerQuotientReflectionIso_snd :
    (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
        pullback.snd
          (GroupScheme.fieldPoint (cyclotomicField N)
            (AlgebraicClosure (cyclotomicField N))).hom
          (smoothProperEulerFibreStructureMap N m 𝒞
            (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
            (one_sub_realEulerParameter_isUnit N ξ)) =
      pullback.snd _ _ ≫
        (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ)).hom :=
  Scheme.baseChangedIso_snd _ _ _ _

/-- The geometric quotient map is invariant under the base change of the
same reflection that fixes the specialized quotient map. -/
theorem geometricProperEulerFibreToRealQuotient_invariant :
    (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
      geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ =
    geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ := by
  apply pullback.hom_ext
  · simp only [Category.assoc,
      geometricProperEulerFibreToRealQuotient_fst]
    exact Scheme.baseChangedIso_fst _ _ _ _
  · simp only [Category.assoc,
      geometricProperEulerFibreToRealQuotient_snd]
    rw [← Category.assoc,
      show (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
          pullback.snd _ _ = pullback.snd _ _ ≫
            (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
              (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
              (one_sub_realEulerParameter_isUnit N ξ)).hom from
        Scheme.baseChangedIso_snd _ _ _ _,
      Category.assoc, smoothProperEulerFibreToRealQuotient_invariant]

/-- The actual reflection pullback on coefficient-extended cohomology. -/
def geometricProperEulerCoefficientReflection
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    Module.End L (GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :=
  (Representation.baseChange L (Representation.baseChange ℚ_[ℓ]
    ((geometricSmoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).ellAdicCohomologyAutRepresentation
        ℓ 1)))
    (MulOpposite.op (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ))

/-- The coefficient reflection is pullback by the selected geometric
reflection, in the same cohomology representation as the deck action. -/
theorem geometricProperEulerCoefficientReflection_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L =
      (Representation.baseChange L (Representation.baseChange ℚ_[ℓ]
        ((geometricSmoothProperEulerFibre N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ)).ellAdicCohomologyAutRepresentation
          ℓ 1)))
        (MulOpposite.op (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ)) :=
  (rfl)

/-- The chosen family reflection remains an involution on the selected
geometric fibre.  Both base changes use the same family automorphism. -/
theorem geometricProperEulerQuotientReflectionIso_sq :
    geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ ≪≫
      geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ = Iso.refl _ := by
  let t := realEulerParameter N ξ
  let ht := realEulerParameter_isUnit N ξ
  let h1t := one_sub_realEulerParameter_isUnit N ξ
  let F := Over.pullback (EulerCover.puncturedParameterPoint
      (cyclotomicField N) (cyclotomicField N) t ht h1t) ⋙
    Over.forget (Spec (CommRingCat.of (cyclotomicField N)))
  have hfamily := congrArg Iso.hom 𝒬.involution_sq
  have hfamilyHom : 𝒬.involution.hom ≫ 𝒬.involution.hom = 𝟙 _ := by
    change 𝒬.involution.hom ≫ 𝒬.involution.hom = 𝟙 _ at hfamily
    exact hfamily
  have hinnerHom :
      (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom ≫
        (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom =
          𝟙 _ := by
    have hmap := congrArg (fun f => F.map f) hfamilyHom
    change F.map 𝒬.involution.hom ≫ F.map 𝒬.involution.hom = 𝟙 _
    simpa using hmap
  have hf :
      (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
        pullback.fst _ _ = pullback.fst _ _ :=
    Scheme.baseChangedIso_fst _ _ _ _
  have hs :
      (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ).hom ≫
        pullback.snd _ _ = pullback.snd _ _ ≫
          (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom :=
    Scheme.baseChangedIso_snd _ _ _ _
  apply Iso.ext
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, Iso.refl_hom]
    rw [Category.assoc, hf, hf, Category.id_comp]
  · simp only [Iso.trans_hom, Iso.refl_hom]
    rw [Category.assoc, hs, ← Category.assoc, hs, Category.assoc,
      hinnerHom, Category.comp_id, Category.id_comp]

/-- Cohomological reflection squares to the identity on the actual proper
Euler fibre; this is a consequence of the family involution law. -/
theorem geometricProperEulerCoefficientReflection_sq
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (v : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
      (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v) = v := by
  let e : Aut (geometricSmoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)) :=
    geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ
  let R := Representation.baseChange L (Representation.baseChange ℚ_[ℓ]
    ((geometricSmoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).ellAdicCohomologyAutRepresentation
        ℓ 1))
  have he : (MulOpposite.op e) * (MulOpposite.op e) = 1 := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    change e.hom ≫ e.hom = 𝟙 _
    have h := congrArg Iso.hom
      (geometricProperEulerQuotientReflectionIso_sq N m 𝒞 𝒬 ξ)
    change e.hom ≫ e.hom = 𝟙 _ at h
    exact h
  change R (MulOpposite.op e) (R (MulOpposite.op e) v) = v
  change (R (MulOpposite.op e) * R (MulOpposite.op e)) v = v
  rw [← map_mul, he, map_one]
  simp

/-- The selected proper-fibre reflection is defined over the cyclotomic
ground field.  Its cohomological action therefore commutes with cyclotomic
Galois on the same geometric fibre. -/
theorem geometricProperEulerCoefficientReflection_comm_galois
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (cyclotomicField N))
    (v : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
      (geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g v) =
      geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
          (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v) := by
  let p := smoothProperEulerFibreStructureMap N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)
  let f := smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ)
  let e := geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ
  let a := (Scheme.fieldBaseChangeGaloisAut (cyclotomicField N)
    (AlgebraicClosure (cyclotomicField N)) p g).unop
  have h0 : (Scheme.ellAdicCohomologyLinearEquiv e ℓ 1).toLinearMap.comp
        (Scheme.ellAdicCohomologyLinearEquiv a ℓ 1).toLinearMap =
      (Scheme.ellAdicCohomologyLinearEquiv a ℓ 1).toLinearMap.comp
        (Scheme.ellAdicCohomologyLinearEquiv e ℓ 1).toLinearMap := by
    ext x
    exact Scheme.ellAdicCohomologyEquiv_baseChangedIso_comm_galois
      (cyclotomicField N) (AlgebraicClosure (cyclotomicField N)) p f
      (smoothProperEulerFibreAutomorphism_snd N m 𝒞 𝒬.involution ξ)
      g ℓ 1 x
  have hL := congrArg
    (fun u => LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] u)) h0
  simp only [LinearMap.baseChange_comp] at hL
  have he : geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L =
      LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
        (Scheme.ellAdicCohomologyLinearEquiv e ℓ 1).toLinearMap) := (rfl)
  have ha : geometricProperEulerGaloisRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L g =
      LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
        (Scheme.ellAdicCohomologyLinearEquiv a ℓ 1).toLinearMap) := by
    rw [geometricProperEulerGaloisRepresentation_eq]
    rfl
  rw [he, ha]
  exact congrArg (fun u : _ →ₗ[L] _ => u v) hL

/-- Pullback on coefficient-extended degree-one cohomology along the
specialization of the *chosen* Euler quotient morphism.  The integral map
is the standard functorial cohomological pullback, before either coefficient
extension. -/
def geometricProperEulerQuotientCohomologyPullback
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L →ₗ[L]
      GeometricProperEulerCohomology N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L :=
  LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
    ((Scheme.ellAdicCohomologyMorphismPullback ℓ).map
      (geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ)))

/-- Galois acts on the algebraic-closure factor of both selected fibres.
The chosen quotient morphism acts on their cyclotomic-fibre factor, so the
resulting square of actual schemes commutes. -/
theorem geometricProperEulerFibreToRealQuotient_comm_galois
    (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (cyclotomicField N)) :
    geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ ≫
        (Scheme.fieldBaseChangeGaloisAut (cyclotomicField N)
          (AlgebraicClosure (cyclotomicField N))
          (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ) g).unop.hom =
      (Scheme.fieldBaseChangeGaloisAut (cyclotomicField N)
          (AlgebraicClosure (cyclotomicField N))
          (smoothProperEulerFibreStructureMap N m 𝒞
            (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
            (one_sub_realEulerParameter_isUnit N ξ)) g).unop.hom ≫
        geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Scheme.fieldBaseChangeGaloisAut_fst,
      geometricProperEulerFibreToRealQuotient_fst]
    exact (Category.assoc _ _ _).symm.trans (congrArg
      (fun f => f ≫ Spec.map (CommRingCat.ofHom g.toRingEquiv.toRingHom))
      (geometricProperEulerFibreToRealQuotient_fst N m 𝒞 𝒬 ξ))
  · simp only [Category.assoc, Scheme.fieldBaseChangeGaloisAut_snd,
      geometricProperEulerFibreToRealQuotient_snd]
    simp only [← Category.assoc, Scheme.fieldBaseChangeGaloisAut_snd]

/-- Pullback for the selected quotient map commutes with the actual
cyclotomic-field Galois actions.  This follows from the preceding square
and functoriality of the standard cohomological pullback. -/
theorem geometricProperEulerQuotientCohomologyPullback_galois
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (cyclotomicField N))
    (v : GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :
    geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L
      (geometricCyclotomicRealEulerQuotientGaloisRepresentation
        N m 𝒞 𝒬 ξ ℓ L g v) =
    geometricProperEulerGaloisRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
        (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v) := by
  let U := Scheme.ellAdicCohomologyMorphismPullback ℓ
  let q := geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ
  let a := (Scheme.fieldBaseChangeGaloisAut (cyclotomicField N)
    (AlgebraicClosure (cyclotomicField N))
    (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ) g).unop
  let b := (Scheme.fieldBaseChangeGaloisAut (cyclotomicField N)
    (AlgebraicClosure (cyclotomicField N))
    (smoothProperEulerFibreStructureMap N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)) g).unop
  have hs : q ≫ a.hom = b.hom ≫ q :=
    geometricProperEulerFibreToRealQuotient_comm_galois N m 𝒞 𝒬 ξ g
  have h0 : (U.map q).comp
        (Scheme.ellAdicCohomologyLinearEquiv a ℓ 1).toLinearMap =
          (Scheme.ellAdicCohomologyLinearEquiv b ℓ 1).toLinearMap.comp
            (U.map q) := by
    rw [← U.map_iso a, ← U.map_iso b,
      ← U.map_comp q a.hom, ← U.map_comp b.hom q, hs]
  have h1 := congrArg
    (fun f => LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] f)) h0
  dsimp only [U, q] at h1
  simp only [LinearMap.baseChange_comp] at h1
  have ha : geometricCyclotomicRealEulerQuotientGaloisRepresentation
      N m 𝒞 𝒬 ξ ℓ L g =
      LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
        (Scheme.ellAdicCohomologyLinearEquiv a ℓ 1).toLinearMap) := (rfl)
  have hb : geometricProperEulerGaloisRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L g =
      LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
        (Scheme.ellAdicCohomologyLinearEquiv b ℓ 1).toLinearMap) := by
    rw [geometricProperEulerGaloisRepresentation_eq]
    rfl
  rw [ha, hb]
  simpa only [geometricProperEulerQuotientCohomologyPullback, LinearMap.comp_apply] using
    congrArg (fun f : _ →ₗ[L] _ => f v) h1

/-- The specialized quotient morphism is reflection invariant, hence its
actual cohomological pullback lands in the reflection-fixed subspace.  This
uses functoriality and the proved equality of scheme morphisms. -/
theorem geometricProperEulerQuotientCohomologyPullback_reflection
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L).comp
        (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L) =
      geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L := by
  let U := Scheme.ellAdicCohomologyMorphismPullback ℓ
  let e := geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ
  let q := geometricProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ
  have hinv : e.hom ≫ q = q :=
    geometricProperEulerFibreToRealQuotient_invariant N m 𝒞 𝒬 ξ
  have h0 : (Scheme.ellAdicCohomologyLinearEquiv e ℓ 1).toLinearMap.comp
      (U.map q) = U.map q := by
    rw [← U.map_iso e, ← U.map_comp e.hom q, hinv]
  have h1 := congrArg
    (fun f => LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ] f)) h0
  dsimp only [U, e, q] at h1
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h1
  have hrepr :
      geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L =
        LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
          (Scheme.ellAdicCohomologyLinearEquiv
            (geometricProperEulerQuotientReflectionIso N m 𝒞 𝒬 ξ) ℓ 1).toLinearMap) := by
    rfl
  rw [hrepr]
  exact h1

/-- The reflection-fixed part of the cohomology of the actual proper Euler
fibre.  This is formed from the selected geometric reflection, before any
transfer map is supplied. -/
def geometricProperEulerReflectionFixed
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    Submodule L (GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) where
  carrier := {v | geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [map_add, hv, hw]
  smul_mem' := by
    intro a v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [map_smul, hv]

/-- Pullback along the selected quotient map, with its proved reflection
invariance recorded in the codomain. -/
def geometricProperEulerQuotientPullbackFixed
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L →ₗ[L]
      geometricProperEulerReflectionFixed N m 𝒞 𝒬 ξ ℓ L :=
  (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L).codRestrict
    (geometricProperEulerReflectionFixed N m 𝒞 𝒬 ξ ℓ L) (by
      intro v
      change geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
        (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v) = _
      exact congrArg (fun f : _ →ₗ[L] _ => f v)
        (geometricProperEulerQuotientCohomologyPullback_reflection
          N m 𝒞 𝒬 ξ ℓ L))

/-- The sum of the identity and the chosen reflection lands in the fixed
part when the geometric reflection squares to the identity. -/
def geometricProperEulerReflectionSum
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    GeometricProperEulerCohomology N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L →ₗ[L]
      geometricProperEulerReflectionFixed N m 𝒞 𝒬 ξ ℓ L :=
  (LinearMap.id + geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L).codRestrict
    (geometricProperEulerReflectionFixed N m 𝒞 𝒬 ξ ℓ L) (by
      intro v
      change geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
        (v + geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v) = _
      rw [map_add, geometricProperEulerCoefficientReflection_sq]
      exact add_comm _ _)

/-- The degree-two transfer is forced by pullback onto invariant cohomology:
it is the inverse pullback applied to `1 + reflection`.  This construction
keeps transfer attached to the actual specialized quotient map. -/
def geometricProperEulerTransferOfInvariantPullback
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (hbij : Function.Bijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L)) :
    GeometricProperEulerCohomology N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L →ₗ[L]
      GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L :=
  (LinearEquiv.ofBijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L) hbij).symm.toLinearMap.comp
    (geometricProperEulerReflectionSum N m 𝒞 𝒬 ξ ℓ L)

/-- The transfer constructed from invariant pullback satisfies the
push–pull identity for the chosen proper quotient map. -/
theorem geometricProperEulerTransferOfInvariantPullback_pullback_transfer
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (hbij : Function.Bijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L))
    (v : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L
      (geometricProperEulerTransferOfInvariantPullback N m 𝒞 𝒬 ξ ℓ L hbij v) =
    v + geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v := by
  let p := geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L
  let a := geometricProperEulerReflectionSum N m 𝒞 𝒬 ξ ℓ L
  let e := LinearEquiv.ofBijective p hbij
  have h := e.apply_symm_apply (a v)
  exact congrArg Subtype.val h

/-- The reverse push–pull identity, including at residue characteristic two:
the coefficient field has characteristic zero, so no division by two occurs
in this proof. -/
theorem geometricProperEulerTransferOfInvariantPullback_transfer_pullback
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (hbij : Function.Bijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L))
    (v : GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :
    geometricProperEulerTransferOfInvariantPullback N m 𝒞 𝒬 ξ ℓ L hbij
      (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v) =
      (2 : L) • v := by
  apply hbij.1
  apply Subtype.ext
  change geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L
    (geometricProperEulerTransferOfInvariantPullback N m 𝒞 𝒬 ξ ℓ L hbij
      (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v)) =
    geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L ((2 : L) • v)
  rw [geometricProperEulerTransferOfInvariantPullback_pullback_transfer]
  have hfixed := congrArg (fun f : _ →ₗ[L] _ => f v)
    (geometricProperEulerQuotientCohomologyPullback_reflection
      N m 𝒞 𝒬 ξ ℓ L)
  change geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
    (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v) =
      geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v at hfixed
  rw [hfixed, ← two_smul L _, map_smul]

/-- The cohomological comparison for the *fixed* specialized map
`geometricProperEulerFibreToRealQuotient`.  For the odd-prime cover the full
quotient H¹ is used.  The `pullback` and `transfer` maps and their naturality
are the cited étale pullback/degree-two transfer; no Frobenius trace or
arithmetic comparison is stipulated.  The deck relation is the cohomological
form of [GPRV, equation (76)] for this same proper reflection. -/
structure GeometricEulerQuotientTransfer
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] where
  transfer : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L →ₗ[L]
    GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L
  transfer_pullback : ∀ v,
    transfer (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v) =
      (2 : L) • v
  pullback_transfer : ∀ v,
    geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L (transfer v) =
    v + geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v
  reflection_deck : ∀
      (ζ : rootsOfUnity N (cyclotomicField N)) v,
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
      (geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ v) =
      geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ⁻¹
        (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v)
  pullback_galois : ∀
      (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
        AlgebraicClosure (cyclotomicField N)) v,
    geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L
      (geometricCyclotomicRealEulerQuotientGaloisRepresentation
        N m 𝒞 𝒬 ξ ℓ L g v) =
    geometricProperEulerGaloisRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
        (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v)
  transfer_galois : ∀
      (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
        AlgebraicClosure (cyclotomicField N)) v,
    transfer (geometricProperEulerGaloisRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L g v) =
    geometricCyclotomicRealEulerQuotientGaloisRepresentation
      N m 𝒞 𝒬 ξ ℓ L g (transfer v)

/-- Galois naturality of transfer follows from naturality of the actual
quotient pullback and reflection.  Bijectivity onto the invariant part is the
geometric cohomology input; no independent transfer naturality is assumed. -/
theorem geometricProperEulerTransferOfInvariantPullback_galois
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (hbij : Function.Bijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L))
    (hgal : ∀ g v,
      geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L
        (geometricCyclotomicRealEulerQuotientGaloisRepresentation
          N m 𝒞 𝒬 ξ ℓ L g v) =
      geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
          (geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L v))
    (hscomm : ∀ g v,
      geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
        (geometricProperEulerGaloisRepresentation N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ℓ L g v) =
      geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
          (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v))
    (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (cyclotomicField N))
    (v : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    geometricProperEulerTransferOfInvariantPullback N m 𝒞 𝒬 ξ ℓ L hbij
      (geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g v) =
      geometricCyclotomicRealEulerQuotientGaloisRepresentation
        N m 𝒞 𝒬 ξ ℓ L g
          (geometricProperEulerTransferOfInvariantPullback
            N m 𝒞 𝒬 ξ ℓ L hbij v) := by
  let p := geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L
  let T := geometricProperEulerTransferOfInvariantPullback N m 𝒞 𝒬 ξ ℓ L hbij
  let G := geometricProperEulerGaloisRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
  let H := geometricCyclotomicRealEulerQuotientGaloisRepresentation
    N m 𝒞 𝒬 ξ ℓ L g
  let s := geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
  apply hbij.1
  apply Subtype.ext
  change p (T (G v)) = p (H (T v))
  calc
    p (T (G v)) = G v + s (G v) :=
      geometricProperEulerTransferOfInvariantPullback_pullback_transfer
        N m 𝒞 𝒬 ξ ℓ L hbij (G v)
    _ = G (v + s v) := by rw [hscomm g v, map_add]
    _ = G (p (T v)) := by rw [geometricProperEulerTransferOfInvariantPullback_pullback_transfer]
    _ = p (H (T v)) := (hgal g (T v)).symm

/-- Build the quotient transfer package from invariant pullback for the
chosen geometric map.  Pullback Galois naturality follows from the actual
commutative square above; transfer identities and naturality are deductions.
The invariant-H¹ comparison and proper-fibre deck relation remain inputs.
The selected geometric construction discharges the deck relation separately. -/
def GeometricEulerQuotientTransfer.ofInvariantPullbackWithDeckRelation
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (hbij : Function.Bijective
      (geometricProperEulerQuotientPullbackFixed N m 𝒞 𝒬 ξ ℓ L))
    (hdeck : ∀ (ζ : rootsOfUnity N (cyclotomicField N)) v,
      geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
        (geometricProperEulerCoefficientDeckRepresentation N m 𝒞
          (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
          (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ v) =
      geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ⁻¹
          (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v))
    :
    GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L where
  transfer := geometricProperEulerTransferOfInvariantPullback N m 𝒞 𝒬 ξ ℓ L hbij
  transfer_pullback :=
    geometricProperEulerTransferOfInvariantPullback_transfer_pullback
      N m 𝒞 𝒬 ξ ℓ L hbij
  pullback_transfer :=
    geometricProperEulerTransferOfInvariantPullback_pullback_transfer
      N m 𝒞 𝒬 ξ ℓ L hbij
  reflection_deck := hdeck
  pullback_galois := geometricProperEulerQuotientCohomologyPullback_galois
    N m 𝒞 𝒬 ξ ℓ L
  transfer_galois :=
    geometricProperEulerTransferOfInvariantPullback_galois
      N m 𝒞 𝒬 ξ ℓ L hbij
        (geometricProperEulerQuotientCohomologyPullback_galois N m 𝒞 𝒬 ξ ℓ L)
        (geometricProperEulerCoefficientReflection_comm_galois N m 𝒞 𝒬 ξ ℓ L)

/-- The pullback in a quotient transfer package is the cohomological pullback
of its selected geometric quotient map. -/
abbrev GeometricEulerQuotientTransfer.pullback
    {N m : ℕ} [NeZero N] {𝒞 : SmoothProperEulerFamily N m}
    {𝒬 : SmoothProperRealEulerQuotient N m 𝒞}
    {ξ : ProjectiveLine.Parameter (realCyclotomicField N)}
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]
    (_P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L) :
    GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L →ₗ[L]
      GeometricProperEulerCohomology N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L :=
  geometricProperEulerQuotientCohomologyPullback N m 𝒞 𝒬 ξ ℓ L

/-- Reflection fixes pullback from the quotient.  This follows from the two
degree-two transfer identities, so it needs no separate cohomological input. -/
theorem GeometricEulerQuotientTransfer.reflection_pullback
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (v : GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L (P.pullback v) =
      P.pullback v := by
  have h := P.pullback_transfer (P.pullback v)
  rw [P.transfer_pullback, map_smul, two_smul L (P.pullback v)] at h
  exact (add_left_cancel h).symm

/-- Reflection on the cover commutes with cyclotomic Galois because both
pullback and transfer do. -/
theorem GeometricEulerQuotientTransfer.reflection_comm_galois
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (cyclotomicField N))
    (v : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L
      (geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g v) =
      geometricProperEulerGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
        (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v) := by
  let G := geometricProperEulerGaloisRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
  have h := P.pullback_transfer (G v)
  rw [P.transfer_galois, P.pullback_galois] at h
  have h' := congrArg G (P.pullback_transfer v)
  rw [map_add] at h'
  change G (P.pullback (P.transfer v)) = G v +
    G (geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L v) at h'
  exact add_left_cancel (h.symm.trans h')

/-- The degree-two transfer identity makes pullback from the quotient
injective in characteristic zero. -/
theorem GeometricEulerQuotientTransfer.pullback_injective
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L] [CharZero L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L) :
    Function.Injective P.pullback := by
  intro v w h
  have htwo : (2 : L) • v = (2 : L) • w := by
    calc
      _ = P.transfer (P.pullback v) := (P.transfer_pullback v).symm
      _ = P.transfer (P.pullback w) := congrArg P.transfer h
      _ = _ := P.transfer_pullback w
  have h' := congrArg (fun z => (2 : L)⁻¹ • z) htwo
  have h2 : (2 : L) ≠ 0 := by norm_num
  simpa [smul_smul, h2] using h'

/-- The fixed part of the proper cover's cohomology is precisely the image of
pullback from the chosen quotient.  The inverse on this image is half the
transfer, by the two degree-two identities. -/
theorem GeometricEulerQuotientTransfer.mem_pullback_range_iff_reflection_fixed
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L] [CharZero L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (w : GeometricProperEulerCohomology N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L) :
    (∃ v, P.pullback v = w) ↔
      geometricProperEulerCoefficientReflection N m 𝒞 𝒬 ξ ℓ L w = w := by
  constructor
  · rintro ⟨v, rfl⟩
    exact P.reflection_pullback N m 𝒞 𝒬 ξ v
  · intro hw
    refine ⟨(2 : L)⁻¹ • P.transfer w, ?_⟩
    rw [map_smul, P.pullback_transfer, hw, ← two_smul L w, smul_smul]
    have h2 : (2 : L) ≠ 0 := by norm_num
    simp [h2]

/-- The real cyclotomic generator obtained from this very quotient map:
`q_* D_ζ q^*`. -/
def GeometricEulerQuotientTransfer.generator
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (ζ : rootsOfUnity N (cyclotomicField N)) :
    Module.End L (GeometricCyclotomicRealEulerQuotientCohomology
      N m 𝒞 𝒬 ξ ℓ L) :=
  P.transfer.comp ((geometricProperEulerCoefficientDeckRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ).comp P.pullback)

/-- The generator built from the fixed geometric deck correspondence
commutes with the arithmetic Galois action over the cyclotomic field. -/
theorem GeometricEulerQuotientTransfer.generator_comm_galois
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (ζ : rootsOfUnity N (cyclotomicField N))
    (g : AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
      AlgebraicClosure (cyclotomicField N))
    (v : GeometricCyclotomicRealEulerQuotientCohomology N m 𝒞 𝒬 ξ ℓ L) :
    P.generator N m 𝒞 𝒬 ξ ζ
        (geometricCyclotomicRealEulerQuotientGaloisRepresentation
          N m 𝒞 𝒬 ξ ℓ L g v) =
      geometricCyclotomicRealEulerQuotientGaloisRepresentation
        N m 𝒞 𝒬 ξ ℓ L g (P.generator N m 𝒞 𝒬 ξ ζ v) := by
  let D := geometricProperEulerCoefficientDeckRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ
  let G := geometricProperEulerGaloisRepresentation N m 𝒞
    (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
    (one_sub_realEulerParameter_isUnit N ξ) ℓ L g
  have hdeck : D (G (P.pullback v)) = G (D (P.pullback v)) := by
    exact congrArg (fun f : Module.End L _ => f (P.pullback v))
      (geometricProperEulerCoefficientDeckGalois_comm N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ g)
  change P.transfer
      (D (P.pullback
        (geometricCyclotomicRealEulerQuotientGaloisRepresentation
          N m 𝒞 𝒬 ξ ℓ L g v))) =
    geometricCyclotomicRealEulerQuotientGaloisRepresentation
      N m 𝒞 𝒬 ξ ℓ L g (P.transfer (D (P.pullback v)))
  rw [P.pullback_galois, hdeck, P.transfer_galois]

/-- Pulling the quotient generator back to the cover gives the sum of the
two inverse deck operators.  Thus the RM generator is geometrically fixed,
and the label can subsequently be read on the fixed `χ₀` component. -/
theorem GeometricEulerQuotientTransfer.pullback_generator
    {ℓ : ℕ} [Fact ℓ.Prime] {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]
    (P : GeometricEulerQuotientTransfer N m 𝒞 𝒬 ξ ℓ L)
    (ζ : rootsOfUnity N (cyclotomicField N))
    (v : GeometricCyclotomicRealEulerQuotientCohomology
      N m 𝒞 𝒬 ξ ℓ L) :
    P.pullback (P.generator N m 𝒞 𝒬 ξ ζ v) =
      geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ (P.pullback v) +
      geometricProperEulerCoefficientDeckRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ⁻¹ (P.pullback v) := by
  change P.pullback (P.transfer
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ) ℓ L ζ (P.pullback v))) = _
  rw [P.pullback_transfer, P.reflection_deck,
    P.reflection_pullback N m 𝒞 𝒬 ξ]

end HilbertModularity.Hypergeometric
