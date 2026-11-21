/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine
public import HilbertModularity.Geometry.ProjectiveNaturality
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # The complement involution on the punctured projective line

The homogeneous substitution `[X₀ : X₁] ↦ [X₁ - X₀ : X₁]` constructs the actual
scheme involution underlying `t ↦ 1 - t` in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveLine

variable (R : Type*) [CommRing R]

/-- Homogeneous coordinates for the complement map. -/
def complementCoordinates : Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 1 - X 0, X 1]

/-- Complementing the affine coordinate preserves the standard grading. -/
def complementGraded :
    MvPolynomial.homogeneousSubmodule (Fin 2) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin 2) R where
  __ := (MvPolynomial.aeval (complementCoordinates R)).toRingHom
  map_mem {i} {x} hx := by
    change x.IsHomogeneous i at hx
    change (MvPolynomial.aeval (complementCoordinates R) x).IsHomogeneous i
    have hc : ∀ j, (complementCoordinates R j).IsHomogeneous 1 := by
      intro j
      fin_cases j
      · exact (isHomogeneous_X R (1 : Fin 2)).sub (isHomogeneous_X R (0 : Fin 2))
      · exact isHomogeneous_X R (1 : Fin 2)
    simpa using hx.aeval (complementCoordinates R) hc

@[simp]
theorem complementGraded_C (r : R) : complementGraded R (C r) = C r := by
  simp [complementGraded]

@[simp]
theorem complementGraded_X_zero : complementGraded R (X 0) = X 1 - X 0 := by
  simp [complementGraded, complementCoordinates]

@[simp]
theorem complementGraded_X_one : complementGraded R (X 1) = X 1 := by
  simp [complementGraded, complementCoordinates]

/-- The homogeneous substitution is its own inverse. -/
theorem complementGraded_comp :
    (complementGraded R).comp (complementGraded R) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin 2) R) := by
  have h : (complementGraded R).toRingHom.comp (complementGraded R).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp
  apply GradedRingHom.ext
  intro x
  exact congrArg (fun f : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R => f x) h

@[simp]
theorem complementGraded_apply_twice (x : MvPolynomial (Fin 2) R) :
    complementGraded R (complementGraded R x) = x :=
  congrArg (fun f : MvPolynomial.homogeneousSubmodule (Fin 2) R →+*ᵍ
    MvPolynomial.homogeneousSubmodule (Fin 2) R => f x) (complementGraded_comp R)

/-- The irrelevant ideal is covered, so the graded substitution defines a morphism on all of Proj. -/
theorem complementGraded_irrelevant :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R)).map
        (complementGraded R) := by
  intro x hx
  have hfx : complementGraded R x ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      ← GradedRingHom.map_directSumDecompose]
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx
    rw [hx, map_zero]
  have hm := Ideal.mem_map_of_mem (complementGraded R).toRingHom hfx
  change complementGraded R (complementGraded R x) ∈
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R)).map
      (complementGraded R) at hm
  simpa only [complementGraded_apply_twice] using hm

/-- The actual projective scheme morphism complementing the affine parameter. -/
def complement : ProjectiveLine R ⟶ ProjectiveLine R :=
  Proj.map (complementGraded R) (complementGraded_irrelevant R)

/-- Complementing twice is the identity scheme morphism. -/
theorem complement_comp : complement R ≫ complement R = 𝟙 (ProjectiveLine R) := by
  have h := Proj.map_comp (complementGraded R) (complementGraded R)
    (complementGraded_irrelevant R) (complementGraded_irrelevant R)
  simp only [complementGraded_comp, Proj.map_id] at h
  exact h.symm

/-- The complement map as an actual projective scheme automorphism. -/
def complementIso : ProjectiveLine R ≅ ProjectiveLine R where
  hom := complement R
  inv := complement R
  hom_inv_id := complement_comp R
  inv_hom_id := complement_comp R

/-- The excluded homogeneous divisor is preserved by complementing the parameter. -/
theorem complementGraded_boundary :
    complementGraded R ((X 0 : MvPolynomial (Fin 2) R) * X 1 * (X 0 - X 1)) =
      (X 0 : MvPolynomial (Fin 2) R) * X 1 * (X 0 - X 1) := by
  simp only [map_mul, map_sub, complementGraded_X_zero, complementGraded_X_one]
  ring

/-- The complement scheme morphism preserves the actual three-punctured open. -/
theorem complement_preimage_puncturedOpen :
    complement R ⁻¹ᵁ puncturedOpen R = puncturedOpen R := by
  change Proj.map _ _ ⁻¹ᵁ Proj.basicOpen _ _ = _
  rw [Proj.map_preimage_basicOpen, complementGraded_boundary]
  rfl

instance isIso_complement : IsIso (complement R) := (complementIso R).isIso_hom

/-- Restricting the actual complement automorphism gives an automorphism of the punctured line. -/
def puncturedComplementIso : punctured R ≅ punctured R :=
  (Scheme.isoOfEq (ProjectiveLine R) (complement_preimage_puncturedOpen R).symm) ≪≫
    (complement R).preimageIso (puncturedOpen R)

/-- The punctured automorphism is the restriction of the projective complement map. -/
@[reassoc]
theorem puncturedComplementIso_hom_inclusion :
    (puncturedComplementIso R).hom ≫ puncturedInclusion R =
      puncturedInclusion R ≫ complement R := by
  change ((Scheme.isoOfEq (ProjectiveLine R) _).hom ≫
    ((complement R).preimageIso (puncturedOpen R)).hom) ≫ (puncturedOpen R).ι = _
  rw [Category.assoc, Scheme.Hom.preimageIso_hom_ι, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  rfl

/-- The restricted complement map is itself involutive. -/
theorem puncturedComplementIso_hom_comp :
    (puncturedComplementIso R).hom ≫ (puncturedComplementIso R).hom = 𝟙 (punctured R) := by
  apply (cancel_mono (puncturedInclusion R)).mp
  rw [Category.assoc, puncturedComplementIso_hom_inclusion,
    ← Category.assoc, puncturedComplementIso_hom_inclusion,
    Category.assoc, complement_comp, Category.comp_id, Category.id_comp]

/-- On homogeneous parameter sections, complementing sends the affine parameter to `1 - ξ`. -/
theorem eval_comp_complementGraded (ξ : R) :
    (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then ξ else 1)).comp
      (complementGraded R).toRingHom =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then 1 - ξ else 1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

/-- The actual global sections of the parameter point transform with the same affine formula. -/
theorem parameterSections_comp_complementGraded (ξ : R) :
    (parameterSections R ξ).comp (complementGraded R).toRingHom =
      parameterSections R (1 - ξ) := by
  unfold parameterSections
  rw [RingHom.comp_assoc, eval_comp_complementGraded]

set_option backward.isDefEq.respectTransparency false in
/-- The projective complement automorphism is defined over the original coefficient ring. -/
@[reassoc]
theorem complement_toSpec : complement R ≫ toSpec R = toSpec R := by
  apply (Proj.mapAffineOpenCover (complementGraded R)
    (complementGraded_irrelevant R)).openCover.hom_ext
  intro s
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
    complement, toSpec]
  rw [Proj.awayι_comp_map_assoc (complementGraded R) (complementGraded_irrelevant R)
    s.1.2 s.2.1 s.2.2]
  simp only [Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, constants]
  rfl

/-- The punctured complement automorphism also lies over the original coefficient ring. -/
@[reassoc]
theorem puncturedComplementIso_hom_toSpec :
    (puncturedComplementIso R).hom ≫ puncturedToSpec R = puncturedToSpec R := by
  rw [puncturedToSpec, ← Category.assoc, puncturedComplementIso_hom_inclusion,
    Category.assoc, complement_toSpec]

/-- Complementing the actual parameter-point morphism sends `ξ` to `1 - ξ`. -/
@[reassoc]
theorem affinePoint_complement (ξ : R) :
    affinePoint R ξ ≫ complement R = affinePoint R (1 - ξ) := by
  have hφf : (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 2) R)).toIdeal.map
      ((parameterSections R ξ).comp (complementGraded R).toRingHom) = ⊤ := by
    rw [parameterSections_comp_complementGraded]
    exact parameterSections_irrelevant R (1 - ξ)
  have h := Proj.fromOfGlobalSections_comp_map
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (parameterSections R ξ) (complementGraded R) (complementGraded_irrelevant R)
    (parameterSections_irrelevant R ξ) hφf
  simpa only [parameterSections_comp_complementGraded, affinePoint, complement, ProjectiveLine] using h

variable (K : Type*) [Field K]

/-- Complementing a parameter preserves avoidance of zero and one. -/
def complementParameter (ξ : Parameter K) : Parameter K :=
  ⟨1 - ξ.val, by
    constructor
    · intro h
      exact ξ.property.2 (sub_eq_zero.mp h).symm
    · intro h
      exact ξ.property.1 (sub_eq_self.mp h)⟩

@[simp]
theorem complementParameter_val (ξ : Parameter K) :
    (complementParameter K ξ).val = 1 - ξ.val := rfl

/-- The parameter involution is itself inverse. -/
@[simp]
theorem complementParameter_twice (ξ : Parameter K) :
    complementParameter K (complementParameter K ξ) = ξ := by
  apply Subtype.ext
  simp [complementParameter]

/-- The existing punctured parameter-point morphism transforms by the actual punctured
scheme automorphism over the same coefficient field. -/
@[reassoc]
theorem puncturedPoint_complement (ξ : Parameter K) :
    puncturedPoint K ξ ≫ (puncturedComplementIso K).hom =
      puncturedPoint K (complementParameter K ξ) := by
  apply (cancel_mono (puncturedInclusion K)).mp
  rw [Category.assoc, puncturedComplementIso_hom_inclusion,
    ← Category.assoc, puncturedPoint_inclusion, affinePoint_complement,
    puncturedPoint_inclusion]
  rfl

end AlgebraicGeometry.ProjectiveLine
