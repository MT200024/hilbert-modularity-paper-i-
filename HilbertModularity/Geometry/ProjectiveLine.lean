/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The projective line and its three-punctured open subscheme

We use `Proj R[X₀,X₁]` with its usual grading. Removing the coordinate divisors
`X₀ = 0`, `X₀ = X₁`, and `X₁ = 0` gives the base curve of
[TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- The projective line over a ring, with homogeneous coordinates `[X₀ : X₁]`. -/
def ProjectiveLine (R : Type*) [CommRing R] : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)

namespace ProjectiveLine

variable (R : Type*) [CommRing R]

/-- Constants, viewed in the degree-zero part of the homogeneous coordinate ring. -/
def constants : R →+* ↥(MvPolynomial.homogeneousSubmodule (Fin 2) R 0) where
  toFun r := ⟨C r, isHomogeneous_C (Fin 2) r⟩
  map_one' := Subtype.ext (map_one C)
  map_zero' := Subtype.ext (map_zero C)
  map_add' a b := Subtype.ext (map_add C a b)
  map_mul' a b := Subtype.ext (map_mul C a b)

/-- The structure morphism of the projective line over its coefficient ring. -/
def toSpec : ProjectiveLine R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) R) ≫
    Spec.map (CommRingCat.ofHom (constants R))

/-- The open complement of zero, one, and infinity in homogeneous coordinates. -/
def puncturedOpen : (ProjectiveLine R).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    ((X 0 : MvPolynomial (Fin 2) R) * X 1 * (X 0 - X 1))

/-- The three-punctured projective line as an actual open subscheme. -/
def punctured : Scheme := (puncturedOpen R).toScheme

/-- The open immersion of the three-punctured line into the projective line. -/
def puncturedInclusion : punctured R ⟶ ProjectiveLine R := (puncturedOpen R).ι

instance isOpenImmersion_puncturedInclusion : IsOpenImmersion (puncturedInclusion R) := inferInstanceAs
  (IsOpenImmersion (puncturedOpen R).ι)

/-- The structure morphism of the punctured line. -/
def puncturedToSpec : punctured R ⟶ Spec (CommRingCat.of R) :=
  puncturedInclusion R ≫ toSpec R

/-- Removing the three points is the intersection of their standard basic opens. -/
theorem puncturedOpen_eq : puncturedOpen R =
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (X 0) ⊓
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (X 1) ⊓
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (X 0 - X 1) := by
  simp only [puncturedOpen, Proj.basicOpen_mul]
  rfl

/-- Parameters in the affine coordinate `X₀/X₁` away from zero and one. -/
abbrev Parameter (K : Type*) [Field K] := {ξ : K // ξ ≠ 0 ∧ ξ ≠ 1}

/-- The excluded homogeneous divisor evaluated at `[ξ : 1]`. -/
theorem eval_boundary (ξ : R) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then ξ else 1)
      ((X 0 : MvPolynomial (Fin 2) R) * X 1 * (X 0 - X 1)) = ξ * (ξ - 1) := by
  simp

/-- Homogeneous coordinates `[ξ : 1]` as global sections on `Spec R`. -/
def parameterSections (ξ : R) :
    MvPolynomial (Fin 2) R →+* Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
    (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then ξ else 1))

/-- The second coordinate is one, so these sections generate the unit ideal. -/
theorem parameterSections_irrelevant (ξ : R) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R)).toIdeal.map
      (parameterSections R ξ) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem (parameterSections R ξ)
    (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (by decide : 0 < 1)
      (isHomogeneous_X R (1 : Fin 2)))
  simpa [parameterSections] using h

/-- The projective-line section `[ξ : 1]` as a scheme morphism. -/
def affinePoint (ξ : R) : Spec (CommRingCat.of R) ⟶ ProjectiveLine R :=
  Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (parameterSections R ξ) (parameterSections_irrelevant R ξ)

/-- Pulling back the punctured open along `[ξ : 1]` inverts `ξ(ξ-1)`. -/
theorem affinePoint_preimage_puncturedOpen (ξ : R) :
    affinePoint R ξ ⁻¹ᵁ puncturedOpen R =
      (Spec (CommRingCat.of R)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (ξ * (ξ - 1))) := by
  have h := Proj.fromOfGlobalSections_preimage_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (parameterSections R ξ) (parameterSections_irrelevant R ξ) (by decide : 0 < 3)
    (((isHomogeneous_X R (0 : Fin 2)).mul (isHomogeneous_X R (1 : Fin 2))).mul
      ((isHomogeneous_X R (0 : Fin 2)).sub (isHomogeneous_X R (1 : Fin 2))))
  simp only [parameterSections, RingHom.comp_apply, eval_boundary] at h
  exact h

/-- The section `[ξ : 1]` is a section over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem affinePoint_toSpec (ξ : R) : affinePoint R ξ ≫ toSpec R = 𝟙 _ := by
  change (Proj.fromOfGlobalSections _ _ _ ≫ Proj.toSpecZero _) ≫
    Spec.map (CommRingCat.ofHom (constants R)) = _
  rw [Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (constants R) ≫
      CommRingCat.ofHom ((parameterSections R ξ).comp (algebraMap _ _)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    ext r
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then ξ else 1) (C r)) = _
    rw [MvPolynomial.eval_C]
  rw [h]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv _

variable (K : Type*) [Field K]

/-- A parameter avoiding zero and one has its entire spectrum in the punctured open. -/
theorem affinePoint_preimage_puncturedOpen_eq_top (ξ : Parameter K) :
    affinePoint K ξ.val ⁻¹ᵁ puncturedOpen K = ⊤ := by
  rw [affinePoint_preimage_puncturedOpen]
  apply Scheme.basicOpen_of_isUnit
  exact (isUnit_iff_ne_zero.mpr
    (mul_ne_zero ξ.property.1 (sub_ne_zero.mpr ξ.property.2))).map
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- Exactly the parameters different from zero and one land in the punctured open. -/
theorem affinePoint_preimage_puncturedOpen_eq_top_iff (ξ : K) :
    affinePoint K ξ ⁻¹ᵁ puncturedOpen K = ⊤ ↔ ξ ≠ 0 ∧ ξ ≠ 1 := by
  constructor
  · intro h
    rw [affinePoint_preimage_puncturedOpen] at h
    constructor
    · intro hz
      simp [hz] at h
    · intro ho
      simp [ho] at h
  · intro h
    exact affinePoint_preimage_puncturedOpen_eq_top K ⟨ξ, h⟩

/-- A nonsingular parameter as a rational point of the punctured projective line. -/
def puncturedPoint (ξ : Parameter K) : Spec (CommRingCat.of K) ⟶ punctured K :=
  (Spec (CommRingCat.of K)).topIso.inv ≫
    (affinePoint K ξ.val).resLE (puncturedOpen K) ⊤
      (le_of_eq (affinePoint_preimage_puncturedOpen_eq_top K ξ).symm)

/-- Inclusion of the parameter point has homogeneous coordinates `[ξ : 1]`. -/
@[reassoc (attr := simp)]
theorem puncturedPoint_inclusion (ξ : Parameter K) :
    puncturedPoint K ξ ≫ puncturedInclusion K = affinePoint K ξ.val := by
  change ((Spec (CommRingCat.of K)).topIso.inv ≫
    (affinePoint K ξ.val).resLE (puncturedOpen K) ⊤ _) ≫ (puncturedOpen K).ι = _
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.toIso_inv_ι_assoc]

/-- The parameter point is a morphism over `K`. -/
@[reassoc (attr := simp)]
theorem puncturedPoint_toSpec (ξ : Parameter K) :
    puncturedPoint K ξ ≫ puncturedToSpec K = 𝟙 _ := by
  rw [puncturedToSpec, ← Category.assoc, puncturedPoint_inclusion, affinePoint_toSpec]

end ProjectiveLine

end AlgebraicGeometry
