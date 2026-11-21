/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveChart
import HilbertModularity.FieldTheory.RatFunc.Involution

/-! # Four branch neighbourhoods on the projective line

The four distinct sections of the Euler cover in [TripathiGoswamiRevised,
Definition 2.3] determine an open cover of its *target* projective line.  The
coordinate on each member vanishes at its retained section; that section's
form is omitted from the product inverted on the neighbourhood.  These are base
neighbourhoods; no cyclic-cover normalization or gluing is asserted here.
-/

public section
noncomputable section

open CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveLine

/-- The four sections of the target projective line. -/
inductive FourPointBranch
  | zero | one | inverseParameter | infinity
  deriving DecidableEq

instance : Fintype FourPointBranch :=
  ⟨{.zero, .one, .inverseParameter, .infinity}, by
    intro i
    cases i <;> simp⟩

variable (R : Type*) [CommRing R] (t : R)

/-- The homogeneous linear form vanishing at a branch section. -/
def branchForm : FourPointBranch → MvPolynomial (Fin 2) R
  | .zero => X 0
  | .one => X 1 - X 0
  | .inverseParameter => X 1 - C t * X 0
  | .infinity => X 1

/-- The product of the three forms away from the selected branch section. -/
def otherBranchProduct : FourPointBranch → MvPolynomial (Fin 2) R
  | .zero => branchForm R t .one * branchForm R t .inverseParameter *
      branchForm R t .infinity
  | .one => branchForm R t .zero * branchForm R t .inverseParameter *
      branchForm R t .infinity
  | .inverseParameter => branchForm R t .zero * branchForm R t .one *
      branchForm R t .infinity
  | .infinity => branchForm R t .zero * branchForm R t .one *
      branchForm R t .inverseParameter

/-- The product of all four branch forms. -/
def allBranchProduct : MvPolynomial (Fin 2) R :=
  branchForm R t .zero * branchForm R t .one *
    branchForm R t .inverseParameter * branchForm R t .infinity

/-- The target neighbourhood obtained by deleting the other three branch sections. -/
def branchOpen (i : FourPointBranch) : (ProjectiveLine R).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (otherBranchProduct R t i)

/-- The common complement of all four branch sections. -/
def fourPointOpen : (ProjectiveLine R).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (allBranchProduct R t)

/-- The actual open subscheme of a target branch neighbourhood. -/
@[expose]
def branchNeighbourhood (i : FourPointBranch) : Scheme :=
  (branchOpen R t i).toScheme

/-- The common open subscheme in the target projective line. -/
@[expose]
def fourPointComplement : Scheme := (fourPointOpen R t).toScheme

/-- Inclusion of a target branch neighbourhood in the projective line. -/
@[expose]
def branchInclusion (i : FourPointBranch) : branchNeighbourhood R t i ⟶ ProjectiveLine R :=
  (branchOpen R t i).ι

instance branchInclusion_isOpenImmersion (i : FourPointBranch) :
    IsOpenImmersion (branchInclusion R t i) :=
  inferInstanceAs (IsOpenImmersion (branchOpen R t i).ι)

/-- The image of a branch-neighbourhood inclusion is its defining open. -/
theorem branchInclusion_range (i : FourPointBranch) :
    Set.range ⇑(branchInclusion R t i) =
      (branchOpen R t i : Set (ProjectiveLine R)) :=
  Scheme.Opens.range_ι (branchOpen R t i)

/-- Inclusion of the four-point complement in the projective line. -/
@[expose]
def fourPointInclusion : fourPointComplement R t ⟶ ProjectiveLine R :=
  (fourPointOpen R t).ι

instance fourPointInclusion_isOpenImmersion :
    IsOpenImmersion (fourPointInclusion R t) :=
  inferInstanceAs (IsOpenImmersion (fourPointOpen R t).ι)

/-- The image of the common inclusion is the four-point complement. -/
theorem fourPointInclusion_range :
    Set.range ⇑(fourPointInclusion R t) =
      (fourPointOpen R t : Set (ProjectiveLine R)) :=
  Scheme.Opens.range_ι (fourPointOpen R t)

theorem branchForm_isHomogeneous (i : FourPointBranch) :
    (branchForm R t i).IsHomogeneous 1 := by
  cases i with
  | zero => exact isHomogeneous_X R 0
  | one => exact (isHomogeneous_X R 1).sub (isHomogeneous_X R 0)
  | inverseParameter =>
      exact (isHomogeneous_X R 1).sub (isHomogeneous_C_mul_X t 0)
  | infinity => exact isHomogeneous_X R 1

/-- Multiplying the branch forms identifies any two distinct neighbourhoods on
their common four-point complement. -/
theorem branchOpen_inf_of_ne (i j : FourPointBranch) (hij : i ≠ j) :
    branchOpen R t i ⊓ branchOpen R t j = fourPointOpen R t := by
  cases i <;> cases j
  all_goals first | exact (hij rfl).elim | skip
  all_goals simp only [branchOpen, otherBranchProduct, fourPointOpen,
    allBranchProduct, Proj.basicOpen_mul]
  all_goals ext x
  all_goals change ((_ ∧ _) ∧ _) ∧ ((_ ∧ _) ∧ _) ↔ (((_ ∧ _) ∧ _) ∧ _)
  all_goals tauto

/-- The common complement is obtained from each branch neighbourhood by deleting
its one remaining branch form. -/
theorem fourPointOpen_eq_branchOpen_inf (i : FourPointBranch) :
    fourPointOpen R t = branchOpen R t i ⊓
      Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (branchForm R t i) := by
  cases i <;>
    simp only [fourPointOpen, allBranchProduct, branchOpen, otherBranchProduct,
      Proj.basicOpen_mul]
  all_goals ext x
  all_goals change (((_ ∧ _) ∧ _) ∧ _) ↔ (((_ ∧ _) ∧ _) ∧ _)
  all_goals tauto

/-- At every target point, at most one branch form vanishes. Thus the product
of the other three is nonvanishing for some branch, and these opens cover the line. -/
theorem branchOpens_cover (ht : IsUnit t) (ht1 : IsUnit (1 - t)) :
    ⨆ i : FourPointBranch, branchOpen R t i = ⊤ := by
  apply top_unique
  intro x _
  let I := x.asHomogeneousIdeal.toIdeal
  have hcoordinates : (X 0 : MvPolynomial (Fin 2) R) ∉ I ∨
      (X 1 : MvPolynomial (Fin 2) R) ∉ I := by
    have hcover := Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule (Fin 2) R)
      (X : Fin 2 → MvPolynomial (Fin 2) R)
      (fun i => ⟨1, isHomogeneous_X R i⟩) (adjoin_coordinates_eq_top R)
    have hx : x ∈ ⨆ i : Fin 2,
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X i) := by
      rw [hcover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hzero_one (h₀ : (X 0 : MvPolynomial (Fin 2) R) ∈ I)
      (hL : branchForm R t .one ∈ I) : False := by
    apply hcoordinates.elim (fun h => h h₀) (fun h => ?_)
    apply h
    convert I.add_mem hL h₀ using 1; simp [branchForm]
  have hzero_inverse (h₀ : (X 0 : MvPolynomial (Fin 2) R) ∈ I)
      (hL : branchForm R t .inverseParameter ∈ I) : False := by
    apply hcoordinates.elim (fun h => h h₀) (fun h => ?_)
    apply h
    convert I.add_mem hL (I.mul_mem_left (C t) h₀) using 1
    simp [branchForm]
  have hone_infinity (h₁ : (X 1 : MvPolynomial (Fin 2) R) ∈ I)
      (hL : branchForm R t .one ∈ I) : False := by
    apply hcoordinates.elim (fun h => ?_) (fun h => h h₁)
    apply h
    convert I.sub_mem h₁ hL using 1; simp [branchForm]
  have hinverse_infinity (h₁ : (X 1 : MvPolynomial (Fin 2) R) ∈ I)
      (hL : branchForm R t .inverseParameter ∈ I) : False := by
    have htunit : IsUnit (C t : MvPolynomial (Fin 2) R) :=
      ht.map (C : R →+* MvPolynomial (Fin 2) R)
    have htx : (C t : MvPolynomial (Fin 2) R) * X 0 ∈ I := by
      convert I.sub_mem h₁ hL using 1; simp [branchForm]
    have h₀ : (X 0 : MvPolynomial (Fin 2) R) ∈ I :=
      (I.unit_mul_mem_iff_mem htunit).mp htx
    exact hcoordinates.elim (fun h => h h₀) (fun h => h h₁)
  have hone_inverse (hL₁ : branchForm R t .one ∈ I)
      (hLt : branchForm R t .inverseParameter ∈ I) : False := by
    have htunit : IsUnit (C (1 - t) : MvPolynomial (Fin 2) R) :=
      ht1.map
        (C : R →+* MvPolynomial (Fin 2) R)
    have htx : (C (1 - t) : MvPolynomial (Fin 2) R) * X 0 ∈ I := by
      convert I.sub_mem hLt hL₁ using 1; simp [branchForm]; ring
    have h₀ : (X 0 : MvPolynomial (Fin 2) R) ∈ I :=
      (I.unit_mul_mem_iff_mem htunit).mp htx
    exact hzero_one h₀ hL₁
  by_cases h₀ : (X 0 : MvPolynomial (Fin 2) R) ∈ I
  · have h₁ : (X 1 : MvPolynomial (Fin 2) R) ∉ I :=
      hcoordinates.elim (fun h => (h h₀).elim) (fun h => h)
    have hL₁ : branchForm R t .one ∉ I := fun h => hzero_one h₀ h
    have hLt : branchForm R t .inverseParameter ∉ I :=
      fun h => hzero_inverse h₀ h
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨.zero, ?_⟩
    change x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) R)
      (branchForm R t .one * branchForm R t .inverseParameter *
        branchForm R t .infinity)
    rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
    exact ⟨⟨hL₁, hLt⟩, h₁⟩
  · by_cases h₁ : (X 1 : MvPolynomial (Fin 2) R) ∈ I
    · have hL₁ : branchForm R t .one ∉ I := fun h => hone_infinity h₁ h
      have hLt : branchForm R t .inverseParameter ∉ I :=
        fun h => hinverse_infinity h₁ h
      apply TopologicalSpace.Opens.mem_iSup.mpr
      refine ⟨.infinity, ?_⟩
      change x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) R)
        (branchForm R t .zero * branchForm R t .one *
          branchForm R t .inverseParameter)
      rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
      exact ⟨⟨h₀, hL₁⟩, hLt⟩
    · by_cases hL₁ : branchForm R t .one ∈ I
      · have hLt : branchForm R t .inverseParameter ∉ I :=
          fun h => hone_inverse hL₁ h
        apply TopologicalSpace.Opens.mem_iSup.mpr
        refine ⟨.one, ?_⟩
        change x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) R)
          (branchForm R t .zero * branchForm R t .inverseParameter *
            branchForm R t .infinity)
        rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
        exact ⟨⟨h₀, hLt⟩, h₁⟩
      · apply TopologicalSpace.Opens.mem_iSup.mpr
        refine ⟨.inverseParameter, ?_⟩
        change x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) R)
          (branchForm R t .zero * branchForm R t .one *
            branchForm R t .infinity)
        rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
        exact ⟨⟨h₀, hL₁⟩, h₁⟩

/-- The ordinary projective chart containing a branch neighbourhood.  The first
three use `x = X₀/X₁`; infinity uses `u = X₁/X₀`. -/
def branchStandardChart : FourPointBranch →
    (Spec (CommRingCat.of (Polynomial R)) ⟶ ProjectiveLine R)
  | .zero | .one | .inverseParameter => chartMap R 0 1 (by decide)
  | .infinity => chartMap R 1 0 (by decide)

instance branchStandardChart_isOpenImmersion (i : FourPointBranch) :
    IsOpenImmersion (branchStandardChart R i) := by
  cases i <;> dsimp [branchStandardChart] <;> infer_instance

/-- The product defining a branch neighbourhood in its standard affine chart. -/
def branchStandardDenominator : FourPointBranch → Polynomial R
  | .zero => (1 - Polynomial.X) * (1 - Polynomial.C t * Polynomial.X)
  | .one => Polynomial.X * (1 - Polynomial.C t * Polynomial.X)
  | .inverseParameter => Polynomial.X * (1 - Polynomial.X)
  | .infinity => (Polynomial.X - 1) * (Polynomial.X - Polynomial.C t)

/-- The coordinate of the one branch point retained by the standard affine chart. -/
def branchStandardMissingCoordinate : FourPointBranch → Polynomial R
  | .zero => Polynomial.X
  | .one => 1 - Polynomial.X
  | .inverseParameter => 1 - Polynomial.C t * Polynomial.X
  | .infinity => Polynomial.X

/-- Every branch neighbourhood lies in its indicated standard affine chart. -/
theorem branchOpen_le_standardChart (i : FourPointBranch) :
    branchOpen R t i ≤ (branchStandardChart R i).opensRange := by
  cases i <;>
    simp only [branchOpen, branchStandardChart, otherBranchProduct,
      Proj.basicOpen_mul, chartMap_opensRange]
  · exact inf_le_right
  · exact inf_le_right
  · exact inf_le_right
  · exact (inf_le_left.trans inf_le_left)

/-- In the standard affine chart, each branch neighbourhood is a polynomial
principal open. -/
theorem branchStandardChart_preimage_branchOpen (i : FourPointBranch) :
    branchStandardChart R i ⁻¹ᵁ branchOpen R t i =
      PrimeSpectrum.basicOpen (branchStandardDenominator R t i) := by
  have h (a b : Fin 2) (hab : a ≠ b) (s : MvPolynomial (Fin 2) R)
      (hs : s.IsHomogeneous 1) :
      chartMap R a b hab ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s =
          PrimeSpectrum.basicOpen (chartCoordinates R a s) :=
    Proj.fromSpecOfUnit_preimage_basicOpen_one (homogeneousSubmodule (Fin 2) R)
      (chartCoordinates R a) (isHomogeneous_X R b) hs
      (by simp [chartCoordinates, Ne.symm hab])
  have hthree (a b : Fin 2) (hab : a ≠ b)
      (s₁ s₂ s₃ : MvPolynomial (Fin 2) R)
      (hs₁ : s₁.IsHomogeneous 1) (hs₂ : s₂.IsHomogeneous 1)
      (hs₃ : s₃.IsHomogeneous 1) :
      chartMap R a b hab ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (s₁ * s₂ * s₃) =
        PrimeSpectrum.basicOpen
          (chartCoordinates R a s₁ * chartCoordinates R a s₂ *
            chartCoordinates R a s₃) := by
    rw [Proj.basicOpen_mul, Proj.basicOpen_mul]
    change (chartMap R a b hab ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s₁) ⊓
      (chartMap R a b hab ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s₂) ⊓
      (chartMap R a b hab ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s₃) = _
    rw [h a b hab s₁ hs₁, h a b hab s₂ hs₂, h a b hab s₃ hs₃]
    simp only [PrimeSpectrum.basicOpen_mul]
    rfl
  cases i <;>
    simp only [branchStandardChart, branchOpen, otherBranchProduct]
  all_goals
    rw [hthree _ _ (by decide) _ _ _
      (branchForm_isHomogeneous R t _)
      (branchForm_isHomogeneous R t _)
      (branchForm_isHomogeneous R t _)]
    simp [branchForm, branchStandardDenominator, chartCoordinates,
      PrimeSpectrum.basicOpen_mul]
  all_goals rfl

/-- Dehomogenizing the retained branch form gives its affine coordinate. -/
theorem branchStandardChart_preimage_branchForm (i : FourPointBranch) :
    branchStandardChart R i ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (branchForm R t i) =
        PrimeSpectrum.basicOpen (branchStandardMissingCoordinate R t i) := by
  have h (a b : Fin 2) (hab : a ≠ b) (s : MvPolynomial (Fin 2) R)
      (hs : s.IsHomogeneous 1) :
      chartMap R a b hab ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) s =
          PrimeSpectrum.basicOpen (chartCoordinates R a s) :=
    Proj.fromSpecOfUnit_preimage_basicOpen_one (homogeneousSubmodule (Fin 2) R)
      (chartCoordinates R a) (isHomogeneous_X R b) hs
      (by simp [chartCoordinates, Ne.symm hab])
  cases i <;> simp only [branchStandardChart]
  all_goals
    rw [h _ _ (by decide) _ (branchForm_isHomogeneous R t _)]
    simp [branchForm, branchStandardMissingCoordinate, chartCoordinates]
  all_goals rfl

/-- In the standard polynomial chart, the common complement in a branch
neighbourhood is the principal open of the remaining coordinate. -/
theorem branchStandardChart_preimage_fourPointOpen (i : FourPointBranch) :
    branchStandardChart R i ⁻¹ᵁ fourPointOpen R t =
      PrimeSpectrum.basicOpen
        (branchStandardDenominator R t i * branchStandardMissingCoordinate R t i) := by
  rw [fourPointOpen_eq_branchOpen_inf]
  change (branchStandardChart R i ⁻¹ᵁ branchOpen R t i) ⊓
      (branchStandardChart R i ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (branchForm R t i)) = _
  rw [branchStandardChart_preimage_branchOpen,
    branchStandardChart_preimage_branchForm, PrimeSpectrum.basicOpen_mul]
  rfl

/-- The restricted standard chart has exactly the branch-neighbourhood image. -/
theorem branchStandardChart_range_eq (i : FourPointBranch) :
    Set.range ⇑((branchStandardChart R i ⁻¹ᵁ branchOpen R t i).ι ≫
      branchStandardChart R i) = Set.range ⇑(branchInclusion R t i) := by
      have h : branchStandardChart R i ''ᵁ
          (branchStandardChart R i ⁻¹ᵁ branchOpen R t i) = branchOpen R t i := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
          inf_eq_right.mpr (branchOpen_le_standardChart R t i)]
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      change ((branchStandardChart R i ''ᵁ
        (branchStandardChart R i ⁻¹ᵁ branchOpen R t i)) : Set (ProjectiveLine R)) = _
      rw [h]
      exact (Scheme.Opens.range_ι (branchOpen R t i)).symm

/-- The restriction of the standard chart is the entire branch neighbourhood. -/
def branchStandardChartIso (i : FourPointBranch) :
    (branchStandardChart R i ⁻¹ᵁ branchOpen R t i).toScheme ≅
      branchNeighbourhood R t i :=
  IsOpenImmersion.isoOfRangeEq
    ((branchStandardChart R i ⁻¹ᵁ branchOpen R t i).ι ≫ branchStandardChart R i)
    (branchInclusion R t i) (branchStandardChart_range_eq R t i)

/-- The standard affine coordinate description of a branch neighbourhood. -/
def branchStandardAffineIso (i : FourPointBranch) :
    branchNeighbourhood R t i ≅
      Spec (CommRingCat.of (Localization.Away (branchStandardDenominator R t i))) :=
  (branchStandardChartIso R t i).symm ≪≫
    Scheme.isoOfEq _ (branchStandardChart_preimage_branchOpen R t i) ≪≫
      basicOpenIsoSpecAway _

/-- The standard affine description has the expected inclusion in the target line. -/
@[reassoc]
theorem branchStandardAffineIso_inv_inclusion (i : FourPointBranch) :
    (branchStandardAffineIso R t i).inv ≫ branchInclusion R t i =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R)
        (Localization.Away (branchStandardDenominator R t i)))) ≫
          branchStandardChart R i := by
  simp only [branchStandardAffineIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac
    ((branchStandardChart R i ⁻¹ᵁ branchOpen R t i).ι ≫ branchStandardChart R i)
    (branchInclusion R t i) (branchStandardChart_range_eq R t i)
  unfold branchStandardChartIso
  rw [h]
  have h' := Scheme.isoOfEq_inv_ι_assoc (Spec (CommRingCat.of (Polynomial R)))
    (branchStandardChart_preimage_branchOpen R t i) (branchStandardChart R i)
  rw [h', ← basicOpenIsoSpecAway_hom_SpecMap
    (R := CommRingCat.of (Polynomial R)) (branchStandardDenominator R t i)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The affine description retains the given `R`-scheme structure. -/
@[reassoc]
theorem branchStandardAffineIso_inv_toSpec (i : FourPointBranch) :
    (branchStandardAffineIso R t i).inv ≫ branchInclusion R t i ≫ toSpec R =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Polynomial R)
          (Localization.Away (branchStandardDenominator R t i))).comp
            Polynomial.C)) := by
  rw [← Category.assoc, branchStandardAffineIso_inv_inclusion,
    Category.assoc]
  cases i <;> simp only [branchStandardChart, chartMap_toSpec, ← Spec.map_comp]
  all_goals rfl

/-- The prescribed coordinate denominator on each branch neighbourhood. -/
def branchDenominator : FourPointBranch → Polynomial R
  | .zero => (1 - Polynomial.X) * (1 - Polynomial.C t * Polynomial.X)
  | .one => (1 - Polynomial.X) *
      (1 - Polynomial.C t + Polynomial.C t * Polynomial.X)
  | .inverseParameter => (1 - Polynomial.X) *
      (Polynomial.C t - 1 + Polynomial.X)
  | .infinity => (Polynomial.X - 1) * (Polynomial.X - Polynomial.C t)

/-- Substitution from a prescribed branch coordinate to the standard affine
coordinate of that projective chart. -/
def branchCoordinateChange (i : FourPointBranch) (ht : IsUnit t) :
    Polynomial R ≃ₐ[R] Polynomial R :=
  match i with
  | .zero => AlgEquiv.refl
  | .one => Polynomial.complementAlgEquiv R
  | .inverseParameter =>
      letI : Invertible (-t) := by
        let h := isUnit_iff_exists_inv.mp ht.neg
        exact ⟨Classical.choose h,
          by simpa only [mul_comm] using Classical.choose_spec h,
          Classical.choose_spec h⟩
      Polynomial.algEquivCMulXAddC (-t) 1
  | .infinity => AlgEquiv.refl

/-- The prescribed coordinates are respectively `x`, `1-x`, `1-tx`, and
`1/x` on the two standard projective charts. -/
theorem branchCoordinateChange_X (i : FourPointBranch) (ht : IsUnit t) :
    branchCoordinateChange R t i ht Polynomial.X =
      branchStandardMissingCoordinate R t i := by
  cases i <;> simp [branchCoordinateChange, branchStandardMissingCoordinate,
    Polynomial.algEquivCMulXAddC_apply]
  · ring

/-- In the inverse-parameter chart the prescribed denominator differs from
the standard one by the unit `t²`. -/
theorem branchCoordinateChange_denominator_inverseParameter (ht : IsUnit t) :
    branchCoordinateChange R t .inverseParameter ht
        (branchDenominator R t .inverseParameter) =
      Polynomial.C (t * t) *
        branchStandardDenominator R t .inverseParameter := by
  simp [branchCoordinateChange, branchDenominator,
    branchStandardDenominator, Polynomial.algEquivCMulXAddC_apply]
  ring

/-- The transformed prescribed denominator cuts out the standard chart open. -/
theorem branchCoordinateChange_denominator_associated (i : FourPointBranch)
    (ht : IsUnit t) :
    Associated (branchCoordinateChange R t i ht (branchDenominator R t i))
      (branchStandardDenominator R t i) := by
  cases i with
  | zero => exact Associated.of_eq (by simp [branchCoordinateChange, branchDenominator,
      branchStandardDenominator])
  | one =>
      apply Associated.of_eq
      simp [branchCoordinateChange, branchDenominator, branchStandardDenominator]
      ring
  | inverseParameter =>
      rw [branchCoordinateChange_denominator_inverseParameter R t ht]
      exact associated_unit_mul_left _ _
        ((ht.mul ht).map Polynomial.C)
  | infinity => exact Associated.of_eq (by simp [branchCoordinateChange,
      branchDenominator, branchStandardDenominator])

/-- The prescribed polynomial coordinate identifies its localization with the
standard projective-chart localization.  For the inverse-parameter section the
two denominators differ by the unit `t²`. -/
def branchAffineAlgEquiv (i : FourPointBranch) (ht : IsUnit t) :
    Localization.Away (branchDenominator R t i) ≃ₐ[R]
      Localization.Away (branchStandardDenominator R t i) := by
  letI : IsLocalization.Away
      (branchCoordinateChange R t i ht (branchDenominator R t i))
      (Localization.Away (branchStandardDenominator R t i)) :=
    IsLocalization.Away.of_associated
      (branchCoordinateChange_denominator_associated R t i ht).symm
  exact IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (branchDenominator R t i))
    (T := Submonoid.powers
      (branchCoordinateChange R t i ht (branchDenominator R t i)))
    (Localization.Away (branchDenominator R t i))
    (Localization.Away (branchStandardDenominator R t i))
    (branchCoordinateChange R t i ht) (by simp only [Submonoid.map_powers])

/-- The localized prescribed coordinate becomes the retained section's
coordinate in the standard chart. -/
theorem branchAffineAlgEquiv_X (i : FourPointBranch) (ht : IsUnit t) :
    branchAffineAlgEquiv R t i ht
        (algebraMap (Polynomial R)
          (Localization.Away (branchDenominator R t i)) Polynomial.X) =
      algebraMap (Polynomial R)
        (Localization.Away (branchStandardDenominator R t i))
          (branchStandardMissingCoordinate R t i) := by
  simp only [branchAffineAlgEquiv, IsLocalization.algEquivOfAlgEquiv_eq,
    branchCoordinateChange_X]

/-- Each target branch neighbourhood is the affine scheme with the exact
prescribed coordinate and denominator of Definition 2.3. -/
def branchAffineIso (i : FourPointBranch) (ht : IsUnit t) :
    branchNeighbourhood R t i ≅
      Spec (CommRingCat.of (Localization.Away (branchDenominator R t i))) :=
  branchStandardAffineIso R t i ≪≫
    Scheme.Spec.mapIso (branchAffineAlgEquiv R t i ht).toCommRingCatIso.op

/-- The prescribed affine presentation maps into the target through its
ordinary projective chart. -/
@[reassoc]
theorem branchAffineIso_inv_inclusion (i : FourPointBranch) (ht : IsUnit t) :
    (branchAffineIso R t i ht).inv ≫ branchInclusion R t i =
      Spec.map (CommRingCat.ofHom
        ((branchAffineAlgEquiv R t i ht).symm.toRingHom.comp
          (algebraMap (Polynomial R)
            (Localization.Away (branchStandardDenominator R t i))))) ≫
        branchStandardChart R i := by
  simp only [branchAffineIso, Iso.trans_inv, Category.assoc,
    branchStandardAffineIso_inv_inclusion]
  change Spec.map (CommRingCat.ofHom
      (branchAffineAlgEquiv R t i ht).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R)
        (Localization.Away (branchStandardDenominator R t i)))) ≫
      branchStandardChart R i = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The prescribed affine presentation carries the original coefficient-ring map. -/
@[reassoc]
theorem branchAffineIso_inv_toSpec (i : FourPointBranch) (ht : IsUnit t) :
    (branchAffineIso R t i ht).inv ≫ branchInclusion R t i ≫ toSpec R =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (branchDenominator R t i)))) := by
  simp only [branchAffineIso, Iso.trans_inv, Category.assoc,
    branchStandardAffineIso_inv_toSpec]
  change Spec.map (CommRingCat.ofHom
      (branchAffineAlgEquiv R t i ht).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (branchStandardDenominator R t i)))) = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (branchAffineAlgEquiv R t i ht).symm.commutes a

/-- The common four-point complement is the missing-coordinate principal open
in each standard affine presentation. -/
theorem branchStandardAffineIso_preimage_fourPointOpen (i : FourPointBranch) :
    ((branchStandardAffineIso R t i).inv ≫ branchInclusion R t i) ⁻¹ᵁ
        fourPointOpen R t =
      PrimeSpectrum.basicOpen
        (algebraMap (Polynomial R)
          (Localization.Away (branchStandardDenominator R t i))
          (branchStandardMissingCoordinate R t i)) := by
  rw [branchStandardAffineIso_inv_inclusion, Scheme.Hom.comp_preimage,
    branchStandardChart_preimage_fourPointOpen, SpecMap_preimage_basicOpen,
    map_mul, PrimeSpectrum.basicOpen_mul]
  have hunit : IsUnit (algebraMap (Polynomial R)
      (Localization.Away (branchStandardDenominator R t i))
      (branchStandardDenominator R t i)) :=
    IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
  have htop : PrimeSpectrum.basicOpen (algebraMap (Polynomial R)
      (Localization.Away (branchStandardDenominator R t i))
      (branchStandardDenominator R t i)) = ⊤ := by
    have hm : PrimeSpectrum.basicOpen (algebraMap (Polynomial R)
        (Localization.Away (branchStandardDenominator R t i))
        (branchStandardDenominator R t i)) ⊓ PrimeSpectrum.basicOpen v = ⊤ := by
      rw [← PrimeSpectrum.basicOpen_mul, hv, PrimeSpectrum.basicOpen_one]
    exact top_unique (hm ▸ inf_le_left)
  simp [htop]
  rfl

/-- In the prescribed coordinate, the four-point complement is exactly `D(u)`. -/
theorem branchAffineIso_preimage_fourPointOpen (i : FourPointBranch) (ht : IsUnit t) :
    ((branchAffineIso R t i ht).inv ≫ branchInclusion R t i) ⁻¹ᵁ
        fourPointOpen R t =
      PrimeSpectrum.basicOpen
        (algebraMap (Polynomial R)
          (Localization.Away (branchDenominator R t i)) Polynomial.X) := by
  simp only [branchAffineIso, Iso.trans_inv, Category.assoc]
  change (Spec.map (CommRingCat.ofHom
      (branchAffineAlgEquiv R t i ht).symm.toRingHom) ≫
      (branchStandardAffineIso R t i).inv ≫ branchInclusion R t i) ⁻¹ᵁ
        fourPointOpen R t = _
  rw [Scheme.Hom.comp_preimage,
    branchStandardAffineIso_preimage_fourPointOpen, SpecMap_preimage_basicOpen]
  congr 1
  rw [← branchAffineAlgEquiv_X R t i ht]
  simp

end AlgebraicGeometry.ProjectiveLine
