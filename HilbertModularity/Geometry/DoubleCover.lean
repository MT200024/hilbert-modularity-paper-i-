/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.QuadraticLocalization
public import HilbertModularity.Geometry.ProjectiveLine
public import HilbertModularity.Geometry.ProjectiveChart
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Double covers obtained from reciprocal affine charts

A degree `2n` binary section gives two quadratic algebras. On their common
Laurent chart the quadratic generators differ by the transition `u⁻ⁿ` of
`O(-n)`. Gluing their spectra constructs the relative spectrum of
`O ⊕ O(-n)` with the specified quadratic multiplication. The two chart
pullback theorems identify this construction over the standard affine cover
of the actual scheme `Proj R[U,Z]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial LaurentPolynomial
open scoped QuadraticAlgebra

namespace AlgebraicGeometry.DoubleCover

variable {R : Type*} [CommRing R]

/-- The coordinate ring of a quadratic affine chart. -/
abbrev ChartRing (f : R[X]) := QuadraticAlgebra R[X] f 0

/-- The quadratic chart is free on the constant and square-root coordinates. -/
def chartBasis (f : R[X]) : Module.Basis (Fin 2) R[X] (ChartRing f) :=
  QuadraticAlgebra.basis f 0

/-- The square-root coordinate satisfies precisely the branch equation. -/
theorem chartGenerator_sq (f : R[X]) :
    (QuadraticAlgebra.omega : ChartRing f) ^ 2 = algebraMap R[X] (ChartRing f) f := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp

/-- The coordinate ring where the base coordinate is invertible. -/
abbrev OverlapRing (f : R[X]) :=
  QuadraticAlgebra R[T;T⁻¹] (algebraMap R[X] R[T;T⁻¹] f)
    (algebraMap R[X] R[T;T⁻¹] 0)

/-- The overlap is the localization of the affine chart away from its coordinate. -/
instance overlap_isLocalization (f : R[X]) :
    IsLocalization.Away (algebraMap R[X] (ChartRing f) X) (OverlapRing f) :=
  QuadraticAlgebra.isLocalizationAway f 0 X

/-- Inclusion of the Laurent overlap into a quadratic affine chart. -/
def overlapInclusion (f : R[X]) :
    Spec (CommRingCat.of (OverlapRing f)) ⟶ Spec (CommRingCat.of (ChartRing f)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChartRing f) (OverlapRing f)))

instance overlapInclusion_isOpenImmersion (f : R[X]) :
    IsOpenImmersion (overlapInclusion f) :=
  IsOpenImmersion.of_isLocalization (algebraMap R[X] (ChartRing f) X)

/-- The overlap is exactly the open locus where the affine coordinate is invertible. -/
theorem overlapInclusion_opensRange (f : R[X]) :
    (overlapInclusion f).opensRange =
      PrimeSpectrum.basicOpen (algebraMap R[X] (ChartRing f) X) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (OverlapRing f)
    (algebraMap R[X] (ChartRing f) X)

/-- An integral power of the invertible Laurent coordinate. -/
def coordinateUnit (n : ℤ) : R[T;T⁻¹]ˣ :=
  Units.mkOfMulEqOne (T n) (T (-n)) (by rw [← T_add]; simp)

@[simp] theorem coe_coordinateUnit (n : ℤ) :
    (coordinateUnit (R := R) n : R[T;T⁻¹]) = T n := rfl

/-- The change of quadratic generator and reciprocal base coordinate on the overlap. -/
def transition (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    OverlapRing g ≃+* OverlapRing f :=
  (QuadraticAlgebra.mapCoeffsEquiv invert.toRingEquiv
    (algebraMap R[X] R[T;T⁻¹] g) (algebraMap R[X] R[T;T⁻¹] 0)).trans
    (QuadraticAlgebra.changeGeneratorEquiv
      (algebraMap R[X] R[T;T⁻¹] f) (algebraMap R[X] R[T;T⁻¹] 0)
      (coordinateUnit (-(n : ℤ))) 0
      (a' := invert (algebraMap R[X] R[T;T⁻¹] g))
      (b' := invert (algebraMap R[X] R[T;T⁻¹] 0))
      (by
        rw [LaurentPolynomial.algebraMap_eq_toLaurent g,
          LaurentPolynomial.algebraMap_eq_toLaurent f]
        simpa only [map_zero, coe_coordinateUnit, mul_zero, sub_zero,
          zero_pow (by decide : 2 ≠ 0)] using h)
      (by simp)).toRingEquiv

/-- The scalar part of the overlap transition substitutes the reciprocal coordinate. -/
@[simp]
theorem transition_re (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) (z : OverlapRing g) :
    (transition f g n h z).re = invert z.re := by
  simp [transition, QuadraticAlgebra.mapCoeffsEquiv, QuadraticAlgebra.mapCoeffs,
    QuadraticAlgebra.changeGeneratorEquiv_apply]

/-- The quadratic generator transforms by the transition of `O(-n)`. -/
@[simp]
theorem transition_im (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) (z : OverlapRing g) :
    (transition f g n h z).im = invert z.im * T (-(n : ℤ)) := by
  simp [transition, QuadraticAlgebra.mapCoeffsEquiv, QuadraticAlgebra.mapCoeffs,
    QuadraticAlgebra.changeGeneratorEquiv_apply]

/-- On the overlap the square-root coordinate transforms by `u⁻ⁿ`. -/
theorem transition_generator (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    transition f g n h (QuadraticAlgebra.omega : OverlapRing g) =
      algebraMap R[T;T⁻¹] (OverlapRing f) (T (-(n : ℤ))) * QuadraticAlgebra.omega := by
  apply QuadraticAlgebra.ext <;> simp

/-- The second inclusion of the common Laurent chart, after its transition. -/
def overlapInclusionInfinity (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    Spec (CommRingCat.of (OverlapRing f)) ⟶ Spec (CommRingCat.of (ChartRing g)) :=
  Spec.map (transition f g n h).toCommRingCatIso.hom ≫ overlapInclusion g

instance overlapInclusionInfinity_isOpenImmersion (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsOpenImmersion (overlapInclusionInfinity f g n h) := by
  unfold overlapInclusionInfinity
  infer_instance

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous base coordinates `[u : 1]` on the finite chart. -/
def finiteCoordinates (f : R[X]) : MvPolynomial (Fin 2) R →+* ChartRing f :=
  MvPolynomial.eval₂Hom (algebraMap R (ChartRing f))
    (fun i => if i = 0 then algebraMap R[X] (ChartRing f) X else 1)

/-- Homogeneous base coordinates `[1 : z]` on the chart at infinity. -/
def infinityCoordinates (g : R[X]) : MvPolynomial (Fin 2) R →+* ChartRing g :=
  MvPolynomial.eval₂Hom (algebraMap R (ChartRing g))
    (fun i => if i = 0 then 1 else algebraMap R[X] (ChartRing g) X)

/-- Projection of the finite quadratic chart into the actual projective line `Proj R[U,Z]`. -/
def finiteProjection (f : R[X]) :
    Spec (CommRingCat.of (ChartRing f)) ⟶ ProjectiveLine R :=
  Proj.fromSpecOfUnit (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (finiteCoordinates f) (r := MvPolynomial.X 1) (by decide : 0 < 1)
    (MvPolynomial.isHomogeneous_X R 1) (by simp [finiteCoordinates])

/-- Projection of the quadratic chart at infinity into `Proj R[U,Z]`. -/
def infinityProjection (g : R[X]) :
    Spec (CommRingCat.of (ChartRing g)) ⟶ ProjectiveLine R :=
  Proj.fromSpecOfUnit (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (infinityCoordinates g) (r := MvPolynomial.X 0) (by decide : 0 < 1)
    (MvPolynomial.isHomogeneous_X R 0) (by simp [infinityCoordinates])

set_option backward.isDefEq.respectTransparency false in
/-- The finite chart projection factors through the standard affine chart of the base. -/
theorem finiteProjection_factor (f : R[X]) :
    finiteProjection f = Spec.map (CommRingCat.ofHom (algebraMap R[X] (ChartRing f))) ≫
      ProjectiveLine.chartMap R 0 1 (by decide) := by
  have hc : finiteCoordinates f = (algebraMap R[X] (ChartRing f)).comp
      (ProjectiveLine.chartCoordinates R 0) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      apply QuadraticAlgebra.ext <;>
        simp [finiteCoordinates, ProjectiveLine.chartCoordinates]
    · intro i
      fin_cases i <;> simp [finiteCoordinates, ProjectiveLine.chartCoordinates]
  unfold finiteProjection ProjectiveLine.chartMap
  rw [← Proj.fromSpecOfUnit_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The reciprocal chart projection factors through the other standard affine chart of the base. -/
theorem infinityProjection_factor (g : R[X]) :
    infinityProjection g = Spec.map (CommRingCat.ofHom (algebraMap R[X] (ChartRing g))) ≫
      ProjectiveLine.chartMap R 1 0 (by decide) := by
  have hc : infinityCoordinates g = (algebraMap R[X] (ChartRing g)).comp
      (ProjectiveLine.chartCoordinates R 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      apply QuadraticAlgebra.ext <;>
        simp [infinityCoordinates, ProjectiveLine.chartCoordinates]
    · intro i
      fin_cases i <;> simp [infinityCoordinates, ProjectiveLine.chartCoordinates]
  unfold infinityProjection ProjectiveLine.chartMap
  rw [← Proj.fromSpecOfUnit_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The finite chart lies over the finite standard open of the projective line. -/
theorem finiteProjection_preimage_finite (f : R[X]) :
    finiteProjection f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X 1) = ⊤ := by
  unfold finiteProjection
  rw [Proj.fromSpecOfUnit_preimage_basicOpen_one _ _ _ (MvPolynomial.isHomogeneous_X R 1)
    (by simp [finiteCoordinates])]
  simp [finiteCoordinates]

set_option backward.isDefEq.respectTransparency false in
/-- The reciprocal chart meets the finite standard open precisely on the Laurent overlap. -/
theorem infinityProjection_preimage_finite (g : R[X]) :
    infinityProjection g ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X 1) = (overlapInclusion g).opensRange := by
  unfold infinityProjection
  rw [Proj.fromSpecOfUnit_preimage_basicOpen_one _ _ _ (MvPolynomial.isHomogeneous_X R 1)
    (by simp [infinityCoordinates]), overlapInclusion_opensRange]
  simp [infinityCoordinates]

set_option backward.isDefEq.respectTransparency false in
/-- The reciprocal chart lies over the reciprocal standard open of the projective line. -/
theorem infinityProjection_preimage_infinity (g : R[X]) :
    infinityProjection g ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X 0) = ⊤ := by
  unfold infinityProjection
  rw [Proj.fromSpecOfUnit_preimage_basicOpen_one _ _ _ (MvPolynomial.isHomogeneous_X R 0)
    (by simp [infinityCoordinates])]
  simp [infinityCoordinates]

set_option backward.isDefEq.respectTransparency false in
/-- The finite chart meets the reciprocal standard open precisely on the Laurent overlap. -/
theorem finiteProjection_preimage_infinity (f : R[X]) :
    finiteProjection f ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X 0) = (overlapInclusion f).opensRange := by
  unfold finiteProjection
  rw [Proj.fromSpecOfUnit_preimage_basicOpen_one _ _ _ (MvPolynomial.isHomogeneous_X R 0)
    (by simp [finiteCoordinates]), overlapInclusion_opensRange]
  simp [finiteCoordinates]

/-- Finite-chart homogeneous coordinates restricted to the Laurent overlap. -/
def finiteOverlapCoordinates (f : R[X]) : MvPolynomial (Fin 2) R →+* OverlapRing f :=
  (algebraMap (ChartRing f) (OverlapRing f)).comp (finiteCoordinates f)

/-- Infinity-chart homogeneous coordinates transported to the same Laurent overlap. -/
def infinityOverlapCoordinates (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    MvPolynomial (Fin 2) R →+* OverlapRing f :=
  (transition f g n h).toRingHom.comp
    ((algebraMap (ChartRing g) (OverlapRing g)).comp (infinityCoordinates g))

/-- The finite coordinates on the overlap are `[u : 1]`. -/
theorem finiteOverlapCoordinates_X (f : R[X]) (i : Fin 2) :
    finiteOverlapCoordinates f (MvPolynomial.X i) =
      if i = 0 then algebraMap R[T;T⁻¹] (OverlapRing f) (T 1) else 1 := by
  fin_cases i <;> apply QuadraticAlgebra.ext <;>
    simp [finiteOverlapCoordinates, finiteCoordinates, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, LaurentPolynomial.algebraMap_eq_toLaurent]

/-- The infinity coordinates on the overlap are `[1 : u⁻¹]`. -/
theorem infinityOverlapCoordinates_X (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) (i : Fin 2) :
    infinityOverlapCoordinates f g n h (MvPolynomial.X i) =
      if i = 0 then 1 else algebraMap R[T;T⁻¹] (OverlapRing f) (T (-1)) := by
  fin_cases i <;> apply QuadraticAlgebra.ext <;>
    simp [infinityOverlapCoordinates, infinityCoordinates, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, LaurentPolynomial.algebraMap_eq_toLaurent]

/-- Both chart descriptions preserve the coefficient ring on the overlap. -/
@[simp]
theorem finiteOverlapCoordinates_C (f : R[X]) (r : R) :
    finiteOverlapCoordinates f (MvPolynomial.C r) = algebraMap R (OverlapRing f) r := by
  apply QuadraticAlgebra.ext <;>
    simp [finiteOverlapCoordinates, finiteCoordinates, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, LaurentPolynomial.algebraMap_eq_toLaurent,
      LaurentPolynomial.algebraMap_apply]

/-- The infinity coordinates preserve the same coefficient ring after transition. -/
@[simp]
theorem infinityOverlapCoordinates_C (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) (r : R) :
    infinityOverlapCoordinates f g n h (MvPolynomial.C r) = algebraMap R (OverlapRing f) r := by
  apply QuadraticAlgebra.ext <;>
    simp [infinityOverlapCoordinates, infinityCoordinates, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs, LaurentPolynomial.algebraMap_eq_toLaurent,
      LaurentPolynomial.algebraMap_apply]

/-- The unit that relates `[u:1]` to `[1:u⁻¹]` on the overlap. -/
def overlapCoordinateUnit (f : R[X]) : (OverlapRing f)ˣ :=
  (coordinateUnit (R := R) 1).map (algebraMap R[T;T⁻¹] (OverlapRing f)).toMonoidHom

@[simp]
theorem coe_overlapCoordinateUnit (f : R[X]) :
    (overlapCoordinateUnit f : OverlapRing f) =
      algebraMap R[T;T⁻¹] (OverlapRing f) (T 1) := rfl

/-- The two homogeneous coordinate pairs differ by their common invertible coordinate. -/
theorem overlapCoordinates_X (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) (i : Fin 2) :
    finiteOverlapCoordinates f (MvPolynomial.X i) =
      (overlapCoordinateUnit f : OverlapRing f) *
        infinityOverlapCoordinates f g n h (MvPolynomial.X i) := by
  rw [finiteOverlapCoordinates_X, infinityOverlapCoordinates_X, coe_overlapCoordinateUnit]
  by_cases hi : i = 0
  · simp [hi]
  · simp only [ite_eq_right hi]
    rw [← map_mul, ← T_add]
    simp

/-- The two coordinate descriptions scale every homogeneous polynomial by its degree. -/
theorem overlapCoordinates_homogeneous (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f)
    (k : ℕ) (P : MvPolynomial (Fin 2) R) (hP : P.IsHomogeneous k) :
    finiteOverlapCoordinates f P = (overlapCoordinateUnit f : OverlapRing f) ^ k *
      infinityOverlapCoordinates f g n h P := by
  let v := fun i => infinityOverlapCoordinates f g n h (MvPolynomial.X i)
  have hψ : infinityOverlapCoordinates f g n h =
      MvPolynomial.eval₂Hom (algebraMap R (OverlapRing f)) v := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp [v]
  have hφ : finiteOverlapCoordinates f =
      MvPolynomial.eval₂Hom (algebraMap R (OverlapRing f))
        (fun i => (overlapCoordinateUnit f : OverlapRing f) * v i) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
      exact overlapCoordinates_X f g n h i
  rw [hφ, hψ]
  exact hP.eval₂_mul_variables (algebraMap R (OverlapRing f)) v (overlapCoordinateUnit f)

set_option backward.isDefEq.respectTransparency false in
/-- The two chart projections agree on their Laurent overlap as morphisms into `Proj R[U,Z]`. -/
theorem projection_overlap (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    overlapInclusion f ≫ finiteProjection f =
      overlapInclusionInfinity f g n h ≫ infinityProjection g := by
  have hfr : IsUnit (finiteOverlapCoordinates f (MvPolynomial.X 1)) := by
    simp [finiteOverlapCoordinates_X]
  have hfs : IsUnit (finiteOverlapCoordinates f (MvPolynomial.X 0)) := by
    simpa [finiteOverlapCoordinates_X] using
      (coordinateUnit (R := R) 1).isUnit.map (algebraMap R[T;T⁻¹] (OverlapRing f))
  have hgr : IsUnit (infinityOverlapCoordinates f g n h (MvPolynomial.X 1)) := by
    simpa [infinityOverlapCoordinates_X] using
      (coordinateUnit (R := R) (-1)).isUnit.map (algebraMap R[T;T⁻¹] (OverlapRing f))
  have hgs : IsUnit (infinityOverlapCoordinates f g n h (MvPolynomial.X 0)) := by
    simp [infinityOverlapCoordinates_X]
  have he := Proj.fromSpecOfUnit_eq_of_unit_scaling_chart
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (finiteOverlapCoordinates f) (infinityOverlapCoordinates f g n h) (overlapCoordinateUnit f)
    (overlapCoordinates_homogeneous f g n h)
    (by decide : 0 < 1) (by decide : 0 < 1)
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2)) hfr hfs hgr hgs
  unfold overlapInclusionInfinity overlapInclusion finiteProjection infinityProjection
  rw [Category.assoc]
  rw [← Proj.fromSpecOfUnit_comp, ← Proj.fromSpecOfUnit_comp]
  change _ = Spec.map (CommRingCat.ofHom (transition f g n h).toRingHom) ≫ _
  rw [← Proj.fromSpecOfUnit_comp]
  exact he

/-- The global double-cover scheme, including both affine charts. -/
def scheme (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) : Scheme :=
  pushout (overlapInclusion f) (overlapInclusionInfinity f g n h)

/-- The global double cover as a morphism to the actual projective line. -/
def toProjectiveLine (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    scheme f g n h ⟶ ProjectiveLine R :=
  pushout.desc (finiteProjection f) (infinityProjection g) (projection_overlap f g n h)

/-- The finite-coordinate chart in the glued cover. -/
def finiteChart (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    Spec (CommRingCat.of (ChartRing f)) ⟶ scheme f g n h :=
  pushout.inl (overlapInclusion f) (overlapInclusionInfinity f g n h)

/-- The chart at infinity in the glued cover. -/
def infinityChart (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    Spec (CommRingCat.of (ChartRing g)) ⟶ scheme f g n h :=
  pushout.inr (overlapInclusion f) (overlapInclusionInfinity f g n h)

instance finiteChart_isOpenImmersion (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsOpenImmersion (finiteChart f g n h) := by
  change IsOpenImmersion (colimit.ι
    (span (overlapInclusion f) (overlapInclusionInfinity f g n h)) WalkingSpan.left)
  infer_instance

instance infinityChart_isOpenImmersion (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsOpenImmersion (infinityChart f g n h) := by
  change IsOpenImmersion (colimit.ι
    (span (overlapInclusion f) (overlapInclusionInfinity f g n h)) WalkingSpan.right)
  infer_instance

/-- The finite and reciprocal charts cover the entire glued scheme. -/
theorem charts_jointly_surjective (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f)
    (x : scheme f g n h) :
    (∃ y, finiteChart f g n h y = x) ∨ (∃ y, infinityChart f g n h y = x) := by
  obtain ⟨i, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (overlapInclusion f) (overlapInclusionInfinity f g n h)) x
  rcases i with _ | (_ | _)
  · left
    refine ⟨overlapInclusion f y, ?_⟩
    exact congrArg (fun m => m y) (colimit.w
      (span (overlapInclusion f) (overlapInclusionInfinity f g n h)) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

/-- The two quadratic spectra form an open cover of the glued double cover. -/
def openCover (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    (scheme f g n h).OpenCover where
  I₀ := Bool
  X b := Bool.rec (Spec (CommRingCat.of (ChartRing f)))
    (Spec (CommRingCat.of (ChartRing g))) b
  f b := Bool.rec (finiteChart f g n h) (infinityChart f g n h) b
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases charts_jointly_surjective f g n h x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩
    · intro b
      cases b <;> dsimp <;> infer_instance

/-- The two chart morphisms identify exactly along the prescribed overlap. -/
@[reassoc]
theorem overlap_condition (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    overlapInclusion f ≫ finiteChart f g n h =
      overlapInclusionInfinity f g n h ≫ infinityChart f g n h :=
  pushout.condition

/-- The finite chart recovers its original projection. -/
@[reassoc (attr := simp)]
theorem finiteChart_toProjectiveLine (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    finiteChart f g n h ≫ toProjectiveLine f g n h = finiteProjection f :=
  pushout.inl_desc _ _ _

/-- The chart at infinity recovers its original projection. -/
@[reassoc (attr := simp)]
theorem infinityChart_toProjectiveLine (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    infinityChart f g n h ≫ toProjectiveLine f g n h = infinityProjection g :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse image of the finite base chart is exactly the finite quadratic chart. -/
theorem toProjectiveLine_preimage_finite (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    toProjectiveLine f g n h ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) =
        (finiteChart f g n h).opensRange := by
  ext x
  constructor
  · intro hx
    rcases charts_jointly_surjective f g n h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨y, rfl⟩
    · have hy : y ∈ infinityProjection g ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) := by
        change (infinityChart f g n h ≫ toProjectiveLine f g n h) y ∈
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) at hx
        rwa [infinityChart_toProjectiveLine] at hx
      rw [infinityProjection_preimage_finite] at hy
      obtain ⟨z, rfl⟩ := hy
      obtain ⟨w, rfl⟩ := (Spec.map (transition f g n h).toCommRingCatIso.hom).homeomorph.surjective z
      refine ⟨overlapInclusion f w, ?_⟩
      exact congrArg (fun m => m w) (overlap_condition f g n h)
  · rintro ⟨y, rfl⟩
    change (finiteChart f g n h ≫ toProjectiveLine f g n h) y ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1)
    rw [finiteChart_toProjectiveLine]
    have hy : y ∈ finiteProjection f ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) := by
      rw [finiteProjection_preimage_finite]
      trivial
    exact hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse image of the reciprocal base chart is exactly the reciprocal quadratic chart. -/
theorem toProjectiveLine_preimage_infinity (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    toProjectiveLine f g n h ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) =
        (infinityChart f g n h).opensRange := by
  ext x
  constructor
  · intro hx
    rcases charts_jointly_surjective f g n h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have hy : y ∈ finiteProjection f ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) := by
        change (finiteChart f g n h ≫ toProjectiveLine f g n h) y ∈
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) at hx
        rwa [finiteChart_toProjectiveLine] at hx
      rw [finiteProjection_preimage_infinity] at hy
      obtain ⟨w, rfl⟩ := hy
      refine ⟨overlapInclusionInfinity f g n h w, ?_⟩
      exact congrArg (fun m => m w) (overlap_condition f g n h).symm
    · exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    change (infinityChart f g n h ≫ toProjectiveLine f g n h) y ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0)
    rw [infinityChart_toProjectiveLine]
    have hy : y ∈ infinityProjection g ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) := by
      rw [infinityProjection_preimage_infinity]
      trivial
    exact hy

/-- Over the finite affine chart of the base, the cover is exactly the spectrum of its quadratic algebra. -/
theorem finiteChart_isPullback (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] (ChartRing f))))
      (finiteChart f g n h) (ProjectiveLine.chartMap R 0 1 (by decide))
      (toProjectiveLine f g n h) := by
  apply IsOpenImmersion.isPullback
  · rw [finiteChart_toProjectiveLine, finiteProjection_factor]
  · rw [ProjectiveLine.chartMap_opensRange, toProjectiveLine_preimage_finite]

/-- Over the reciprocal affine chart of the base, the cover is exactly the other quadratic spectrum. -/
theorem infinityChart_isPullback (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R[X] (ChartRing g))))
      (infinityChart f g n h) (ProjectiveLine.chartMap R 1 0 (by decide))
      (toProjectiveLine f g n h) := by
  apply IsOpenImmersion.isPullback
  · rw [infinityChart_toProjectiveLine, infinityProjection_factor]
  · rw [ProjectiveLine.chartMap_opensRange, toProjectiveLine_preimage_infinity]

/-- The finite chart projection respects the coefficient-ring structure. -/
@[reassoc (attr := simp)]
theorem finiteProjection_toSpec (f : R[X]) :
    finiteProjection f ≫ ProjectiveLine.toSpec R =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing f))) := by
  rw [finiteProjection_factor, Category.assoc, ProjectiveLine.chartMap_toSpec, ← Spec.map_comp]
  congr 1

/-- The reciprocal chart projection respects the coefficient-ring structure. -/
@[reassoc (attr := simp)]
theorem infinityProjection_toSpec (g : R[X]) :
    infinityProjection g ≫ ProjectiveLine.toSpec R =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing g))) := by
  rw [infinityProjection_factor, Category.assoc, ProjectiveLine.chartMap_toSpec, ← Spec.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/-- Each quadratic chart is finite over the corresponding affine base chart. -/
instance chartProjection_isFinite (f : R[X]) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R[X] (ChartRing f)))) := by
  rw [IsFinite.SpecMap_iff]
  change (algebraMap R[X] (ChartRing f)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Gluing the two finite quadratic algebras gives a finite morphism to the projective line. -/
instance toProjectiveLine_isFinite (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsFinite (toProjectiveLine f g n h) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite)
    (ProjectiveLine.standardOpenCover R)
  intro b
  cases b
  · change IsFinite (pullback.snd (toProjectiveLine f g n h)
      (ProjectiveLine.chartMap R 0 1 (by decide)))
    rw [← (finiteChart_isPullback f g n h).flip.isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (toProjectiveLine f g n h)
      (ProjectiveLine.chartMap R 1 0 (by decide)))
    rw [← (infinityChart_isPullback f g n h).flip.isoPullback_inv_snd]
    infer_instance

/-- The glued double cover is proper over the coefficient ring. -/
instance toSpec_isProper (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    IsProper (toProjectiveLine f g n h ≫ ProjectiveLine.toSpec R) := by
  infer_instance

/-- Localization in the base coordinate is injective on the free quadratic coordinate algebra. -/
theorem overlap_algebraMap_injective (f : R[X]) :
    Function.Injective (algebraMap (ChartRing f) (OverlapRing f)) := by
  intro x y hxy
  apply QuadraticAlgebra.ext
  · apply Polynomial.toLaurent_injective
    exact congrArg (fun z : OverlapRing f => z.re) hxy
  · apply Polynomial.toLaurent_injective
    exact congrArg (fun z : OverlapRing f => z.im) hxy

/-- The Laurent overlap is dense in each quadratic affine chart. -/
theorem overlapInclusion_denseRange (f : R[X]) : DenseRange (overlapInclusion f) := by
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  change RingHom.ker (algebraMap (ChartRing f) (OverlapRing f)) ≤ nilradical (ChartRing f)
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (overlap_algebraMap_injective f)]
  exact bot_le

/-- The reciprocal inclusion of the Laurent overlap is also dense. -/
theorem overlapInclusionInfinity_denseRange (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    DenseRange (overlapInclusionInfinity f g n h) :=
  (overlapInclusion_denseRange g).comp
    (Spec.map (transition f g n h).toCommRingCatIso.hom).homeomorph.surjective.denseRange
    (overlapInclusion g).continuous

/-- The finite affine equation is a dense open subscheme of the projective completion. -/
theorem finiteChart_denseRange (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f) :
    DenseRange (finiteChart f g n h) := by
  intro x
  rcases charts_jointly_surjective f g n h x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact subset_closure ⟨y, rfl⟩
  · have hy := (infinityChart f g n h).continuous.range_subset_closure_image_dense
      (overlapInclusionInfinity_denseRange f g n h) (Set.mem_range_self y)
    apply closure_mono ?_ hy
    rintro z ⟨w, ⟨v, rfl⟩, rfl⟩
    refine ⟨overlapInclusion f v, ?_⟩
    exact congrArg (fun m => m v) (overlap_condition f g n h)

end AlgebraicGeometry.DoubleCover
