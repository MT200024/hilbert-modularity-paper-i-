/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Morphisms into projective charts

Evaluation of homogeneous fractions constructs a morphism into a standard
projective chart whenever its distinguished homogeneous coordinate is a unit.
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Evaluate degree-zero homogeneous fractions in a ring where the denominator is a unit. -/
def homogeneousEvaluation (φ : A →+* B) (r : A) (hr : IsUnit (φ r)) :
    Away 𝒜 r →+* B :=
  (Localization.awayLift φ r hr).comp (algebraMap (Away 𝒜 r) (Localization.Away r))

/-- Evaluation is unchanged when its homogeneous denominator is multiplied by another unit. -/
theorem homogeneousEvaluation_comp_awayMap (φ : A →+* B) {r s : A}
    {m : ℕ} (hs : s ∈ 𝒜 m) (hr : IsUnit (φ r)) (hsu : IsUnit (φ s)) :
    (homogeneousEvaluation 𝒜 φ (r * s) (by simpa using hr.mul hsu)).comp
      (HomogeneousLocalization.awayMap 𝒜 hs rfl) = homogeneousEvaluation 𝒜 φ r hr := by
  have hrs : IsUnit (φ (r * s)) := by simpa using hr.mul hsu
  have hrl : IsUnit (algebraMap A (Localization.Away (r * s)) r) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right r s))
      (IsLocalization.Away.algebraMap_isUnit (r * s))
  ext z
  change Localization.awayLift φ (r * s) hrs
    (HomogeneousLocalization.val (HomogeneousLocalization.awayMap 𝒜 hs rfl z)) = _
  rw [HomogeneousLocalization.val_awayMap]
  change ((Localization.awayLift φ (r * s) hrs).comp
    (Localization.awayLift (algebraMap A (Localization.Away (r * s))) r hrl)) z.val =
      Localization.awayLift φ r hr z.val
  have hmap : (Localization.awayLift φ (r * s) hrs).comp
      (Localization.awayLift (algebraMap A (Localization.Away (r * s))) r hrl) =
        Localization.awayLift φ r hr := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    ext a
    simp [Localization.awayLift, IsLocalization.Away.lift_eq]
  rw [hmap]

/-- Evaluation of a homogeneous fraction satisfies its numerator-denominator identity. -/
theorem homogeneousEvaluation_mk_spec (φ : A →+* B) (r : A) (hr : IsUnit (φ r))
    (c : NumDenSameDeg 𝒜 (Submonoid.powers r)) :
    homogeneousEvaluation 𝒜 φ r hr (HomogeneousLocalization.mk c) * φ c.den = φ c.num := by
  have h := congrArg (Localization.awayLift φ r hr)
    (IsLocalization.mk'_spec (Localization.Away r) (c.num : A)
      (⟨c.den, c.den_mem⟩ : Submonoid.powers r))
  change Localization.awayLift φ r hr
    (Localization.mk (c.num : A) ⟨c.den, c.den_mem⟩) * φ c.den = φ c.num
  rw [Localization.mk_eq_mk']
  simpa only [map_mul, Localization.awayLift, IsLocalization.Away.lift_eq] using h

/-- Homogeneous rescaling by a unit has no effect on degree-zero homogeneous fractions. -/
theorem homogeneousEvaluation_eq_of_unit_scaling (φ ψ : A →+* B) (u : Bˣ)
    (hscale : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a = (u : B) ^ n * ψ a)
    (r : A) (hφ : IsUnit (φ r)) (hψ : IsUnit (ψ r)) :
    homogeneousEvaluation 𝒜 φ r hφ = homogeneousEvaluation 𝒜 ψ r hψ := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  have hf := homogeneousEvaluation_mk_spec 𝒜 φ r hφ c
  have hg := homogeneousEvaluation_mk_spec 𝒜 ψ r hψ c
  rw [hscale c.deg c.den c.den.property, hscale c.deg c.num c.num.property] at hf
  have hf' : (u : B) ^ c.deg *
      (homogeneousEvaluation 𝒜 φ r hφ (HomogeneousLocalization.mk c) * ψ c.den) =
        (u : B) ^ c.deg * ψ c.num := by
    simpa only [mul_left_comm, mul_assoc] using hf
  have heq := (u.isUnit.pow c.deg).mul_left_cancel hf'
  have hden : IsUnit (ψ c.den) := by
    obtain ⟨k, hk⟩ := c.den_mem
    rw [← hk, map_pow]
    exact hψ.pow k
  exact hden.mul_right_cancel (heq.trans hg.symm)

/-- A morphism into `Proj` obtained by evaluation on one standard affine chart. -/
def fromSpecOfUnit (φ : A →+* B) {r : A} {m : ℕ}
    (hm : 0 < m) (hr : r ∈ 𝒜 m) (hu : IsUnit (φ r)) :
    Spec (CommRingCat.of B) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (homogeneousEvaluation 𝒜 φ r hu)) ≫ awayι 𝒜 r hr hm

/-- Unit rescaling of homogeneous coordinates gives the same projective morphism. -/
theorem fromSpecOfUnit_eq_of_unit_scaling (φ ψ : A →+* B) (u : Bˣ)
    (hscale : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a = (u : B) ^ n * ψ a)
    {r : A} {m : ℕ} (hm : 0 < m) (hr : r ∈ 𝒜 m)
    (hφ : IsUnit (φ r)) (hψ : IsUnit (ψ r)) :
    fromSpecOfUnit 𝒜 φ hm hr hφ = fromSpecOfUnit 𝒜 ψ hm hr hψ := by
  unfold fromSpecOfUnit
  rw [homogeneousEvaluation_eq_of_unit_scaling 𝒜 φ ψ u hscale]

/-- Evaluation on a projective chart commutes with a homomorphism of target rings. -/
theorem homogeneousEvaluation_comp {C : Type u} [CommRing C]
    (φ : A →+* B) (χ : B →+* C) (r : A) (hr : IsUnit (φ r)) :
    homogeneousEvaluation 𝒜 (χ.comp φ) r (hr.map χ) =
      χ.comp (homogeneousEvaluation 𝒜 φ r hr) := by
  have hmap : Localization.awayLift (χ.comp φ) r (hr.map χ) =
      χ.comp (Localization.awayLift φ r hr) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    ext a
    simp [Localization.awayLift, IsLocalization.Away.lift_eq]
  ext z
  exact congrArg (fun f : Localization.Away r →+* C => f z.val) hmap

/-- Evaluation in the full localization is the canonical inclusion of homogeneous fractions. -/
theorem homogeneousEvaluation_algebraMap (r : A) :
    homogeneousEvaluation 𝒜 (algebraMap A (Localization.Away r)) r
      (IsLocalization.Away.algebraMap_isUnit r) =
        algebraMap (Away 𝒜 r) (Localization.Away r) := by
  have h : Localization.awayLift (algebraMap A (Localization.Away r)) r
      (IsLocalization.Away.algebraMap_isUnit r) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    ext a
    simp [Localization.awayLift]
  simp [homogeneousEvaluation, h]

/-- Projective chart morphisms are natural in the affine source. -/
@[reassoc]
theorem fromSpecOfUnit_comp {C : Type u} [CommRing C]
    (φ : A →+* B) (χ : B →+* C) {r : A} {m : ℕ}
    (hm : 0 < m) (hr : r ∈ 𝒜 m) (hu : IsUnit (φ r)) :
    fromSpecOfUnit 𝒜 (χ.comp φ) hm hr (hu.map χ) =
      Spec.map (CommRingCat.ofHom χ) ≫ fromSpecOfUnit 𝒜 φ hm hr hu := by
  unfold fromSpecOfUnit
  rw [homogeneousEvaluation_comp 𝒜 φ χ r hu, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc]

/-- Multiplying the chart coordinate by another homogeneous unit does not change the morphism. -/
theorem fromSpecOfUnit_mul (φ : A →+* B) {r s : A} {m n : ℕ}
    (hm : 0 < m) (hr : r ∈ 𝒜 m) (hs : s ∈ 𝒜 n)
    (hu : IsUnit (φ r)) (hv : IsUnit (φ s)) :
    fromSpecOfUnit 𝒜 φ (hm.trans_le (Nat.le_add_right m n))
      (SetLike.mul_mem_graded hr hs) (by simpa using hu.mul hv) =
        fromSpecOfUnit 𝒜 φ hm hr hu := by
  unfold fromSpecOfUnit
  rw [← SpecMap_awayMap_awayι 𝒜 hr hm hs rfl]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    homogeneousEvaluation_comp_awayMap 𝒜 φ hs hu hv]

/-- Two homogeneous coordinate descriptions agree even when different coordinates choose the charts. -/
theorem fromSpecOfUnit_eq_of_unit_scaling_chart (φ ψ : A →+* B) (u : Bˣ)
    (hscale : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → φ a = (u : B) ^ n * ψ a)
    {r s : A} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hr : r ∈ 𝒜 m) (hs : s ∈ 𝒜 n)
    (hφr : IsUnit (φ r)) (hφs : IsUnit (φ s))
    (hψr : IsUnit (ψ r)) (hψs : IsUnit (ψ s)) :
    fromSpecOfUnit 𝒜 φ hm hr hφr = fromSpecOfUnit 𝒜 ψ hn hs hψs := by
  rw [← fromSpecOfUnit_mul 𝒜 φ hm hr hs hφr hφs]
  rw [fromSpecOfUnit_eq_of_unit_scaling 𝒜 φ ψ u hscale
    (hm.trans_le (Nat.le_add_right m n)) (SetLike.mul_mem_graded hr hs)
    (by simpa using hφr.mul hφs) (by simpa using hψr.mul hψs)]
  have h := fromSpecOfUnit_mul 𝒜 ψ hn hs hr hψs hψr
  simpa only [mul_comm s r, Nat.add_comm n m] using h

/-- On a degree-one chart normalized to one, basic opens pull back by ordinary evaluation. -/
theorem fromSpecOfUnit_preimage_basicOpen_one (φ : A →+* B) {r s : A}
    (hr : r ∈ 𝒜 1) (hs : s ∈ 𝒜 1) (hφ : φ r = 1) :
    fromSpecOfUnit 𝒜 φ (by decide : 0 < 1) hr (by rw [hφ]; exact isUnit_one) ⁻¹ᵁ
      basicOpen 𝒜 s = PrimeSpectrum.basicOpen (φ s) := by
  unfold fromSpecOfUnit
  rw [Scheme.Hom.comp_preimage, awayι_preimage_basicOpen 𝒜 hr (by decide : 0 < 1)
    hs (by decide : 0 < 1), SpecMap_preimage_basicOpen]
  congr 1
  have h := homogeneousEvaluation_mk_spec 𝒜 φ r (by rw [hφ]; exact isUnit_one)
    ⟨1, ⟨s, hs⟩, ⟨r, hr⟩, ⟨1, pow_one _⟩⟩
  simpa [Away.isLocalizationElem, Away.mk, hφ] using h

end AlgebraicGeometry.Proj

namespace MvPolynomial

/-- Scaling every variable of a homogeneous polynomial multiplies its value by the degree power. -/
theorem IsHomogeneous.eval₂_mul_variables {R S ι : Type*} [CommSemiring R]
    [CommSemiring S] [Fintype ι] {P : MvPolynomial ι R} {n : ℕ}
    (hP : P.IsHomogeneous n) (φ : R →+* S) (v : ι → S) (u : S) :
    MvPolynomial.eval₂ φ (fun i => u * v i) P = u ^ n * MvPolynomial.eval₂ φ v P := by
  classical
  simp only [eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg := hP (mem_support_iff.mp hd)
  change (Finsupp.weight (fun _ : ι => (1 : ℕ))) d = n at hdeg
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at hdeg
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveLine

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type*) [CommRing R]

/-- The homogeneous localization defining a standard chart of the projective line. -/
abbrev ChartRing (j : Fin 2) :=
  HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) R) (X j)

/-- The constant coefficients in a standard projective chart. -/
def chartConstants (j : Fin 2) : R →+* ChartRing R j :=
  (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin 2) R)
    (Submonoid.powers (X j))).comp (constants R)

/-- The affine coordinate `Xᵢ/Xⱼ` in a standard projective chart. -/
def chartVariable (i j : Fin 2) : ChartRing R j :=
  HomogeneousLocalization.mk ⟨1, ⟨X i, isHomogeneous_X R i⟩,
    ⟨X j, isHomogeneous_X R j⟩, ⟨1, pow_one _⟩⟩

/-- Substitution of the chart coordinate in a one-variable polynomial. -/
def chartPolynomialMap (i j : Fin 2) : Polynomial R →+* ChartRing R j :=
  Polynomial.eval₂RingHom (chartConstants R j) (chartVariable R i j)

/-- Homogeneous coordinates of the affine parameterization with `Xⱼ = 1`. -/
def chartCoordinates (i : Fin 2) : MvPolynomial (Fin 2) R →+* Polynomial R :=
  eval₂Hom Polynomial.C (fun k => if k = i then Polynomial.X else 1)

/-- Evaluation of homogeneous fractions on the standard affine parameterization. -/
def chartEvaluation (i j : Fin 2) (hij : i ≠ j) : ChartRing R j →+* Polynomial R :=
  Proj.homogeneousEvaluation (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R i) (X j) (by simp [chartCoordinates, Ne.symm hij])

@[simp]
theorem chartEvaluation_constants (i j : Fin 2) (hij : i ≠ j) (r : R) :
    chartEvaluation R i j hij (chartConstants R j r) = Polynomial.C r := by
  have h := Proj.homogeneousEvaluation_mk_spec (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R i) (X j) (by simp [chartCoordinates, Ne.symm hij])
    ⟨0, ⟨C r, isHomogeneous_C (Fin 2) r⟩, 1, one_mem _⟩
  change Proj.homogeneousEvaluation (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R i) (X j) _
    (HomogeneousLocalization.mk ⟨0, ⟨C r, isHomogeneous_C (Fin 2) r⟩, 1, one_mem _⟩) = _
  simpa [chartCoordinates] using h

@[simp]
theorem chartEvaluation_variable (i j : Fin 2) (hij : i ≠ j) :
    chartEvaluation R i j hij (chartVariable R i j) = Polynomial.X := by
  have h := Proj.homogeneousEvaluation_mk_spec (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R i) (X j) (by simp [chartCoordinates, Ne.symm hij])
    ⟨1, ⟨X i, isHomogeneous_X R i⟩, ⟨X j, isHomogeneous_X R j⟩, ⟨1, pow_one _⟩⟩
  simpa [chartEvaluation, chartVariable, chartCoordinates, Ne.symm hij] using h

/-- Evaluation is a left inverse to polynomial substitution in the chart coordinate. -/
theorem chartEvaluation_comp_polynomialMap (i j : Fin 2) (hij : i ≠ j) :
    (chartEvaluation R i j hij).comp (chartPolynomialMap R i j) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [chartPolynomialMap]
  · simp [chartPolynomialMap]

/-- Constants in the chart map to ordinary constants in the full localization. -/
@[simp]
theorem chartConstants_val (j : Fin 2) (r : R) :
    (chartConstants R j r).val =
      algebraMap (MvPolynomial (Fin 2) R) (Localization.Away (X j)) (C r) := by
  change Localization.mk (C r) (1 : Submonoid.powers (X j)) = _
  exact Localization.mk_one_eq_algebraMap _

/-- The chart coordinate satisfies its defining fraction identity. -/
theorem chartVariable_val_mul (i j : Fin 2) :
    (chartVariable R i j).val *
      algebraMap (MvPolynomial (Fin 2) R) (Localization.Away (X j)) (X j) =
      algebraMap (MvPolynomial (Fin 2) R) (Localization.Away (X j)) (X i) := by
  change Localization.mk (X i : MvPolynomial (Fin 2) R)
    (⟨X j, ⟨1, pow_one _⟩⟩ : Submonoid.powers (X j : MvPolynomial (Fin 2) R)) *
      algebraMap (MvPolynomial (Fin 2) R) (Localization.Away (X j)) (X j) = _
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ _ _

/-- Normalized affine coordinates differ from the homogeneous coordinates by a unit. -/
theorem chartCoordinates_normalization (i j : Fin 2) (hij : i ≠ j) :
    let A := MvPolynomial (Fin 2) R
    let L := Localization.Away (X j : A)
    let α := algebraMap A L
    let χ := (algebraMap (ChartRing R j) L).comp (chartPolynomialMap R i j)
    ∀ k, α (X k) = α (X j) * χ (chartCoordinates R i (X k)) := by
  dsimp
  intro k
  have hk : k = i ∨ k = j := by omega
  rcases hk with hk | hk
  · subst k
    simp only [chartCoordinates, eval₂Hom_X', ite_true,
      chartPolynomialMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    exact (chartVariable_val_mul R i j).symm.trans (mul_comm _ _)
  · subst k
    simp [chartCoordinates, Ne.symm hij]

/-- Homogeneous polynomials obey the same normalization as their coordinates. -/
theorem chartCoordinates_normalization_homogeneous (i j : Fin 2) (hij : i ≠ j)
    (n : ℕ) (P : MvPolynomial (Fin 2) R) (hP : P.IsHomogeneous n) :
    let A := MvPolynomial (Fin 2) R
    let L := Localization.Away (X j : A)
    let α := algebraMap A L
    let χ := (algebraMap (ChartRing R j) L).comp (chartPolynomialMap R i j)
    α P = α (X j) ^ n * χ (chartCoordinates R i P) := by
  dsimp
  let A := MvPolynomial (Fin 2) R
  let L := Localization.Away (X j : A)
  let α := algebraMap A L
  let χ := (algebraMap (ChartRing R j) L).comp (chartPolynomialMap R i j)
  let ψ := χ.comp (chartCoordinates R i)
  let c := α.comp C
  let v := fun k => ψ (X k)
  have hc (r : R) : ψ (C r) = c r := by
    change algebraMap (ChartRing R j) L
      (chartPolynomialMap R i j (chartCoordinates R i (C r))) = _
    simp only [chartCoordinates, eval₂Hom_C, chartPolynomialMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact chartConstants_val R j r
  have hψ : ψ = eval₂Hom c v := by
    apply MvPolynomial.ringHom_ext
    · intro r; simpa using hc r
    · intro k; simp [v]
  have hα : α = eval₂Hom c (fun k => α (X j) * v k) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [c]
    · intro k
      rw [eval₂Hom_X']
      exact chartCoordinates_normalization R i j hij k
  change α P = α (X j) ^ n * ψ P
  conv_lhs => rw [hα]
  rw [hψ]
  exact hP.eval₂_mul_variables c v (α (X j))

/-- Polynomial substitution is also a right inverse on homogeneous fractions. -/
theorem chartPolynomialMap_comp_evaluation (i j : Fin 2) (hij : i ≠ j) :
    (chartPolynomialMap R i j).comp (chartEvaluation R i j hij) = RingHom.id _ := by
  let A := MvPolynomial (Fin 2) R
  let L := Localization.Away (X j : A)
  let α := algebraMap A L
  let χ := (algebraMap (ChartRing R j) L).comp (chartPolynomialMap R i j)
  let ψ := χ.comp (chartCoordinates R i)
  have hu : IsUnit (α (X j)) := IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨u, hu⟩ := hu
  have hscale (n : ℕ) (P : A) (hP : P.IsHomogeneous n) :
      α P = (u : L) ^ n * ψ P := by
    rw [hu]
    exact chartCoordinates_normalization_homogeneous R i j hij n P hP
  have hψunit : IsUnit (ψ (X j)) := by simp [ψ, chartCoordinates, Ne.symm hij]
  have he := Proj.homogeneousEvaluation_eq_of_unit_scaling
    (homogeneousSubmodule (Fin 2) R) α ψ u hscale (X j)
    (by rw [← hu]; exact u.isUnit) hψunit
  rw [Proj.homogeneousEvaluation_algebraMap] at he
  change algebraMap (ChartRing R j) L =
    Proj.homogeneousEvaluation (homogeneousSubmodule (Fin 2) R)
      (χ.comp (chartCoordinates R i)) (X j) _ at he
  rw [Proj.homogeneousEvaluation_comp (homogeneousSubmodule (Fin 2) R)
    (chartCoordinates R i) χ (X j) (by simp [chartCoordinates, Ne.symm hij])] at he
  ext z
  exact (congrArg (fun f : ChartRing R j →+* L => f z) he).symm

/-- The standard projective chart has the ordinary polynomial coordinate ring. -/
def chartEquivPolynomial (i j : Fin 2) (hij : i ≠ j) :
    ChartRing R j ≃+* Polynomial R :=
  RingEquiv.ofRingHom (chartEvaluation R i j hij) (chartPolynomialMap R i j)
    (chartEvaluation_comp_polynomialMap R i j hij)
    (chartPolynomialMap_comp_evaluation R i j hij)

/-- The affine parameterization of a standard chart of the projective line. -/
def chartMap (i j : Fin 2) (hij : i ≠ j) :
    Spec (CommRingCat.of (Polynomial R)) ⟶ ProjectiveLine R :=
  Proj.fromSpecOfUnit (homogeneousSubmodule (Fin 2) R) (chartCoordinates R i)
    (r := X j) (by decide : 0 < 1) (isHomogeneous_X R j)
    (by simp [chartCoordinates, Ne.symm hij])

set_option backward.isDefEq.respectTransparency false in
/-- The affine parameterization identifies the polynomial spectrum with a standard open chart. -/
instance chartMap_isOpenImmersion (i j : Fin 2) (hij : i ≠ j) :
    IsOpenImmersion (chartMap R i j hij) := by
  change IsOpenImmersion
    (Spec.map (chartEquivPolynomial R i j hij).toCommRingCatIso.hom ≫
      Proj.awayι (homogeneousSubmodule (Fin 2) R) (X j) (isHomogeneous_X R j)
        (by decide : 0 < 1))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The affine parameterization has precisely the distinguished coordinate open as its image. -/
theorem chartMap_opensRange (i j : Fin 2) (hij : i ≠ j) :
    (chartMap R i j hij).opensRange =
      Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X j) := by
  change (Spec.map (chartEquivPolynomial R i j hij).toCommRingCatIso.hom ≫
    Proj.awayι (homogeneousSubmodule (Fin 2) R) (X j) (isHomogeneous_X R j)
      (by decide : 0 < 1)).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The two homogeneous coordinates generate the coordinate algebra over its degree-zero part. -/
theorem adjoin_coordinates_eq_top : Algebra.adjoin (homogeneousSubmodule (Fin 2) R 0)
    (Set.range (X : Fin 2 → MvPolynomial (Fin 2) R)) = ⊤ := by
  apply top_unique
  intro P hP
  clear hP
  induction P using MvPolynomial.induction_on with
  | C r =>
    exact (Algebra.adjoin (homogeneousSubmodule (Fin 2) R 0)
      (Set.range (X : Fin 2 → MvPolynomial (Fin 2) R))).algebraMap_mem
        ⟨C r, isHomogeneous_C (Fin 2) r⟩
  | add P Q hP hQ => exact add_mem hP hQ
  | mul_X P i hP => exact mul_mem hP (Algebra.subset_adjoin (Set.mem_range_self i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two standard affine parameterizations cover the actual projective line. -/
theorem chartMaps_jointly_surjective (x : ProjectiveLine R) :
    (∃ y, chartMap R 0 1 (by decide) y = x) ∨
      (∃ y, chartMap R 1 0 (by decide) y = x) := by
  have hadj := adjoin_coordinates_eq_top R
  have hcover := Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule (Fin 2) R)
    (X : Fin 2 → MvPolynomial (Fin 2) R) (fun i => ⟨1, isHomogeneous_X R i⟩) hadj
  have hx : x ∈ ⨆ i : Fin 2, Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X i) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  fin_cases i
  · right
    change x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X 0) at hi
    rw [← chartMap_opensRange R 1 0 (by decide)] at hi
    exact hi
  · left
    change x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) R) (X 1) at hi
    rw [← chartMap_opensRange R 0 1 (by decide)] at hi
    exact hi

set_option backward.isDefEq.respectTransparency false in
/-- Each standard affine parameterization is a morphism over the coefficient ring. -/
@[reassoc (attr := simp)]
theorem chartMap_toSpec (i j : Fin 2) (hij : i ≠ j) :
    chartMap R i j hij ≫ toSpec R =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  unfold chartMap Proj.fromSpecOfUnit toSpec
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r : 2
  exact chartEvaluation_constants R i j hij r

/-- The two ordinary polynomial charts as an open cover of the projective line. -/
def standardOpenCover : (ProjectiveLine R).OpenCover where
  I₀ := Bool
  X _ := Spec (CommRingCat.of (Polynomial R))
  f b := if b then chartMap R 1 0 (by decide) else chartMap R 0 1 (by decide)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases chartMaps_jointly_surjective R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩
    · intro b
      cases b <;> dsimp <;> infer_instance

/-- The degree-zero homogeneous coordinate ring is the coefficient ring. -/
def constantsEquiv : R ≃+* ↥(homogeneousSubmodule (Fin 2) R 0) :=
  RingEquiv.ofBijective (constants R) ⟨fun a b hab => by
    apply MvPolynomial.C_injective
    exact congrArg Subtype.val hab, fun P => by
      refine ⟨P.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr P.property)).symm⟩

/-- The projective line is proper over its coefficient ring. -/
instance toSpec_isProper : IsProper (toSpec R) := by
  classical
  have : Algebra.FiniteType (homogeneousSubmodule (Fin 2) R 0)
      (MvPolynomial (Fin 2) R) :=
    ⟨⟨Finset.univ.image (X : Fin 2 → MvPolynomial (Fin 2) R), by
      simpa using adjoin_coordinates_eq_top R⟩⟩
  change IsProper (Proj.toSpecZero (homogeneousSubmodule (Fin 2) R) ≫
    Spec.map (constantsEquiv R).toCommRingCatIso.hom)
  infer_instance

end AlgebraicGeometry.ProjectiveLine
