/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Hyperelliptic
public import HilbertModularity.Geometry.RationalPoints
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Sum

/-! # Rational points of hyperelliptic charts

The coordinate description is identified with actual sections of the affine
scheme, so finite solution counts can be transferred to geometric point counts.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

namespace AlgebraicGeometry.Hyperelliptic

universe u
variable {R : Type u} [CommRing R]

/-- Solutions of the affine hyperelliptic equation. -/
def AffineSolutions (f : R[X]) := {xy : R × R // xy.2 ^ 2 = f.eval xy.1}

instance affineSolutions_finite [Finite R] (f : R[X]) : Finite (AffineSolutions f) := by
  unfold AffineSolutions
  infer_instance

/-- Algebra maps from the quadratic chart are precisely its coordinate solutions. -/
def chartAlgHomEquiv (f : R[X]) :
    (DoubleCover.ChartRing f →ₐ[R] R) ≃ AffineSolutions f where
  toFun φ := ⟨(φ (algebraMap R[X] (DoubleCover.ChartRing f) X), φ QuadraticAlgebra.omega),
    by simpa using algHom_generator_sq f φ⟩
  invFun xy := eval f xy.val.1 xy.val.2 (by simpa using xy.property)
  left_inv φ := by apply algHom_ext f <;> simp
  right_inv xy := by apply Subtype.ext; simp

/-- Actual rational points of the affine scheme are the usual coordinate pairs. -/
def affineRationalPointEquiv (f : R[X]) :
    Scheme.RationalPoint
      (Spec.map (CommRingCat.ofHom (algebraMap R (DoubleCover.ChartRing f)))) ≃
      AffineSolutions f :=
  (Scheme.affineRationalPointEquiv R (DoubleCover.ChartRing f)).trans (chartAlgHomEquiv f)

end AlgebraicGeometry.Hyperelliptic
attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.DoubleCover

open LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- In the reciprocal chart, the finite chart is exactly the nonzero-coordinate locus. -/
theorem infinityChart_mem_finite_iff (f g : R[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f)
    (y : PrimeSpectrum (ChartRing g)) :
    infinityChart f g n h y ∈ Set.range (finiteChart f g n h) ↔
      algebraMap R[X] (ChartRing g) X ∉ y.asIdeal := by
  change infinityChart f g n h y ∈ (finiteChart f g n h).opensRange ↔ _
  rw [← toProjectiveLine_preimage_finite]
  change (infinityChart f g n h ≫ toProjectiveLine f g n h) y ∈
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) ↔ _
  rw [infinityChart_toProjectiveLine]
  change y ∈ infinityProjection g ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) ↔ _
  rw [infinityProjection_preimage_finite, overlapInclusion_opensRange]
  exact PrimeSpectrum.mem_basicOpen _ _

end AlgebraicGeometry.DoubleCover

namespace AlgebraicGeometry.Hyperelliptic

variable {K : Type*} [Field K]

/-- The inverse coordinate equivalence is the scheme morphism induced by evaluation. -/
theorem affineRationalPointEquiv_symm_val (f : K[X]) (xy : AffineSolutions f) :
    ((affineRationalPointEquiv f).symm xy).val =
      Spec.map (CommRingCat.ofHom
        (eval f xy.val.1 xy.val.2 (by simpa using xy.property)).toRingHom) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The finite-chart points of a completed hyperelliptic curve are affine solutions. -/
def finiteChartPointsEquiv (f : K[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    Scheme.RationalPoint
      (DoubleCover.finiteChart f f.reverse n (reverse_transition f n hf) ≫ toSpec f n hf) ≃
      AffineSolutions f := by
  refine (Scheme.RationalPoint.congr ?_).trans (affineRationalPointEquiv f)
  unfold toSpec projection
  rw [DoubleCover.finiteChart_toProjectiveLine_assoc, DoubleCover.finiteProjection_toSpec]

set_option backward.isDefEq.respectTransparency false in
/-- The reciprocal-chart points are solutions of the reversed equation. -/
def infinityChartPointsEquiv (f : K[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    Scheme.RationalPoint
      (DoubleCover.infinityChart f f.reverse n (reverse_transition f n hf) ≫ toSpec f n hf) ≃
      AffineSolutions f.reverse := by
  refine (Scheme.RationalPoint.congr ?_).trans (affineRationalPointEquiv f.reverse)
  unfold toSpec projection
  rw [DoubleCover.infinityChart_toProjectiveLine_assoc, DoubleCover.infinityProjection_toSpec]

set_option backward.isDefEq.respectTransparency false in
/-- Reciprocal coordinate solutions induce the expected evaluation morphism. -/
theorem infinityChartPointsEquiv_symm_val (f : K[X]) (n : ℕ)
    (hf : f.natDegree = 2 * n) (xy : AffineSolutions f.reverse) :
    ((infinityChartPointsEquiv f n hf).symm xy).val =
      Spec.map (CommRingCat.ofHom
        (eval f.reverse xy.val.1 xy.val.2 (by simpa using xy.property)).toRingHom) := by
  unfold infinityChartPointsEquiv
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A reciprocal-chart point lies outside the affine chart exactly at coordinate zero. -/
theorem infinityPoint_not_mem_finite_iff (f : K[X]) (n : ℕ)
    (hf : f.natDegree = 2 * n) (xy : AffineSolutions f.reverse) :
    DoubleCover.infinityChart f f.reverse n (reverse_transition f n hf)
      (((infinityChartPointsEquiv f n hf).symm xy).val (⊥ : PrimeSpectrum K)) ∉
        Set.range (DoubleCover.finiteChart f f.reverse n (reverse_transition f n hf)) ↔
      xy.val.1 = 0 := by
  rw [DoubleCover.infinityChart_mem_finite_iff, not_not, infinityChartPointsEquiv_symm_val]
  change eval f.reverse xy.val.1 xy.val.2 (by simpa using xy.property)
    (algebraMap K[X] (DoubleCover.ChartRing f.reverse) X) ∈ (⊥ : Ideal K) ↔ _
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The projective points are affine solutions together with reciprocal solutions at zero. -/
def rationalPointEquiv (f : K[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    Scheme.RationalPoint (toSpec f n hf) ≃
      AffineSolutions f ⊕ {xy : AffineSolutions f.reverse // xy.val.1 = 0} := by
  refine (Scheme.RationalPoint.twoChartEquiv (toSpec f n hf)
    (DoubleCover.finiteChart f f.reverse n (reverse_transition f n hf))
    (DoubleCover.infinityChart f f.reverse n (reverse_transition f n hf))
    (DoubleCover.charts_jointly_surjective f f.reverse n (reverse_transition f n hf))).trans
      (Equiv.sumCongr (finiteChartPointsEquiv f n hf) ?_)
  refine (infinityChartPointsEquiv f n hf).subtypeEquiv ?_
  intro s
  have h := infinityPoint_not_mem_finite_iff f n hf (infinityChartPointsEquiv f n hf s)
  simpa only [Equiv.symm_apply_apply] using! h

/-- Reciprocal solutions at zero are square roots of the leading coefficient. -/
def infinitySolutionsEquiv (f : K[X]) :
    {xy : AffineSolutions f.reverse // xy.val.1 = 0} ≃
      {y : K // y ^ 2 = f.leadingCoeff} where
  toFun xy := ⟨xy.val.val.2, by
    simpa [xy.property, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
      using xy.val.property⟩
  invFun y := ⟨⟨(0, y.val), by
    simpa [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse] using y.property⟩, rfl⟩
  left_inv xy := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext xy.property.symm rfl
  right_inv y := rfl

/-- Rational points of an even-degree completion, including all points at infinity. -/
def rationalPointEquivAffineSumInfinity (f : K[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    Scheme.RationalPoint (toSpec f n hf) ≃
      AffineSolutions f ⊕ {y : K // y ^ 2 = f.leadingCoeff} :=
  (rationalPointEquiv f n hf).trans (Equiv.sumCongr (Equiv.refl _) (infinitySolutionsEquiv f))

/-- A monic even-degree hyperelliptic equation has exactly two points at infinity
in odd characteristic. -/
theorem card_rationalPoint [Fintype K] (f : K[X]) (n : ℕ)
    (hf : f.natDegree = 2 * n) (hm : f.Monic) (h2 : (2 : K) ≠ 0) :
    Nat.card (Scheme.RationalPoint (toSpec f n hf)) = Nat.card (AffineSolutions f) + 2 := by
  classical
  have hone : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hinf : Nat.card {y : K // y ^ 2 = f.leadingCoeff} = 2 := by
    rw [hm.leadingCoeff, Nat.card_eq_fintype_card]
    simp only [sq_eq_one_iff]
    exact Fintype.card_subtype_eq_or_eq_of_ne hone
  rw [Nat.card_congr (rationalPointEquivAffineSumInfinity f n hf), Nat.card_sum, hinf]

end AlgebraicGeometry.Hyperelliptic
