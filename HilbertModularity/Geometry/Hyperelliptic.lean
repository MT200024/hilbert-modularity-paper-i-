/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.DoubleCover
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Even-degree hyperelliptic double covers

The projective completion is glued from the branch polynomial and its reverse.
The affine coordinate algebra also has its usual universal property in terms of
pairs `(x,y)` satisfying `y² = f(x)`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial LaurentPolynomial
open scoped QuadraticAlgebra

namespace AlgebraicGeometry.Hyperelliptic

variable {R : Type*} [CommRing R]

/-- The reciprocal branch polynomial has the required line-bundle transition. -/
theorem reverse_transition (f : R[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    invert (toLaurent f.reverse) = T (-(n : ℤ)) ^ 2 * toLaurent f := by
  rw [toLaurent_reverse, map_mul, involutive_invert, invert_T, hf, T_pow]
  push_cast
  ring_nf

/-- The projective double cover of an even-degree polynomial. -/
def curve (f : R[X]) (n : ℕ) (hf : f.natDegree = 2 * n) : Scheme :=
  DoubleCover.scheme f f.reverse n (reverse_transition f n hf)

/-- The degree-two map from the hyperelliptic completion to the projective line. -/
def projection (f : R[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    curve f n hf ⟶ ProjectiveLine R :=
  DoubleCover.toProjectiveLine f f.reverse n (reverse_transition f n hf)

/-- The structure morphism over the coefficient ring. -/
def toSpec (f : R[X]) (n : ℕ) (hf : f.natDegree = 2 * n) :
    curve f n hf ⟶ Spec (CommRingCat.of R) :=
  projection f n hf ≫ ProjectiveLine.toSpec R

/-- Evaluation of the quadratic chart at any pair satisfying its equation. -/
def eval {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    (x y : B) (hy : y ^ 2 = aeval x f) : DoubleCover.ChartRing f →ₐ[R] B where
  toFun z := aeval x z.re + aeval x z.im * y
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      zero_mul, add_zero]
    linear_combination -(aeval x z.im * aeval x w.im) * hy
  commutes' r := by simp

theorem eval_apply {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    (x y : B) (hy : y ^ 2 = aeval x f) (z : DoubleCover.ChartRing f) :
    eval f x y hy z = aeval x z.re + aeval x z.im * y := rfl

@[simp]
theorem eval_coordinate {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    (x y : B) (hy : y ^ 2 = aeval x f) :
    eval f x y hy (algebraMap R[X] (DoubleCover.ChartRing f) X) = x := by
  simp [eval_apply]

@[simp]
theorem eval_generator {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    (x y : B) (hy : y ^ 2 = aeval x f) :
    eval f x y hy QuadraticAlgebra.omega = y := by
  simp [eval_apply]

/-- Morphisms from the affine curve are determined by the two coordinates. -/
theorem algHom_ext {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    {φ ψ : DoubleCover.ChartRing f →ₐ[R] B}
    (hx : φ (algebraMap R[X] (DoubleCover.ChartRing f) X) =
      ψ (algebraMap R[X] (DoubleCover.ChartRing f) X))
    (hy : φ QuadraticAlgebra.omega = ψ QuadraticAlgebra.omega) : φ = ψ := by
  have hpoly : φ.comp (IsScalarTower.toAlgHom R R[X] (DoubleCover.ChartRing f)) =
      ψ.comp (IsScalarTower.toAlgHom R R[X] (DoubleCover.ChartRing f)) :=
    Polynomial.algHom_ext hx
  apply AlgHom.ext
  intro z
  rw [← QuadraticAlgebra.re_smul_add_im_smul z]
  simp only [Algebra.smul_def, map_add, map_mul, mul_one, hy]
  rw [show φ (algebraMap R[X] (DoubleCover.ChartRing f) z.re) =
      ψ (algebraMap R[X] (DoubleCover.ChartRing f) z.re) from DFunLike.congr_fun hpoly z.re,
    show φ (algebraMap R[X] (DoubleCover.ChartRing f) z.im) =
      ψ (algebraMap R[X] (DoubleCover.ChartRing f) z.im) from DFunLike.congr_fun hpoly z.im]

/-- A morphism from the affine chart evaluates its polynomial coordinate in the usual way. -/
theorem algHom_algebraMap {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    (φ : DoubleCover.ChartRing f →ₐ[R] B) (P : R[X]) :
    φ (algebraMap R[X] (DoubleCover.ChartRing f) P) =
      aeval (φ (algebraMap R[X] (DoubleCover.ChartRing f) X)) P := by
  have h : φ.comp (IsScalarTower.toAlgHom R R[X] (DoubleCover.ChartRing f)) =
      aeval (φ (algebraMap R[X] (DoubleCover.ChartRing f) X)) :=
    Polynomial.algHom_ext (by simp)
  exact DFunLike.congr_fun h P

/-- Every image of the two affine coordinates satisfies the branch equation. -/
theorem algHom_generator_sq {B : Type*} [CommRing B] [Algebra R B] (f : R[X])
    (φ : DoubleCover.ChartRing f →ₐ[R] B) :
    φ QuadraticAlgebra.omega ^ 2 =
      aeval (φ (algebraMap R[X] (DoubleCover.ChartRing f) X)) f := by
  rw [← map_pow, DoubleCover.chartGenerator_sq, algHom_algebraMap]

end AlgebraicGeometry.Hyperelliptic

namespace Polynomial

/-- A first-order Newton correction lifts a square-root equation through a square-zero error. -/
theorem square_root_newton {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (f : R[X]) (x y e u v c : B) (he : e ^ 2 = 0)
    (herror : y ^ 2 - aeval x f = e)
    (hbez : u * aeval x f + v * aeval x f.derivative = 1)
    (h2 : 2 * c = 1) :
    (y - e * u * y * c) ^ 2 = aeval (x + e * v) f := by
  rw [aeval_add_of_sq_eq_zero f x (e * v) (by rw [mul_pow, he, zero_mul])]
  linear_combination (1 - e * u) * herror - e * hbez - e * u * y ^ 2 * h2 +
    (u ^ 2 * y ^ 2 * c ^ 2 - u) * he

end Polynomial

namespace AlgebraicGeometry.Hyperelliptic

/-- A separable hyperelliptic affine equation is formally smooth away from characteristic two. -/
theorem formallySmooth_chart {K : Type*} [Field K] (f : K[X])
    (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Algebra.FormallySmooth K (DoubleCover.ChartRing f) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI φ
  let q := Ideal.Quotient.mkₐ K I
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (φ (algebraMap K[X] (DoubleCover.ChartRing f) X))
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ QuadraticAlgebra.omega)
  change q x = _ at hx
  change q y = _ at hy
  let e := y ^ 2 - aeval x f
  have heq : q e = 0 := by
    simp only [e, map_sub, map_pow, ← Polynomial.aeval_algHom_apply, hx, hy,
      algHom_generator_sq, sub_self]
  have heI : e ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp heq
  have he2 : e ^ 2 = 0 := by
    have he := Ideal.pow_mem_pow heI 2
    rw [hI] at he
    exact he
  obtain ⟨a, b, hab⟩ := hf
  have hbez : aeval x a * aeval x f + aeval x b * aeval x f.derivative = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg (aeval x) hab
  let c := algebraMap K B (2 : K)⁻¹
  have hc : (2 : B) * c = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (algebraMap K B) (mul_inv_cancel₀ h2)
  have hroot := Polynomial.square_root_newton f x y e (aeval x a) (aeval x b) c
    he2 rfl hbez hc
  refine ⟨eval f (x + e * aeval x b) (y - e * aeval x a * y * c) hroot, ?_⟩
  apply algHom_ext f
  · simp only [AlgHom.comp_apply, eval_coordinate]
    change q (x + e * aeval x b) = _
    simp only [map_add, map_mul, heq, zero_mul, add_zero, hx]
  · simp only [AlgHom.comp_apply, eval_generator]
    change q (y - e * aeval x a * y * c) = _
    simp only [map_sub, map_mul, heq, zero_mul, sub_zero, hy]

/-- The separable affine hyperelliptic chart is a smooth algebra over its coefficient field. -/
theorem smooth_chart {K : Type*} [Field K] (f : K[X])
    (hf : f.Separable) (h2 : (2 : K) ≠ 0) : Algebra.Smooth K (DoubleCover.ChartRing f) := by
  have hft : Algebra.FiniteType K (DoubleCover.ChartRing f) :=
    Algebra.FiniteType.trans (S := K[X]) inferInstance inferInstance
  exact ⟨formallySmooth_chart f hf h2, Algebra.FinitePresentation.of_finiteType.mp hft⟩

end AlgebraicGeometry.Hyperelliptic

namespace Polynomial

private theorem reverse_linear {K : Type*} [Field K] (r : K) :
    (X - C r).reverse = 1 - C r * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_C]
  have h := reflect_monomial (R := K) 1 1
  simpa only [pow_one, revAt_le le_rfl, Nat.sub_self, pow_zero] using
    congrArg (fun P : K[X] => P - C r * X) h

private theorem separable_reciprocal_linear {K : Type*} [Field K] (r : K) :
    (1 - C r * X : K[X]).Separable := by
  by_cases hr : r = 0
  · simp [hr, separable_one]
  · refine ⟨0, C (-r⁻¹), ?_⟩
    simp [derivative_sub, derivative_mul, ← C_mul, hr]

private theorem isCoprime_reciprocal_linear {K : Type*} [Field K] (r s : K) (hrs : r ≠ s) :
    IsCoprime (1 - C r * X : K[X]) (1 - C s * X) := by
  have hid : C s * (1 - C r * X) - C r * (1 - C s * X) = C (s - r) := by
    rw [map_sub]
    ring
  refine ⟨C (s - r)⁻¹ * C s, -(C (s - r)⁻¹ * C r), ?_⟩
  calc
    _ = C (s - r)⁻¹ * (C s * (1 - C r * X) - C r * (1 - C s * X)) := by ring
    _ = C (s - r)⁻¹ * C (s - r) := by rw [hid]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hrs.symm), C_1]

private theorem separable_reverse_of_splits {K : Type*} [Field K] (f : K[X])
    (hf : f.Separable) (hs : f.Splits) : f.reverse.Separable := by
  classical
  let roots : Finset K := ⟨f.roots, nodup_roots hf⟩
  let rev : K[X] →* K[X] :=
    { toFun := reverse
      map_one' := by simpa using reverse_C (1 : K)
      map_mul' := reverse_mul_of_domain }
  have hfactor : f = C f.leadingCoeff * ∏ r ∈ roots, (X - C r) := hs.eq_prod_roots
  have hrev : (∏ r ∈ roots, (X - C r)).reverse = ∏ r ∈ roots, (1 - C r * X) := by
    change rev (∏ r ∈ roots, (X - C r)) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro r hr
    exact reverse_linear r
  rw [hfactor, reverse_mul_of_domain, reverse_C, hrev]
  apply Separable.unit_mul
  · exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero))
  · exact separable_prod' (fun r _ s _ hrs => isCoprime_reciprocal_linear r s hrs)
      (fun r _ => separable_reciprocal_linear r)

/-- Reversing a separable polynomial preserves separability, including when zero is a root. -/
theorem Separable.reverse {K : Type*} [Field K] {f : K[X]} (hf : f.Separable) :
    f.reverse.Separable := by
  let L := AlgebraicClosure K
  let ι := algebraMap K L
  have hmap : f.reverse.map ι = (f.map ι).reverse := by
    rw [Polynomial.reverse, Polynomial.reverse, natDegree_map_eq_of_injective ι.injective]
    exact (reflect_map ι f f.natDegree).symm
  apply (separable_map ι).mp
  rw [hmap]
  exact separable_reverse_of_splits _ hf.map (IsAlgClosed.splits _)

end Polynomial

namespace AlgebraicGeometry.Hyperelliptic

set_option backward.isDefEq.respectTransparency.types false in
/-- The spectrum of a separable quadratic coordinate algebra is smooth over the field. -/
theorem smooth_chart_toSpec {K : Type*} [Field K] (f : K[X])
    (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (DoubleCover.ChartRing f)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (DoubleCover.ChartRing f)).Smooth
  rw [RingHom.smooth_algebraMap]
  exact smooth_chart f hf h2

/-- The even-degree hyperelliptic completion is proper over the coefficient ring. -/
instance toSpec_isProper {R : Type*} [CommRing R] (f : R[X]) (n : ℕ)
    (hf : f.natDegree = 2 * n) : IsProper (toSpec f n hf) := by
  exact DoubleCover.toSpec_isProper f f.reverse n (reverse_transition f n hf)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A separable even-degree hyperelliptic completion is smooth away from characteristic two. -/
theorem smooth_toSpec {K : Type*} [Field K] (f : K[X]) (n : ℕ)
    (hdeg : f.natDegree = 2 * n) (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Smooth (toSpec f n hdeg) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (DoubleCover.openCover f f.reverse n (reverse_transition f n hdeg))
  intro b
  cases b
  · change Smooth (DoubleCover.finiteChart f f.reverse n (reverse_transition f n hdeg) ≫
      (DoubleCover.toProjectiveLine f f.reverse n (reverse_transition f n hdeg) ≫
        ProjectiveLine.toSpec K))
    rw [← Category.assoc, DoubleCover.finiteChart_toProjectiveLine,
      DoubleCover.finiteProjection_toSpec]
    exact smooth_chart_toSpec f hf h2
  · change Smooth (DoubleCover.infinityChart f f.reverse n (reverse_transition f n hdeg) ≫
      (DoubleCover.toProjectiveLine f f.reverse n (reverse_transition f n hdeg) ≫
        ProjectiveLine.toSpec K))
    rw [← Category.assoc, DoubleCover.infinityChart_toProjectiveLine,
      DoubleCover.infinityProjection_toSpec]
    exact smooth_chart_toSpec f.reverse hf.reverse h2

end AlgebraicGeometry.Hyperelliptic
