/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.Projective
public import HilbertModularity.Hyperelliptic.SpecialFiberCharts

/-! # Coefficient change in the scaled double cover

The two quadratic charts of the scaled model specialize coefficientwise. The
reciprocal chart requires the degree of the branch polynomial to survive the
coefficient map; monicity guarantees this for the residue map used below.
-/

public noncomputable section

open Polynomial LaurentPolynomial

namespace HilbertModularity.Hyperelliptic

section General

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Monicity keeps the reciprocal chart's exponent fixed under residue reduction. -/
theorem monic_natDegree_map [Nontrivial S] (f : R →+* S) (P : R[X])
    (hP : P.Monic) : (P.map f).natDegree = P.natDegree :=
  hP.natDegree_map f

/-- The finite scaled branch equation commutes with coefficient change. -/
theorem finiteBranchPolynomial_map (f : R →+* S) (P : R[X]) (t : R) :
    (finiteBranchPolynomial P t).map f = finiteBranchPolynomial (P.map f) (f t) := by
  simp [finiteBranchPolynomial, map_ofNat]

/-- The reciprocal scaled branch equation commutes with degree-preserving coefficient change. -/
theorem infinityBranchPolynomial_map (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    (infinityBranchPolynomial P t).map f =
      infinityBranchPolynomial (P.map f) (f t) := by
  have hreverse : P.reverse.map f = (P.map f).reverse := by
    rw [Polynomial.reverse, Polynomial.reverse, hdeg]
    exact (reflect_map f P P.natDegree).symm
  simp [infinityBranchPolynomial, hdeg, hreverse, map_ofNat]

private def quadraticMapOfEq {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (a b : A) (c d : B)
    (ha : g a = c) (hb : g b = d) :
    QuadraticAlgebra A a b →+* QuadraticAlgebra B c d := by
  cases ha
  cases hb
  exact QuadraticAlgebra.mapCoeffs g a b

private theorem quadraticMapOfEq_re {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (a b : A) (c d : B)
    (ha : g a = c) (hb : g b = d) (z : QuadraticAlgebra A a b) :
    (quadraticMapOfEq g a b c d ha hb z).re = g z.re := by
  cases ha
  cases hb
  rfl

private theorem quadraticMapOfEq_im {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (a b : A) (c d : B)
    (ha : g a = c) (hb : g b = d) (z : QuadraticAlgebra A a b) :
    (quadraticMapOfEq g a b c d ha hb z).im = g z.im := by
  cases ha
  cases hb
  rfl

/-- Change coefficients in the actual finite quadratic chart. -/
def finiteChartMap (f : R →+* S) (P : R[X]) (t : R) :
    AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t) →+*
      AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial (P.map f) (f t)) := by
  let g := Polynomial.mapRingHom f
  exact quadraticMapOfEq g (finiteBranchPolynomial P t) 0
    (finiteBranchPolynomial (P.map f) (f t)) 0
    (finiteBranchPolynomial_map f P t) g.map_zero

/-- Change coefficients in the actual reciprocal quadratic chart. -/
def infinityChartMap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t) →+*
      AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial (P.map f) (f t)) := by
  let g := Polynomial.mapRingHom f
  exact quadraticMapOfEq g (infinityBranchPolynomial P t) 0
    (infinityBranchPolynomial (P.map f) (f t)) 0
    (infinityBranchPolynomial_map f P t hdeg) g.map_zero

/-- The finite chart of the actual family specializes to its square-branch chart. -/
def finiteSpecializationMap (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0) :
    AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t) →+*
      AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial (P.map f) 0) :=
  quadraticMapOfEq (Polynomial.mapRingHom f) (finiteBranchPolynomial P t) 0
    (finiteBranchPolynomial (P.map f) 0) 0 (by
      change (finiteBranchPolynomial P t).map f = _
      simpa only [ht] using finiteBranchPolynomial_map f P t)
    (Polynomial.mapRingHom f).map_zero

/-- The reciprocal chart specializes with the same projective twist for monic `P`. -/
def infinitySpecializationMap [Nontrivial S] (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0) (hP : P.Monic) :
    AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t) →+*
      AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial (P.map f) 0) :=
  quadraticMapOfEq (Polynomial.mapRingHom f) (infinityBranchPolynomial P t) 0
    (infinityBranchPolynomial (P.map f) 0) 0 (by
      change (infinityBranchPolynomial P t).map f = _
      simpa only [ht] using
        infinityBranchPolynomial_map f P t (monic_natDegree_map f P hP))
    (Polynomial.mapRingHom f).map_zero

@[simp] theorem finiteChartMap_re (f : R →+* S) (P : R[X]) (t : R)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    (finiteChartMap f P t z).re = z.re.map f := by
  exact quadraticMapOfEq_re (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem finiteChartMap_im (f : R →+* S) (P : R[X]) (t : R)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    (finiteChartMap f P t z).im = z.im.map f := by
  exact quadraticMapOfEq_im (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem infinityChartMap_re (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    (infinityChartMap f P t hdeg z).re = z.re.map f := by
  exact quadraticMapOfEq_re (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem infinityChartMap_im (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    (infinityChartMap f P t hdeg z).im = z.im.map f := by
  exact quadraticMapOfEq_im (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem finiteSpecializationMap_re (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    (finiteSpecializationMap f P t ht z).re = z.re.map f :=
  quadraticMapOfEq_re (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem finiteSpecializationMap_im (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    (finiteSpecializationMap f P t ht z).im = z.im.map f :=
  quadraticMapOfEq_im (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem infinitySpecializationMap_re [Nontrivial S] (f : R →+* S) (P : R[X])
    (t : R) (ht : f t = 0) (hP : P.Monic)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    (infinitySpecializationMap f P t ht hP z).re = z.re.map f :=
  quadraticMapOfEq_re (Polynomial.mapRingHom f) _ _ _ _ _ _ z

@[simp] theorem infinitySpecializationMap_im [Nontrivial S] (f : R →+* S) (P : R[X])
    (t : R) (ht : f t = 0) (hP : P.Monic)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    (infinitySpecializationMap f P t ht hP z).im = z.im.map f :=
  quadraticMapOfEq_im (Polynomial.mapRingHom f) _ _ _ _ _ _ z

/-- Apply a coefficient map to the Laurent coordinate ring of the chart overlap. -/
def laurentCoefficientMap (f : R →+* S) : R[T;T⁻¹] →+* S[T;T⁻¹] :=
  AddMonoidAlgebra.mapRingHom ℤ f

@[simp] theorem laurentCoefficientMap_T (f : R →+* S) (n : ℤ) :
    laurentCoefficientMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  ext m
  simp [laurentCoefficientMap, AddMonoidAlgebra.coeff_mapRingHom]

@[simp] theorem laurentCoefficientMap_C (f : R →+* S) (a : R) :
    laurentCoefficientMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  ext m
  by_cases hm : m = 0 <;>
    simp [laurentCoefficientMap, AddMonoidAlgebra.coeff_mapRingHom, hm]

@[simp] theorem laurentCoefficientMap_invert (f : R →+* S) (q : R[T;T⁻¹]) :
    laurentCoefficientMap f (invert q) = invert (laurentCoefficientMap f q) := by
  ext n
  simp [laurentCoefficientMap, AddMonoidAlgebra.coeff_mapRingHom,
    LaurentPolynomial.invert_apply]

@[simp] theorem laurentCoefficientMap_toLaurent (f : R →+* S) (P : R[X]) :
    laurentCoefficientMap f (toLaurent P) = toLaurent (P.map f) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp

/-- Coefficient change in the quadratic ring of a Laurent overlap. -/
def overlapCoefficientMap (f : R →+* S) (F : R[X]) :
    AlgebraicGeometry.DoubleCover.OverlapRing F →+*
      AlgebraicGeometry.DoubleCover.OverlapRing (F.map f) :=
  quadraticMapOfEq (laurentCoefficientMap f) (toLaurent F) 0
    (toLaurent (F.map f)) 0 (laurentCoefficientMap_toLaurent f F)
    (laurentCoefficientMap f).map_zero

@[simp] theorem overlapCoefficientMap_re (f : R →+* S) (F : R[X])
    (z : AlgebraicGeometry.DoubleCover.OverlapRing F) :
    (overlapCoefficientMap f F z).re = laurentCoefficientMap f z.re :=
  quadraticMapOfEq_re (laurentCoefficientMap f) _ _ _ _ _ _ z

@[simp] theorem overlapCoefficientMap_im (f : R →+* S) (F : R[X])
    (z : AlgebraicGeometry.DoubleCover.OverlapRing F) :
    (overlapCoefficientMap f F z).im = laurentCoefficientMap f z.im :=
  quadraticMapOfEq_im (laurentCoefficientMap f) _ _ _ _ _ _ z

/-- Changing coefficients respects the reciprocal transition whenever the exponent is fixed. -/
theorem overlapCoefficientMap_transition (f : R →+* S) (F G : R[X]) (n : ℕ)
    (h : invert (toLaurent G) = T (-(n : ℤ)) ^ 2 * toLaurent F)
    (h' : invert (toLaurent (G.map f)) =
      T (-(n : ℤ)) ^ 2 * toLaurent (F.map f))
    (z : AlgebraicGeometry.DoubleCover.OverlapRing G) :
    overlapCoefficientMap f F (AlgebraicGeometry.DoubleCover.transition F G n h z) =
      AlgebraicGeometry.DoubleCover.transition (F.map f) (G.map f) n h'
        (overlapCoefficientMap f G z) := by
  apply QuadraticAlgebra.ext
  · simp
  · simp [map_mul]

/-- Coefficient change on the finite Laurent overlap of the scaled cover. -/
def finiteOverlapMap (f : R →+* S) (P : R[X]) (t : R) :
    AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P t) →+*
      AlgebraicGeometry.DoubleCover.OverlapRing
        (finiteBranchPolynomial (P.map f) (f t)) :=
  quadraticMapOfEq (laurentCoefficientMap f) (toLaurent (finiteBranchPolynomial P t)) 0
    (toLaurent (finiteBranchPolynomial (P.map f) (f t))) 0
    (by rw [laurentCoefficientMap_toLaurent, finiteBranchPolynomial_map])
    (laurentCoefficientMap f).map_zero

/-- Coefficient change on the reciprocal Laurent overlap when the branch degree is fixed. -/
def infinityOverlapMap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P t) →+*
      AlgebraicGeometry.DoubleCover.OverlapRing
        (infinityBranchPolynomial (P.map f) (f t)) :=
  quadraticMapOfEq (laurentCoefficientMap f) (toLaurent (infinityBranchPolynomial P t)) 0
    (toLaurent (infinityBranchPolynomial (P.map f) (f t))) 0
    (by rw [laurentCoefficientMap_toLaurent, infinityBranchPolynomial_map f P t hdeg])
    (laurentCoefficientMap f).map_zero

@[simp] theorem finiteOverlapMap_re (f : R →+* S) (P : R[X]) (t : R)
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P t)) :
    (finiteOverlapMap f P t z).re = laurentCoefficientMap f z.re :=
  quadraticMapOfEq_re (laurentCoefficientMap f) _ _ _ _ _ _ z

@[simp] theorem finiteOverlapMap_im (f : R →+* S) (P : R[X]) (t : R)
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P t)) :
    (finiteOverlapMap f P t z).im = laurentCoefficientMap f z.im :=
  quadraticMapOfEq_im (laurentCoefficientMap f) _ _ _ _ _ _ z

@[simp] theorem infinityOverlapMap_re (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree)
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P t)) :
    (infinityOverlapMap f P t hdeg z).re = laurentCoefficientMap f z.re :=
  quadraticMapOfEq_re (laurentCoefficientMap f) _ _ _ _ _ _ z

@[simp] theorem infinityOverlapMap_im (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree)
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P t)) :
    (infinityOverlapMap f P t hdeg z).im = laurentCoefficientMap f z.im :=
  quadraticMapOfEq_im (laurentCoefficientMap f) _ _ _ _ _ _ z

/-- The two coefficient maps respect the actual gluing transition of the scaled cover. -/
theorem scaledOverlapMap_transition (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree)
    (z : AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P t)) :
    finiteOverlapMap f P t
        (AlgebraicGeometry.DoubleCover.transition _ _ (P.natDegree + 1)
          (branch_transition P t) z) =
      AlgebraicGeometry.DoubleCover.transition _ _ (P.natDegree + 1)
        (by simpa only [hdeg] using branch_transition (P.map f) (f t))
        (infinityOverlapMap f P t hdeg z) := by
  apply QuadraticAlgebra.ext
  · simp
  · simp [map_mul]

/-- Finite-chart reduction commutes with restriction to the Laurent overlap. -/
theorem finiteChartMap_overlap (f : R →+* S) (P : R[X]) (t : R) :
    (finiteOverlapMap f P t).comp
      (algebraMap (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t))
        (AlgebraicGeometry.DoubleCover.OverlapRing (finiteBranchPolynomial P t))) =
      (algebraMap (AlgebraicGeometry.DoubleCover.ChartRing
          (finiteBranchPolynomial (P.map f) (f t)))
        (AlgebraicGeometry.DoubleCover.OverlapRing
          (finiteBranchPolynomial (P.map f) (f t)))).comp (finiteChartMap f P t) := by
  apply RingHom.ext
  intro z
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs]
  · simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs]

/-- Reciprocal-chart reduction commutes with restriction to the Laurent overlap. -/
theorem infinityChartMap_overlap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    (infinityOverlapMap f P t hdeg).comp
      (algebraMap (AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t))
        (AlgebraicGeometry.DoubleCover.OverlapRing (infinityBranchPolynomial P t))) =
      (algebraMap (AlgebraicGeometry.DoubleCover.ChartRing
          (infinityBranchPolynomial (P.map f) (f t)))
        (AlgebraicGeometry.DoubleCover.OverlapRing
          (infinityBranchPolynomial (P.map f) (f t)))).comp
        (infinityChartMap f P t hdeg) := by
  apply RingHom.ext
  intro z
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs]
  · simp [QuadraticAlgebra.algebraMap_baseChange, QuadraticAlgebra.baseChange,
      QuadraticAlgebra.mapCoeffs]

end General

section Field

variable {R S : Type*} [CommRing R] [Field S]

/-- Reduction followed by the positive finite component is the signed polynomial evaluation. -/
theorem finiteSpecialization_positive (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    finitePositiveComponent (P.map f) (finiteSpecializationMap f P t ht z) =
      z.re.map f + z.im.map f * (X * P.map f) := by
  rw [finitePositiveComponent_apply, finiteSpecializationMap_re,
    finiteSpecializationMap_im]
  rw [finiteComponentPolynomial_eq]

/-- Reduction followed by the negative finite component is the opposite signed evaluation. -/
theorem finiteSpecialization_negative (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    finiteNegativeComponent (P.map f) (finiteSpecializationMap f P t ht z) =
      z.re.map f - z.im.map f * (X * P.map f) := by
  rw [finiteNegativeComponent_apply, finiteSpecializationMap_re,
    finiteSpecializationMap_im]
  rw [finiteComponentPolynomial_eq]

/-- Reduction followed by the positive reciprocal component uses the reversed residue polynomial. -/
theorem infinitySpecialization_positive (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0) (hP : P.Monic)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    infinityPositiveComponent (P.map f) (infinitySpecializationMap f P t ht hP z) =
      z.re.map f + z.im.map f * (P.map f).reverse := by
  rw [infinityPositiveComponent_apply, infinitySpecializationMap_re,
    infinitySpecializationMap_im]
  rw [infinityComponentPolynomial_eq]

/-- Reduction followed by the negative reciprocal component uses the opposite sign. -/
theorem infinitySpecialization_negative (f : R →+* S) (P : R[X]) (t : R)
    (ht : f t = 0) (hP : P.Monic)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    infinityNegativeComponent (P.map f) (infinitySpecializationMap f P t ht hP z) =
      z.re.map f - z.im.map f * (P.map f).reverse := by
  rw [infinityNegativeComponent_apply, infinitySpecializationMap_re,
    infinitySpecializationMap_im]
  rw [infinityComponentPolynomial_eq]

end Field

section Scheme

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The coefficient map on the finite Laurent overlap is the restriction of the chart map. -/
private theorem finiteChartMap_overlap_spec (f : R →+* S) (P : R[X]) (t : R) :
    Spec.map (CommRingCat.ofHom (finiteOverlapMap f P t)) ≫
        AlgebraicGeometry.DoubleCover.overlapInclusion (finiteBranchPolynomial P t) =
      AlgebraicGeometry.DoubleCover.overlapInclusion
          (finiteBranchPolynomial (P.map f) (f t)) ≫
        Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (finiteChartMap_overlap f P t)

/-- The reciprocal chart map restricts to its Laurent coefficient map. -/
private theorem infinityChartMap_overlap_spec (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    Spec.map (CommRingCat.ofHom (infinityOverlapMap f P t hdeg)) ≫
        AlgebraicGeometry.DoubleCover.overlapInclusion (infinityBranchPolynomial P t) =
      AlgebraicGeometry.DoubleCover.overlapInclusion
          (infinityBranchPolynomial (P.map f) (f t)) ≫
        Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) := by
  unfold AlgebraicGeometry.DoubleCover.overlapInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    (infinityChartMap_overlap f P t hdeg)

/-- The coefficient map intertwines both scheme overlap transitions. -/
private theorem scaledOverlapMap_transition_spec (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    Spec.map (CommRingCat.ofHom (finiteOverlapMap f P t)) ≫
        Spec.map (AlgebraicGeometry.DoubleCover.transition
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)).toCommRingCatIso.hom =
      Spec.map (AlgebraicGeometry.DoubleCover.transition
          (finiteBranchPolynomial (P.map f) (f t))
          (infinityBranchPolynomial (P.map f) (f t))
          (P.natDegree + 1)
          (by simpa only [hdeg] using branch_transition (P.map f) (f t))).toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (infinityOverlapMap f P t hdeg)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (by
    apply RingHom.ext
    intro z
    exact scaledOverlapMap_transition f P t hdeg z)

private theorem scaledDoubleCoverMap_compat (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    AlgebraicGeometry.DoubleCover.overlapInclusion
        (finiteBranchPolynomial (P.map f) (f t)) ≫
      (Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫
        AlgebraicGeometry.DoubleCover.finiteChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)) =
    AlgebraicGeometry.DoubleCover.overlapInclusionInfinity
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t)) (P.natDegree + 1)
        (by simpa only [hdeg] using branch_transition (P.map f) (f t)) ≫
      (Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫
        AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)) := by
  rw [← Category.assoc]
  rw [← finiteChartMap_overlap_spec]
  rw [Category.assoc]
  rw [AlgebraicGeometry.DoubleCover.overlap_condition]
  simp only [AlgebraicGeometry.DoubleCover.overlapInclusionInfinity, Category.assoc]
  simp only [← Category.assoc]
  rw [scaledOverlapMap_transition_spec f P t hdeg]
  simp only [Category.assoc]
  conv_lhs =>
    arg 2
    rw [← Category.assoc]
  rw [infinityChartMap_overlap_spec f P t hdeg]
  simp only [Category.assoc]

private theorem scaledDoubleCoverMap_compat_exact (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    AlgebraicGeometry.DoubleCover.overlapInclusion
        (finiteBranchPolynomial (P.map f) (f t)) ≫
      (Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫
        AlgebraicGeometry.DoubleCover.finiteChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)) =
    AlgebraicGeometry.DoubleCover.overlapInclusionInfinity
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t)) ((P.map f).natDegree + 1)
        (branch_transition (P.map f) (f t)) ≫
      (Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫
        AlgebraicGeometry.DoubleCover.infinityChart
          (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
          (P.natDegree + 1) (branch_transition P t)) := by
  simpa only [hdeg] using scaledDoubleCoverMap_compat f P t hdeg

/-- Coefficient change on both quadratic charts glues to a map of the scaled covers. -/
def scaledDoubleCoverMap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    scaledDoubleCover (P.map f) (f t) ⟶ scaledDoubleCover P t := by
  unfold scaledDoubleCover AlgebraicGeometry.DoubleCover.scheme
  exact pushout.desc
    (Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫
      AlgebraicGeometry.DoubleCover.finiteChart _ _ _ (branch_transition P t))
    (Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫
      AlgebraicGeometry.DoubleCover.infinityChart _ _ _ (branch_transition P t))
    (scaledDoubleCoverMap_compat_exact f P t hdeg)

/-- The glued coefficient map restricts to the finite quadratic chart map. -/
theorem finiteChart_scaledDoubleCoverMap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t)) ((P.map f).natDegree + 1)
        (branch_transition (P.map f) (f t)) ≫
      scaledDoubleCoverMap f P t hdeg =
    Spec.map (CommRingCat.ofHom (finiteChartMap f P t)) ≫
      AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) := by
  simp only [scaledDoubleCoverMap, AlgebraicGeometry.DoubleCover.finiteChart]
  dsimp only [id]
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ _

/-- The glued coefficient map restricts to the reciprocal quadratic chart map. -/
theorem infinityChart_scaledDoubleCoverMap (f : R →+* S) (P : R[X]) (t : R)
    (hdeg : (P.map f).natDegree = P.natDegree) :
    AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial (P.map f) (f t))
        (infinityBranchPolynomial (P.map f) (f t)) ((P.map f).natDegree + 1)
        (branch_transition (P.map f) (f t)) ≫
      scaledDoubleCoverMap f P t hdeg =
    Spec.map (CommRingCat.ofHom (infinityChartMap f P t hdeg)) ≫
      AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) := by
  simp only [scaledDoubleCoverMap, AlgebraicGeometry.DoubleCover.infinityChart]
  dsimp only [id]
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ _

/-- The square-branch reduction maps into the scaled model when the parameter vanishes. -/
@[expose] def scaledDoubleCoverSpecializationMap [Nontrivial S] (f : R →+* S)
    (P : R[X]) (t : R) (ht : f t = 0) (hP : P.Monic) :
    scaledDoubleCover (P.map f) 0 ⟶ scaledDoubleCover P t :=
  ht ▸ scaledDoubleCoverMap f P t (monic_natDegree_map f P hP)

end Scheme

end HilbertModularity.Hyperelliptic
