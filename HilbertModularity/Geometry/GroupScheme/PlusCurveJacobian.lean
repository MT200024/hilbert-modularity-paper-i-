/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.PlusCurve
public import HilbertModularity.Geometry.HyperellipticPoints
public import HilbertModularity.Geometry.GroupScheme.Fiber

/-! # The pointed plus curve and its Jacobian property

The branch point `(-2, 0)` gives the Abel–Jacobi map a canonical origin.
The universal property below identifies a group scheme over the coefficient
field with the Jacobian of this *actual* completed curve. -/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace HilbertModularity.Hyperelliptic

variable {K : Type*} [Field K]

/-- The affine coordinate of the generic point of the punctured parameter line. -/
def plusGenericParameter (K : Type*) [Field K] : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) Polynomial.X

/-- The rational ramification point with affine coordinates `(-2, 0)`. -/
def plusBranchSolution (p : ℕ) (t : K) :
    AlgebraicGeometry.Hyperelliptic.AffineSolutions (plusPolynomial p t) :=
  ⟨⟨-2, 0⟩, by simp [plusPolynomial]⟩

theorem plusBranchSolution_val (p : ℕ) (t : K) :
    (plusBranchSolution p t).val = (-2, 0) :=
  (rfl)

/-- The distinguished branch point on the completed plus curve. -/
def plusBranchPoint (p : ℕ) (hp : Odd p) (t : K) :
    Scheme.RationalPoint (plusCurveToSpec p hp t) :=
  Scheme.RationalPoint.map (plusAffineInclusion p hp t) rfl
    ((AlgebraicGeometry.Hyperelliptic.finiteChartPointsEquiv
      (plusPolynomial p t) ((p + 1) / 2) (plusPolynomial_evenDegree p hp t)).symm
        (plusBranchSolution p t))

/-- The point `(-2, 0)` viewed as a morphism over the coefficient field. -/
def plusBranchOver (p : ℕ) (hp : Odd p) (t : K) :
    Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk (plusCurveToSpec p hp t) :=
  Over.homMk (plusBranchPoint p hp t).val (by
    exact (plusBranchPoint p hp t).property)

end HilbertModularity.Hyperelliptic

namespace AlgebraicGeometry.GroupScheme

open HilbertModularity.Hyperelliptic

/-- A pointed Abel–Jacobi map whose target is universal among abelian varieties.
The normalization is at the explicit rational branch point, and the target is
the *same scheme-theoretic fibre* used by its RM and Tate representations.
This is a geometric Jacobian property; it asserts no reduction or modularity. -/
structure PlusCurveJacobian (K : Type*) [Field K] (p : ℕ) (hp : Odd p) (t : K)
    (J : CommGrp (Over (Spec (CommRingCat.of K)))) where
  curveProper : IsProper (plusCurveToSpec p hp t)
  curveSmooth : Smooth (plusCurveToSpec p hp t)
  curveGeometricallyConnected : GeometricallyConnected (plusCurveToSpec p hp t)
  targetProper : IsProper J.X.hom
  targetSmooth : Smooth J.X.hom
  targetGeometricallyConnected : GeometricallyConnected J.X.hom
  abelJacobi : Over.mk (plusCurveToSpec p hp t) ⟶ J.X
  normalized : plusBranchOver p hp t ≫ abelJacobi =
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ J.X)
  universal : ∀ (A : CommGrp (Over (Spec (CommRingCat.of K)))),
    IsProper A.X.hom → Smooth A.X.hom → GeometricallyConnected A.X.hom →
    ∀ (f : Over.mk (plusCurveToSpec p hp t) ⟶ A.X),
      plusBranchOver p hp t ≫ f =
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) →
      ∃! h : J ⟶ A, abelJacobi ≫ h.hom.hom.hom = f

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme

open HilbertModularity.Hyperelliptic

/-- The pointed universal property of a Jacobian, for a curve already supplied
as an object over its coefficient field. This formulation lets an isomorphism
of proper curves transport the Jacobian property without changing the chosen
abelian variety or its real multiplication. -/
structure PointedCurveJacobian (K : Type*) [Field K]
    (C : Over (Spec (CommRingCat.of K)))
    (b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ C)
    (J : CommGrp (Over (Spec (CommRingCat.of K)))) where
  targetProper : IsProper J.X.hom
  targetSmooth : Smooth J.X.hom
  targetGeometricallyConnected : GeometricallyConnected J.X.hom
  abelJacobi : C ⟶ J.X
  normalized : b ≫ abelJacobi =
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ J.X)
  universal : ∀ (A : CommGrp (Over (Spec (CommRingCat.of K)))),
    IsProper A.X.hom → Smooth A.X.hom → GeometricallyConnected A.X.hom →
    ∀ (f : C ⟶ A.X),
      b ≫ f = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) →
      ∃! h : J ⟶ A, abelJacobi ≫ h.hom.hom.hom = f

/-- A pointed isomorphism of curves transports the universal property to the
same abelian variety. In particular the selected RM and Tate actions stay on
the same target. -/
def PlusCurveJacobian.transport {K : Type*} [Field K]
    {p : ℕ} {hp : Odd p} {t : K}
    {J : CommGrp (Over (Spec (CommRingCat.of K)))}
    (hJ : PlusCurveJacobian K p hp t J)
    {C : Over (Spec (CommRingCat.of K))}
    (e : C ≅ Over.mk (plusCurveToSpec p hp t)) :
    PointedCurveJacobian K C (plusBranchOver p hp t ≫ e.inv) J where
  targetProper := hJ.targetProper
  targetSmooth := hJ.targetSmooth
  targetGeometricallyConnected := hJ.targetGeometricallyConnected
  abelJacobi := e.hom ≫ hJ.abelJacobi
  normalized := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hJ.normalized
  universal := by
    intro A hproper hsmooth hconn f hnorm
    have hnorm' : plusBranchOver p hp t ≫ (e.inv ≫ f) =
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) := by
      simpa only [Category.assoc] using hnorm
    obtain ⟨h, hh, hu⟩ := hJ.universal A hproper hsmooth hconn
      (e.inv ≫ f) hnorm'
    refine ⟨h, ?_, ?_⟩
    · calc
        (e.hom ≫ hJ.abelJacobi) ≫ h.hom.hom.hom =
            e.hom ≫ (hJ.abelJacobi ≫ h.hom.hom.hom) := Category.assoc _ _ _
        _ = e.hom ≫ (e.inv ≫ f) := by rw [hh]
        _ = f := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    · intro h' hh'
      apply hu
      calc
        hJ.abelJacobi ≫ h'.hom.hom.hom =
            e.inv ≫ ((e.hom ≫ hJ.abelJacobi) ≫ h'.hom.hom.hom) := by
              simp only [Category.assoc, ← Category.assoc e.inv e.hom,
                e.inv_hom_id, Category.id_comp]
        _ = e.inv ≫ f := by rw [hh']

end AlgebraicGeometry.GroupScheme
