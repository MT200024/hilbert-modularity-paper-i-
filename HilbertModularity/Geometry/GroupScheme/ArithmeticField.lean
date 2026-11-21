/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticField
public import HilbertModularity.Geometry.GroupScheme.GeometricField
public import HilbertModularity.Algebra.TateModule.Equiv

/-! # Actual Tate fibres over a larger parameter field -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme
universe u
variable (E K : Type u) [Field E] [Field K] [Algebra E K]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (j : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)

/-- The geometric point obtained by the chosen closure embedding is the geometric point
of the same rational point over the larger parameter field. -/
def arithmeticGeometricPointFieldIso :
    Over.mk (Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      (Scheme.geometricPointOver E x).hom) ≅
        Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x) :=
  Over.isoMk (Iso.refl _) (by
    exact (Category.id_comp _).trans
      (Scheme.geometricPointOver_fieldExtension E K x j).symm)

/-- The identification of geometric points leaves every underlying scheme morphism unchanged. -/
@[simp]
theorem arithmeticGeometricPointFieldIso_inv_left :
    (arithmeticGeometricPointFieldIso E K x j).inv.left = 𝟙 _ := rfl

variable (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The actual integral Tate fibre is unchanged when the parameter field is enlarged.
The equivalence first extends torsion points and then identifies the geometric points. -/
def arithmeticTateFieldEquiv :
    TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X)) ≃ₗ[ℤ_[p]]
      TateModule.integral p
        (Additive (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x) ⟶ A.X)) := by
  let : Algebra (AlgebraicClosure E) (AlgebraicClosure K) := j.toRingHom.toAlgebra
  let i := arithmeticGeometricPointFieldIso E K x j
  let e := ((yonedaMonObj A.X).mapIso i.symm.op).monCatIsoToMulEquiv.toAdditive
  exact (geometricTateFieldEquiv (AlgebraicClosure E) (AlgebraicClosure K)
    (Scheme.geometricPointOver E x).hom A p).trans (TateModule.mapEquiv p e)

/-- At every torsion level, the fibre comparison is the original scheme-theoretic field map. -/
@[simp]
theorem arithmeticTateFieldEquiv_projection
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) (n : ℕ) :
    ((arithmeticTateFieldEquiv E K x j A p v).val n).val.toMul.left =
      Spec.map (CommRingCat.ofHom j.toRingHom) ≫ (v.val n).val.toMul.left := by
  change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom j.toRingHom) ≫
    (v.val n).val.toMul.left) = _
  exact Category.id_comp _

/-- Rationalizing gives the same fibre comparison with p-adic field coefficients. -/
def arithmeticRationalTateFieldEquiv :
    TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X)) ≃ₗ[ℚ_[p]]
      TateModule.rational p
        (Additive (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x) ⟶ A.X)) :=
  LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ (arithmeticTateFieldEquiv E K x j A p)

/-- The rational comparison fixes the coefficient and applies the integral field comparison. -/
@[simp]
theorem arithmeticRationalTateFieldEquiv_tmul (c : ℚ_[p])
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    arithmeticRationalTateFieldEquiv E K x j A p (c ⊗ₜ v) =
      c ⊗ₜ arithmeticTateFieldEquiv E K x j A p v := rfl

end AlgebraicGeometry.GroupScheme
