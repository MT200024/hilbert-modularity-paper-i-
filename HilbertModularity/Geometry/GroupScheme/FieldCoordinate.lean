/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticFieldEquiv
public import HilbertModularity.Algebra.TateModule.Equiv
public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.Geometry.GroupScheme.GeometricField
public import HilbertModularity.NumberTheory.RingOfIntegers.ScalarExtension

/-! # Tate fibres under isomorphisms of parameter fields

A field-coordinate isomorphism gives an actual isomorphism of geometric points.
Its group-valued Yoneda map identifies the integral and rational Tate modules,
without needing a separate finite-étale torsion hypothesis for this isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
variable (E K : Type u) [Field E] [Field K] (σ : E ≃+* K)
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]

/-- The actual integral Tate comparison induced by the field-coordinate isomorphism. -/
def tateFieldCoordinateEquiv :
    TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X)) ≃ₗ[ℤ_[p]]
      TateModule.integral p (Additive (Scheme.geometricPointOver K
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) ⟶ A.X)) :=
  TateModule.mapEquiv p ((yonedaMonObj A.X).mapIso
    (Scheme.arithmeticGeometricPointFieldEquiv E K σ x).op).monCatIsoToMulEquiv.toAdditive

/-- Every torsion coordinate is precomposed by the actual closure spectrum map. -/
@[simp]
theorem tateFieldCoordinateEquiv_projection
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) (n : ℕ) :
    ((tateFieldCoordinateEquiv E K σ x A p v).val n).val.toMul.left =
      Spec.map (CommRingCat.ofHom
        (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).toRingHom) ≫
          (v.val n).val.toMul.left := rfl

/-- Rationalization of the actual field-coordinate Tate comparison. -/
def rationalTateFieldCoordinateEquiv :
    TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X)) ≃ₗ[ℚ_[p]]
      TateModule.rational p (Additive (Scheme.geometricPointOver K
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) ⟶ A.X)) :=
  LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ (tateFieldCoordinateEquiv E K σ x A p)

/-- The rational comparison retains the p-adic coefficient and transforms the integral coordinate. -/
@[simp]
theorem rationalTateFieldCoordinateEquiv_tmul (c : ℚ_[p])
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    rationalTateFieldCoordinateEquiv E K σ x A p (c ⊗ₜ v) =
      c ⊗ₜ tateFieldCoordinateEquiv E K σ x A p v := rfl

/-- Field-coordinate transport commutes with every original group-scheme endomorphism. -/
theorem tateFieldCoordinateEquiv_endomorphism (f : End A)
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    tateFieldCoordinateEquiv E K σ x A p
        (TateModule.map p (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A f) v) =
      TateModule.map p (CommGrp.pointsEndomorphismMap
        (Scheme.geometricPointOver K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) A f)
        (tateFieldCoordinateEquiv E K σ x A p v) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm

/-- The same naturality holds after rationalization, retaining the original endomorphism. -/
theorem rationalTateFieldCoordinateEquiv_endomorphism (f : End A)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    rationalTateFieldCoordinateEquiv E K σ x A p
        (TateModule.rationalMap p
          (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A f) v) =
      TateModule.rationalMap p (CommGrp.pointsEndomorphismMap
        (Scheme.geometricPointOver K (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) A f)
        (rationalTateFieldCoordinateEquiv E K σ x A p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c v =>
    exact congrArg (fun w => c ⊗ₜ[ℤ_[p]] w)
      (tateFieldCoordinateEquiv_endomorphism E K σ x A p f v)
  | add v w hv hw => simp only [map_add, hv, hw]

open scoped NumberField in
/-- Field-coordinate transport intertwines the entire native tensor coefficient action
induced by the same integral real-multiplication endomorphisms. -/
theorem rationalTateFieldCoordinateEquiv_tensorCoefficients
    (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
    (a : ℚ_[p] ⊗[ℚ] F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    rationalTateFieldCoordinateEquiv E K σ x A p
        (NumberField.RingOfIntegers.tensorExtension F ℚ_[p]
          ((TateModule.rationalEndomorphismMap p
            (Additive (Scheme.geometricPointOver E x ⟶ A.X))).comp
            ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A).comp φ)) a v) =
      NumberField.RingOfIntegers.tensorExtension F ℚ_[p]
        ((TateModule.rationalEndomorphismMap p
          (Additive (Scheme.geometricPointOver K
            (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x) ⟶ A.X))).comp
          ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K
            (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x)) A).comp φ)) a
        (rationalTateFieldCoordinateEquiv E K σ x A p v) :=
  NumberField.RingOfIntegers.tensorExtension_intertwines F _ _
    (rationalTateFieldCoordinateEquiv E K σ x A p).toLinearMap
    (fun c w => rationalTateFieldCoordinateEquiv_endomorphism E K σ x A p (φ c) w) a v

end AlgebraicGeometry.GroupScheme
