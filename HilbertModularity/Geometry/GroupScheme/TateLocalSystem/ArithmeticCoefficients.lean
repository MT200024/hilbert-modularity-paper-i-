/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.ArithmeticField
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientAction
public import HilbertModularity.Algebra.Category.ModuleCat.FunctorCategory

/-! # Coefficients in the arithmetic field comparison -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra

namespace AlgebraicGeometry.GroupScheme
universe u
variable (E K : Type u) [Field E] [Field K] [Algebra E K]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (j : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The common-field integral Tate comparison commutes with every original endomorphism. -/
theorem arithmeticTateFieldEquiv_endomorphism (f : End A)
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    arithmeticTateFieldEquiv E K x j A p
        (TateModule.map p (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A f) v) =
      TateModule.map p (CommGrp.pointsEndomorphismMap
        (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x)) A f)
        (arithmeticTateFieldEquiv E K x j A p v) := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  apply Over.OverMorphism.ext
  have h₁ := arithmeticTateFieldEquiv_projection E K x j A p
    (TateModule.map p (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A f) v) n
  have h₂ := arithmeticTateFieldEquiv_projection E K x j A p v n
  exact h₁.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ f.hom.hom.hom.left) h₂.symm))

/-- Rational common-field Tate comparison retains all original group-scheme endomorphisms. -/
theorem arithmeticRationalTateFieldEquiv_endomorphism (f : End A)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    arithmeticRationalTateFieldEquiv E K x j A p
        (TateModule.rationalMap p
          (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A f) v) =
      TateModule.rationalMap p (CommGrp.pointsEndomorphismMap
        (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x)) A f)
        (arithmeticRationalTateFieldEquiv E K x j A p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c v =>
    change c ⊗ₜ (arithmeticTateFieldEquiv E K x j A p
        (TateModule.map p (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A f) v)) =
      c ⊗ₜ (TateModule.map p (CommGrp.pointsEndomorphismMap
        (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x)) A f)
        (arithmeticTateFieldEquiv E K x j A p v))
    exact congrArg (fun w => c ⊗ₜ[ℤ_[p]] w)
      (arithmeticTateFieldEquiv_endomorphism E K x j A p f v)
  | add v w hv hw => simp only [map_add, hv, hw]

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option maxHeartbeats 1000000 in
/-- Evaluating the number-field family action agrees pointwise with the native rational extension. -/
theorem numberFieldTateLocalSystemAction_app_apply (a : F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    ((numberFieldTateLocalSystemAction K A p F φ a).app (Scheme.etaleFiberPoint K S x)).hom v =
      NumberField.RingOfIntegers.rationalExtension F
        ((TateModule.rationalEndomorphismMap p
          (Additive (Scheme.geometricPointOver K x ⟶ A.X))).comp
          ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A).comp φ)) a v := by
  obtain ⟨t, rfl⟩ := (NumberField.RingOfIntegers.rationalizationEquiv F).surjective a
  induction t using TensorProduct.inductionOn with
  | tmul q c =>
    simp only [NumberField.RingOfIntegers.rationalizationEquiv_tmul, map_smul,
      numberFieldTateLocalSystemAction_integer, NumberField.RingOfIntegers.rationalExtension_apply]
    change q • (((rationalTateLocalSystemMap K p (φ c)).app
        (Scheme.etaleFiberPoint K S x)).hom v) =
      q • (TateModule.rationalMap p
        (CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A (φ c)) v)
    exact congrArg (fun w => q • w) (rationalTateLocalSystemMap_app_apply K p (φ c) x v)
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (fun v w => v + w) ha hb

set_option maxHeartbeats 1000000 in
/-- Evaluating the family coefficient action gives the tensor extension of the original
integer action on its native group of geometric points. -/
theorem tensorTateLocalSystemAction_app (a : ℚ_[p] ⊗[ℚ] F) :
    ((tensorTateLocalSystemAction K A p F φ a).app (Scheme.etaleFiberPoint K S x)).hom =
      NumberField.RingOfIntegers.tensorExtension F ℚ_[p]
        ((TateModule.rationalEndomorphismMap p
          (Additive (Scheme.geometricPointOver K x ⟶ A.X))).comp
          ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A).comp φ)) a := by
  apply LinearMap.ext
  intro v
  induction a using TensorProduct.inductionOn with
  | tmul c a =>
    rw [tensorTateLocalSystemAction_tmul, NumberField.RingOfIntegers.tensorExtension_tmul]
    change c • (((numberFieldTateLocalSystemAction K A p F φ a).app
        (Scheme.etaleFiberPoint K S x)).hom v) =
      c • (NumberField.RingOfIntegers.rationalExtension F
        ((TateModule.rationalEndomorphismMap p
          (Additive (Scheme.geometricPointOver K x ⟶ A.X))).comp
          ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver K x) A).comp φ)) a v)
    exact congrArg (fun w => c • w) (numberFieldTateLocalSystemAction_app_apply K A p F φ x a v)
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (fun v w => v + w) ha hb

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
variable (E K : Type u) [Field E] [Field K] [Algebra E K]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (j : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)

set_option maxHeartbeats 1000000 in
/-- The actual common-field Tate comparison intertwines the full coefficient tensor algebra. -/
theorem arithmeticRationalTateFieldEquiv_tensorCoefficients (a : ℚ_[p] ⊗[ℚ] F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver E x ⟶ A.X))) :
    arithmeticRationalTateFieldEquiv E K x j A p
        (((tensorTateLocalSystemAction E A p F φ a).app (Scheme.etaleFiberPoint E S x)).hom v) =
      ((tensorTateLocalSystemAction K A p F φ a).app
        (Scheme.etaleFiberPoint K S (Spec.algebraMap E K ≫ x))).hom
        (arithmeticRationalTateFieldEquiv E K x j A p v) := by
  let aE := (TateModule.rationalEndomorphismMap p
    (Additive (Scheme.geometricPointOver E x ⟶ A.X))).comp
      ((CommGrp.pointsEndomorphismMap (Scheme.geometricPointOver E x) A).comp φ)
  let aK := (TateModule.rationalEndomorphismMap p
    (Additive (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x) ⟶ A.X))).comp
      ((CommGrp.pointsEndomorphismMap
        (Scheme.geometricPointOver K (Spec.algebraMap E K ≫ x)) A).comp φ)
  let e := arithmeticRationalTateFieldEquiv E K x j A p
  have h := NumberField.RingOfIntegers.tensorExtension_intertwines F aE aK e.toLinearMap
    (fun c w => arithmeticRationalTateFieldEquiv_endomorphism E K x j A p (φ c) w) a v
  exact (congrArg e (LinearMap.congr_fun (tensorTateLocalSystemAction_app E A p F φ x a) v)).trans
    (h.trans (LinearMap.congr_fun
      (tensorTateLocalSystemAction_app K A p F φ (Spec.algebraMap E K ≫ x) a) (e v)).symm)

end AlgebraicGeometry.GroupScheme
