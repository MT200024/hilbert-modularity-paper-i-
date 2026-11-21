/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientAction
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Fiber
public import HilbertModularity.Geometry.GroupScheme.Endomorphism

/-! # Coefficients and arithmetic fibre comparison -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)
variable (x : Spec (CommRingCat.of K) ⟶ S)

set_option maxHeartbeats 1000000 in
/-- Fibre comparison respects every integral coefficient from the original family. -/
theorem rationalGeometricFiberTateEquiv_integer (a : 𝓞 F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalGeometricFiberTateEquiv K A x p
        (((numberFieldTateLocalSystemAction K A p F φ (a : F)).app
          (Scheme.etaleFiberPoint K S x)).hom v) =
      fiberNumberFieldTateAction K A x p F φ (a : F)
        (rationalGeometricFiberTateEquiv K A x p v) := by
  rw [numberFieldTateLocalSystemAction_integer, fiberNumberFieldTateAction_integer]
  have h₁ := congrArg (fun w :
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) =>
        rationalGeometricFiberTateEquiv K A x p w)
    (rationalTateLocalSystemMap_app_apply K p (φ a) x v)
  have h₂ := LinearMap.congr_fun (rationalGeometricFiberTateEquiv_natural K A A x p (φ a)) v
  exact h₁.trans h₂

set_option maxHeartbeats 1000000 in
/-- The arithmetic comparison intertwines the full number-field coefficient action. -/
theorem rationalGeometricFiberTateEquiv_coefficients (a : F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalGeometricFiberTateEquiv K A x p
        (((numberFieldTateLocalSystemAction K A p F φ a).app
          (Scheme.etaleFiberPoint K S x)).hom v) =
      fiberNumberFieldTateAction K A x p F φ a
        (rationalGeometricFiberTateEquiv K A x p v) := by
  obtain ⟨t, rfl⟩ := (NumberField.RingOfIntegers.rationalizationEquiv F).surjective a
  induction t using TensorProduct.inductionOn with
  | tmul q a =>
    simp only [NumberField.RingOfIntegers.rationalizationEquiv_tmul, map_smul]
    change rationalGeometricFiberTateEquiv K A x p
        (q • (((numberFieldTateLocalSystemAction K A p F φ (a : F)).app
          (Scheme.etaleFiberPoint K S x)).hom v)) =
      q • fiberNumberFieldTateAction K A x p F φ (a : F)
        (rationalGeometricFiberTateEquiv K A x p v)
    exact ((rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toLinearMap.map_smul_of_tower
      q _).trans (congrArg (fun w => q • w)
        (rationalGeometricFiberTateEquiv_integer K A p F φ x a v))
  | add t u ht hu =>
    simp only [map_add]
    change rationalGeometricFiberTateEquiv K A x p
        ((((numberFieldTateLocalSystemAction K A p F φ
          (NumberField.RingOfIntegers.rationalizationEquiv F t)).app
            (Scheme.etaleFiberPoint K S x)).hom v) +
          (((numberFieldTateLocalSystemAction K A p F φ
            (NumberField.RingOfIntegers.rationalizationEquiv F u)).app
              (Scheme.etaleFiberPoint K S x)).hom v)) =
      fiberNumberFieldTateAction K A x p F φ (NumberField.RingOfIntegers.rationalizationEquiv F t)
          (rationalGeometricFiberTateEquiv K A x p v) +
        fiberNumberFieldTateAction K A x p F φ (NumberField.RingOfIntegers.rationalizationEquiv F u)
          (rationalGeometricFiberTateEquiv K A x p v)
    exact ((rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.map_add _ _).trans
      (congrArg₂ (fun y z => y + z) ht hu)

set_option maxHeartbeats 1000000 in
/-- Arithmetic fibre comparison respects the whole native coefficient tensor algebra. -/
theorem rationalGeometricFiberTateEquiv_tensorCoefficients (a : ℚ_[p] ⊗[ℚ] F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalGeometricFiberTateEquiv K A x p
        (((tensorTateLocalSystemAction K A p F φ a).app
          (Scheme.etaleFiberPoint K S x)).hom v) =
      fiberTensorTateAction K A x p F φ a
        (rationalGeometricFiberTateEquiv K A x p v) := by
  induction a using TensorProduct.inductionOn with
  | tmul c a =>
    simp only [tensorTateLocalSystemAction_tmul, fiberTensorTateAction_tmul]
    change rationalGeometricFiberTateEquiv K A x p
        (c • (((numberFieldTateLocalSystemAction K A p F φ a).app
          (Scheme.etaleFiberPoint K S x)).hom v)) =
      c • fiberNumberFieldTateAction K A x p F φ a
        (rationalGeometricFiberTateEquiv K A x p v)
    exact (map_smul (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv c _).trans
      (congrArg (fun w => c • w)
        (rationalGeometricFiberTateEquiv_coefficients K A p F φ x a v))
  | add a b ha hb =>
    simp only [map_add]
    change rationalGeometricFiberTateEquiv K A x p
        ((((tensorTateLocalSystemAction K A p F φ a).app
          (Scheme.etaleFiberPoint K S x)).hom v) +
          (((tensorTateLocalSystemAction K A p F φ b).app
            (Scheme.etaleFiberPoint K S x)).hom v)) =
      fiberTensorTateAction K A x p F φ a (rationalGeometricFiberTateEquiv K A x p v) +
        fiberTensorTateAction K A x p F φ b (rationalGeometricFiberTateEquiv K A x p v)
    exact ((rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.map_add _ _).trans
      (congrArg₂ (fun y z => y + z) ha hb)

end AlgebraicGeometry.GroupScheme
