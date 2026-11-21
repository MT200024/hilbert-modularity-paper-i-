/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientAction
public import HilbertModularity.Algebra.Category.ModuleCat.FunctorCategory

/-! # The coefficient tensor algebra on the native geometric Tate module

Evaluating the natural coefficient action gives an algebra action on the
ordinary Tate module at an actual geometric point. Its commutation with
monodromy follows from the naturality of the original family endomorphisms.
-/

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
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option maxHeartbeats 1000000 in
/-- The full coefficient tensor algebra acts on the native geometric Tate module. -/
def geometricTensorTateAction : ℚ_[p] ⊗[ℚ] F →ₐ[ℚ_[p]]
    Module.End ℚ_[p] (TateModule.rational p
      (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
  (ModuleCat.functorEndApp ℚ_[p] (rationalTateLocalSystem K A p)
    (Scheme.etaleFiberPoint K S x)).comp (tensorTateLocalSystemAction K A p F φ)

set_option maxHeartbeats 1000000 in
/-- Actual monodromy commutes with the full tensor coefficient action of the same scheme. -/
theorem rationalTateMonodromy_tensorCoefficients
    (σ : Scheme.etaleFundamentalGroup K x) (a : ℚ_[p] ⊗[ℚ] F)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalTateMonodromy K x A p σ (geometricTensorTateAction K A p F φ x a v) =
      geometricTensorTateAction K A p F φ x a (rationalTateMonodromy K x A p σ v) := by
  let e := Scheme.etaleFiberPath K S (x := x) (y := x) σ
  have h := (tensorTateLocalSystemAction K A p F φ a).naturality e
  have hv := congrArg (fun f : (rationalTateLocalSystem K A p).obj (Scheme.etaleFiberPoint K S x) ⟶
      (rationalTateLocalSystem K A p).obj (Scheme.etaleFiberPoint K S x) => f v) h
  change geometricTensorTateAction K A p F φ x a
      (((rationalTateLocalSystem K A p).map e).hom v) =
    ((rationalTateLocalSystem K A p).map e).hom
      (geometricTensorTateAction K A p F φ x a v) at hv
  exact (rationalTateLocalSystem_loop K A p x σ
    (geometricTensorTateAction K A p F φ x a v)).symm.trans
      (hv.symm.trans (congrArg (geometricTensorTateAction K A p F φ x a)
        (rationalTateLocalSystem_loop K A p x σ v)))

end AlgebraicGeometry.GroupScheme
