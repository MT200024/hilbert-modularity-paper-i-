/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionLocalSystem
public import HilbertModularity.Topology.TateModule.Maps

/-! # Tate-module families on the actual geometric fibre groupoid -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- One actual torsion tower gives a family of ordinary integral Tate modules. -/
def integralTateLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat ℤ_[p] where
  obj x := ModuleCat.of ℤ_[p]
    (TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X)))
  map e := ModuleCat.ofHom (TateModule.mapOfTorsion p
    (fun n => ((torsionPadicLocalSystem K A p n).map e).hom)
    (torsionPadicLocalSystem_transition K A p e))
  map_id x := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    exact congrArg (fun f : (torsionPadicLocalSystem K A p n).obj x ⟶
        (torsionPadicLocalSystem K A p n).obj x => f (v.val n))
      ((torsionPadicLocalSystem K A p n).map_id x)
  map_comp {x y z} e f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    exact congrArg (fun g : (torsionPadicLocalSystem K A p n).obj x ⟶
        (torsionPadicLocalSystem K A p n).obj z => g (v.val n))
      ((torsionPadicLocalSystem K A p n).map_comp e f)

/-- The family's action at every loop is the actual integral Tate monodromy. -/
@[simp]
theorem integralTateLocalSystem_loop (x : Spec (CommRingCat.of K) ⟶ S)
    (σ : Scheme.etaleFundamentalGroup K x)
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    ((integralTateLocalSystem K A p).map
      (X := Scheme.etaleFiberPoint K S x) (Y := Scheme.etaleFiberPoint K S x)
      (Scheme.etaleFiberPath K S (x := x) (y := x) σ)).hom v =
      integralTateMonodromy K x A p σ v := by
  apply Subtype.ext
  funext n
  exact torsionPadicLocalSystem_loop K A p x σ n (v.val n)

/-- Scalar extension gives one rational Tate-module family over the same actual fibre groupoid. -/
def rationalTateLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ ModuleCat ℚ_[p] where
  obj x := ModuleCat.of ℚ_[p]
    (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)))
  map e := ModuleCat.ofHom (((integralTateLocalSystem K A p).map e).hom.baseChange ℚ_[p])
  map_id x := by
    apply ModuleCat.hom_ext
    change (((integralTateLocalSystem K A p).map (𝟙 x)).hom).baseChange ℚ_[p] = LinearMap.id
    rw [(integralTateLocalSystem K A p).map_id]
    exact LinearMap.baseChange_id
  map_comp e f := by
    apply ModuleCat.hom_ext
    change (((integralTateLocalSystem K A p).map (e ≫ f)).hom).baseChange ℚ_[p] =
      (((integralTateLocalSystem K A p).map f).hom.baseChange ℚ_[p]).comp
        (((integralTateLocalSystem K A p).map e).hom.baseChange ℚ_[p])
    rw [(integralTateLocalSystem K A p).map_comp]
    exact LinearMap.baseChange_comp _ _

/-- Its object at every point is the ordinary rational Tate module of the same group scheme. -/
@[simp]
theorem rationalTateLocalSystem_obj (x : Scheme.EtaleFiberGroupoid K S) :
    (rationalTateLocalSystem K A p).obj x = ModuleCat.of ℚ_[p]
      (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) := rfl

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Rational path transport fixes coefficients and transports the actual integral Tate vector. -/
@[simp]
theorem rationalTateLocalSystem_map_tmul {x y : Scheme.EtaleFiberGroupoid K S} (e : x ⟶ y)
    (c : ℚ_[p]) (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    ((rationalTateLocalSystem K A p).map e).hom (c ⊗ₜ v) =
      c ⊗ₜ ((integralTateLocalSystem K A p).map e).hom v := rfl

set_option maxHeartbeats 400000 in
/-- On pure tensors, a rational loop fixes the coefficient and has the actual Tate action. -/
theorem rationalTateLocalSystem_loop_tmul (x : Spec (CommRingCat.of K) ⟶ S)
    (σ : Scheme.etaleFundamentalGroup K x) (c : ℚ_[p])
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    ((rationalTateLocalSystem K A p).map
      (X := Scheme.etaleFiberPoint K S x) (Y := Scheme.etaleFiberPoint K S x)
      (Scheme.etaleFiberPath K S (x := x) (y := x) σ)).hom (c ⊗ₜ v) =
      rationalTateMonodromy K x A p σ (c ⊗ₜ v) := by
  have h₁ := rationalTateLocalSystem_map_tmul K A p
    (x := Scheme.etaleFiberPoint K S x) (y := Scheme.etaleFiberPoint K S x)
    (Scheme.etaleFiberPath K S (x := x) (y := x) σ) c v
  have h₂ := integralTateLocalSystem_loop K A p x σ v
  have h₃ := congrArg (TensorProduct.mk ℤ_[p] ℚ_[p]
    (TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) c) h₂
  have h₄ := rationalTateMonodromy_tmul K x A p σ c v
  have h₅ := h₃.trans h₄.symm
  exact h₁.trans h₅

set_option maxHeartbeats 400000 in
/-- The rational family's loop action is the actual rational geometric Tate monodromy. -/
@[simp]
theorem rationalTateLocalSystem_loop (x : Spec (CommRingCat.of K) ⟶ S)
    (σ : Scheme.etaleFundamentalGroup K x)
    (v : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    (show TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →ₗ[ℚ_[p]]
        TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) from
      ((rationalTateLocalSystem K A p).map
        (X := Scheme.etaleFiberPoint K S x) (Y := Scheme.etaleFiberPoint K S x)
        (Scheme.etaleFiberPath K S (x := x) (y := x) σ)).hom) v =
      rationalTateMonodromy K x A p σ v := by
  let F : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →ₗ[ℚ_[p]]
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) :=
    ((rationalTateLocalSystem K A p).map
      (X := Scheme.etaleFiberPoint K S x) (Y := Scheme.etaleFiberPoint K S x)
      (Scheme.etaleFiberPath K S (x := x) (y := x) σ)).hom
  let G := rationalTateMonodromy K x A p σ
  have h : F.restrictScalars ℤ_[p] = G.restrictScalars ℤ_[p] :=
    TensorProduct.ext' (fun c w => rationalTateLocalSystem_loop_tmul K A p x σ c w)
  exact LinearMap.congr_fun h v

variable {x y : Scheme.EtaleFiberGroupoid K S}
  [TopologicalSpace (Additive (Scheme.geometricPointOver K x ⟶ A.X))]
  [TopologicalSpace (Additive (Scheme.geometricPointOver K y ⟶ A.X))]
  [DiscreteTopology (Additive (Scheme.geometricPointOver K x ⟶ A.X))]

/-- Every actual étale path acts continuously on the ordinary integral Tate modules. -/
theorem continuous_integralTateLocalSystem_map (e : x ⟶ y) :
    Continuous (show TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →
      TateModule.integral p (Additive (Scheme.geometricPointOver K y ⟶ A.X)) from
        ((integralTateLocalSystem K A p).map (X := x) (Y := y) e).hom) :=
  TateModule.continuous_mapOfTorsion p
    (fun n => ((torsionPadicLocalSystem K A p n).map e).hom)
    (torsionPadicLocalSystem_transition K A p e) (fun _ => continuous_of_discreteTopology)

/-- The rational extension of actual étale path transport is continuous. -/
theorem continuous_rationalTateLocalSystem_map (e : x ⟶ y) :
    Continuous (show TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →
      TateModule.rational p (Additive (Scheme.geometricPointOver K y ⟶ A.X)) from
        ((rationalTateLocalSystem K A p).map (X := x) (Y := y) e).hom) :=
  TateModule.continuous_baseChange_map p ((integralTateLocalSystem K A p).map (X := x) (Y := y) e).hom
    (continuous_integralTateLocalSystem_map K A p e)

end AlgebraicGeometry.GroupScheme
