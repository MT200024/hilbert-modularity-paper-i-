/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.FiniteGeneration
public import HilbertModularity.Geometry.Etale.LocalSystem
public import HilbertModularity.Topology.TateModule.FiniteFree

/-! # The continuous rational Tate local system of one group scheme -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))

local instance tatePointTopology (x : Scheme.EtaleFiberGroupoid K S) :
    TopologicalSpace (Additive (Scheme.geometricPointOver K x ⟶ A.X)) := ⊥

local instance tatePointDiscreteTopology (x : Scheme.EtaleFiberGroupoid K S) :
    DiscreteTopology (Additive (Scheme.geometricPointOver K x ⟶ A.X)) := ⟨rfl⟩

variable (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The actual rational Tate family, retaining its native topological module structure. -/
def topologicalTateLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ TopModuleCat ℚ_[p] where
  obj x := TopModuleCat.of ℚ_[p]
    (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)))
  map {x y} e := TopModuleCat.ofHom (show
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →L[ℚ_[p]]
        TateModule.rational p (Additive (Scheme.geometricPointOver K y ⟶ A.X)) from {
    toLinearMap := ((rationalTateLocalSystem K A p).map (X := x) (Y := y) e).hom
    cont := continuous_rationalTateLocalSystem_map K A p e })
  map_id x := by
    apply (forget₂ (TopModuleCat ℚ_[p]) (ModuleCat ℚ_[p])).map_injective
    exact (rationalTateLocalSystem K A p).map_id x
  map_comp e f := by
    apply (forget₂ (TopModuleCat ℚ_[p]) (ModuleCat ℚ_[p])).map_injective
    exact (rationalTateLocalSystem K A p).map_comp e f

set_option maxHeartbeats 400000 in
/-- The actual topological Tate family's monodromy has continuous orbit maps. -/
theorem continuous_topologicalTateLocalSystem_loop
    (x : Spec (CommRingCat.of K) ⟶ S)
    (v : (topologicalTateLocalSystem K A p).obj (Scheme.etaleFiberPoint K S x)) :
    Continuous (fun σ : Scheme.etaleFundamentalGroup K x =>
      ((topologicalTateLocalSystem K A p).map (Scheme.etaleFiberPath K S σ)).hom v) := by
  let : TopologicalSpace (Additive (Scheme.geometricPointOver K x ⟶ A.X)) :=
    tatePointTopology K A (Scheme.etaleFiberPoint K S x)
  let : DiscreteTopology (Additive (Scheme.geometricPointOver K x ⟶ A.X)) := ⟨rfl⟩
  let w : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) := v
  have hρ := continuous_rationalTateMonodromy K x A p
  have hι : Continuous (fun σ : Scheme.etaleFundamentalGroup K x => (σ, w)) :=
    continuous_id.prodMk continuous_const
  have h := hρ.comp hι
  apply h.congr
  intro σ
  exact (rationalTateLocalSystem_loop K A p x σ w).symm

variable [Surjective (p • 𝟙 A).hom.hom.hom.left]

local instance : IsFinite (p • 𝟙 A).hom.hom.hom.left := by
  simpa only [pow_one] using
    (inferInstance : IsFinite (p ^ 1 • 𝟙 A).hom.hom.hom.left)

local instance : Etale (p • 𝟙 A).hom.hom.hom.left := by
  simpa only [pow_one] using
    (inferInstance : Etale (p ^ 1 • 𝟙 A).hom.hom.hom.left)

local instance (x : Scheme.EtaleFiberGroupoid K S) : Module.Finite ℤ_[p]
    (TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
  integralGeometricTate_finite K x A p

set_option maxHeartbeats 400000 in
/-- Finite étale multiplication and surjectivity give the one actual rational Tate local system. -/
def tateEtaleLocalSystem : Scheme.EtaleLocalSystem K S ℚ_[p] where
  toFunctor := topologicalTateLocalSystem K A p
  finite x := by
    change Module.Finite ℚ_[p]
      (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)))
    infer_instance
  hausdorff x := by
    change T2Space (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)))
    infer_instance
  continuous_monodromy x v :=
    continuous_topologicalTateLocalSystem_loop K A p x v

end AlgebraicGeometry.GroupScheme
