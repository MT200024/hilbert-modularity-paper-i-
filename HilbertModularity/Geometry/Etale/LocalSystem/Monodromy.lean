/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem

/-! # Continuous monodromy of natural retracts -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u v w
variable (K : Type u) [Field K] (S : Scheme.{u})
  (R : Type v) [Field R] [TopologicalSpace R]
  (L M : EtaleFiberGroupoid K S ⥤ TopModuleCat.{w} R)
  (i : M ⟶ L) (r : L ⟶ M) (h : i ≫ r = 𝟙 M)

include h in
/-- A natural retract of a family with continuous monodromy again has continuous monodromy. -/
theorem continuous_monodromy_of_retract
    (hL : ∀ (x : Spec (CommRingCat.of K) ⟶ S)
      (v : L.obj (etaleFiberPoint K S x)),
      Continuous (fun σ : etaleFundamentalGroup K x =>
        (L.map (etaleFiberPath K S σ)).hom v))
    (x : Spec (CommRingCat.of K) ⟶ S)
    (v : M.obj (etaleFiberPoint K S x)) :
    Continuous (fun σ : etaleFundamentalGroup K x =>
      (M.map (etaleFiberPath K S σ)).hom v) := by
  have hc := ((r.app (etaleFiberPoint K S x)).hom.continuous).comp
    (hL x ((i.app (etaleFiberPoint K S x)).hom v))
  apply hc.congr
  intro σ
  have hcomp := NatTrans.congr_app h (etaleFiberPoint K S x)
  change i.app (etaleFiberPoint K S x) ≫ r.app (etaleFiberPoint K S x) =
    𝟙 (M.obj (etaleFiberPoint K S x)) at hcomp
  have he : i.app (etaleFiberPoint K S x) ≫ L.map (etaleFiberPath K S σ) ≫
      r.app (etaleFiberPoint K S x) = M.map (etaleFiberPath K S σ) := by
    rw [← Category.assoc, ← i.naturality, Category.assoc, hcomp, Category.comp_id]
  exact congrArg (fun f => f.hom v) he

end AlgebraicGeometry.Scheme
