/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricPath
public import HilbertModularity.Geometry.GroupScheme.TateGeometricPathMonodromy
public import HilbertModularity.CategoryTheory.Conjugation

/-! # Monodromy on coefficient-labelled Tate factors along geometric paths -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct ModuleCat.Algebra ChangeOfRings
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K L : Type u) [Field K] [Field L] {S : Scheme.{u}}
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : Scheme.finiteArithmeticFiberFunctor K x ≅ Scheme.finiteArithmeticFiberFunctor L y)
  (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (C : Type u) [Field C] [Algebra ℚ_[p] C]

set_option maxHeartbeats 1000000 in
/-- The scalar-extended Tate path intertwines actual monodromy loops. -/
theorem extendedTateGeometricPathIso_monodromy (σ : Scheme.etaleFundamentalGroup K x) :
    (extendedTateLocalSystem K A p C).map (Scheme.etaleFiberPath K S σ) ≫
        (extendedTateGeometricPathIso K L e A p C).hom =
      (extendedTateGeometricPathIso K L e A p C).hom ≫
        (extendedTateLocalSystem L A p C).map
          (Scheme.etaleFiberPath L S (Scheme.geometricFiberPathGroupEquiv K L e σ)) := by
  let E := rationalTateGeometricPathIso K L e A p
  let T := ModuleCat.extendScalars (algebraMap ℚ_[p] C)
  have h : (rationalTateLocalSystem K A p).map (Scheme.etaleFiberPath K S σ) ≫ E.hom =
      E.hom ≫ (rationalTateLocalSystem L A p).map
        (Scheme.etaleFiberPath L S (Scheme.geometricFiberPathGroupEquiv K L e σ)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hx := rationalTateLocalSystem_loop K A p x σ v
    have hy := rationalTateLocalSystem_loop L A p y
      (Scheme.geometricFiberPathGroupEquiv K L e σ) (rationalTateGeometricPathEquiv K L e A p v)
    have ht := LinearMap.congr_fun
      ((rationalTateGeometricPathRepresentationEquiv K L e A p).isIntertwining' σ) v
    exact (congrArg (rationalTateGeometricPathEquiv K L e A p) hx).trans (ht.trans hy.symm)
  change T.map _ ≫ T.map E.hom = T.map E.hom ≫ T.map _
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

variable (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ C]
  (hC : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ C)).Splits)

set_option maxHeartbeats 2000000 in
/-- Restricting the ambient geometric path intertwines monodromy on each labelled factor. -/
theorem labelledTateGeometricPathIso_monodromy (τ : F →ₐ[ℚ] C)
    (σ : Scheme.etaleFundamentalGroup K x) :
    (labelledTateLocalSystem K A p C F φ hC τ).map (Scheme.etaleFiberPath K S σ) ≫
        (labelledTateGeometricPathIso K L e A p C F φ hC τ).hom =
      (labelledTateGeometricPathIso K L e A p C F φ hC τ).hom ≫
        (labelledTateLocalSystem L A p C F φ hC τ).map
          (Scheme.etaleFiberPath L S (Scheme.geometricFiberPathGroupEquiv K L e σ)) :=
  CategoryTheory.NatTrans.intertwines_of_mono
    (labelledTateLocalSystemInclusion K A p C F φ hC τ)
    (labelledTateLocalSystemInclusion L A p C F φ hC τ)
    (Scheme.etaleFiberPoint K S x) (Scheme.etaleFiberPoint L S y)
    (Scheme.etaleFiberPath K S σ)
    (Scheme.etaleFiberPath L S (Scheme.geometricFiberPathGroupEquiv K L e σ))
    (labelledTateGeometricPathIso K L e A p C F φ hC τ).hom
    (extendedTateGeometricPathIso K L e A p C).hom
    (labelledTateGeometricPathIso_hom_inclusion K L e A p C F φ hC τ)
    (extendedTateGeometricPathIso_monodromy K L e A p C σ)

set_option maxHeartbeats 1000000 in
/-- A geometric path compares the actual monodromy representations on the same labelled Tate factor. -/
def labelledTateGeometricPathRepresentationEquiv (τ : F →ₐ[ℚ] C) :
    Representation.Equiv
      (Scheme.fiberMonodromy K S (labelledTateLocalSystem K A p C F φ hC τ) x)
      ((Scheme.fiberMonodromy L S (labelledTateLocalSystem L A p C F φ hC τ) y).comp
        (Scheme.geometricFiberPathGroupEquiv K L e).toMonoidHom) :=
  .mk (labelledTateGeometricPathIso K L e A p C F φ hC τ).toLinearEquiv
    (fun σ => congrArg ModuleCat.Hom.hom
      (labelledTateGeometricPathIso_monodromy K L e A p C F φ hC τ σ))

end AlgebraicGeometry.GroupScheme
