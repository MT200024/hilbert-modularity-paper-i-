/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem.ScalarExtension
public import HilbertModularity.Geometry.Etale.LocalSystem.Monodromy
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.FiniteCoefficients
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LabelledFiber

/-! # Continuous labelled coefficient families

The extended and labelled Tate families retain continuous monodromy and their
canonical arithmetic specializations. The labels are images of natural
coefficient projectors on one family, as in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.GroupScheme
open CategoryTheory
open scoped CategoryTheory.MonObj
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [NontriviallyNormedField L] [Algebra ℚ_[p] L]

/-- The extended single Tate family with its canonical coefficient-module topology. -/
def topologicalExtendedTateLocalSystem : Scheme.EtaleFiberGroupoid K S ⥤ TopModuleCat L :=
  extendedTateLocalSystem K A p L ⋙ TopModuleCat.withModuleTopology L

variable [Surjective (p • 𝟙 A).hom.hom.hom.left]

/-- Forgetting the native Tate topology recovers the same original rational family. -/
theorem tateEtaleLocalSystem_algebraicFunctor :
    (tateEtaleLocalSystem K A p).algebraicFunctor = rationalTateLocalSystem K A p := rfl

variable [ContinuousSMul ℚ_[p] L]

/-- The actual rational Tate local system admits extension of its coefficient field. -/
def extendedTateEtaleLocalSystem : Scheme.EtaleLocalSystem K S L :=
  (tateEtaleLocalSystem K A p).extendScalars L

/-- The continuous extended family has exactly the previously constructed underlying functor. -/
theorem extendedTateEtaleLocalSystem_toFunctor :
    (extendedTateEtaleLocalSystem K A p L).toFunctor = topologicalExtendedTateLocalSystem K A p L := by
  change (tateEtaleLocalSystem K A p).algebraicFunctor ⋙
      ModuleCat.extendScalars (algebraMap ℚ_[p] L) ⋙ TopModuleCat.withModuleTopology L = _
  rw [tateEtaleLocalSystem_algebraicFunctor]
  rfl

/-- The coefficient-extended family's actual monodromy has continuous orbit maps. -/
theorem continuous_topologicalExtendedTateLocalSystem_loop
    (x : Spec (CommRingCat.of K) ⟶ S)
    (v : (topologicalExtendedTateLocalSystem K A p L).obj (Scheme.etaleFiberPoint K S x)) :
    Continuous (fun σ : Scheme.etaleFundamentalGroup K x =>
      ((topologicalExtendedTateLocalSystem K A p L).map (Scheme.etaleFiberPath K S σ)).hom v) := by
  have h := (extendedTateEtaleLocalSystem K A p L).continuous_monodromy
  rw [extendedTateEtaleLocalSystem_toFunctor] at h
  exact h x v

/-- Arithmetic specialization of the continuous extended family is the native extended Tate representation. -/
def extendedTateEtaleLocalSystem_arithmeticEquiv (x : Spec (CommRingCat.of K) ⟶ S) :
    Representation.Equiv ((extendedTateEtaleLocalSystem K A p L).arithmeticRepresentation x)
      ((tateRepresentation K (fiber K A x).X p).baseChange L) :=
  extendedTateLocalSystem_arithmeticEquiv K A p L x

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  (L : Type u) [NontriviallyNormedField L] [Algebra ℚ_[p] L]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A) [Algebra ℚ L]
  (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)


/-- The labelled image family with its canonical coefficient-module topology. -/
def topologicalLabelledTateLocalSystem (σ : F →ₐ[ℚ] L) :
    Scheme.EtaleFiberGroupoid K S ⥤ TopModuleCat L :=
  labelledTateLocalSystem K A p L F φ hL σ ⋙ TopModuleCat.withModuleTopology L

variable [Surjective (p • 𝟙 A).hom.hom.hom.left] [ContinuousSMul ℚ_[p] L]

set_option maxHeartbeats 1000000 in
/-- Each labelled family's actual monodromy has continuous orbit maps. -/
theorem continuous_topologicalLabelledTateLocalSystem_loop (σ : F →ₐ[ℚ] L)
    (x : Spec (CommRingCat.of K) ⟶ S)
    (v : (topologicalLabelledTateLocalSystem K A p L F φ hL σ).obj
      (Scheme.etaleFiberPoint K S x)) :
    Continuous (fun g : Scheme.etaleFundamentalGroup K x =>
      ((topologicalLabelledTateLocalSystem K A p L F φ hL σ).map
        (Scheme.etaleFiberPath K S g)).hom v) := by
  let P := labelledTateLocalSystemProjection K A p L F φ hL σ
  let T := TopModuleCat.withModuleTopology L
  let i := Functor.whiskerRight (CategoryTheory.Limits.image.ι P) T
  let r := Functor.whiskerRight (CategoryTheory.Limits.factorThruImage P) T
  have hr : i ≫ r = 𝟙 (topologicalLabelledTateLocalSystem K A p L F φ hL σ) := by
    apply NatTrans.ext
    funext y
    change T.map ((CategoryTheory.Limits.image.ι P).app y) ≫
      T.map ((CategoryTheory.Limits.factorThruImage P).app y) = 𝟙 _
    rw [← T.map_comp]
    have h := NatTrans.congr_app (labelledTateLocalSystem_retraction K A p L F φ hL σ) y
    change (CategoryTheory.Limits.image.ι P).app y ≫
      (CategoryTheory.Limits.factorThruImage P).app y = 𝟙 ((CategoryTheory.Limits.image P).obj y) at h
    rw [h, T.map_id]
  exact Scheme.continuous_monodromy_of_retract K S L
    (topologicalExtendedTateLocalSystem K A p L)
    (topologicalLabelledTateLocalSystem K A p L F φ hL σ) i r hr
    (continuous_topologicalExtendedTateLocalSystem_loop K A p L) x v

/-- Every labelled coefficient factor is a continuous finite-dimensional family on the same groupoid. -/
def labelledTateEtaleLocalSystem (σ : F →ₐ[ℚ] L) : Scheme.EtaleLocalSystem K S L where
  toFunctor := topologicalLabelledTateLocalSystem K A p L F φ hL σ
  finite x := labelledTateLocalSystem_finite K A p L F φ hL σ x
  hausdorff x := by
    let : Module.Finite L ((topologicalLabelledTateLocalSystem K A p L F φ hL σ).obj x) :=
      labelledTateLocalSystem_finite K A p L F φ hL σ x
    have : IsModuleTopology L ((topologicalLabelledTateLocalSystem K A p L F φ hL σ).obj x) := ⟨rfl⟩
    let e := (Module.finBasis L ((topologicalLabelledTateLocalSystem K A p L F φ hL σ).obj x)).equivFun
    let eL : ((topologicalLabelledTateLocalSystem K A p L F φ hL σ).obj x) ≃L[L]
        (Fin (Module.finrank L ((topologicalLabelledTateLocalSystem K A p L F φ hL σ).obj x)) → L) :=
      { e with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
    exact eL.toHomeomorph.symm.t2Space
  continuous_monodromy x v := continuous_topologicalLabelledTateLocalSystem_loop K A p L F φ hL σ x v

/-- The continuous labelled family's arithmetic fibre is the native labelled Tate representation. -/
def labelledTateEtaleLocalSystem_arithmeticEquiv (σ : F →ₐ[ℚ] L)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    Representation.Equiv ((labelledTateEtaleLocalSystem K A p L F φ hL σ).arithmeticRepresentation x)
      (labelledTateSubrepresentation K (fiber K A x).X p F L hL
        (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x (𝓞 F) φ) σ).toRepresentation :=
  labelledTateLocalSystem_arithmeticEquiv K A p L x F φ hL σ

end AlgebraicGeometry.GroupScheme
