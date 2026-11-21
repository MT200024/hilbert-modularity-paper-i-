/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GroupSchemeCoefficients
public import HilbertModularity.Geometry.Etale.GroupFiberAction
public import HilbertModularity.Geometry.Etale.LocalSystem
public import Mathlib.Algebra.Group.TypeTags.Finite

/-! # Continuous coefficient local systems from actual finite étale group schemes

The actual finite geometric point groups have discrete Hausdorff topology.
Their profinite monodromy is the original continuous action on finite covers.
For discrete field coefficients, the previously constructed linear family
therefore satisfies the native finite-dimensional étale local-system interface.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme

universe u
attribute [local instance] finiteEtaleCartesianMonoidalCategory finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  [AlgebraicGeometry.Etale A.X.hom] [IsFinite A.X.hom]

/-- The original geometric point group of a finite étale group scheme is finite. -/
instance finiteEtalePoint_finite (x : EtaleFiberGroupoid K S) :
    Finite (Additive (geometricPointOver K x ⟶ A.X)) := by
  let : Finite ((finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A)) :=
    finiteGroupFiber_finite K x (finiteEtaleGroupObject A)
  exact Finite.of_equiv (Additive ((finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A)))
    (finiteGroupFiberPointsEquiv K x A).toAdditive.toEquiv

/-- The finite original point group is given its discrete topology. -/
local instance pointTopology (x : EtaleFiberGroupoid K S) :
    TopologicalSpace (Additive (geometricPointOver K x ⟶ A.X)) := ⊥

/-- The chosen point topology is discrete by construction. -/
local instance pointDiscreteTopology (x : EtaleFiberGroupoid K S) :
    DiscreteTopology (Additive (geometricPointOver K x ⟶ A.X)) := ⟨rfl⟩

variable (R : Type*) [Field R] [TopologicalSpace R] [DiscreteTopology R]
  (φ : R →+* End A)

/-- The actual coefficient-linear point family, with its finite discrete module topology. -/
def topologicalFiniteCoefficientLocalSystem : EtaleFiberGroupoid K S ⥤ TopModuleCat R := by
  letI (x : EtaleFiberGroupoid K S) := finiteEtalePointModule K A R φ x
  letI (x : EtaleFiberGroupoid K S) : ContinuousSMul R
      (Additive (geometricPointOver K x ⟶ A.X)) := ⟨continuous_of_discreteTopology⟩
  exact {
    obj x := TopModuleCat.of R (Additive (geometricPointOver K x ⟶ A.X))
    map {x y} e := TopModuleCat.ofHom (show
        Additive (geometricPointOver K x ⟶ A.X) →L[R]
          Additive (geometricPointOver K y ⟶ A.X) from {
      toLinearMap := ((finiteEtaleCoefficientLocalSystem K A R φ).map e).hom
      cont := continuous_of_discreteTopology })
    map_id x := by
      apply (forget₂ (TopModuleCat R) (ModuleCat R)).map_injective
      exact (finiteEtaleCoefficientLocalSystem K A R φ).map_id x
    map_comp e f := by
      apply (forget₂ (TopModuleCat R) (ModuleCat R)).map_injective
      exact (finiteEtaleCoefficientLocalSystem K A R φ).map_comp e f }

/-- Monodromy of the actual finite coefficient family has continuous orbit maps. -/
theorem continuous_topologicalFiniteCoefficientLocalSystem_loop
    (x : Spec (CommRingCat.of K) ⟶ S)
    (v : (topologicalFiniteCoefficientLocalSystem K A R φ).obj (etaleFiberPoint K S x)) :
    Continuous (fun σ : etaleFundamentalGroup K x =>
      ((topologicalFiniteCoefficientLocalSystem K A R φ).map (etaleFiberPath K S σ)).hom v) := by
  let : TopologicalSpace (Additive (geometricPointOver K x ⟶ A.X)) := pointTopology K A x
  let : DiscreteTopology (Additive (geometricPointOver K x ⟶ A.X)) := ⟨rfl⟩
  let e := finiteGroupFiberPointsEquiv K x A
  let w := e.symm v.toMul
  have ho : Continuous (fun z : (finiteGroupFiberFunctor K x).obj (finiteEtaleGroupObject A) =>
      Additive.ofMul (e z)) := continuous_of_discreteTopology
  have ha : Continuous (fun σ : etaleFundamentalGroup K x => σ • w) := continuous_id.smul continuous_const
  apply (ho.comp ha).congr
  intro σ
  change e (σ • w) = ((finiteEtaleCoefficientLocalSystem K A R φ).map
    (etaleFiberPath K S σ) v).toMul
  erw [finiteGroupFiberPointsEquiv_apply K x A]

/-- Actual finite étale group schemes with discrete field coefficients give continuous finite-dimensional local systems. -/
def finiteCoefficientEtaleLocalSystem : EtaleLocalSystem K S R := by
  letI (x : EtaleFiberGroupoid K S) := finiteEtalePointModule K A R φ x
  letI (x : EtaleFiberGroupoid K S) : ContinuousSMul R
      (Additive (geometricPointOver K x ⟶ A.X)) := ⟨continuous_of_discreteTopology⟩
  exact {
    toFunctor := topologicalFiniteCoefficientLocalSystem K A R φ
    finite x := by
      change Module.Finite R (Additive (geometricPointOver K x ⟶ A.X))
      infer_instance
    hausdorff x := by
      change T2Space (Additive (geometricPointOver K x ⟶ A.X))
      infer_instance
    continuous_monodromy x v := continuous_topologicalFiniteCoefficientLocalSystem_loop K A R φ x v }

/-- Forgetting topology recovers exactly the previously constructed actual coefficient point family. -/
theorem finiteCoefficientEtaleLocalSystem_algebraicFunctor :
    (finiteCoefficientEtaleLocalSystem K A R φ).algebraicFunctor =
      finiteEtaleCoefficientLocalSystem K A R φ := rfl

end AlgebraicGeometry.Scheme
