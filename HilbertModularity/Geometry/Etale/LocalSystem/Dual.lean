/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Contragredient families on the actual étale fibre groupoid

Dual transport is pullback along the inverse path. Thus its arithmetic
specializations are the actual contragredient representations. Over a finite
discrete coefficient field, continuous finite-dimensional families retain
these properties after duality.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u v w
variable (K : Type u) [Field K] (S : Scheme.{u})
  (R : Type v) [CommRing R]

/-- The contragredient of one actual module-valued fibre family uses inverse-path pullback on duals. -/
def dualFiberFunctor (L : EtaleFiberGroupoid K S ⥤ ModuleCat.{w} R) :
    EtaleFiberGroupoid K S ⥤ ModuleCat R where
  obj x := ModuleCat.of R (Module.Dual R (L.obj x))
  map e := ModuleCat.ofHom ((L.map (inv e)).hom.dualMap)
  map_id x := by
    apply ModuleCat.hom_ext
    ext f v
    change f ((L.map (inv (𝟙 x))) v) = f v
    simp
  map_comp {x y z} e f := by
    apply ModuleCat.hom_ext
    ext l v
    change l ((L.map (inv (e ≫ f))) v) = l ((L.map (inv e)) ((L.map (inv f)) v))
    simp

/-- Dual path transport is evaluation after the actual inverse path map. -/
theorem dualFiberFunctor_map_apply (L : EtaleFiberGroupoid K S ⥤ ModuleCat.{w} R)
    {x y : EtaleFiberGroupoid K S} (e : x ⟶ y)
    (f : Module.Dual R (L.obj x)) (v : L.obj y) :
    (show Module.Dual R (L.obj y) from (dualFiberFunctor K S R L).map e f) v = f (L.map (inv e) v) := rfl

/-- Actual monodromy of the dual family is the contragredient of actual monodromy. -/
theorem fiberMonodromy_dualFiberFunctor (L : EtaleFiberGroupoid K S ⥤ ModuleCat.{w} R)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    fiberMonodromy K S (dualFiberFunctor K S R L) x = (fiberMonodromy K S L x).dual := by
  apply MonoidHom.ext
  intro g
  change etaleFundamentalGroup K x at g
  apply LinearMap.ext
  intro f
  change Module.Dual R (L.obj (etaleFiberPoint K S x)) at f
  apply LinearMap.ext
  intro v
  change f (L.map (inv (etaleFiberPath K S g)) v) =
    f (L.map (etaleFiberPath K S (g⁻¹ : etaleFundamentalGroup K x)) v)
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- Arithmetic specialization of the dual family is the actual contragredient arithmetic representation. -/
theorem arithmeticFiberRepresentation_dualFiberFunctor
    (L : EtaleFiberGroupoid K S ⥤ ModuleCat.{w} R)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    arithmeticFiberRepresentation K S (dualFiberFunctor K S R L) x =
      (arithmeticFiberRepresentation K S L x).dual := by
  unfold arithmeticFiberRepresentation
  rw [fiberMonodromy_dualFiberFunctor]
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro f
  change Module.Dual R (L.obj (etaleFiberPoint K S x)) at f
  apply LinearMap.ext
  intro v
  change f ((fiberMonodromy K S L x) (galoisToEtaleFundamentalGroup K x g)⁻¹ v) =
    f ((fiberMonodromy K S L x) (galoisToEtaleFundamentalGroup K x g⁻¹) v)
  rw [(galoisToEtaleFundamentalGroup K x).map_inv]

namespace EtaleLocalSystem

variable {K S} {R : Type v} [Field R] [Finite R]
  [TopologicalSpace R] [DiscreteTopology R] (L : EtaleLocalSystem K S R)

omit [DiscreteTopology R] in
/-- Finite coefficients make every finite-dimensional Hausdorff fibre discrete. -/
theorem fiber_discrete (x : EtaleFiberGroupoid K S) :
    DiscreteTopology (L.toFunctor.obj x) := by
  let := L.finite x
  let := L.hausdorff x
  let : Finite (L.toFunctor.obj x) := Module.finite_of_finite R
  infer_instance

/-- Dual fibres carry their finite discrete topology. -/
local instance dualTopology (x : EtaleFiberGroupoid K S) :
    TopologicalSpace (Module.Dual R (L.toFunctor.obj x)) := ⊥

/-- The specified dual topology is discrete. -/
local instance dualDiscreteTopology (x : EtaleFiberGroupoid K S) :
    DiscreteTopology (Module.Dual R (L.toFunctor.obj x)) := ⟨rfl⟩

/-- The contragredient family with discrete topological dual fibres. -/
def dualTopologicalFunctor : EtaleFiberGroupoid K S ⥤ TopModuleCat R := by
  letI (x : EtaleFiberGroupoid K S) : ContinuousSMul R
      (Module.Dual R (L.toFunctor.obj x)) := ⟨continuous_of_discreteTopology⟩
  exact {
    obj x := TopModuleCat.of R (Module.Dual R (L.toFunctor.obj x))
    map e := TopModuleCat.ofHom {
      toLinearMap := ((dualFiberFunctor K S R L.algebraicFunctor).map e).hom
      cont := continuous_of_discreteTopology }
    map_id x := by
      apply (forget₂ (TopModuleCat R) (ModuleCat R)).map_injective
      exact (dualFiberFunctor K S R L.algebraicFunctor).map_id x
    map_comp e f := by
      apply (forget₂ (TopModuleCat R) (ModuleCat R)).map_injective
      exact (dualFiberFunctor K S R L.algebraicFunctor).map_comp e f }

/-- Orbit maps of the contragredient family are continuous for actual profinite monodromy. -/
theorem continuous_dual_monodromy (x : Spec (CommRingCat.of K) ⟶ S)
    (f : Module.Dual R (L.toFunctor.obj (etaleFiberPoint K S x))) :
    Continuous (fun g : etaleFundamentalGroup K x =>
      ((dualTopologicalFunctor L).map (etaleFiberPath K S g)).hom f) := by
  let := L.finite (etaleFiberPoint K S x)
  let := L.fiber_discrete (etaleFiberPoint K S x)
  let b := Module.Basis.ofVectorSpace R (L.toFunctor.obj (etaleFiberPoint K S x))
  have hf : Continuous f := continuous_of_discreteTopology
  have hc : Continuous (fun g : etaleFundamentalGroup K x =>
      fun i => f ((L.toFunctor.map (etaleFiberPath K S (g⁻¹ : etaleFundamentalGroup K x))).hom (b i))) :=
    continuous_pi fun i => hf.comp ((L.continuous_monodromy x (b i)).comp continuous_inv)
  have he : Continuous (b.constr R (M' := R)) := continuous_of_discreteTopology
  apply (he.comp hc).congr
  intro g
  apply b.ext
  intro i
  simp only [Function.comp_apply, Module.Basis.constr_basis]
  change f (L.algebraicFunctor.map (etaleFiberPath K S (g⁻¹ : etaleFundamentalGroup K x)) (b i)) =
    f (L.algebraicFunctor.map (inv (etaleFiberPath K S g)) (b i))
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- The continuous contragredient local system over a finite discrete coefficient field. -/
def dual : EtaleLocalSystem K S R where
  toFunctor := L.dualTopologicalFunctor
  finite x := by
    let := L.finite x
    change Module.Finite R (Module.Dual R (L.toFunctor.obj x))
    infer_instance
  hausdorff x := by
    change T2Space (Module.Dual R (L.toFunctor.obj x))
    infer_instance
  continuous_monodromy x f := L.continuous_dual_monodromy x f

/-- Forgetting topology in duality gives the actual inverse-path dual functor. -/
theorem dual_algebraicFunctor :
    L.dual.algebraicFunctor = dualFiberFunctor K S R L.algebraicFunctor := rfl

/-- Every arithmetic specialization of the continuous dual family is the actual contragredient. -/
theorem dual_arithmeticRepresentation (x : Spec (CommRingCat.of K) ⟶ S) :
    L.dual.arithmeticRepresentation x = (L.arithmeticRepresentation x).dual :=
  arithmeticFiberRepresentation_dualFiberFunctor K S R L.algebraicFunctor x

end EtaleLocalSystem
end AlgebraicGeometry.Scheme
