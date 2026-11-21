/- Assembled by AxiomProver. -/

module

public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.CategoryTheory.Conj

/-! # Continuous natural actions on finite-set-valued functors

A continuous action on each finite fibre gives a continuous homomorphism to
its natural automorphism group, without additional Galois-category axioms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped CategoryTheory.PreGaloisCategory

namespace CategoryTheory.PreGaloisCategory

universe u v w
variable {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})
  (G : Type*) [Group G] [TopologicalSpace G]
  [∀ X, MulAction G (F.obj X)] [IsNaturalSMul F G]
  [∀ X, ContinuousSMul G (F.obj X)]

/-- Fibrewise continuous natural actions induce a continuous homomorphism into
natural automorphisms. No exactness or connectedness assumption on the functor is needed. -/
theorem continuous_toAut_of_continuous_fibers : Continuous (toAut F G) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding F).isInducing,
    continuous_pi_iff]
  intro X
  let e : Aut (F.obj X) → (F.obj X → F.obj X) := fun a => a.hom
  have he : Function.Injective e := by
    intro a b h
    apply Iso.ext
    apply FintypeCat.hom_ext
    exact congrFun h
  have hc : Topology.IsClosedEmbedding e :=
    (continuous_of_discreteTopology : Continuous e).isClosedEmbedding he
  rw [hc.isInducing.continuous_iff, continuous_pi_iff]
  intro y
  change Continuous (fun g : G => g • y)
  exact continuous_id.smul continuous_const

variable {D : Type*} [Category* D]

/-- Restriction along a functor is continuous on natural automorphism groups. -/
theorem continuous_mapAut_whiskeringLeft (H : D ⥤ C) :
    Continuous (((whiskeringLeft D C FintypeCat).obj H).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro X
  change Continuous (fun a : Aut F => autEmbedding F a (H.obj X))
  exact (continuous_apply (H.obj X)).comp continuous_induced_dom

variable {F} in
/-- A natural fibre equivalence gives a continuous conjugation of automorphism groups. -/
theorem continuous_conjAut {F' : C ⥤ FintypeCat.{w}} (e : F ≅ F') :
    Continuous e.conjAut := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding F').isInducing,
    continuous_pi_iff]
  intro X
  change Continuous (fun a : Aut F => (e.app X).conjAut (autEmbedding F a X))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply X).comp continuous_induced_dom)

/-- Natural automorphisms are determined on an essentially surjective family of objects. -/
theorem mapAut_whiskeringLeft_injective (H : D ⥤ C) [H.EssSurj] :
    Function.Injective (((whiskeringLeft D C FintypeCat).obj H).mapAut F) := by
  intro a b h
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage H Y
  have he : a.hom.app (H.obj X) = b.hom.app (H.obj X) :=
    congrArg (fun t : Aut (H ⋙ F) => t.hom.app X) h
  apply (cancel_epi (F.map e.hom)).mp
  rw [a.hom.naturality, b.hom.naturality, he]

end CategoryTheory.PreGaloisCategory
