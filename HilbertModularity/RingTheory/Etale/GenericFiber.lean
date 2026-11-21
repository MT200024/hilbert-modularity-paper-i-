/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.Smooth.GenericFiber
public import Mathlib.RingTheory.Etale.Finite

/-! # Finite étale algebras and their generic fibres

Over an integrally closed domain, fraction-field base change on the actual
category of finite étale algebras is full and faithful. Every generic-fibre map
extends uniquely to the original finite étale algebras.
-/

@[expose] public section
open CategoryTheory
namespace CommAlgCat.FiniteEtale
universe u v w
variable (R : Type u) [CommRing R] [IsIntegrallyClosed R]
  (F : Type w) [Field F] [Algebra R F] [IsFractionRing R F]

/-- Every map of generic fibres extends to the original finite étale algebras. -/
instance baseChange_fractionField_full : Functor.Full (baseChange.{v} R F) where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ :=
      (Algebra.TensorProduct.genericFiber_map_bijective R Y F (T := X)).surjective f.hom.hom
    refine ⟨FiniteEtale.ofHom g, ?_⟩
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact hg

/-- A map of finite étale algebras is determined by its generic fibre. -/
instance baseChange_fractionField_faithful : Functor.Faithful (baseChange.{v} R F) where
  map_injective {X Y} f g h := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply (Algebra.TensorProduct.genericFiber_map_bijective R Y F (T := X)).injective
    exact congrArg (fun k : (baseChange.{v} R F).obj X ⟶ (baseChange.{v} R F).obj Y =>
      k.hom.hom) h

end CommAlgCat.FiniteEtale
