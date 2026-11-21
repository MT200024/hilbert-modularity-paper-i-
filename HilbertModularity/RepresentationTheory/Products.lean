/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.LinearAlgebra.Prod

/-! # Products of representations

Equivalences act componentwise on products. The corresponding group-algebra
module is the product module, so semisimplicity is preserved.
-/

@[expose] public noncomputable section

namespace Representation.Equiv

variable {K G V W V' W' : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
  {ρ : Representation K G V} {σ : Representation K G W}
  {ρ' : Representation K G V'} {σ' : Representation K G W'}

/-- Equivalences of two constituents induce an equivalence of their direct sum. -/
def prod (e : ρ.Equiv ρ') (f : σ.Equiv σ') : (ρ.prod σ).Equiv (ρ'.prod σ') :=
  .mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact e.toIntertwiningMap.isIntertwining ρ ρ' g x.1
    · exact f.toIntertwiningMap.isIntertwining σ σ' g x.2)

end Representation.Equiv

namespace Representation

open scoped MonoidAlgebra

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (ρ : Representation K G V) (σ : Representation K G W)

/-- The group-algebra module of a product representation is the product of the
corresponding group-algebra modules. -/
def prodAsModuleEquiv : (ρ.prod σ).asModule ≃ₗ[K[G]] (ρ.asModule × σ.asModule) where
  toAddEquiv := (ρ.prod σ).asModuleEquiv.toAddEquiv.trans
    (ρ.asModuleEquiv.symm.prodCongr σ.asModuleEquiv.symm).toAddEquiv
  map_smul' r x := by
    change (ρ.prod σ).asAlgebraHom r ((ρ.prod σ).asModuleEquiv x) =
      (ρ.asAlgebraHom r ((ρ.prod σ).asModuleEquiv x).1,
        σ.asAlgebraHom r ((ρ.prod σ).asModuleEquiv x).2)
    generalize (ρ.prod σ).asModuleEquiv x = y
    induction r using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero, map_zero, map_zero]; rfl
    | add a b ha hb =>
      simpa only [map_add, LinearMap.add_apply, Prod.mk_add_mk] using congrArg₂ (fun a b : V × W => a + b) ha hb
    | single g a =>
      simp only [asAlgebraHom_single, LinearMap.smul_apply]
      rfl

/-- A direct sum of two semisimple representations is semisimple. -/
theorem isSemisimple_prod [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    (ρ.prod σ).IsSemisimpleRepresentation := by
  let : IsSemisimpleModule K[G] ρ.asModule :=
    (ρ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mp inferInstance
  let : IsSemisimpleModule K[G] σ.asModule :=
    (σ.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mp inferInstance
  have hs := IsSemisimpleModule.sup
    (IsSemisimpleModule.range (LinearMap.inl K[G] ρ.asModule σ.asModule))
    (IsSemisimpleModule.range (LinearMap.inr K[G] ρ.asModule σ.asModule))
  rw [LinearMap.sup_range_inl_inr] at hs
  let := hs
  let : IsSemisimpleModule K[G] (ρ.asModule × σ.asModule) :=
    IsSemisimpleModule.congr Submodule.topEquiv.symm
  apply ((ρ.prod σ).isSemisimpleRepresentation_iff_isSemisimpleModule_asModule).mpr
  exact IsSemisimpleModule.congr (prodAsModuleEquiv ρ σ)

end Representation
