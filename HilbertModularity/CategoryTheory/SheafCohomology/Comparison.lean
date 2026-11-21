/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.SheafCohomology.Coherence

/-! # Comparison of naturally isomorphic site transports

Naturally isomorphic inverse-image site functors yield canonically isomorphic
transported sheaves. The comparison preserves constant sections, as needed
to compare their induced cohomological maps.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Abelian

universe u v u' v' w t t'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (e e' : C ≌ D) [e.inverse.IsDenseSubsite K J] [e'.inverse.IsDenseSubsite K J]
  (τ : e.inverse ≅ e'.inverse) (A : Type*) [Category* A]

/-- A natural isomorphism of inverse site functors induces a canonical
comparison between the transported sheaves. -/
def Equivalence.sheafCongrIso :
    (e.sheafCongr J K A).functor ≅ (e'.sheafCongr J K A).functor :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op τ).symm F.obj))
    (by
      intro F G φ
      ext U
      exact (φ.hom.naturality (τ.inv.app U.unop).op).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison preserves the canonical transported constant sections. -/
theorem Equivalence.sheafCongrConstant_inv_comp_iso
    [HasWeakSheafify J A] [HasWeakSheafify K A] {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') (M : A) :
    (e.sheafCongrConstant J K A hT).inv.app M ≫
        (e.sheafCongrIso J K e' τ A).hom.app ((constantSheaf J A).obj M) =
      (e'.sheafCongrConstant J K A hT').inv.app M := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext K _ _
    ((e'.sheafCongr J K A).functor.obj ((constantSheaf J A).obj M)).property
  ext U
  change (toSheafify K ((Functor.const Dᵒᵖ).obj M)).app U ≫
      (((e.sheafCongrConstant J K A hT).inv.app M).hom.app U ≫
        ((constantSheaf J A).obj M).obj.map (τ.inv.app U.unop).op) =
    (toSheafify K ((Functor.const Dᵒᵖ).obj M)).app U ≫
      ((e'.sheafCongrConstant J K A hT').inv.app M).hom.app U
  refine Eq.trans ?_ (e'.sheafCongrConstant_inv_toSheafify J A K hT' M U).symm
  calc
    _ = ((toSheafify K ((Functor.const Dᵒᵖ).obj M)).app U ≫
        ((e.sheafCongrConstant J K A hT).inv.app M).hom.app U) ≫
          ((constantSheaf J A).obj M).obj.map (τ.inv.app U.unop).op :=
      (Category.assoc _ _ _).symm
    _ = (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (e.inverse.op.obj U) ≫
        ((constantSheaf J A).obj M).obj.map (τ.inv.app U.unop).op :=
      congrArg (fun a => a ≫ ((constantSheaf J A).obj M).obj.map (τ.inv.app U.unop).op)
        (e.sheafCongrConstant_inv_toSheafify J A K hT M U)
    _ = (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (e'.inverse.op.obj U) :=
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality (τ.inv.app U.unop).op).symm.trans
        (Category.id_comp _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturally isomorphic inverse site functors induce the same cohomology
transport after the canonical comparison of the transported coefficient sheaves. -/
theorem Equivalence.sheafCongrCohomology_comp_iso
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [HasExt.{t} (Sheaf J AddCommGrpCat.{w})] [HasExt.{t'} (Sheaf K AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    Sheaf.H.map ((e.sheafCongrIso J K e' τ AddCommGrpCat.{w}).hom.app F) n
        (e.sheafCongrCohomology J K hT F n x) =
      e'.sheafCongrCohomology J K hT' F n x := by
  rw [Sheaf.H.map_apply,
    Equivalence.sheafCongrCohomology_apply J K e hT F n x,
    Equivalence.sheafCongrCohomology_apply J K e' hT' F n x]
  simp only [Iso.app_inv]
  rw [Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp x
      (e.sheafCongrIso J K e' τ AddCommGrpCat.{w}).hom,
    Ext.mk₀_comp_mk₀_assoc,
    e.sheafCongrConstant_inv_comp_iso J K e' τ AddCommGrpCat.{w} hT hT']

end CategoryTheory
