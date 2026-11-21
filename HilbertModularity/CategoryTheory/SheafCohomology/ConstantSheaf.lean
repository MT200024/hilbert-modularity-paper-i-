/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.SheafCohomology.Equivalence

/-! # Canonical transport of constant sheaves

The constant-sheaf comparison used in cohomological transport is characterized
by its effect on the presheaf of constant sections. This characterization
removes dependence on a chosen terminal object when proving coherence.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Opposite

universe u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type*) [Category* A] [HasWeakSheafify J A]

/-- A map from the constant sheaf, constructed from a global section, sends a
constant section to its restriction along the unique map to the terminal object. -/
theorem constantSheafAdj_homEquiv_symm_toSheafify {T : C} (hT : IsTerminal T)
    (M : A) (F : Sheaf J A) (a : M ⟶ F.obj.obj (op T)) (U : Cᵒᵖ) :
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app U ≫
        (((constantSheafAdj J A hT).homEquiv M F).symm a).hom.app U =
      a ≫ F.obj.map (hT.from U.unop).op := by
  rw [constantSheafAdj]
  have h := congrFun (congrFun (Adjunction.comp_homEquiv (constantPresheafAdj A hT)
    (sheafificationAdjunction J A)) M) F
  erw [h]
  let b := ((constantPresheafAdj A hT).homEquiv M F.obj).symm a
  exact NatTrans.congr_app (toSheafify_sheafifyLift J b F.property) U

variable {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D)
  [HasWeakSheafify K A] (e : C ≌ D) [e.inverse.IsDenseSubsite K J]

/-- The canonical constant-sheaf comparison transports each constant section
to the same section on the inverse-image object. -/
theorem Equivalence.sheafCongrConstant_inv_toSheafify {T : C} (hT : IsTerminal T)
    (M : A) (U : Dᵒᵖ) :
    (toSheafify K ((Functor.const Dᵒᵖ).obj M)).app U ≫
        ((e.sheafCongrConstant J K A hT).inv.app M).hom.app U =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (e.inverse.op.obj U) := by
  let hT' := hT.isTerminalObj e.functor T
  let adj := (constantSheafAdj J A hT).comp (e.sheafCongr J K A).toAdjunction
  let F := (e.sheafCongr J K A).functor.obj ((constantSheaf J A).obj M)
  have hc : (e.sheafCongrConstant J K A hT).inv.app M =
      ((constantSheafAdj K A hT').homEquiv M F).symm (adj.unit.app M) := by
    apply ((constantSheafAdj K A hT').homEquiv M F).injective
    erw [Equiv.apply_symm_apply]
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app (constantSheafAdj K A hT') adj M
  rw [hc]
  erw [constantSheafAdj_homEquiv_symm_toSheafify K A hT' M F (adj.unit.app M) U]
  dsimp only [adj]
  erw [Adjunction.comp_unit_app, constantSheafAdj, Adjunction.comp_unit_app]
  dsimp [F, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.sheafCongr, Equivalence.sheafCongr.unitIso, Equivalence.sheafCongr.functor,
    Equivalence.op, Functor.isoWhiskerRight, ObjectProperty.isoMk, ObjectProperty.homMk,
    constantPresheafAdj]
  change ((𝟙 M ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (Opposite.op T)) ≫
      ((constantSheaf J A).obj M).obj.map (e.unitInv.app T).op) ≫
        ((constantSheaf J A).obj M).obj.map (e.inverse.map (hT'.from U.unop)).op = _
  erw [Category.id_comp, Category.assoc, ← Functor.map_comp, ← op_comp]
  have hm : e.inverse.map (hT'.from U.unop) ≫ e.unitInv.app T =
      hT.from (e.inverse.obj U.unop) := hT.hom_ext _ _
  rw [hm]
  exact ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality
    (hT.from (e.inverse.obj U.unop)).op).symm.trans (Category.id_comp _)

/-- Constant-sheaf transport is independent of the terminal object used to
construct its adjunction. -/
theorem Equivalence.sheafCongrConstant_inv_eq {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') (M : A) :
    (e.sheafCongrConstant J K A hT).inv.app M =
      (e.sheafCongrConstant J K A hT').inv.app M := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext K _ _
    ((e.sheafCongr J K A).functor.obj ((constantSheaf J A).obj M)).property
  ext U
  exact (e.sheafCongrConstant_inv_toSheafify J A K hT M U).trans
    (e.sheafCongrConstant_inv_toSheafify J A K hT' M U).symm

variable {E : Type u''} [Category.{v''} E] (L : GrothendieckTopology E)
  [HasWeakSheafify L A] (f : D ≌ E) [f.inverse.IsDenseSubsite L K]

include K in
/-- A composite of site equivalences again transports the same topologies. -/
theorem Equivalence.trans_inverse_isDenseSubsite :
    (e.trans f).inverse.IsDenseSubsite L J where
  functorPushforward_mem_iff := by
    intro X S
    change S.functorPushforward (f.inverse ⋙ e.inverse) ∈ J _ ↔ S ∈ L _
    erw [Sieve.functorPushforward_comp,
      e.inverse.functorPushforward_mem_iff K J, f.inverse.functorPushforward_mem_iff L K]

omit [HasWeakSheafify J A] [HasWeakSheafify K A] [HasWeakSheafify L A] in
/-- The sheaf transport functor preserves composition of site equivalences. -/
theorem Equivalence.sheafCongr_trans_functor :
    letI := e.trans_inverse_isDenseSubsite J K L f
    ((e.trans f).sheafCongr J L A).functor =
      (e.sheafCongr J K A).functor ⋙ (f.sheafCongr K L A).functor := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Constant-sheaf transport respects composition, independently of the two
terminal objects used in its construction. -/
theorem Equivalence.sheafCongrConstant_trans_inv_app {T : C} {T' : D}
    (hT : IsTerminal T) (hT' : IsTerminal T') (M : A) :
    letI := e.trans_inverse_isDenseSubsite J K L f
    ((e.trans f).sheafCongrConstant J L A hT).inv.app M =
      (f.sheafCongrConstant K L A hT').inv.app M ≫
        (f.sheafCongr K L A).functor.map ((e.sheafCongrConstant J K A hT).inv.app M) := by
  have := e.trans_inverse_isDenseSubsite J K L f
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext L _ _
    (((e.trans f).sheafCongr J L A).functor.obj ((constantSheaf J A).obj M)).property
  ext U
  change (toSheafify L ((Functor.const Eᵒᵖ).obj M)).app U ≫
      (((e.trans f).sheafCongrConstant J L A hT).inv.app M).hom.app U =
    (toSheafify L ((Functor.const Eᵒᵖ).obj M)).app U ≫
      (((f.sheafCongrConstant K L A hT').inv.app M).hom.app U ≫
        ((e.sheafCongrConstant J K A hT).inv.app M).hom.app (f.inverse.op.obj U))
  calc
    _ = (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app
        (e.inverse.op.obj (f.inverse.op.obj U)) :=
      (e.trans f).sheafCongrConstant_inv_toSheafify J A L hT M U
    _ = ((toSheafify L ((Functor.const Eᵒᵖ).obj M)).app U ≫
        ((f.sheafCongrConstant K L A hT').inv.app M).hom.app U) ≫
          ((e.sheafCongrConstant J K A hT).inv.app M).hom.app (f.inverse.op.obj U) := by
      exact ((congrArg (fun a => a ≫
        ((e.sheafCongrConstant J K A hT).inv.app M).hom.app (f.inverse.op.obj U))
          (f.sheafCongrConstant_inv_toSheafify K A L hT' M U)).trans
        (e.sheafCongrConstant_inv_toSheafify J A K hT M (f.inverse.op.obj U))).symm
    _ = _ := Category.assoc _ _ _

end CategoryTheory
