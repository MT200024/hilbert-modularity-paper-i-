/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.SheafCohomology.ConstantSheaf

/-! # Coherence of cohomological transport

The constant-sheaf comparisons in cohomological transport must respect
identities and composition before site automorphisms define an action.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open Limits Abelian

universe u v u' v' u'' v'' w t t' t''
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The identity equivalence exhibits a site as a dense subsite of itself. -/
instance Equivalence.refl_inverse_isDenseSubsite :
    (Equivalence.refl (C := C)).inverse.IsDenseSubsite J J := by
  change (𝟭 C).IsDenseSubsite J J
  exact { functorPushforward_mem_iff := by simp }

/-- The identity site equivalence acts by the identity functor on sheaves. -/
@[simp] theorem Equivalence.sheafCongr_refl_functor (A : Type*) [Category* A] :
    ((Equivalence.refl (C := C)).sheafCongr J J A).functor = 𝟭 (Sheaf J A) := rfl

/-- Constant-sheaf transport along the identity site equivalence is the identity. -/
@[simp] theorem Equivalence.sheafCongrConstant_refl_hom_app (A : Type*) [Category* A]
    [HasWeakSheafify J A] {T : C} (hT : IsTerminal T) (M : A) :
    ((Equivalence.refl (C := C)).sheafCongrConstant J J A hT).hom.app M = 𝟙 _ := by
  have h : (constantSheafAdj J A hT).comp
      ((Equivalence.refl (C := C)).sheafCongr J J A).toAdjunction = constantSheafAdj J A hT := by
    apply Adjunction.ext
    ext N
    simp [Adjunction.comp_unit_app, Equivalence.unit, Equivalence.sheafCongr,
      Equivalence.sheafCongr.unitIso, Equivalence.op, Equivalence.refl,
      NatIso.ofComponents, ObjectProperty.isoMk, ObjectProperty.homMk,
      Functor.isoWhiskerRight, Functor.whiskerRight]
    exact Category.comp_id ((constantSheafAdj J A hT).unit.app N)
  simp only [Equivalence.sheafCongrConstant, h]
  have ht : hT.isTerminalObj (Equivalence.refl (C := C)).functor T = hT := Subsingleton.elim _ _
  rw [ht]
  exact congrArg (fun f => f.app M) (Adjunction.leftAdjointUniq_refl (constantSheafAdj J A hT))

/-- The inverse constant-sheaf comparison for the identity is also the identity. -/
@[simp] theorem Equivalence.sheafCongrConstant_refl_inv_app (A : Type*) [Category* A]
    [HasWeakSheafify J A] {T : C} (hT : IsTerminal T) (M : A) :
    ((Equivalence.refl (C := C)).sheafCongrConstant J J A hT).inv.app M = 𝟙 _ := by
  simpa using ((Equivalence.refl (C := C)).sheafCongrConstant J J A hT).inv_hom_id_app M

/-- The identity site equivalence induces the identity on actual cohomology. -/
@[simp] theorem Equivalence.sheafCongrCohomology_refl
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{t} (Sheaf J AddCommGrpCat.{w})]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    (Equivalence.refl (C := C)).sheafCongrCohomology J J hT F n x = x := by
  rw [Equivalence.sheafCongrCohomology_apply J J (Equivalence.refl (C := C)) hT F n x]
  have hi := Equivalence.sheafCongrConstant_refl_inv_app J AddCommGrpCat.{w} hT
    (AddCommGrpCat.of (ULift.{w} ℤ))
  change (Ext.mk₀ (((Equivalence.refl (C := C)).sheafCongrConstant J J
    AddCommGrpCat.{w} hT).inv.app (AddCommGrpCat.of (ULift.{w} ℤ)))).comp
      (x.mapExactFunctor (𝟭 (Sheaf J AddCommGrpCat.{w}))) (zero_add n) = x
  rw [hi]
  simp

variable {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D)
  (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{t} (Sheaf J AddCommGrpCat.{w})] [HasExt.{t'} (Sheaf K AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual cohomology transport does not depend on the terminal object used
to construct the constant-sheaf comparison. -/
theorem Equivalence.sheafCongrCohomology_congr_terminal {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    e.sheafCongrCohomology J K hT F n x = e.sheafCongrCohomology J K hT' F n x := by
  rw [Equivalence.sheafCongrCohomology_apply J K e hT F n x,
    Equivalence.sheafCongrCohomology_apply J K e hT' F n x]
  exact congrArg (fun a => (Ext.mk₀ a).comp
    (x.mapExactFunctor (e.sheafCongr J K AddCommGrpCat.{w}).functor) (zero_add n))
      (e.sheafCongrConstant_inv_eq J AddCommGrpCat.{w} K hT hT'
        (AddCommGrpCat.of (ULift.{w} ℤ)))

variable {E : Type u''} [Category.{v''} E] (L : GrothendieckTopology E)
  (f : D ≌ E) [f.inverse.IsDenseSubsite L K]
  [HasSheafify L AddCommGrpCat.{w}] [HasExt.{t''} (Sheaf L AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual cohomology transport preserves composition of site equivalences. -/
theorem Equivalence.sheafCongrCohomology_trans {T : C} {T' : D}
    (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (x : F.H n) :
    letI := e.trans_inverse_isDenseSubsite J K L f
    (e.trans f).sheafCongrCohomology J L hT F n x =
      f.sheafCongrCohomology K L hT' ((e.sheafCongr J K AddCommGrpCat.{w}).functor.obj F) n
        (e.sheafCongrCohomology J K hT F n x) := by
  have := e.trans_inverse_isDenseSubsite J K L f
  rw [Equivalence.sheafCongrCohomology_apply J L (e.trans f) hT F n x,
    Equivalence.sheafCongrCohomology_apply K L f hT',
    Equivalence.sheafCongrCohomology_apply J K e hT F n x]
  simp only [Iso.app_inv, Equivalence.sheafCongr_trans_functor J AddCommGrpCat.{w} K e L f,
    Equivalence.sheafCongrConstant_trans_inv_app J AddCommGrpCat.{w} K e L f hT hT',
    Ext.comp_mapExactFunctor, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory
