/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Cohomology.SchemeIso
public import HilbertModularity.CategoryTheory.SheafCohomology.Comparison

/-! # Functoriality of actual pro-étale cohomology

Canonical site comparisons identify the actual cohomological maps induced
by scheme isomorphisms. Their functoriality laws underlie the cohomological
Galois action.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The identity scheme isomorphism induces the identity on actual cohomology. -/
@[simp] theorem ellAdicCohomologyEquiv_refl (n : ℕ) (x : X.EllAdicCohomology ℓ n) :
    ellAdicCohomologyEquiv (Iso.refl X) ℓ n x = x := by
  let E := ProEt.mapEquivalence ((Iso.refl X).symm)
  let I : X.ProEt ≌ X.ProEt := CategoryTheory.Equivalence.refl
  let τ : E.inverse ≅ I.inverse := by
    set_option backward.isDefEq.respectTransparency.types false in
      exact MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X
  let F := (sheafCompose (ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).obj
    (X.ellAdicSheaf ℓ)
  let α := E.sheafCongrIso (ProEt.topology X) (ProEt.topology X) I τ AddCommGrpCat.{u + 1}
  have hi : α.hom.app F = (liftedEllAdicSheafIso (Iso.refl X) ℓ).hom := by
    ext U s
    rfl
  have h := E.sheafCongrCohomology_comp_iso (ProEt.topology X) (ProEt.topology X)
    I τ terminalIsTerminal terminalIsTerminal F n x
  have hi' := congrArg (fun g => Sheaf.H.map g n
    (E.sheafCongrCohomology (ProEt.topology X) (ProEt.topology X)
      terminalIsTerminal F n x)) hi
  have hr := CategoryTheory.Equivalence.sheafCongrCohomology_refl
    (ProEt.topology X) terminalIsTerminal F n x
  exact hi'.symm.trans (h.trans hr)

variable {X} {Y Z : Scheme.{u}}

/-- Actual cohomological pullback is contravariantly compatible with composition. -/
theorem ellAdicCohomologyEquiv_trans (f : X ≅ Y) (g : Y ≅ Z)
    (n : ℕ) (x : Z.EllAdicCohomology ℓ n) :
    ellAdicCohomologyEquiv (f ≪≫ g) ℓ n x =
      ellAdicCohomologyEquiv f ℓ n (ellAdicCohomologyEquiv g ℓ n x) := by
  let E_f := ProEt.mapEquivalence f.symm
  let E_g := ProEt.mapEquivalence g.symm
  let E_c := E_g.trans E_f
  let E_a := ProEt.mapEquivalence (f ≪≫ g).symm
  have : E_c.inverse.IsDenseSubsite (ProEt.topology X) (ProEt.topology Z) :=
    E_g.trans_inverse_isDenseSubsite (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X) E_f
  let τ : E_a.inverse ≅ E_c.inverse := by
    set_option backward.isDefEq.respectTransparency.types false in
      exact MorphismProperty.Over.mapComp (P := @WeaklyEtale) ⊤
        (show WeaklyEtale f.hom from inferInstance) (show WeaklyEtale g.hom from inferInstance)
  let F_Z := (sheafCompose (ProEt.topology Z) AddCommGrpCat.uliftFunctor.{u + 1}).obj
    (Z.ellAdicSheaf ℓ)
  let α := E_a.sheafCongrIso (ProEt.topology Z) (ProEt.topology X) E_c τ AddCommGrpCat.{u + 1}
  let i_f := liftedEllAdicSheafIso f ℓ
  let i_g := liftedEllAdicSheafIso g ℓ
  let b := (E_f.sheafCongr (ProEt.topology Y) (ProEt.topology X) AddCommGrpCat.{u + 1}).functor.map
    i_g.hom
  let u_g := E_g.sheafCongrCohomology (ProEt.topology Z) (ProEt.topology Y)
    terminalIsTerminal F_Z n x
  let u_a := E_a.sheafCongrCohomology (ProEt.topology Z) (ProEt.topology X)
    terminalIsTerminal F_Z n x
  let u_f := E_f.sheafCongrCohomology (ProEt.topology Y) (ProEt.topology X)
    terminalIsTerminal
      ((E_g.sheafCongr (ProEt.topology Z) (ProEt.topology Y) AddCommGrpCat.{u + 1}).functor.obj F_Z)
      n u_g
  have hc : α.hom.app F_Z ≫ (b ≫ i_f.hom) = (liftedEllAdicSheafIso (f ≪≫ g) ℓ).hom := by
    ext U s
    rfl
  have hp := E_a.sheafCongrCohomology_comp_iso (ProEt.topology Z) (ProEt.topology X)
    E_c τ terminalIsTerminal terminalIsTerminal F_Z n x
  have ht := E_g.sheafCongrCohomology_trans (ProEt.topology Z) (ProEt.topology Y)
    (ProEt.topology X) E_f terminalIsTerminal terminalIsTerminal F_Z n x
  have hn := E_f.sheafCongrCohomology_natural (ProEt.topology Y) (ProEt.topology X)
    terminalIsTerminal i_g.hom n u_g
  have hc' := congrArg (fun a => Sheaf.H.map a n u_a) hc
  exact hc'.symm.trans
    ((Sheaf.H.map_comp_apply (α.hom.app F_Z) (b ≫ i_f.hom) u_a).trans
      ((congrArg (Sheaf.H.map (b ≫ i_f.hom) n) hp).trans
        ((congrArg (Sheaf.H.map (b ≫ i_f.hom) n) ht).trans
          ((Sheaf.H.map_comp_apply b i_f.hom u_f).trans
            (congrArg (Sheaf.H.map i_f.hom n) hn.symm)))))

end AlgebraicGeometry.Scheme
