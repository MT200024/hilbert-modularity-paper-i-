/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.Duality
public import HilbertModularity.Algebra.Category.ModuleCat.ScalarExtension
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Natural compatibility of duality with coefficient extension

The canonical finite-free dual base-change equivalence is natural for module
maps, hence for inverse-path transport in a cohomological family. This retains
the chosen realization when enlarging its coefficient field, as in
[TripathiGoswami, cohomological RM factor].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat
universe u
variable (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Extending a finite free dual module is canonically the dual of its scalar extension. -/
def dualScalarExtensionIso (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    (extendScalars (algebraMap R S)).obj (ModuleCat.of R (Module.Dual R M)) ≅
      ModuleCat.of S (Module.Dual S ((extendScalars (algebraMap R S)).obj M)) := by
  let ibc : IsBaseChange S (TensorProduct.mk R S M 1) :=
    IsBaseChange.of_equiv (LinearEquiv.refl S (S ⊗[R] M)) (fun _ => rfl)
  exact ((extendScalarsTensorIso R S (ModuleCat.of R (Module.Dual R M))).toLinearEquiv.trans
    (ibc.toDualBaseChange.trans (extendScalarsTensorIso R S M).toLinearEquiv.dualMap)).toModuleIso

/-- The canonical comparison extends the original evaluation pairing. -/
@[simp] theorem dualScalarExtensionIso_tmul (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] (a : S) (φ : Module.Dual R M) (v : M) :
    (dualScalarExtensionIso R S M).hom.hom (a ⊗ₜ[R, algebraMap R S] φ)
      ((1 : S) ⊗ₜ[R, algebraMap R S] v) = a * algebraMap R S (φ v) := by
  let ibc : IsBaseChange S (TensorProduct.mk R S M 1) :=
    IsBaseChange.of_equiv (LinearEquiv.refl S (S ⊗[R] M)) (fun _ => rfl)
  change ibc.toDualBaseChange
    ((extendScalarsTensorIso R S (ModuleCat.of R (Module.Dual R M))).hom
      (a ⊗ₜ[R, algebraMap R S] φ))
    ((extendScalarsTensorIso R S M).hom ((1 : S) ⊗ₜ[R, algebraMap R S] v)) = _
  rw [extendScalarsTensorIso_tmul, extendScalarsTensorIso_tmul]
  exact ibc.toDualBaseChange_tmul a φ v

/-- The dual base-change comparison commutes with transposing every original module map. -/
@[reassoc] theorem dualScalarExtensionIso_naturality {M N : ModuleCat.{u} R}
    [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]
    (f : M ⟶ N) :
    (extendScalars (algebraMap R S)).map (ModuleCat.ofHom f.hom.dualMap) ≫
        (dualScalarExtensionIso R S M).hom =
      (dualScalarExtensionIso R S N).hom ≫
        ModuleCat.ofHom ((extendScalars (algebraMap R S)).map f).hom.dualMap := by
  apply ExtendScalars.hom_ext
  intro φ
  change Module.Dual R N at φ
  suffices h : ModuleCat.ofHom (R := S)
      (((extendScalars (algebraMap R S)).map (ModuleCat.ofHom f.hom.dualMap) ≫
        (dualScalarExtensionIso R S M).hom).hom ((1 : S) ⊗ₜ[R, algebraMap R S] φ)) =
      ModuleCat.ofHom (R := S)
      (((dualScalarExtensionIso R S N).hom ≫
        ModuleCat.ofHom ((extendScalars (algebraMap R S)).map f).hom.dualMap).hom
          ((1 : S) ⊗ₜ[R, algebraMap R S] φ)) by
    exact congrArg ModuleCat.Hom.hom h
  apply ExtendScalars.hom_ext
  intro v
  change (dualScalarExtensionIso R S M).hom.hom
      (((extendScalars (algebraMap R S)).map (ModuleCat.ofHom f.hom.dualMap))
        ((1 : S) ⊗ₜ[R, algebraMap R S] φ)) ((1 : S) ⊗ₜ[R, algebraMap R S] v) =
    (dualScalarExtensionIso R S N).hom.hom ((1 : S) ⊗ₜ[R, algebraMap R S] φ)
      (((extendScalars (algebraMap R S)).map f) ((1 : S) ⊗ₜ[R, algebraMap R S] v))
  rw [ExtendScalars.map_tmul (algebraMap R S) (ModuleCat.ofHom (R := R) f.hom.dualMap) 1 φ,
    ExtendScalars.map_tmul]
  change (dualScalarExtensionIso R S M).hom.hom
      ((1 : S) ⊗ₜ[R, algebraMap R S] (f.hom.dualMap φ))
      ((1 : S) ⊗ₜ[R, algebraMap R S] v) =
    (dualScalarExtensionIso R S N).hom.hom ((1 : S) ⊗ₜ[R, algebraMap R S] φ)
      ((1 : S) ⊗ₜ[R, algebraMap R S] f.hom v)
  rw [dualScalarExtensionIso_tmul, dualScalarExtensionIso_tmul]
  rfl

universe v w
variable {C : Type v} [Groupoid.{w} C]

/-- Extending coefficients commutes naturally with the cohomological dual of a finite free family. -/
def cohDualScalarExtensionIso (F : C ⥤ ModuleCat.{u} R)
    [∀ x, Module.Free R (F.obj x)] [∀ x, Module.Finite R (F.obj x)] :
    cohDual R F ⋙ extendScalars (algebraMap R S) ≅
      cohDual S (F ⋙ extendScalars (algebraMap R S)) :=
  NatIso.ofComponents (fun x => dualScalarExtensionIso R S (F.obj x)) (by
    intro x y f
    have hR : (cohDual R F).map f = ModuleCat.ofHom (F.map (inv f)).hom.dualMap :=
      ModuleCat.hom_ext (cohDual_map_hom R F f)
    have hS : (cohDual S (F ⋙ extendScalars (algebraMap R S))).map f =
        ModuleCat.ofHom (((F ⋙ extendScalars (algebraMap R S)).map (inv f)).hom.dualMap) :=
      ModuleCat.hom_ext (cohDual_map_hom S (F ⋙ extendScalars (algebraMap R S)) f)
    simp only [Functor.comp_map, hR, hS]
    exact dualScalarExtensionIso_naturality R S (F.map (inv f)))

/-- The natural comparison also commutes with transposing a natural family map. -/
@[reassoc] theorem cohDualScalarExtensionIso_naturality
    {F G : C ⥤ ModuleCat.{u} R}
    [∀ x, Module.Free R (F.obj x)] [∀ x, Module.Finite R (F.obj x)]
    [∀ x, Module.Free R (G.obj x)] [∀ x, Module.Finite R (G.obj x)] (η : F ⟶ G) :
    Functor.whiskerRight (cohDualMap R η) (extendScalars (algebraMap R S)) ≫
        (cohDualScalarExtensionIso R S F).hom =
      (cohDualScalarExtensionIso R S G).hom ≫
        cohDualMap S (Functor.whiskerRight η (extendScalars (algebraMap R S))) := by
  apply NatTrans.ext
  funext x
  exact dualScalarExtensionIso_naturality R S (η.app x)

end ModuleCat
