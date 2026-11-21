/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.SheafCohomology.Equivalence
public import HilbertModularity.Geometry.Etale.Proetale
public import HilbertModularity.Geometry.Etale.Cohomology.Coefficients
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scheme isomorphisms on actual pro-étale cohomology

The equivalence of pro-étale sites induces an equivalence on mathlib's
Ext-defined cohomology, using the actual continuous-function coefficient
sheaf. This is the isomorphism-invariance construction underlying the
cohomological action in [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u
variable {X Y : Scheme.{u}} (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Isomorphism pullback preserves the universe-lifted coefficient sheaf used
by the actual cohomology definition. -/
def liftedEllAdicSheafIso :
    (ProEt.sheafEquivalence e AddCommGrpCat.{u + 1}).functor.obj
        ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (Y.ellAdicSheaf ℓ)) ≅
      (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Contravariant isomorphism invariance of the actual pro-étale cohomology groups. -/
def ellAdicCohomologyEquiv (n : ℕ) :
    Y.EllAdicCohomology ℓ n ≃+ X.EllAdicCohomology ℓ n := by
  let i := liftedEllAdicSheafIso e ℓ
  refine ((ProEt.mapEquivalence e.symm).sheafCongrCohomology
    (ProEt.topology Y) (ProEt.topology X) terminalIsTerminal
      ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (Y.ellAdicSheaf ℓ)) n).trans
    { toFun := Sheaf.H.map i.hom n
      invFun := Sheaf.H.map i.inv n
      left_inv := ?_
      right_inv := ?_
      map_add' := (Sheaf.H.map i.hom n).map_add }
  · intro x
    rw [← Sheaf.H.map_comp_apply i.hom i.inv x, i.hom_inv_id]
    exact Sheaf.H.map_id_apply x
  · intro x
    rw [← Sheaf.H.map_comp_apply i.inv i.hom x, i.inv_hom_id]
    exact Sheaf.H.map_id_apply x

/-- Isomorphism transport commutes with the natural integral p-adic coefficients. -/
theorem ellAdicCohomologyEquiv_smul (n : ℕ) (a : ℤ_[ℓ])
    (x : Y.EllAdicCohomology ℓ n) :
    ellAdicCohomologyEquiv e ℓ n (a • x) = a • ellAdicCohomologyEquiv e ℓ n x := by
  let i := liftedEllAdicSheafIso e ℓ
  let F := (ProEt.sheafEquivalence e AddCommGrpCat.{u + 1}).functor
  let gY := (sheafCompose (ProEt.topology Y) AddCommGrpCat.uliftFunctor.{u + 1}).map
    (ellAdicSheafScalar Y ℓ a)
  let gX := (sheafCompose (ProEt.topology X) AddCommGrpCat.uliftFunctor.{u + 1}).map
    (ellAdicSheafScalar X ℓ a)
  let Φ := (ProEt.mapEquivalence e.symm).sheafCongrCohomology
    (ProEt.topology Y) (ProEt.topology X) terminalIsTerminal
      ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (Y.ellAdicSheaf ℓ)) n
  have hn : Φ (Sheaf.H.map gY n x) = Sheaf.H.map (F.map gY) n (Φ x) :=
    (ProEt.mapEquivalence e.symm).sheafCongrCohomology_natural
      (ProEt.topology Y) (ProEt.topology X) terminalIsTerminal gY n x
  have hc : F.map gY ≫ i.hom = i.hom ≫ gX := by
    ext U s
    rfl
  change Sheaf.H.map i.hom n (Φ (Sheaf.H.map gY n x)) =
    Sheaf.H.map gX n (Sheaf.H.map i.hom n (Φ x))
  rw [hn, ← Sheaf.H.map_comp_apply (F.map gY) i.hom (Φ x),
    ← Sheaf.H.map_comp_apply i.hom gX (Φ x), hc]

/-- The actual cohomological transport is linear over the integral coefficient ring. -/
def ellAdicCohomologyLinearEquiv (n : ℕ) :
    Y.EllAdicCohomology ℓ n ≃ₗ[ℤ_[ℓ]] X.EllAdicCohomology ℓ n :=
  { ellAdicCohomologyEquiv e ℓ n with
    map_smul' := ellAdicCohomologyEquiv_smul e ℓ n }

/-- Scheme isomorphisms induce rational p-adic linear equivalences on actual cohomology. -/
def rationalEllAdicCohomologyEquiv (n : ℕ) :
    Y.RationalEllAdicCohomology ℓ n ≃ₗ[ℚ_[ℓ]] X.RationalEllAdicCohomology ℓ n :=
  (ellAdicCohomologyLinearEquiv e ℓ n).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _

/-- Rational transport acts on the integral cohomology factor of each pure tensor. -/
@[simp] theorem rationalEllAdicCohomologyEquiv_tmul (n : ℕ) (a : ℚ_[ℓ])
    (x : Y.EllAdicCohomology ℓ n) :
    rationalEllAdicCohomologyEquiv e ℓ n (a ⊗ₜ[ℤ_[ℓ]] x) =
      a ⊗ₜ[ℤ_[ℓ]] ellAdicCohomologyEquiv e ℓ n x := rfl

end AlgebraicGeometry.Scheme
