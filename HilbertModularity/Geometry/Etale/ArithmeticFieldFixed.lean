/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticField

/-! # Triviality of arithmetic fibre action after fixing algebraic constants

The actual comparison of geometric fibres over an extension field shows that
an automorphism fixing the embedded original algebraic closure acts trivially
on every finite étale fibre from the original point.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable (E K : Type u) [Field E] [Field K] [Algebra E K]
  {S : Scheme.{u}} (x : Spec (CommRingCat.of E) ⟶ S)
  (j : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)

/-- Fixing the original algebraic closure annihilates the finite étale action
on a point obtained by extension of its residue field. -/
theorem galoisToEtaleFundamentalGroup_eq_one_of_fixes_constants
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hg : ∀ z : AlgebraicClosure E, g (j z) = j z) :
    galoisToEtaleFundamentalGroup K (Spec.algebraMap E K ≫ x) g = 1 := by
  let e := arithmeticFiberFieldIso E K x j
  apply Iso.ext
  apply (cancel_epi e.hom).mp
  change e.hom ≫ (galoisToEtaleFundamentalGroup K (Spec.algebraMap E K ≫ x) g).hom = e.hom ≫ 𝟙 _
  rw [Category.comp_id]
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro v
  apply Over.OverMorphism.ext
  have hj : CommRingCat.ofHom j.toRingHom ≫ CommRingCat.ofHom g.toRingHom =
      CommRingCat.ofHom j.toRingHom := by
    ext z
    exact hg z
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e.hom.app Y v).left = (e.hom.app Y v).left
  rw [arithmeticFiberFieldIso_hom_app_left, ← Category.assoc, ← Spec.map_comp, hj]

end AlgebraicGeometry.Scheme
