/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberPairs
public import HilbertModularity.Geometry.Etale.Clopen
public import HilbertModularity.Geometry.Etale.ConnectedHom

/-! # Injectivity of comparisons between geometric fibre functors

A pair of points lifts to a connected clopen subcover of the product.
If a natural comparison identifies the pair, the two projections agree at a
point on that connected cover, hence agree everywhere.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
  (K L : Type u) [Field K] [Field L]
  (x : Spec (CommRingCat.of K) ⟶ S) (y : Spec (CommRingCat.of L) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- Natural comparisons of actual geometric fibres are pointwise injective over
an affine locally Noetherian base. -/
theorem finiteArithmeticFiber_natTrans_injective
    (η : finiteArithmeticFiberFunctor K x ⟶ finiteArithmeticFiberFunctor L y)
    (X : S.FiniteEtale) : Function.Injective (η.app X) := by
  let F := finiteArithmeticFiberFunctor K x
  let G := finiteArithmeticFiberFunctor L y
  intro a b hab
  obtain ⟨Y, i, hY, _, z, hz⟩ := exists_connected_finiteEtale_subcover
    (finiteEtaleProduct X X) K x (finiteArithmeticFiberPair K x a b)
  have := hY
  let p : Y ⟶ X := i ≫ finiteEtaleProductFst X X
  let q : Y ⟶ X := i ≫ finiteEtaleProductSnd X X
  have hp : F.map p z = a := by
    dsimp only [p]
    rw [F.map_comp]
    change F.map (finiteEtaleProductFst X X) (F.map i z) = a
    rw [hz]
    exact finiteArithmeticFiberPair_fst K x a b
  have hq : F.map q z = b := by
    dsimp only [q]
    rw [F.map_comp]
    change F.map (finiteEtaleProductSnd X X) (F.map i z) = b
    rw [hz]
    exact finiteArithmeticFiberPair_snd K x a b
  have hp' : G.map p (η.app Y z) = η.app X a := by
    have h := ConcreteCategory.congr_hom (η.naturality p) z
    change η.app X (F.map p z) = G.map p (η.app Y z) at h
    exact h.symm.trans (congrArg (η.app X) hp)
  have hq' : G.map q (η.app Y z) = η.app X b := by
    have h := ConcreteCategory.congr_hom (η.naturality q) z
    change η.app X (F.map q z) = G.map q (η.app Y z) at h
    exact h.symm.trans (congrArg (η.app X) hq)
  have he : G.map p (η.app Y z) = G.map q (η.app Y z) := hp'.trans (hab.trans hq'.symm)
  have hpq : p.hom.left = q.hom.left :=
    Hom.eq_of_comp_point X.obj.hom p.hom.left q.hom.left
      ((MorphismProperty.Over.w p.hom).trans (MorphismProperty.Over.w q.hom).symm)
      (AlgebraicClosure L) (η.app Y z).left
      (congrArg (fun w : G.obj X => w.left) he)
  have hpq' : p = q := by
    apply ObjectProperty.hom_ext
    exact MorphismProperty.Over.Hom.ext hpq
  exact hp.symm.trans ((congrArg (fun f : Y ⟶ X => F.map f z) hpq').trans hq)

end AlgebraicGeometry.Scheme
