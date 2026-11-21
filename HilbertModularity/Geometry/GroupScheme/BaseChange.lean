/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Fiber

/-! # Composed base changes of group schemes

The fibre of a pulled-back family is canonically isomorphic to the original
family at the composed parameter. The isomorphism respects the group structure,
and therefore induces actual equivalences of Galois representations on Tate modules.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.GroupScheme

universe u
variable (K : Type u) [Field K] {S T : Scheme.{u}} (A : CommGrp (Over T))
  (f : S ⟶ T) (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The fibre of a pulled-back family is the original fibre at the composed point. -/
def fiberBaseChangeIso :
    fiber K ((Over.pullback f).mapCommGrp.obj A) x ≅ fiber K A (x ≫ f) :=
  (Functor.mapCommGrpCompIso (F := Over.pullback f) (G := Over.pullback x)).symm.app A ≪≫
    (Functor.mapCommGrpNatIso (Over.pullbackComp x f)).symm.app A

variable (p : ℕ) [Fact p.Prime]

/-- Composed base change gives an equivalence of actual integral Tate representations. -/
def fiberBaseChangeIntegralTateEquiv :
    (integralTateRepresentation K (fiber K ((Over.pullback f).mapCommGrp.obj A) x).X p).Equiv
      (integralTateRepresentation K (fiber K A (x ≫ f)).X p) :=
  integralTateEquiv K p (fiberBaseChangeIso K A f x)

/-- Composed base change gives an equivalence of actual covariant rational Tate representations. -/
def fiberBaseChangeTateEquiv :
    (tateRepresentation K (fiber K ((Over.pullback f).mapCommGrp.obj A) x).X p).Equiv
      (tateRepresentation K (fiber K A (x ≫ f)).X p) :=
  tateEquiv K p (fiberBaseChangeIso K A f x)

end AlgebraicGeometry.GroupScheme
