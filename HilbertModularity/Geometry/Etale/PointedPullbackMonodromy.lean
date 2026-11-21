/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystemPullback
public import HilbertModularity.Geometry.Etale.PointedAutomorphism
public import HilbertModularity.Geometry.Etale.LocalSystemInvolution
public import HilbertModularity.Geometry.Etale.ParameterInvolution

/-! # Monodromy of a pointed pullback

The monodromy of the actual pulled-back family is the original monodromy
precomposed with the scheme-induced fundamental-group map. At a fixed point
this identifies the pullback with the action of the pointed automorphism.
-/

public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u v
variable {S T : Scheme.{u}} (K : Type u) [Field K]
  {R : Type v} [Field R] [TopologicalSpace R]

/-- Pullback transports every geometric loop by the actual scheme map. -/
theorem EtaleLocalSystem.pullback_fiberMonodromy
    (F : EtaleLocalSystem K T R) (f : S ⟶ T)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    fiberMonodromy K S (F.pullback f K).algebraicFunctor x =
      (fiberMonodromy K T F.algebraicFunctor (x ≫ f)).comp
        (etaleFundamentalGroupMap f K x) := by
  ext g v
  change (F.toFunctor.map ((etaleFiberGroupoidMap f K).map
    (etaleFiberPath K S g))).hom v =
      (F.toFunctor.map (etaleFiberPath K T
        (etaleFundamentalGroupMap f K x g))).hom v
  rw [etaleFiberGroupoidMap_loop]
  rfl

/-- At a fixed point, actual pullback is equivariantly the original
monodromy precomposed with the pointed fundamental-group automorphism. -/
def EtaleLocalSystem.pointedPullbackMonodromyEquiv
    (F : EtaleLocalSystem K S R) (e : S ≅ S)
    (x : Spec (CommRingCat.of K) ⟶ S) (hx : x ≫ e.hom = x) :
    (fiberMonodromy K S (F.pullback e.hom K).algebraicFunctor x).Equiv
      ((fiberMonodromy K S F.algebraicFunctor x).comp
        (etaleFundamentalGroupPointedAutomorphism K e x hx).toMonoidHom) := by
  have transport (y : Spec (CommRingCat.of K) ⟶ S) (hy : y = x)
      (a : etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K y) :
      Representation.Equiv
        ((fiberMonodromy K S F.algebraicFunctor y).comp a.toMonoidHom)
        ((fiberMonodromy K S F.algebraicFunctor x).comp
          (Eq.mp (congrArg (fun z : Spec (CommRingCat.of K) ⟶ S =>
            etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K z) hy) a
          ).toMonoidHom) := by
    subst y
    exact Representation.Equiv.refl _
  rw [F.pullback_fiberMonodromy]
  exact transport (x ≫ e.hom) hx (etaleFundamentalGroupIsoEquiv e K x)

/-- For the actual parameter complement, the geometric loop action at
`1/2` is precisely the action of the actual complement automorphism.
This supplies the functorial identification used in the cusp comparison;
it does not assert that the two geometric representations are isomorphic. -/
def EtaleLocalSystem.complementMidpointMonodromyEquiv [CharZero K]
    (F : EtaleLocalSystem K (ProjectiveLine.punctured K) R) :
    (fiberMonodromy K (ProjectiveLine.punctured K)
      (F.complementPullback K R).algebraicFunctor
      (ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K))).Equiv
        ((fiberMonodromy K (ProjectiveLine.punctured K) F.algebraicFunctor
          (ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K))).comp
            (ProjectiveLine.complementFundamentalAutomorphism K).toMonoidHom) :=
  F.pointedPullbackMonodromyEquiv K (ProjectiveLine.puncturedComplementIso K)
    (ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K))
    (ProjectiveLine.puncturedPoint_midpoint_complement K)

end AlgebraicGeometry.Scheme
