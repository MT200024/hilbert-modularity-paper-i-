/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GenericFiber
public import HilbertModularity.Geometry.Etale.PullbackComposition
public import HilbertModularity.Geometry.ProjectiveLine.CoordinateRing

/-! # Generic fibres of finite étale covers of the punctured line

The actual rational-function-field point detects morphisms and permits their
unique extension to finite étale covers of the punctured parameter line.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K]

/-- A map of finite étale generic fibres on the punctured line extends over the whole line. -/
instance puncturedRationalPoint_finiteEtalePullback_full :
    (Scheme.finiteEtalePullback (puncturedRationalPoint K)).Full := by
  have : (Scheme.finiteEtalePullback (puncturedAffineIso K).inv).Full :=
    (Scheme.finiteEtalePullbackEquivalence (puncturedAffineIso K).symm).full_functor
  exact Functor.Full.of_iso
    (Scheme.finiteEtalePullbackComp
      (Spec.map (CommRingCat.ofHom (algebraMap (puncturedCoordinateRing K) (RatFunc K))))
      (puncturedAffineIso K).inv).symm

/-- The generic rational coordinate detects morphisms between finite étale covers. -/
instance puncturedRationalPoint_finiteEtalePullback_faithful :
    (Scheme.finiteEtalePullback (puncturedRationalPoint K)).Faithful := by
  have : (Scheme.finiteEtalePullback (puncturedAffineIso K).inv).Faithful :=
    (Scheme.finiteEtalePullbackEquivalence (puncturedAffineIso K).symm).faithful_functor
  exact Functor.Faithful.of_iso
    (Scheme.finiteEtalePullbackComp
      (Spec.map (CommRingCat.ofHom (algebraMap (puncturedCoordinateRing K) (RatFunc K))))
      (puncturedAffineIso K).inv).symm

end AlgebraicGeometry.ProjectiveLine
