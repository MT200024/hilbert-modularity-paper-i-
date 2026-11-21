/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem
public import HilbertModularity.Geometry.Etale.Pullback

/-! # Pullback of continuous étale fibre families

A scheme morphism pulls back finite étale covers. The natural fibre comparison
therefore transports actual paths and induces pullback of a single continuous
family, including all its arithmetic specializations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

universe u v
variable {S T : Scheme.{u}} (f : S ⟶ T) (K : Type u) [Field K]

/-- A scheme morphism transports actual natural-isomorphism paths between fibres. -/
def etaleFiberPathMap {x y : Spec (CommRingCat.of K) ⟶ S}
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y) :
    finiteArithmeticFiberFunctor K (x ≫ f) ≅ finiteArithmeticFiberFunctor K (y ≫ f) :=
  finiteArithmeticFiberPullbackIso f K x ≪≫
    isoWhiskerLeft (finiteEtalePullback f) e ≪≫
      (finiteArithmeticFiberPullbackIso f K y).symm

/-- The actual fibre-groupoid functor induced by a scheme morphism. -/
def etaleFiberGroupoidMap : EtaleFiberGroupoid K S ⥤ EtaleFiberGroupoid K T where
  obj x := etaleFiberPoint K T ((show Spec (CommRingCat.of K) ⟶ S from x) ≫ f)
  map e := etaleFiberPath K T (etaleFiberPathMap f K e.hom.iso)
  map_id x := by
    apply InducedCategory.hom_ext
    apply Core.hom_ext
    change (etaleFiberPathMap f K (Iso.refl _)).hom = 𝟙 _
    simp [etaleFiberPathMap]
  map_comp e d := by
    apply InducedCategory.hom_ext
    apply Core.hom_ext
    change (etaleFiberPathMap f K (e.hom.iso ≪≫ d.hom.iso)).hom =
      (etaleFiberPathMap f K e.hom.iso).hom ≫ (etaleFiberPathMap f K d.hom.iso).hom
    simp [etaleFiberPathMap, Category.assoc]

set_option maxHeartbeats 800000 in
/-- On fundamental-group loops this is the already constructed continuous scheme map. -/
theorem etaleFiberGroupoidMap_loop (x : Spec (CommRingCat.of K) ⟶ S)
    (σ : etaleFundamentalGroup K x) :
    (etaleFiberGroupoidMap f K).map (etaleFiberPath K S σ) =
      etaleFiberPath K T (etaleFundamentalGroupMap f K x σ) := by
  apply InducedCategory.hom_ext
  apply Core.hom_ext
  change (etaleFiberPathMap f K σ).hom = (etaleFundamentalGroupMap f K x σ).hom
  simp only [etaleFundamentalGroupMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Iso.conjAut_hom, Iso.conj_apply]
  rfl

variable {R : Type v} [Field R] [TopologicalSpace R]

/-- Pull back one continuous finite-dimensional family along the actual scheme morphism. -/
def EtaleLocalSystem.pullback (L : EtaleLocalSystem K T R) : EtaleLocalSystem K S R where
  toFunctor := etaleFiberGroupoidMap f K ⋙ L.toFunctor
  finite x := L.finite _
  hausdorff x := L.hausdorff _
  continuous_monodromy x v := by
    change Continuous (fun σ : etaleFundamentalGroup K x =>
      (L.toFunctor.map ((etaleFiberGroupoidMap f K).map (etaleFiberPath K S σ))).hom v)
    simp only [etaleFiberGroupoidMap_loop]
    exact (L.continuous_monodromy (x ≫ f) v).comp (continuous_etaleFundamentalGroupMap f K x)

/-- Specializing the pulled-back family agrees with specialization at the composite point. -/
theorem EtaleLocalSystem.pullback_arithmeticRepresentation
    (L : EtaleLocalSystem K T R) (x : Spec (CommRingCat.of K) ⟶ S) :
    (L.pullback f K).arithmeticRepresentation x = L.arithmeticRepresentation (x ≫ f) := by
  ext g v
  change (L.toFunctor.map ((etaleFiberGroupoidMap f K).map
    (etaleFiberPath K S (galoisToEtaleFundamentalGroup K x g)))).hom v =
      (L.toFunctor.map (etaleFiberPath K T
        (galoisToEtaleFundamentalGroup K (x ≫ f) g))).hom v
  rw [etaleFiberGroupoidMap_loop, etaleFundamentalGroupMap_galois]
  rfl

/-- Equality of the composite point transports the actual specialized fibre and its action. -/
def EtaleLocalSystem.pullbackArithmeticEquiv (L : EtaleLocalSystem K T R)
    (x : Spec (CommRingCat.of K) ⟶ S) (y : Spec (CommRingCat.of K) ⟶ T)
    (h : x ≫ f = y) :
    ((L.pullback f K).arithmeticRepresentation x).Equiv (L.arithmeticRepresentation y) := by
  subst y
  rw [L.pullback_arithmeticRepresentation]
  exact Representation.Equiv.refl _

end AlgebraicGeometry.Scheme
