/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberNaturality

/-! # Transport along actual étale paths

A natural isomorphism of geometric fibre functors identifies their fundamental
groups and transports a module-valued family's fibre representation. The
arithmetic loops at another rational point are conjugated through this actual
path. No existence of paths, or geometric exact sequence, is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K] (S : Scheme.{u})
  {x y : Spec (CommRingCat.of K) ⟶ S}
  (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y)

/-- An actual étale path gives an isomorphism in the fibre groupoid. -/
def etaleFiberPointIso : etaleFiberPoint K S x ≅ etaleFiberPoint K S y :=
  InducedCategory.isoMk (Core.isoMk e)

/-- Changing the geometric fibre functor identifies its profinite automorphism group. -/
def etaleFundamentalGroupPathEquiv : etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K y :=
  { e.conjAut with
    continuous_toFun := PreGaloisCategory.continuous_conjAut e
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := e.conjAut.toEquiv) (PreGaloisCategory.continuous_conjAut e) }

/-- The path equivalence acts by conjugation by the specified fibre isomorphism. -/
theorem etaleFundamentalGroupPathEquiv_apply (g : etaleFundamentalGroup K x) :
    etaleFundamentalGroupPathEquiv K S e g = e.conjAut g := rfl

/-- Arithmetic loops at the second point, transported to the first fibre functor. -/
def arithmeticLoopsAlongPath :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* etaleFundamentalGroup K x :=
  ((etaleFundamentalGroupPathEquiv K S e).symm :
    etaleFundamentalGroup K y →ₜ* etaleFundamentalGroup K x).comp
      (continuousGaloisToEtaleFundamentalGroup K y)

variable {R : Type*} [CommRing R] (L : EtaleFiberGroupoid K S ⥤ ModuleCat R)

/-- Transport in a single family intertwines the actual monodromy actions. -/
def fiberMonodromyPathEquiv :
    (fiberMonodromy K S L x).Equiv
      ((fiberMonodromy K S L y).comp (etaleFundamentalGroupPathEquiv K S e).toMonoidHom) :=
  .mk (L.mapIso (etaleFiberPointIso K S e)).toLinearEquiv (by
    intro σ
    have hp : etaleFiberPath K S σ ≫ etaleFiberPath K S e =
        etaleFiberPath K S e ≫ etaleFiberPath K S (e.conjAut σ) := by
      apply InducedCategory.hom_ext
      apply Core.hom_ext
      change σ.hom ≫ e.hom = e.hom ≫ (e.conjAut σ).hom
      change σ.hom ≫ e.hom = e.hom ≫ (e.inv ≫ σ.hom ≫ e.hom)
      rw [e.hom_inv_id_assoc]
    have hm := congrArg L.map hp
    rw [L.map_comp, L.map_comp] at hm
    exact congrArg ModuleCat.Hom.hom hm)

/-- The arithmetic representation at the second point is the first monodromy
representation pulled back along its transported arithmetic loops. -/
def arithmeticFiberPathEquiv :
    Representation.Equiv
      ((fiberMonodromy K S L x).comp (arithmeticLoopsAlongPath K S e).toMonoidHom)
      (arithmeticFiberRepresentation K S L y) :=
  .mk (L.mapIso (etaleFiberPointIso K S e)).toLinearEquiv (by
    intro g
    have h := (fiberMonodromyPathEquiv K S e L).isIntertwining'
      ((etaleFundamentalGroupPathEquiv K S e).symm (galoisToEtaleFundamentalGroup K y g))
    change (L.mapIso (etaleFiberPointIso K S e)).toLinearEquiv.toLinearMap.comp
        (fiberMonodromy K S L x ((etaleFundamentalGroupPathEquiv K S e).symm
          (galoisToEtaleFundamentalGroup K y g))) =
      (fiberMonodromy K S L y ((etaleFundamentalGroupPathEquiv K S e)
        ((etaleFundamentalGroupPathEquiv K S e).symm (galoisToEtaleFundamentalGroup K y g)))).comp
          (L.mapIso (etaleFiberPointIso K S e)).toLinearEquiv.toLinearMap at h
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h)

end AlgebraicGeometry.Scheme
