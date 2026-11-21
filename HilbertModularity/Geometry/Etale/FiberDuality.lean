/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.Category.ModuleCat.Duality
public import HilbertModularity.Geometry.Etale.FiberNaturality

/-! # Duality and actual arithmetic fibres

Inverse paths in the actual étale fibre groupoid produce the usual
contragredient arithmetic action. This identifies the family-level dual with
the fibrewise dual in [TripathiGoswami, cohomological RM factor].
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable (K : Type u) [Field K] (S : Scheme.{u})

/-- The inverse of an actual fibre path is induced by the inverse fibre isomorphism. -/
@[simp] theorem inv_etaleFiberPath {x y : Spec (CommRingCat.of K) ⟶ S}
    (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor K y) :
    inv (etaleFiberPath K S e) = etaleFiberPath K S e.symm := by
  rw [← Groupoid.inv_eq_inv]
  rfl

variable {R : Type*} [CommRing R]

/-- Monodromy of the dual family is the contragredient of its original monodromy. -/
theorem fiberMonodromy_cohDual (F : EtaleFiberGroupoid K S ⥤ ModuleCat R)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    fiberMonodromy K S (ModuleCat.cohDual R F) x = (fiberMonodromy K S F x).dual := by
  apply MonoidHom.ext
  intro σ
  change ((ModuleCat.cohDual R F).map (etaleFiberPath K S σ)).hom =
    (F.map (etaleFiberPath K S σ.symm)).hom.dualMap
  rw [ModuleCat.cohDual_map_hom]
  exact congrArg (fun f => (F.map f).hom.dualMap) (inv_etaleFiberPath K S σ)

/-- Taking the actual arithmetic fibre commutes with cohomological duality. -/
theorem arithmeticFiberRepresentation_cohDual
    (F : EtaleFiberGroupoid K S ⥤ ModuleCat R)
    (x : Spec (CommRingCat.of K) ⟶ S) :
    arithmeticFiberRepresentation K S (ModuleCat.cohDual R F) x =
      (arithmeticFiberRepresentation K S F x).dual := by
  unfold arithmeticFiberRepresentation
  rw [fiberMonodromy_cohDual]
  apply MonoidHom.ext
  intro g
  change (fiberMonodromy K S F x ((galoisToEtaleFundamentalGroup K x g)⁻¹)).dualMap =
    (fiberMonodromy K S F x (galoisToEtaleFundamentalGroup K x g⁻¹)).dualMap
  rw [(galoisToEtaleFundamentalGroup K x).map_inv]

end AlgebraicGeometry.Scheme
