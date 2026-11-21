/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricPathGroup
public import HilbertModularity.Geometry.Etale.Pullback

/-! # Arithmetic kernels under change of geometric base point

The structure morphism sends a geometric path to a path on the base. Consequently
transport identifies its fundamental-group kernels, even for points over different fields.
-/

public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
universe u
variable {S T : Scheme.{u}} (f : S ⟶ T) (K L : Type u) [Field K] [Field L]
  {x : Spec (CommRingCat.of K) ⟶ S} {y : Spec (CommRingCat.of L) ⟶ S}
  (e : finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor L y)

/-- Pullback of covers maps a path between arbitrary geometric fibres to the base. -/
def geometricFiberPathMap :
    finiteArithmeticFiberFunctor K (x ≫ f) ≅ finiteArithmeticFiberFunctor L (y ≫ f) :=
  finiteArithmeticFiberPullbackIso f K x ≪≫
    isoWhiskerLeft (finiteEtalePullback f) e ≪≫
      (finiteArithmeticFiberPullbackIso f L y).symm

/-- Fundamental-group transport commutes with the map induced by a scheme morphism. -/
theorem etaleFundamentalGroupMap_geometricPath (g : etaleFundamentalGroup K x) :
    etaleFundamentalGroupMap f L y (geometricFiberPathGroupEquiv K L e g) =
      geometricFiberPathGroupEquiv K L (geometricFiberPathMap f K L e)
        (etaleFundamentalGroupMap f K x g) := by
  apply Iso.ext
  change (finiteArithmeticFiberPullbackIso f L y).hom ≫
      whiskerLeft (finiteEtalePullback f) (e.inv ≫ g.hom ≫ e.hom) ≫
        (finiteArithmeticFiberPullbackIso f L y).inv =
    ((finiteArithmeticFiberPullbackIso f L y).hom ≫
      whiskerLeft (finiteEtalePullback f) e.inv ≫
        (finiteArithmeticFiberPullbackIso f K x).inv) ≫
    ((finiteArithmeticFiberPullbackIso f K x).hom ≫
      whiskerLeft (finiteEtalePullback f) g.hom ≫
        (finiteArithmeticFiberPullbackIso f K x).inv) ≫
    ((finiteArithmeticFiberPullbackIso f K x).hom ≫
      whiskerLeft (finiteEtalePullback f) e.hom ≫
        (finiteArithmeticFiberPullbackIso f L y).inv)
  simp [Category.assoc]

/-- A path carries the kernel of the structure-map action exactly to the other kernel. -/
theorem geometricFiberPathGroupEquiv_mem_kernel_iff (g : etaleFundamentalGroup K x) :
    geometricFiberPathGroupEquiv K L e g ∈ (etaleFundamentalGroupMap f L y).ker ↔
      g ∈ (etaleFundamentalGroupMap f K x).ker := by
  change etaleFundamentalGroupMap f L y (geometricFiberPathGroupEquiv K L e g) = 1 ↔ _
  rw [etaleFundamentalGroupMap_geometricPath]
  exact map_eq_one_iff (geometricFiberPathGroupEquiv K L (geometricFiberPathMap f K L e))
    (geometricFiberPathGroupEquiv K L (geometricFiberPathMap f K L e)).injective

/-- The geometric subgroup is independent of the chosen geometric base point. -/
def geometricFiberPathKernelEquiv :
    (etaleFundamentalGroupMap f K x).ker ≃* (etaleFundamentalGroupMap f L y).ker where
  toFun g := ⟨geometricFiberPathGroupEquiv K L e g,
    (geometricFiberPathGroupEquiv_mem_kernel_iff f K L e g).mpr g.property⟩
  invFun g := ⟨(geometricFiberPathGroupEquiv K L e).symm g, by
    apply (geometricFiberPathGroupEquiv_mem_kernel_iff f K L e _).mp
    simpa only [ContinuousMulEquiv.apply_symm_apply] using g.property⟩
  left_inv g := Subtype.ext ((geometricFiberPathGroupEquiv K L e).symm_apply_apply g)
  right_inv g := Subtype.ext ((geometricFiberPathGroupEquiv K L e).apply_symm_apply g)
  map_mul' g h := Subtype.ext (map_mul (geometricFiberPathGroupEquiv K L e)
    (g : etaleFundamentalGroup K x) (h : etaleFundamentalGroup K x))

/-- Kernel transport has the same underlying action as fundamental-group transport. -/
@[simp] theorem geometricFiberPathKernelEquiv_coe
    (g : (etaleFundamentalGroupMap f K x).ker) :
    (geometricFiberPathKernelEquiv f K L e g : etaleFundamentalGroup L y) =
      geometricFiberPathGroupEquiv K L e g := (rfl)

end AlgebraicGeometry.Scheme
