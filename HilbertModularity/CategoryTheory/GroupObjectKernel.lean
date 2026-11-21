/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectReflection
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Actual kernels of commutative group objects

The kernel is the pullback of the given group homomorphism along the unit.
Its underlying object is the actual categorical pullback. The monic kernel
inclusion reflects commutativity from the ambient group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Grp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

/-- The unit section, as a morphism of group objects. -/
def unitHom (B : Grp C) : Grp.trivial C ⟶ B :=
  Grp.homMk' (default : Mon.trivial C ⟶ B.toMon)

instance unitHom_mono (B : Grp C) : Mono (unitHom B) :=
  (Grp.forget C).mono_of_mono_map (inferInstanceAs (Mono η[B.X]))

variable {A B : Grp C} (f : A ⟶ B)

/-- The kernel group object is the actual pullback along the unit section. -/
def pullbackKernel : Grp C := pullback f (unitHom B)

/-- The underlying kernel inclusion is the actual first pullback projection. -/
def kernelInclusion : (pullbackKernel f).X ⟶ A.X :=
  (pullback.fst f (unitHom B)).hom.hom

instance kernelInclusion_isMonHom : IsMonHom (kernelInclusion f) :=
  inferInstanceAs (IsMonHom (pullback.fst f (unitHom B)).hom.hom)

instance kernelInclusion_mono : Mono (kernelInclusion f) :=
  inferInstanceAs (Mono ((Grp.forget C).map (pullback.fst f (unitHom B))))

/-- Forgetting the kernel group gives the actual pullback of the underlying morphism and unit. -/
def pullbackKernelUnderlyingIso :
    (pullbackKernel f).X ≅ pullback f.hom.hom η[B.X] :=
  PreservesPullback.iso (Grp.forget C) f (unitHom B)

/-- The pullback comparison preserves the actual kernel inclusion. -/
@[reassoc]
theorem pullbackKernelUnderlyingIso_fst :
    (pullbackKernelUnderlyingIso f).hom ≫ pullback.fst f.hom.hom η[B.X] =
      kernelInclusion f :=
  PreservesPullback.iso_hom_fst (Grp.forget C) f (unitHom B)

/-- The kernel inclusion is annihilated by the given homomorphism. -/
@[simp]
theorem kernelInclusion_comp : kernelInclusion f ≫ f.hom.hom = 1 := by
  rw [← pullbackKernelUnderlyingIso_fst, Category.assoc, pullback.condition]
  rw [← Category.assoc, CategoryTheory.Hom.one_def]
  congr 1
  exact CartesianMonoidalCategory.toUnit_unique _ _

/-- Lift a point killed by the given homomorphism to the actual kernel. -/
def kernelLift (P : C) (g : P ⟶ A.X) (hg : g ≫ f.hom.hom = 1) :
    P ⟶ (pullbackKernel f).X :=
  pullback.lift g (CartesianMonoidalCategory.toUnit P)
    (by simpa only [CategoryTheory.Hom.one_def] using hg) ≫ (pullbackKernelUnderlyingIso f).inv

/-- The lifted point maps to the original point under the kernel inclusion. -/
@[simp]
theorem kernelLift_inclusion (P : C) (g : P ⟶ A.X) (hg : g ≫ f.hom.hom = 1) :
    kernelLift f P g hg ≫ kernelInclusion f = g := by
  rw [← pullbackKernelUnderlyingIso_fst]
  simp only [kernelLift, Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

/-- Points of the actual kernel are exactly points killed by the given homomorphism. -/
def kernelHomEquiv (P : C) :
    (P ⟶ (pullbackKernel f).X) ≃ { g : P ⟶ A.X // g ≫ f.hom.hom = 1 } where
  toFun g := ⟨g ≫ kernelInclusion f, by
    rw [Category.assoc, kernelInclusion_comp]
    exact MonObj.comp_one _⟩
  invFun g := kernelLift f P g.val g.property
  left_inv g := by
    apply (cancel_mono (kernelInclusion f)).1
    exact kernelLift_inclusion f P _ _
  right_inv g := Subtype.ext (kernelLift_inclusion f P _ _)

/-- The point identification is an isomorphism with the ordinary group-homomorphism kernel. -/
def kernelHomMulEquiv (P : C) :
    (P ⟶ (pullbackKernel f).X) ≃* (IsMonHom.monoidHom f.hom.hom P).ker where
  toEquiv := kernelHomEquiv f P
  map_mul' g h := Subtype.ext (MonObj.mul_comp g h (kernelInclusion f))

/-- The kernel-point group isomorphism is induced by the actual kernel inclusion. -/
@[simp]
theorem kernelHomMulEquiv_apply (P : C) (g : P ⟶ (pullbackKernel f).X) :
    (kernelHomMulEquiv f P g).val = g ≫ kernelInclusion f := rfl

end CategoryTheory.Grp

namespace CategoryTheory.CommGrp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [HasPullbacks C] {A B : CommGrp C}

/-- The actual kernel of a commutative group-object morphism is a commutative group object. -/
def pullbackKernel (f : A ⟶ B) : CommGrp C :=
  ofMono A (Grp.kernelInclusion f.hom)

end CategoryTheory.CommGrp

namespace CategoryTheory.Grp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Limits.HasPullbacks C]
  {A B A' B' : Grp C}

/-- A commutative square of group homomorphisms induces a morphism of their actual kernels. -/
def kernelMap (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) : pullbackKernel f ⟶ pullbackKernel g :=
  Limits.pullback.map f (unitHom B) g (unitHom B') a (𝟙 _) b h (by
    apply Grp.hom_ext
    change η[B.X] ≫ b.hom.hom = 𝟙 _ ≫ η[B'.X]
    simp)

/-- The induced kernel map commutes with the original first projections. -/
@[reassoc]
theorem kernelMap_fst (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) :
    kernelMap f g a b h ≫ Limits.pullback.fst g (unitHom B') =
      Limits.pullback.fst f (unitHom B) ≫ a :=
  Limits.pullback.lift_fst _ _ _

/-- The underlying kernel-point map is induced by the original group homomorphism. -/
@[reassoc]
theorem kernelMap_inclusion (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) :
    (kernelMap f g a b h).hom.hom ≫ kernelInclusion g =
      kernelInclusion f ≫ a.hom.hom :=
  congrArg (fun k : pullbackKernel f ⟶ A' => k.hom.hom) (kernelMap_fst f g a b h)

end CategoryTheory.Grp

namespace CategoryTheory.CommGrp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [Limits.HasPullbacks C] {A B A' B' : CommGrp C}

/-- A square of commutative group-object morphisms induces the actual kernel morphism. -/
def kernelMap (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) : pullbackKernel f ⟶ pullbackKernel g :=
  InducedCategory.homMk (Grp.kernelMap f.hom g.hom a.hom b.hom
    (congrArg (fun k : A ⟶ B' => k.hom) h))

end CategoryTheory.CommGrp
