/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectTorsion

/-! # Functoriality of the actual torsion group object -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace CategoryTheory.CommGrp
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [Limits.HasPullbacks C] {A B D : CommGrp C}

/-- An actual commutative group-object morphism induces a morphism on its multiplication kernels. -/
def torsionMap (f : A ⟶ B) (n : ℕ) : torsionObject A n ⟶ torsionObject B n :=
  kernelMap (n • 𝟙 A) (n • 𝟙 B) f f (by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])

/-- The induced torsion map is compatible with the original group-object morphism. -/
@[reassoc]
theorem torsionMap_inclusion (f : A ⟶ B) (n : ℕ) :
    (torsionMap f n).hom.hom.hom ≫ Grp.kernelInclusion (n • 𝟙 B).hom =
      Grp.kernelInclusion (n • 𝟙 A).hom ≫ f.hom.hom.hom := by
  have h : (n • 𝟙 A) ≫ f = f ≫ (n • 𝟙 B) := by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  exact Grp.kernelMap_inclusion (n • 𝟙 A).hom (n • 𝟙 B).hom f.hom f.hom
    (congrArg (fun k : A ⟶ B => k.hom) h)

/-- The actual torsion construction preserves identities. -/
@[simp]
theorem torsionMap_id (A : CommGrp C) (n : ℕ) : torsionMap (𝟙 A) n = 𝟙 (torsionObject A n) := by
  apply CommGrp.hom_ext
  apply (cancel_mono (Grp.kernelInclusion (n • 𝟙 A).hom)).mp
  erw [torsionMap_inclusion]
  change Grp.kernelInclusion (n • 𝟙 A).hom ≫ 𝟙 A.X =
    𝟙 (torsionObject A n).X ≫ Grp.kernelInclusion (n • 𝟙 A).hom
  exact (Category.comp_id (show (torsionObject A n).X ⟶ A.X from
    Grp.kernelInclusion (n • 𝟙 A).hom)).trans
      (Category.id_comp (show (torsionObject A n).X ⟶ A.X from
        Grp.kernelInclusion (n • 𝟙 A).hom)).symm

/-- The actual torsion construction preserves composition. -/
@[simp]
theorem torsionMap_comp (f : A ⟶ B) (g : B ⟶ D) (n : ℕ) :
    torsionMap (f ≫ g) n = torsionMap f n ≫ torsionMap g n := by
  apply CommGrp.hom_ext
  apply (cancel_mono (Grp.kernelInclusion (n • 𝟙 D).hom)).mp
  change (torsionMap (f ≫ g) n).hom.hom.hom ≫ Grp.kernelInclusion (n • 𝟙 D).hom =
    ((torsionMap f n).hom.hom.hom ≫ (torsionMap g n).hom.hom.hom) ≫
      Grp.kernelInclusion (n • 𝟙 D).hom
  erw [torsionMap_inclusion, Category.assoc, torsionMap_inclusion]
  exact (Category.assoc
    (show (torsionObject A n).X ⟶ A.X from Grp.kernelInclusion (n • 𝟙 A).hom)
    f.hom.hom.hom g.hom.hom.hom).symm.trans
      ((congrArg (fun k : (torsionObject A n).X ⟶ B.X => k ≫ g.hom.hom.hom)
        (torsionMap_inclusion f n)).symm.trans
          (Category.assoc (torsionMap f n).hom.hom.hom
            (show (torsionObject B n).X ⟶ B.X from Grp.kernelInclusion (n • 𝟙 B).hom)
            g.hom.hom.hom))

/-- Taking the actual multiplication kernel is functorial in the commutative group object. -/
def torsionFunctor (n : ℕ) : CommGrp C ⥤ CommGrp C where
  obj A := torsionObject A n
  map f := torsionMap f n
  map_id A := torsionMap_id A n
  map_comp f g := torsionMap_comp f g n

/-- The actual torsion map preserves addition of group-object morphisms. -/
@[simp]
theorem torsionMap_add (f g : A ⟶ B) (n : ℕ) :
    torsionMap (f + g) n = torsionMap f n + torsionMap g n := by
  let iA : (torsionObject A n).X ⟶ A.X := Grp.kernelInclusion (n • 𝟙 A).hom
  let iB : (torsionObject B n).X ⟶ B.X := Grp.kernelInclusion (n • 𝟙 B).hom
  let : Mono iB := Grp.kernelInclusion_mono _
  let : IsMonHom iB := Grp.kernelInclusion_isMonHom _
  apply CommGrp.hom_ext
  apply (cancel_mono iB).mp
  calc
    (torsionMap (f + g) n).hom.hom.hom ≫ iB =
        iA ≫ (f.hom.hom.hom * g.hom.hom.hom) := torsionMap_inclusion (f + g) n
    _ = (iA ≫ f.hom.hom.hom) * (iA ≫ g.hom.hom.hom) := MonObj.comp_mul _ _ _
    _ = ((torsionMap f n).hom.hom.hom ≫ iB) * ((torsionMap g n).hom.hom.hom ≫ iB) :=
      congrArg₂ (fun k l : (torsionObject A n).X ⟶ B.X => k * l)
        (torsionMap_inclusion f n).symm (torsionMap_inclusion g n).symm
    _ = (torsionMap f n + torsionMap g n).hom.hom.hom ≫ iB := (MonObj.mul_comp _ _ _).symm

/-- Taking actual torsion kernels is an additive functor of commutative group objects. -/
instance torsionFunctor_additive (n : ℕ) : (torsionFunctor (C := C) n).Additive where
  map_add {_A _B f g} := torsionMap_add f g n

/-- The actual torsion-kernel inclusion, as a commutative group-object morphism. -/
def torsionInclusion (A : CommGrp C) (n : ℕ) : torsionObject A n ⟶ A :=
  InducedCategory.homMk (Limits.pullback.fst (n • 𝟙 A).hom (Grp.unitHom A.toGrp))

/-- Forgetting the group structure gives the original kernel inclusion. -/
@[simp]
theorem torsionInclusion_hom (A : CommGrp C) (n : ℕ) :
    (torsionInclusion A n).hom.hom.hom = Grp.kernelInclusion (n • 𝟙 A).hom := rfl

/-- Torsion inclusions are natural for actual group-object morphisms. -/
@[reassoc]
theorem torsionMap_inclusion_hom (f : A ⟶ B) (n : ℕ) :
    torsionMap f n ≫ torsionInclusion B n = torsionInclusion A n ≫ f := by
  apply CommGrp.hom_ext
  exact torsionMap_inclusion f n

/-- The inclusion of torsion in the ambient group is monic. -/
instance torsionInclusion_mono (A : CommGrp C) (n : ℕ) : Mono (torsionInclusion A n) :=
  (CommGrp.forget C).mono_of_mono_map
    (inferInstanceAs (Mono (Grp.kernelInclusion (n • 𝟙 A).hom)))

/-- The ordinary torsion transition is multiplication on the actual ambient group object. -/
@[reassoc]
theorem torsionTransition_inclusion_hom (A : CommGrp C) (p n : ℕ) :
    torsionTransition A p n ≫ torsionInclusion A (p ^ n) =
      torsionInclusion A (p ^ (n + 1)) ≫ (p • 𝟙 A) := by
  apply CommGrp.hom_ext
  exact torsionTransition_inclusion A p n

/-- Every group-object morphism commutes with the actual multiplication-kernel tower. -/
theorem torsionMap_transition (f : A ⟶ B) (p n : ℕ) :
    torsionMap f (p ^ (n + 1)) ≫ torsionTransition B p n =
      torsionTransition A p n ≫ torsionMap f (p ^ n) := by
  apply (cancel_mono (torsionInclusion B (p ^ n))).mp
  simp only [Category.assoc, torsionMap_inclusion_hom, torsionTransition_inclusion_hom,
    torsionTransition_inclusion_hom_assoc,
    Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]

end CategoryTheory.CommGrp


