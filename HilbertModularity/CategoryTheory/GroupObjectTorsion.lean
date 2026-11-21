/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectKernel
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Torsion.Basic

/-! # Torsion group objects and their actual points

The torsion object is the kernel of multiplication by an integer. Its points
are the ordinary torsion subgroup of the group of points.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.CommGrp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [Limits.HasPullbacks C] (A : CommGrp C)

omit [Limits.HasPullbacks C] in
/-- Multiplication by a natural number is repeated multiplication on the underlying object. -/
@[simp]
theorem nsmul_id_hom (n : ℕ) :
    (n • 𝟙 A).hom.hom.hom = (𝟙 A.X) ^ n := by
  induction n with
  | zero => simp only [zero_nsmul, zero_hom, pow_zero]
  | succ n hn =>
    rw [succ_nsmul, add_hom, hn]
    exact (pow_succ _ _).symm

omit [Limits.HasPullbacks C] in
/-- Multiplication by a natural number acts by that power on actual points. -/
@[simp]
theorem comp_nsmul_id (n : ℕ) (P : C) (g : P ⟶ A.X) :
    g ≫ (n • 𝟙 A).hom.hom.hom = g ^ n := by
  rw [nsmul_id_hom, MonObj.comp_pow, Category.comp_id]

/-- The actual torsion group object is the kernel of multiplication. -/
def torsionObject (n : ℕ) : CommGrp C := pullbackKernel (n • 𝟙 A)

/-- Points of the torsion object form the kernel of the ordinary power homomorphism. -/
def torsionPointMulEquiv (n : ℕ) (P : C) :
    (P ⟶ (torsionObject A n).X) ≃* (powMonoidHom (α := P ⟶ A.X) n).ker := by
  let e := Grp.kernelHomMulEquiv (n • 𝟙 A).hom P
  have h : IsMonHom.monoidHom (n • 𝟙 A).hom.hom.hom P = powMonoidHom n := by
    ext g
    exact comp_nsmul_id A n P g
  exact e.trans (MulEquiv.subgroupCongr (congrArg MonoidHom.ker h))

/-- Additively, the actual torsion-object points are the usual `n`-torsion subgroup. -/
def torsionPointAddEquiv (n : ℕ) (P : C) :
    Additive (P ⟶ (torsionObject A n).X) ≃+
      AddSubgroup.torsionBy (Additive (P ⟶ A.X)) n := by
  let e := torsionPointMulEquiv A n P
  exact {
    toFun := fun g => ⟨Additive.ofMul (e g.toMul).val,
      AddSubgroup.torsionBy.nsmul_iff.mpr (e g.toMul).property⟩
    invFun := fun g => Additive.ofMul (e.symm ⟨g.val.toMul,
      AddSubgroup.torsionBy.nsmul_iff.mp g.property⟩)
    left_inv := fun g => by exact e.symm_apply_apply g.toMul
    right_inv := fun g => by apply Subtype.ext; exact congrArg Subtype.val (e.apply_symm_apply _)
    map_add' := fun g h => by
      apply Subtype.ext
      exact congrArg Subtype.val (e.map_mul g.toMul h.toMul) }

end CategoryTheory.CommGrp

namespace CategoryTheory.CommGrp

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  [Limits.HasPullbacks C] (A : CommGrp C)

/-- Multiplication by `p` maps the actual `p^(n+1)`-torsion group object to `p^n`-torsion. -/
def torsionTransition (p n : ℕ) : torsionObject A (p ^ (n + 1)) ⟶ torsionObject A (p ^ n) :=
  kernelMap (p ^ (n + 1) • 𝟙 A) (p ^ n • 𝟙 A) (p • 𝟙 A) (𝟙 A) (by
    simp only [Category.comp_id, Preadditive.nsmul_comp, Category.id_comp,
      smul_smul, ← pow_succ'])

/-- The torsion transition induces multiplication by `p` on the ambient group object. -/
@[reassoc]
theorem torsionTransition_inclusion (p n : ℕ) :
    (torsionTransition A p n).hom.hom.hom ≫
        Grp.kernelInclusion (p ^ n • 𝟙 A).hom =
      Grp.kernelInclusion (p ^ (n + 1) • 𝟙 A).hom ≫ (p • 𝟙 A).hom.hom.hom := by
  have h : (p ^ (n + 1) • 𝟙 A) ≫ 𝟙 A = (p • 𝟙 A) ≫ (p ^ n • 𝟙 A) := by
    simp only [Category.comp_id, Preadditive.nsmul_comp, Category.id_comp,
      smul_smul, ← pow_succ']
  exact Grp.kernelMap_inclusion (p ^ (n + 1) • 𝟙 A).hom
    (p ^ n • 𝟙 A).hom (p • 𝟙 A).hom (𝟙 A.toGrp)
    (congrArg (fun k : A ⟶ A => k.hom) h)

/-- On actual points the transition is the ordinary power map, hence repeated addition additively. -/
theorem torsionTransition_points (p n : ℕ) (P : C)
    (g : P ⟶ (torsionObject A (p ^ (n + 1))).X) :
    (g ≫ (torsionTransition A p n).hom.hom.hom) ≫
        Grp.kernelInclusion (p ^ n • 𝟙 A).hom =
      (g ≫ Grp.kernelInclusion (p ^ (n + 1) • 𝟙 A).hom) ^ p := by
  erw [Category.assoc, torsionTransition_inclusion, ← Category.assoc]
  exact comp_nsmul_id A p P _

end CategoryTheory.CommGrp
