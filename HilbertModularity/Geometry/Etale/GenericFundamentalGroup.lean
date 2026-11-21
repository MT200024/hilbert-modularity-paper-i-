/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.AlgebraicFiber
public import HilbertModularity.Geometry.Etale.FiniteProducts
public import HilbertModularity.Geometry.Etale.Continuity
public import HilbertModularity.FieldTheory.Etale.GenericOrbits
public import HilbertModularity.CategoryTheory.GaloisOrbits
public import Mathlib.FieldTheory.Galois.Profinite

/-! # The generic arithmetic group surjects onto the finite étale fundamental group

For a normal affine base, generic Galois orbits are detected by idempotents of
the original finite étale algebras. Finite products and compactness realize each
natural geometric-fibre automorphism by a single arithmetic Galois element.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
open scoped CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme
universe u
variable (R F : Type u) [CommRing R] [IsIntegrallyClosed R]
  [Field F] [Algebra R F] [IsFractionRing R F]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- A geometric-fibre automorphism preserves each arithmetic orbit on a finite étale spectrum. -/
theorem finiteEtaleAlgebraPointOver_mem_genericGaloisOrbit
    (α : Aut (finiteArithmeticFiberFunctor F (Spec.map (CommRingCat.ofHom (algebraMap R F)))))
    (A : CommAlgCat.FiniteEtale.{u} R) (φ : A.obj →ₐ[R] AlgebraicClosure F) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      g • finiteEtaleAlgebraPointOver R F A φ =
        α.hom.app (finiteEtaleAlgebraCover R A) (finiteEtaleAlgebraPointOver R F A φ) := by
  let H := finiteEtaleSpec R
  let e := finiteEtaleAlgebraFiberOverIso R F
  let β : End (CommAlgCat.FiniteEtale.fiber R (AlgebraicClosure F)) :=
    e.hom ≫ Functor.whiskerLeft H α.hom ≫ e.inv
  obtain ⟨g, hg⟩ := CommAlgCat.FiniteEtale.fiberEnd_mem_genericGaloisOrbit R F β A φ
  refine ⟨g, ?_⟩
  rw [finiteEtaleAlgebraPointOver_smul, hg]
  have hb : β ≫ e.hom = e.hom ≫ Functor.whiskerLeft H α.hom := by
    simp only [β, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hp := ConcreteCategory.congr_hom (NatTrans.congr_app hb (op A)) φ
  change e.hom.app (op A) (β.app (op A) φ) =
    α.hom.app (H.obj (op A)) (e.hom.app (op A) φ) at hp
  change e.hom.app (op A) (β.app (op A) φ) =
    α.hom.app (H.obj (op A)) (e.hom.app (op A) φ)
  exact hp

set_option backward.isDefEq.respectTransparency false in
/-- The actual generic arithmetic action realizes a fibre automorphism separately
at every point of every finite étale cover of the normal affine base. -/
theorem finiteArithmeticFiber_mem_genericGaloisOrbit
    (α : Aut (finiteArithmeticFiberFunctor F (Spec.map (CommRingCat.ofHom (algebraMap R F)))))
    (X : (Spec (CommRingCat.of R)).FiniteEtale)
    (x : (finiteArithmeticFiberFunctor F (Spec.map (CommRingCat.ofHom (algebraMap R F)))).obj X) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, g • x = α.hom.app X x := by
  let T := finiteArithmeticFiberFunctor F (Spec.map (CommRingCat.ofHom (algebraMap R F)))
  obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (finiteEtaleSpec R) X
  let y : T.obj ((finiteEtaleSpec R).obj A) := T.map e.inv x
  let φ := (finiteEtaleAlgebraPointOverEquiv R F A.unop).symm y
  have hφ : finiteEtaleAlgebraPointOver R F A.unop φ = y :=
    (finiteEtaleAlgebraPointOverEquiv R F A.unop).apply_symm_apply y
  obtain ⟨g, hg⟩ := finiteEtaleAlgebraPointOver_mem_genericGaloisOrbit R F α A.unop φ
  rw [hφ] at hg
  have hy : T.map e.hom y = x := by
    change T.map e.hom (T.map e.inv x) = x
    rw [← FintypeCat.comp_apply, ← T.map_comp, e.inv_hom_id, T.map_id]
    rfl
  refine ⟨g, ?_⟩
  rw [← hy, ← PreGaloisCategory.IsNaturalSMul.naturality]
  have hm := congrArg (fun z : T.obj ((finiteEtaleSpec R).obj A) => T.map e.hom z) hg
  exact hm.trans (FunctorToFintypeCat.naturality T T α.hom e.hom y).symm

/-- The absolute Galois group of the fraction field surjects onto the actual
finite étale fundamental group of an integrally closed affine base with perfect fraction field. -/
theorem galoisToEtaleFundamentalGroup_surjective_of_fractionField [PerfectField F] :
    Function.Surjective
      (galoisToEtaleFundamentalGroup F (Spec.map (CommRingCat.ofHom (algebraMap R F)))) := by
  intro α
  exact PreGaloisCategory.exists_toAut_eq_of_orbits
    (finiteArithmeticFiberFunctor F (Spec.map (CommRingCat.ofHom (algebraMap R F))))
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) α
    (finiteArithmeticFiber_mem_genericGaloisOrbit R F α)

end AlgebraicGeometry.Scheme
