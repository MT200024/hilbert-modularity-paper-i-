/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteFiber
public import HilbertModularity.CategoryTheory.GaloisAction
public import HilbertModularity.Geometry.Etale.Affine

/-! # Finite étale algebras and geometric fibres of their spectra

The spectrum functor identifies algebra embeddings into the algebraic closure
with actual geometric fibres, naturally in the finite étale algebra.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency false in
/-- A field embedding is the corresponding point of the actual étale spectrum cover. -/
def finiteEtaleAlgebraPoint (A : CommAlgCat.FiniteEtale.{u} K)
    (φ : A.obj →ₐ[K] AlgebraicClosure K) :
    (finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K)))).obj
      (finiteEtaleAlgebraCover K A) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ 𝟙 _
    rw [← Spec.map_comp, Category.comp_id]
    congr 1
    ext a
    exact φ.commutes a)

set_option backward.isDefEq.respectTransparency false in
/-- Embeddings of a finite étale algebra are exactly the points of its geometric fibre. -/
def finiteEtaleAlgebraPointEquiv (A : CommAlgCat.FiniteEtale.{u} K) :
    (A.obj →ₐ[K] AlgebraicClosure K) ≃
      (finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K)))).obj
        (finiteEtaleAlgebraCover K A) where
  toFun := finiteEtaleAlgebraPoint K A
  invFun y :=
    { __ := (Spec.preimage y.left).hom
      commutes' r := by
        have h := y.w
        change y.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
          Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ 𝟙 _ at h
        rw [Category.comp_id] at h
        have hr : CommRingCat.ofHom (algebraMap K A) ≫ Spec.preimage y.left =
            CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
          rw [← Spec.map_inj, Spec.map_comp, Spec.map_preimage]
          exact h
        exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) => f r) hr }
  left_inv φ := by
    apply AlgHom.ext
    intro a
    change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom a = φ a
    rw [Spec.preimage_map]
    rfl
  right_inv y := by
    apply Over.OverMorphism.ext
    exact Spec.map_preimage y.left

set_option backward.isDefEq.respectTransparency false in
/-- On embeddings, the arithmetic action is postcomposition by the field automorphism. -/
theorem finiteEtaleAlgebraPoint_smul (A : CommAlgCat.FiniteEtale.{u} K)
    (φ : A.obj →ₐ[K] AlgebraicClosure K)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    g • finiteEtaleAlgebraPoint K A φ = finiteEtaleAlgebraPoint K A (g.toAlgHom.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (g.toAlgHom.comp φ).toRingHom)
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Fixing the point of a finite étale algebra fixes every value of its embedding. -/
theorem finiteEtaleAlgebraPoint_fixed (A : CommAlgCat.FiniteEtale.{u} K)
    (φ : A.obj →ₐ[K] AlgebraicClosure K)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : g • finiteEtaleAlgebraPoint K A φ = finiteEtaleAlgebraPoint K A φ)
    (a : A.obj) : g (φ a) = φ a := by
  have hh := congrArg (fun z => z.left) h
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) at hh
  rw [← Spec.map_comp, Spec.map_inj] at hh
  exact congrArg (fun f : CommRingCat.of A.obj ⟶ CommRingCat.of (AlgebraicClosure K) => f a) hh

set_option backward.isDefEq.respectTransparency false in
/-- The action of the fibre functor on spectrum maps is composition of embeddings. -/
theorem finiteEtaleAlgebraPoint_map {A B : CommAlgCat.FiniteEtale.{u} K}
    (φ : A.obj →ₐ[K] B.obj) (ψ : B.obj →ₐ[K] AlgebraicClosure K) :
    (finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K)))).map
        (finiteEtaleAlgebraMap K φ) (finiteEtaleAlgebraPoint K B ψ) =
      finiteEtaleAlgebraPoint K A (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom)
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The standard algebraic fibre functor is naturally the geometric fibre of spectra. -/
def finiteEtaleAlgebraFiberIso :
    CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K) ≅
      finiteEtaleSpec K ⋙ finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K))) :=
  NatIso.ofComponents (fun A => FintypeCat.equivEquivIso
    (finiteEtaleAlgebraPointEquiv K A.unop)) (by
      intro A B f
      apply FintypeCat.hom_ext
      intro φ
      exact (finiteEtaleAlgebraPoint_map K f.unop.hom.hom φ).symm)

/-- Restrict a natural automorphism of geometric fibres to the corresponding
standard algebraic fibre functor. -/
def algebraFiberAut : etaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) →*
    Aut (CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K)) :=
  (finiteEtaleAlgebraFiberIso K).symm.conjAut.toMonoidHom.comp
    (((whiskeringLeft _ _ FintypeCat).obj (finiteEtaleSpec K)).mapAut
      (finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K)))))

/-- Restriction to the algebraic fibre functor is continuous in the profinite topologies. -/
theorem continuous_algebraFiberAut : Continuous (algebraFiberAut K) :=
  (PreGaloisCategory.continuous_conjAut (finiteEtaleAlgebraFiberIso K).symm).comp
    (PreGaloisCategory.continuous_mapAut_whiskeringLeft
      (finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K)))) (finiteEtaleSpec K))

/-- Restricting to algebra spectra loses no natural automorphisms of geometric fibres. -/
theorem algebraFiberAut_injective : Function.Injective (algebraFiberAut K) :=
  (finiteEtaleAlgebraFiberIso K).symm.conjAut.injective.comp
    (PreGaloisCategory.mapAut_whiskeringLeft_injective
      (finiteArithmeticFiberFunctor K (𝟙 (Spec (CommRingCat.of K)))) (finiteEtaleSpec K))

end AlgebraicGeometry.Scheme
