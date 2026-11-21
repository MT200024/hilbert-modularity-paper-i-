/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Affine
public import HilbertModularity.Geometry.Etale.FiniteFiber

/-! # Algebra maps and geometric fibres over a field-valued affine point

For an arbitrary affine base, the geometric fibre of a finite étale spectrum
is the set of algebra maps into the chosen algebraic closure. The comparison
retains the actual arithmetic action at the field-valued base point.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
universe u
variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

set_option backward.isDefEq.respectTransparency false in
/-- An algebra map is a geometric point of the actual finite étale spectrum cover. -/
def finiteEtaleAlgebraPointOver (A : CommAlgCat.FiniteEtale.{u} R)
    (φ : A.obj →ₐ[R] AlgebraicClosure K) :
    (finiteArithmeticFiberFunctor K (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
      (finiteEtaleAlgebraCover R A) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact (φ.commutes r).trans (IsScalarTower.algebraMap_apply R K (AlgebraicClosure K) r))

set_option backward.isDefEq.respectTransparency false in
/-- Algebra maps into the chosen closure are exactly the geometric fibre points. -/
def finiteEtaleAlgebraPointOverEquiv (A : CommAlgCat.FiniteEtale.{u} R) :
    (A.obj →ₐ[R] AlgebraicClosure K) ≃
      (finiteArithmeticFiberFunctor K (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (finiteEtaleAlgebraCover R A) where
  toFun := finiteEtaleAlgebraPointOver R K A
  invFun y :=
    { __ := (Spec.preimage y.left).hom
      commutes' r := by
        have h := y.w
        change y.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
          Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)) at h
        have hr : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage y.left =
            CommRingCat.ofHom (algebraMap R (AlgebraicClosure K)) := by
          rw [← Spec.map_inj, Spec.map_comp, Spec.map_preimage]
          rw [h, ← Spec.map_comp]
          congr 1
        exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of (AlgebraicClosure K) => f r) hr }
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
/-- Arithmetic Galois action corresponds to postcomposition on the algebra map. -/
theorem finiteEtaleAlgebraPointOver_smul (A : CommAlgCat.FiniteEtale.{u} R)
    (φ : A.obj →ₐ[R] AlgebraicClosure K)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    g • finiteEtaleAlgebraPointOver R K A φ =
      finiteEtaleAlgebraPointOver R K A ((g.toAlgHom.restrictScalars R).comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom ((g.toAlgHom.restrictScalars R).comp φ).toRingHom)
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Maps of actual spectrum covers act by composition on algebra maps. -/
theorem finiteEtaleAlgebraPointOver_map {A B : CommAlgCat.FiniteEtale.{u} R}
    (φ : A.obj →ₐ[R] B.obj) (ψ : B.obj →ₐ[R] AlgebraicClosure K) :
    (finiteArithmeticFiberFunctor K (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
        (finiteEtaleAlgebraMap R φ) (finiteEtaleAlgebraPointOver R K B ψ) =
      finiteEtaleAlgebraPointOver R K A (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom)
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The algebraic fibre functor is naturally the actual geometric fibre of spectra. -/
def finiteEtaleAlgebraFiberOverIso :
    CommAlgCat.FiniteEtale.fiber R (AlgebraicClosure K) ≅
      finiteEtaleSpec R ⋙
        finiteArithmeticFiberFunctor K (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  NatIso.ofComponents (fun A => FintypeCat.equivEquivIso
    (finiteEtaleAlgebraPointOverEquiv R K A.unop)) (by
      intro A B f
      apply FintypeCat.hom_ext
      intro φ
      exact (finiteEtaleAlgebraPointOver_map R K f.unop.hom.hom φ).symm)

end AlgebraicGeometry.Scheme
