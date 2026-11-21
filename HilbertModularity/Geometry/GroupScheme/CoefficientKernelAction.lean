/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeKernel
public import HilbertModularity.Geometry.GroupScheme.KernelBaseChange
public import HilbertModularity.CategoryTheory.GroupObjectTorsion

/-! # Residue coefficients act by actual kernel-scheme endomorphisms

Commuting integral coefficients restrict to the actual coefficient kernel.
The defining coefficient acts as zero there, so this ring action factors
through the coefficient residue ring. This realizes the residue scalar action
geometrically, before passing to points or Galois representations.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u
variable {S : Scheme.{u}} (A : CommGrp (Over S))
  (R : Type*) [CommRing R] (φ : R →+* End A) (a : R)

/-- A commuting coefficient induces an actual endomorphism of the coefficient kernel. -/
def coefficientKernelEndomorphism (r : R) : End (CommGrp.pullbackKernel (φ a)) :=
  CommGrp.kernelMap (φ a) (φ a) (φ r) (φ r) (by
    change φ r * φ a = φ a * φ r
    rw [← map_mul, ← map_mul, mul_comm r a])

/-- Restriction of coefficients preserves the actual kernel inclusion. -/
@[reassoc]
theorem coefficientKernelEndomorphism_inclusion (r : R) :
    (coefficientKernelEndomorphism A R φ a r).hom.hom.hom ≫ Grp.kernelInclusion (φ a).hom =
      Grp.kernelInclusion (φ a).hom ≫ (φ r).hom.hom.hom := by
  have h : φ a ≫ φ r = φ r ≫ φ a := by
    change φ r * φ a = φ a * φ r
    rw [← map_mul, ← map_mul, mul_comm r a]
  exact Grp.kernelMap_inclusion (φ a).hom (φ a).hom (φ r).hom (φ r).hom
    (congrArg (fun k : A ⟶ A => k.hom) h)

set_option backward.isDefEq.respectTransparency false in
/-- The restricted coefficient endomorphisms form a ring action on the actual kernel scheme. -/
def coefficientKernelAction : R →+* End (CommGrp.pullbackKernel (φ a)) where
  toFun := coefficientKernelEndomorphism A R φ a
  map_one' := by
    apply CommGrp.hom_ext
    apply (cancel_mono (Grp.kernelInclusion (φ a).hom)).1
    erw [coefficientKernelEndomorphism_inclusion A R φ a, map_one]
    exact (Category.id_comp _).symm
  map_mul' r s := by
    apply CommGrp.hom_ext
    apply (cancel_mono (Grp.kernelInclusion (φ a).hom)).1
    change (coefficientKernelEndomorphism A R φ a (r * s)).hom.hom.hom ≫ _ =
      ((coefficientKernelEndomorphism A R φ a s).hom.hom.hom ≫
        (coefficientKernelEndomorphism A R φ a r).hom.hom.hom) ≫ _
    erw [coefficientKernelEndomorphism_inclusion A R φ a, map_mul]
    erw [Category.assoc, coefficientKernelEndomorphism_inclusion A R φ a r,
      coefficientKernelEndomorphism_inclusion_assoc A R φ a s]
    rfl
  map_zero' := by
    apply CommGrp.hom_ext
    apply (cancel_mono (Grp.kernelInclusion (φ a).hom)).1
    erw [coefficientKernelEndomorphism_inclusion A R φ a, map_zero, CommGrp.zero_hom,
      CommGrp.zero_hom, MonObj.comp_one, MonObj.one_comp]
  map_add' r s := by
    apply CommGrp.hom_ext
    apply (cancel_mono (Grp.kernelInclusion (φ a).hom)).1
    erw [coefficientKernelEndomorphism_inclusion A R φ a, map_add, CommGrp.add_hom,
      CommGrp.add_hom, MonObj.comp_mul, MonObj.mul_comp,
      coefficientKernelEndomorphism_inclusion A R φ a, coefficientKernelEndomorphism_inclusion A R φ a]

set_option backward.isDefEq.respectTransparency false in
/-- The defining coefficient is the zero endomorphism on its actual kernel. -/
@[simp]
theorem coefficientKernelAction_self : coefficientKernelAction A R φ a a = 0 := by
  apply CommGrp.hom_ext
  apply (cancel_mono (Grp.kernelInclusion (φ a).hom)).1
  change (coefficientKernelEndomorphism A R φ a a).hom.hom.hom ≫ _ = _
  erw [coefficientKernelEndomorphism_inclusion A R φ a a, Grp.kernelInclusion_comp,
    CommGrp.zero_hom, MonObj.one_comp]

/-- The actual kernel scheme carries an action of the coefficient quotient ring by endomorphisms. -/
def coefficientKernelResidueAction :
    (R ⧸ Ideal.span {a}) →+* End (CommGrp.pullbackKernel (φ a)) :=
  Ideal.Quotient.lift (Ideal.span {a}) (coefficientKernelAction A R φ a) (by
    intro r hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul, coefficientKernelAction_self, zero_mul])

/-- A residue class acts through the actual restriction of its integral coefficient endomorphism. -/
@[simp]
theorem coefficientKernelResidueAction_mk (r : R) :
    coefficientKernelResidueAction A R φ a (Ideal.Quotient.mk (Ideal.span {a}) r) =
      coefficientKernelEndomorphism A R φ a r := rfl

variable (K : Type u) [Field K]
  (B : CommGrp (Over (Spec (CommRingCat.of K)))) (ψ : R →+* End B)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric residue-ring action on the actual kernel induces exactly its canonical scalar action on points. -/
theorem coefficientKernelResidueAction_points (c : R ⧸ Ideal.span {a})
    (x : Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (ψ a)).X) :
    letI := coefficientKernelModule K B R ψ a
    pointsMap K (AlgebraicClosure K) (coefficientKernelResidueAction B R ψ a c).hom.hom.hom x =
      c • x := by
  let := pointsCoefficientModule K B R ψ
  let := coefficientKernelModule K B R ψ a
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [coefficientKernelResidueAction_mk]
  apply (coefficientKernelPointsEquiv K B R ψ a).injective
  apply Subtype.ext
  change pointsMap K (AlgebraicClosure K) (Grp.kernelInclusion (ψ a).hom)
    (pointsMap K (AlgebraicClosure K) (coefficientKernelEndomorphism B R ψ a r).hom.hom.hom x) =
      pointsMap K (AlgebraicClosure K) (Grp.kernelInclusion (ψ a).hom)
        (Ideal.Quotient.mk (Ideal.span {a}) r • x)
  rw [coefficientKernel_smul_mk]
  change Additive.ofMul ((x.toMul ≫ (coefficientKernelEndomorphism B R ψ a r).hom.hom.hom) ≫
    Grp.kernelInclusion (ψ a).hom) =
      Additive.ofMul ((x.toMul ≫ Grp.kernelInclusion (ψ a).hom) ≫ (ψ r).hom.hom.hom)
  congr 1
  erw [Category.assoc, coefficientKernelEndomorphism_inclusion B R ψ a r, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of integral coefficients to the actual kernel commutes with passage to a fibre. -/
theorem coefficientKernelEndomorphism_fiber (x : Spec (CommRingCat.of K) ⟶ S) (r : R) :
    let ψ := (fiberEndomorphismMap K A x).comp φ
    (Over.pullback x).mapCommGrp.map (coefficientKernelEndomorphism A R φ a r) ≫
        (kernelBaseChangeIso x (φ a)).hom =
      (kernelBaseChangeIso x (φ a)).hom ≫
        coefficientKernelEndomorphism (fiber K A x) R ψ a r := by
  let ψ := (fiberEndomorphismMap K A x).comp φ
  let F := Over.pullback x
  let e := kernelBaseChangeIso x (φ a)
  apply CommGrp.hom_ext
  apply (cancel_mono (Grp.kernelInclusion (ψ a).hom)).1
  change (F.map (coefficientKernelEndomorphism A R φ a r).hom.hom.hom ≫ e.hom.hom.hom.hom) ≫
      Grp.kernelInclusion (ψ a).hom =
    (e.hom.hom.hom.hom ≫ (coefficientKernelEndomorphism (fiber K A x) R ψ a r).hom.hom.hom) ≫
      Grp.kernelInclusion (ψ a).hom
  erw [Category.assoc, kernelBaseChangeIso_inclusion,
    ← F.map_comp, coefficientKernelEndomorphism_inclusion A R φ a r, F.map_comp]
  erw [Category.assoc, coefficientKernelEndomorphism_inclusion (fiber K A x) R ψ a r]
  erw [kernelBaseChangeIso_inclusion_assoc x (φ a)]
  rfl

/-- The residue-ring action on the actual kernel is compatible with the actual fibre kernel isomorphism. -/
theorem coefficientKernelResidueAction_fiber (x : Spec (CommRingCat.of K) ⟶ S)
    (c : R ⧸ Ideal.span {a}) :
    let ψ := (fiberEndomorphismMap K A x).comp φ
    (Over.pullback x).mapCommGrp.map (coefficientKernelResidueAction A R φ a c) ≫
        (kernelBaseChangeIso x (φ a)).hom =
      (kernelBaseChangeIso x (φ a)).hom ≫
        coefficientKernelResidueAction (fiber K A x) R ψ a c := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact coefficientKernelEndomorphism_fiber A R φ a K x r

end AlgebraicGeometry.GroupScheme
