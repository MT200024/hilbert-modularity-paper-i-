/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.CoefficientKernelAction
public import HilbertModularity.Geometry.Etale.GroupSchemeCoefficients

/-! # Actual kernel local systems and their arithmetic fibres

The actual kernel base-change isomorphism respects the residue-ring scheme
actions. On geometric points it therefore gives a linear Galois-equivariant
comparison with the canonical kernel-point representation.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u
variable {S : Scheme.{u}} (A : CommGrp (Over S))
  (R : Type*) [CommRing R] (φ : R →+* End A) (a : R)
  (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The actual kernel base-change isomorphism gives the canonical residue-linear equivalence on points. -/
def coefficientKernelFiberPointsEquiv :
    let ψ := (fiberEndomorphismMap K A x).comp φ
    letI := pointsCoefficientModule K (fiber K (CommGrp.pullbackKernel (φ a)) x)
      (R ⧸ Ideal.span {a})
      ((fiberEndomorphismMap K (CommGrp.pullbackKernel (φ a)) x).comp
        (coefficientKernelResidueAction A R φ a))
    letI := coefficientKernelModule K (fiber K A x) R ψ a
    Points K (AlgebraicClosure K) (fiber K (CommGrp.pullbackKernel (φ a)) x).X ≃ₗ[
      R ⧸ Ideal.span {a}]
      Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (ψ a)).X := by
  let ψ := (fiberEndomorphismMap K A x).comp φ
  letI := pointsCoefficientModule K (fiber K (CommGrp.pullbackKernel (φ a)) x)
    (R ⧸ Ideal.span {a})
    ((fiberEndomorphismMap K (CommGrp.pullbackKernel (φ a)) x).comp
      (coefficientKernelResidueAction A R φ a))
  letI := coefficientKernelModule K (fiber K A x) R ψ a
  let e : (fiber K (CommGrp.pullbackKernel (φ a)) x).X ≅
      (CommGrp.pullbackKernel (ψ a)).X :=
    (CommGrp.forget _).mapIso (kernelBaseChangeIso x (φ a))
  letI : IsMonHom e.hom := inferInstanceAs
    (IsMonHom (kernelBaseChangeIso x (φ a)).hom.hom.hom.hom)
  letI : IsMonHom e.inv := inferInstanceAs
    (IsMonHom (kernelBaseChangeIso x (φ a)).inv.hom.hom.hom)
  exact {
    toFun := pointsMap K (AlgebraicClosure K) e.hom
    invFun := pointsMap K (AlgebraicClosure K) e.inv
    left_inv v := by
      change (v.toMul ≫ e.hom) ≫ e.inv = v.toMul
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    right_inv v := by
      change (v.toMul ≫ e.inv) ≫ e.hom = v.toMul
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    map_add' := (pointsMap K (AlgebraicClosure K) e.hom).map_add
    map_smul' c v := by
      erw [← coefficientKernelResidueAction_points R a K (fiber K A x) ψ c
        (pointsMap K (AlgebraicClosure K) e.hom v)]
      change ((v.toMul ≫
        ((Over.pullback x).mapCommGrp.map (coefficientKernelResidueAction A R φ a c)).hom.hom.hom) ≫
          e.hom) =
        ((v.toMul ≫ e.hom) ≫
          (coefficientKernelResidueAction (fiber K A x) R ψ a c).hom.hom.hom)
      rw [Category.assoc, Category.assoc]
      have h := congrArg
        (fun f : (Over.pullback x).mapCommGrp.obj (CommGrp.pullbackKernel (φ a)) ⟶
          CommGrp.pullbackKernel (ψ a) => f.hom.hom.hom)
        (coefficientKernelResidueAction_fiber A R φ a K x c)
      exact congrArg (fun f => v.toMul ≫ f) h }

/-- The residue-linear kernel comparison is the point map of the actual scheme isomorphism. -/
theorem coefficientKernelFiberPointsEquiv_apply
    (v : Points K (AlgebraicClosure K) (fiber K (CommGrp.pullbackKernel (φ a)) x).X) :
    coefficientKernelFiberPointsEquiv A R φ a K x v =
      pointsMap K (AlgebraicClosure K) (kernelBaseChangeIso x (φ a)).hom.hom.hom.hom v := rfl

/-- The actual residue-linear kernel comparison commutes with the original Galois action. -/
theorem coefficientKernelFiberPointsEquiv_galois
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : Points K (AlgebraicClosure K) (fiber K (CommGrp.pullbackKernel (φ a)) x).X) :
    coefficientKernelFiberPointsEquiv A R φ a K x (g • v) =
      g • coefficientKernelFiberPointsEquiv A R φ a K x v :=
  pointsMap_galois K (AlgebraicClosure K) (kernelBaseChangeIso x (φ a)).hom.hom.hom.hom g v

variable [IsFinite (CommGrp.pullbackKernel (φ a)).X.hom]
  [Etale (CommGrp.pullbackKernel (φ a)).X.hom]

/-- The actual kernel local-system fibre is linearly equivalent to the canonical kernel points of the actual fibre. -/
def coefficientKernelLocalSystemEquiv :
    let ψ := (fiberEndomorphismMap K A x).comp φ
    letI := coefficientKernelModule K (fiber K A x) R ψ a
    (Scheme.finiteEtaleCoefficientLocalSystem K (CommGrp.pullbackKernel (φ a))
      (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a)).obj x ≃ₗ[
        R ⧸ Ideal.span {a}]
      Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (ψ a)).X :=
  (Scheme.finiteEtaleCoefficientFiberEquiv K (CommGrp.pullbackKernel (φ a))
    (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a) x).trans
      (coefficientKernelFiberPointsEquiv A R φ a K x)

/-- Arithmetic specialization of the actual kernel local system is the actual canonical kernel-point representation. -/
def coefficientKernelLocalSystemRepresentationEquiv :
    let ψ := (fiberEndomorphismMap K A x).comp φ
    letI := coefficientKernelModule K (fiber K A x) R ψ a
    (Scheme.arithmeticFiberRepresentation K S
      (Scheme.finiteEtaleCoefficientLocalSystem K (CommGrp.pullbackKernel (φ a))
        (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a)) x).Equiv
      (coefficientKernelRepresentation K (fiber K A x) R ψ a) := by
  let ψ := (fiberEndomorphismMap K A x).comp φ
  letI := coefficientKernelModule K (fiber K A x) R ψ a
  exact .mk (coefficientKernelLocalSystemEquiv A R φ a K x) (fun g => by
    apply LinearMap.ext
    intro v
    change coefficientKernelFiberPointsEquiv A R φ a K x
      (Scheme.finiteEtaleCoefficientFiberEquiv K (CommGrp.pullbackKernel (φ a))
        (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a) x
        ((Scheme.finiteEtaleCoefficientLocalSystem K (CommGrp.pullbackKernel (φ a))
          (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a)).map
            (Scheme.arithmeticFiberLoop K S x g) v)) =
      g • coefficientKernelFiberPointsEquiv A R φ a K x
        (Scheme.finiteEtaleCoefficientFiberEquiv K (CommGrp.pullbackKernel (φ a))
          (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a) x v)
    erw [Scheme.finiteEtaleCoefficientFiberEquiv_arithmetic K (CommGrp.pullbackKernel (φ a))
      (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a) x g v,
      coefficientKernelFiberPointsEquiv_galois A R φ a K x])

/-- The arithmetic determinant of the actual kernel local system equals the determinant on the actual kernel points. -/
theorem det_coefficientKernelLocalSystem
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    let ψ := (fiberEndomorphismMap K A x).comp φ
    let := coefficientKernelModule K (fiber K A x) R ψ a
    LinearMap.det (Scheme.arithmeticFiberRepresentation K S
      (Scheme.finiteEtaleCoefficientLocalSystem K (CommGrp.pullbackKernel (φ a))
        (R ⧸ Ideal.span {a}) (coefficientKernelResidueAction A R φ a)) x g) =
      LinearMap.det (coefficientKernelRepresentation K (fiber K A x) R ψ a g) := by
  let ψ := (fiberEndomorphismMap K A x).comp φ
  let := coefficientKernelModule K (fiber K A x) R ψ a
  let E := coefficientKernelLocalSystemRepresentationEquiv A R φ a K x
  have h := congrArg LinearMap.det (Representation.Equiv.conj_apply_self g E)
  exact (LinearMap.det_conj _ E.toLinearEquiv).symm.trans h

end AlgebraicGeometry.GroupScheme
