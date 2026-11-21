/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.Geometry.GroupScheme.PrimeTorsion
public import HilbertModularity.Geometry.GroupScheme.EtaleKernel
public import Mathlib.Algebra.Module.TransferInstance

/-! # Actual kernels of integral coefficient endomorphisms

A ring action on a commutative group scheme gives the coefficient module
on its actual geometric points. The scheme kernel of a coefficient has
exactly the points in the principal coefficient-torsion module, compatibly
with Galois. See [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (R : Type*) [CommRing R] (φ : R →+* End A)

/-- An actual scheme coefficient action gives the module on its geometric points. -/
@[instance_reducible]
def pointsCoefficientModule : Module R (Points K (AlgebraicClosure K) A.X) :=
  Module.compHom _ ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)

/-- The induced coefficient action is realized by the given scheme endomorphisms. -/
theorem pointsCoefficientModule_realized :
    letI := pointsCoefficientModule K A R φ
    ∀ r, ∃ (f : A.X ⟶ A.X) (_ : IsMonHom f),
      Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A.X) r =
        pointsMap K (AlgebraicClosure K) f := by
  intro r
  exact ⟨(φ r).hom.hom.hom, inferInstance, rfl⟩

/-- Geometric points of the actual coefficient kernel are exactly coefficient torsion. -/
def coefficientKernelPointsEquiv (a : R) :
    letI := pointsCoefficientModule K A R φ
    Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X ≃+
      coefficientTorsion K A.X R a := by
  letI := pointsCoefficientModule K A R φ
  let e := Grp.kernelHomMulEquiv (φ a).hom (fieldPoint K (AlgebraicClosure K))
  exact {
    toFun := fun x => ⟨Additive.ofMul (e x.toMul).val, (e x.toMul).property⟩
    invFun := fun x => Additive.ofMul (e.symm ⟨x.val.toMul, x.property⟩)
    left_inv := fun x => e.symm_apply_apply x.toMul
    right_inv := fun x => by
      apply Subtype.ext
      exact congrArg Subtype.val (e.apply_symm_apply _)
    map_add' := fun x y => by
      apply Subtype.ext
      exact congrArg Subtype.val (e.map_mul x.toMul y.toMul) }

/-- The kernel-point comparison is the actual kernel inclusion on geometric points. -/
@[simp]
theorem coefficientKernelPointsEquiv_apply (a : R)
    (x : Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) :
    letI := pointsCoefficientModule K A R φ
    (coefficientKernelPointsEquiv K A R φ a x : Points K (AlgebraicClosure K) A.X) =
      pointsMap K (AlgebraicClosure K) (Grp.kernelInclusion (φ a).hom) x := rfl

/-- The actual kernel-point comparison preserves the Galois action. -/
theorem coefficientKernelPointsEquiv_galois (a : R)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) :
    letI := pointsCoefficientModule K A R φ
    (coefficientKernelPointsEquiv K A R φ a (g • x) : Points K (AlgebraicClosure K) A.X) =
      g • (coefficientKernelPointsEquiv K A R φ a x : Points K (AlgebraicClosure K) A.X) :=
  pointsMap_galois K (AlgebraicClosure K) (Grp.kernelInclusion (φ a).hom) g x

/-- The actual coefficient-kernel points carry the residue coefficient module. -/
@[instance_reducible]
def coefficientKernelModule (a : R) :
    Module (R ⧸ Ideal.span {a})
      (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) := by
  letI := pointsCoefficientModule K A R φ
  exact (coefficientKernelPointsEquiv K A R φ a).module (R ⧸ Ideal.span {a})

/-- Kernel inclusion identifies its residue module with actual coefficient torsion. -/
def coefficientKernelLinearEquiv (a : R) :
    letI := pointsCoefficientModule K A R φ
    letI := coefficientKernelModule K A R φ a
    Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X ≃ₗ[R ⧸ Ideal.span {a}]
      coefficientTorsion K A.X R a := by
  letI := pointsCoefficientModule K A R φ
  exact (coefficientKernelPointsEquiv K A R φ a).linearEquiv (R ⧸ Ideal.span {a})

/-- The residue-linear kernel comparison intertwines the original point Galois actions. -/
theorem coefficientKernelLinearEquiv_galois (a : R)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) :
    letI := pointsCoefficientModule K A R φ
    letI := coefficientKernelModule K A R φ a
    coefficientKernelLinearEquiv K A R φ a (g • x) =
      coefficientTorsionRepresentation K A.X R (pointsCoefficientModule_realized K A R φ) a g
        (coefficientKernelLinearEquiv K A R φ a x) := by
  apply Subtype.ext
  exact coefficientKernelPointsEquiv_galois K A R φ a g x

/-- The actual Galois action on the scheme kernel is linear over the residue coefficient ring. -/
def coefficientKernelRepresentation (a : R) :
    letI := coefficientKernelModule K A R φ a
    Representation (R ⧸ Ideal.span {a}) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) := by
  letI := pointsCoefficientModule K A R φ
  letI := coefficientKernelModule K A R φ a
  let E := coefficientKernelLinearEquiv K A R φ a
  exact {
    toFun := fun g => {
      toFun := fun x => g • x
      map_add' := smul_add g
      map_smul' := fun c x => by
        apply E.injective
        change coefficientKernelLinearEquiv K A R φ a (g • (c • x)) =
          coefficientKernelLinearEquiv K A R φ a (c • (g • x))
        simp only [coefficientKernelLinearEquiv_galois, map_smul] }
    map_one' := by
      apply LinearMap.ext
      intro x
      exact one_smul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x
    map_mul' := fun g h => by
      apply LinearMap.ext
      intro x
      exact mul_smul g h x }

/-- This representation uses the original geometric Galois action on kernel points. -/
@[simp]
theorem coefficientKernelRepresentation_apply (a : R)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) :
    letI := coefficientKernelModule K A R φ a
    coefficientKernelRepresentation K A R φ a g x = g • x := rfl

/-- The actual scheme-kernel and coefficient-torsion representations are equivariantly identical. -/
def coefficientKernelRepresentationEquiv (a : R) :
    letI := pointsCoefficientModule K A R φ
    letI := coefficientKernelModule K A R φ a
    (coefficientKernelRepresentation K A R φ a).Equiv
      (coefficientTorsionRepresentation K A.X R (pointsCoefficientModule_realized K A R φ) a) := by
  letI := pointsCoefficientModule K A R φ
  letI := coefficientKernelModule K A R φ a
  exact .mk (coefficientKernelLinearEquiv K A R φ a) (fun g => by
    apply LinearMap.ext
    intro x
    exact coefficientKernelLinearEquiv_galois K A R φ a g x)

/-- The actual scheme-kernel determinant equals that of its coefficient-torsion realization. -/
theorem det_coefficientKernelRepresentation (a : R)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    letI := pointsCoefficientModule K A R φ
    letI := coefficientKernelModule K A R φ a
    LinearMap.det (coefficientKernelRepresentation K A R φ a g) =
      LinearMap.det (coefficientTorsionRepresentation K A.X R
        (pointsCoefficientModule_realized K A R φ) a g) := by
  let := pointsCoefficientModule K A R φ
  let := coefficientKernelModule K A R φ a
  let E := coefficientKernelRepresentationEquiv K A R φ a
  have h := congrArg LinearMap.det (Representation.Equiv.conj_apply_self g E)
  exact (LinearMap.det_conj _ E.toLinearEquiv).symm.trans h

/-- Residue scalars on kernel points are induced by the original scheme coefficient endomorphisms. -/
theorem coefficientKernel_smul_mk (a r : R)
    (x : Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ a)).X) :
    letI := coefficientKernelModule K A R φ a
    pointsMap K (AlgebraicClosure K) (Grp.kernelInclusion (φ a).hom)
      (Ideal.Quotient.mk (Ideal.span {a}) r • x) =
      pointsMap K (AlgebraicClosure K) (φ r).hom.hom.hom
        (pointsMap K (AlgebraicClosure K) (Grp.kernelInclusion (φ a).hom) x) := by
  let := pointsCoefficientModule K A R φ
  let := coefficientKernelModule K A R φ a
  exact congrArg Subtype.val
    ((coefficientKernelLinearEquiv K A R φ a).map_smul (Ideal.Quotient.mk (Ideal.span {a}) r) x)

variable (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A.X p).left] [Surjective (multiplicationMap K A.X p).left]

/-- Reduction of the actual RM-prime Tate lattice is the Galois representation on the actual scheme kernel. -/
def primeResidualKernelEquiv (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)}) :
    letI := pointsCoefficientModule K A R φ
    letI := coefficientKernelModule K A R φ a
    letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A.X)
      (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    ((primeIntegralTateRepresentation K A.X R (pointsCoefficientModule_realized K A R φ)
      p (Ideal.span {a}) e he hJ).baseChange (R ⧸ Ideal.span {a})).Equiv
        (coefficientKernelRepresentation K A R φ a) := by
  letI := pointsCoefficientModule K A R φ
  letI := coefficientKernelModule K A R φ a
  letI := TateModule.coefficientPrimeModule p R (Points K (AlgebraicClosure K) A.X)
    (Ideal.span {a}) e he hJ
  letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
  exact (primeResidualIntegralTateEquiv K A.X R (pointsCoefficientModule_realized K A R φ)
    p a b hab e he hJ).trans (coefficientKernelRepresentationEquiv K A R φ a).symm

end AlgebraicGeometry.GroupScheme
