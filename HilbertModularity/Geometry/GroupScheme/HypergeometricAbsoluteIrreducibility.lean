/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricIrreducibility
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.GeometricPathMonodromy
public import HilbertModularity.Geometry.Etale.GeometricPathKernel
public import HilbertModularity.Geometry.ProjectiveLine.GenericFiberPath
public import HilbertModularity.RepresentationTheory.SurjectiveRestriction

/-! # Absolute irreducibility of the labelled Darmon monodromy

The two cusp generators remain transverse over every extension of the specified
coefficient field. The coefficient tensor comparison retains the original label.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic Algebra.TensorProduct

/-- Scalar extension of a fixed labelled factor is irreducible on the actual
arithmetic kernel, using the same simultaneous cusp basis. -/
theorem darmonLabelledMonodromy_arithmeticKernel_baseChange_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L)
    (M : Type) [Field M] [Algebra L M] [Algebra ℚ_[p] M] [Algebra ℚ M]
    [IsScalarTower ℚ ℚ_[p] M] [IsScalarTower ℚ L M] [IsScalarTower ℚ_[p] L M] :
    Representation.IsIrreducible (Representation.baseChange M
      ((Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N))
        (GroupScheme.labelledTateLocalSystem (RatFunc (realCyclotomicField N))
          (darmonFamily N hN) p L (realCyclotomicField N)
          (darmonRealMultiplication N hN) hL σ)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).comp
          (Scheme.etaleFundamentalGroupMap
            (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
            (RatFunc (realCyclotomicField N))
            (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype)) := by
  let V := TateModule.rational p
    (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ (darmonFamily N hN).X))
  let : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
    Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
  let σM := (IsScalarTower.toAlgHom ℚ L M).comp σ
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) M :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) M σM).toAlgebra
  let : IsScalarTower (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L M :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul r a =>
        change coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) M σM
          (r ⊗ₜ[ℚ] a) = algebraMap L M
            (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ (r ⊗ₜ[ℚ] a))
        simp only [coefficientTensorEmbedding_tmul,
          map_mul,
          σM,
          AlgHom.comp_apply,
          IsScalarTower.algebraMap_apply ℚ_[p] L M]
        rfl)
  let k := (Scheme.etaleFundamentalGroupMap
    (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
    (RatFunc (realCyclotomicField N))
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype
  let ρ := (GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
    (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).comp k
  let e := ((GroupScheme.coefficientTateMonodromyLabelledEquiv
    (RatFunc (realCyclotomicField N)) (darmonFamily N hN)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) p
    (realCyclotomicField N) (darmonRealMultiplication N hN) L hL σ
    (ProjectiveLine.puncturedRationalPoint_galoisToEtaleFundamentalGroup_surjective
      (realCyclotomicField N))).compHom k).baseChange M
  have h := darmonCoefficientMonodromy_arithmeticKernel_specialization_isIrreducible
    N hN p M σM
  have ht : (Representation.baseChange M (Representation.baseChange L ρ)).IsIrreducible :=
    (OrderIso.isSimpleOrder_iff (Representation.baseChangeTowerEquiv
      (L := L) (M := M) ρ).subrepresentationOrderIso).mpr h
  exact (OrderIso.isSimpleOrder_iff e.subrepresentationOrderIso).mp ht

/-- The same absolute irreducibility holds at every rational geometric base point.
The path transports the structure-map kernel and the fixed coefficient label. -/
theorem darmonLabelledMonodromy_at_arithmeticKernel_baseChange_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L)
    (M : Type) [Field M] [Algebra L M] [Algebra ℚ_[p] M] [Algebra ℚ M]
    [IsScalarTower ℚ ℚ_[p] M] [IsScalarTower ℚ L M] [IsScalarTower ℚ_[p] L M]
    (x : Spec (CommRingCat.of (realCyclotomicField N)) ⟶
      ProjectiveLine.punctured (realCyclotomicField N)) :
    Representation.IsIrreducible (Representation.baseChange M
      ((Scheme.fiberMonodromy (realCyclotomicField N)
        (ProjectiveLine.punctured (realCyclotomicField N))
        (GroupScheme.labelledTateLocalSystem (realCyclotomicField N)
          (darmonFamily N hN) p L (realCyclotomicField N)
          (darmonRealMultiplication N hN) hL σ) x).comp
          (Scheme.etaleFundamentalGroupMap
            (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
            (realCyclotomicField N) x).ker.subtype)) := by
  let path := ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N) x
  let k := (Scheme.etaleFundamentalGroupMap
    (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
    (RatFunc (realCyclotomicField N))
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype
  let e := ((GroupScheme.labelledTateGeometricPathRepresentationEquiv
    (RatFunc (realCyclotomicField N)) (realCyclotomicField N) path
    (darmonFamily N hN) p L (realCyclotomicField N)
    (darmonRealMultiplication N hN) hL σ).compHom k).baseChange M
  let ek := Scheme.geometricFiberPathKernelEquiv
    (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
    (RatFunc (realCyclotomicField N)) (realCyclotomicField N) path
  apply (Representation.isIrreducible_comp_iff_of_surjective _
    ek.toMonoidHom ek.surjective).mp
  have h := (OrderIso.isSimpleOrder_iff e.subrepresentationOrderIso).mp
    (darmonLabelledMonodromy_arithmeticKernel_baseChange_isIrreducible N hN p L hL σ M)
  convert h using 1
  apply MonoidHom.ext
  intro g
  change LinearMap.baseChange M
    (Scheme.fiberMonodromy (realCyclotomicField N) _
      (GroupScheme.labelledTateLocalSystem (realCyclotomicField N)
        (darmonFamily N hN) p L (realCyclotomicField N)
        (darmonRealMultiplication N hN) hL σ) x (ek g).val) =
    LinearMap.baseChange M
      (Scheme.fiberMonodromy (realCyclotomicField N) _
        (GroupScheme.labelledTateLocalSystem (realCyclotomicField N)
          (darmonFamily N hN) p L (realCyclotomicField N)
          (darmonRealMultiplication N hN) hL σ) x
        (Scheme.geometricFiberPathGroupEquiv _ _ path g.val))
  rw [Scheme.geometricFiberPathKernelEquiv_coe]

end HilbertModularity.Hypergeometric
