/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricFamily
public import HilbertModularity.Geometry.GroupScheme.StandardInertiaIrreducibility
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientArithmeticMonodromy
public import HilbertModularity.Geometry.ProjectiveLine.GenericFundamentalGroup
public import HilbertModularity.RepresentationTheory.Quotient
public import HilbertModularity.LinearAlgebra.CoefficientTensorFactor
public import HilbertModularity.Monodromy.AbsoluteIrreducibility
public import HilbertModularity.Geometry.ProjectiveLine.CuspArithmetic

/-! # Irreducibility of the chosen Darmon monodromy

The simultaneous inertia basis from [DarmonFibres, Propositions 3.2 and 3.4]
contains two transverse transvections. Evaluating the coefficient tensor algebra
at any field-valued embedding preserves their distinct fixed lines, as in
[TripathiGoswami, admissible triple lemma].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic Algebra.TensorProduct

/-- Every field-valued coefficient specialization of the actual native generic
Tate monodromy of the single chosen Darmon family is irreducible. -/
theorem darmonCoefficientMonodromy_specialization_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    let V := TateModule.rational p
      (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ (darmonFamily N hN).X))
    letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
      Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
        (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
      (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
    ((GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).baseChange L).IsIrreducible := by
  exact HasStandardInertiaRealization.specialization_isIrreducible N hN
    (darmonFamily N hN) (darmonRealMultiplication N hN)
    (fun n hn => @darmonFamily_multiplication_isFinite N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (fun n hn => @darmonFamily_multiplication_etale N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (darmonFamily_inertia_realization N hN) p L σ

/-- The same field-valued specialization is irreducible on the kernel of the
actual structure-map action on finite étale covers of the constant field. -/
theorem darmonCoefficientMonodromy_arithmeticKernel_specialization_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    let V := TateModule.rational p
      (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ (darmonFamily N hN).X))
    letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
      Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
        (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
      (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
    (Representation.baseChange L ((GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).comp
        (Scheme.etaleFundamentalGroupMap
          (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
          (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype)).IsIrreducible := by
  exact HasStandardInertiaRealization.arithmeticKernel_specialization_isIrreducible N hN
    (darmonFamily N hN) (darmonRealMultiplication N hN)
    (fun n hn => @darmonFamily_multiplication_isFinite N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (fun n hn => @darmonFamily_multiplication_etale N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (darmonFamily_inertia_realization N hN) p L σ

/-- Every coefficient-labelled generic Tate factor is geometrically irreducible:
the two finite cusp generators lie in the actual arithmetic kernel. -/
theorem darmonLabelledMonodromy_arithmeticKernel_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    Representation.IsIrreducible
      ((Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N))
        (GroupScheme.labelledTateLocalSystem (RatFunc (realCyclotomicField N))
          (darmonFamily N hN) p L (realCyclotomicField N)
          (darmonRealMultiplication N hN) hL σ)
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).comp
          (Scheme.etaleFundamentalGroupMap
            (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
            (RatFunc (realCyclotomicField N))
            (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype) := by
  let V := TateModule.rational p
    (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ (darmonFamily N hN).X))
  let : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
    Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
  let e := (GroupScheme.coefficientTateMonodromyLabelledEquiv
    (RatFunc (realCyclotomicField N)) (darmonFamily N hN)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) p
    (realCyclotomicField N) (darmonRealMultiplication N hN) L hL σ
    (ProjectiveLine.puncturedRationalPoint_galoisToEtaleFundamentalGroup_surjective
      (realCyclotomicField N))).compHom
        (Scheme.etaleFundamentalGroupMap
          (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
          (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype
  exact (OrderIso.isSimpleOrder_iff e.subrepresentationOrderIso).mp
    (darmonCoefficientMonodromy_arithmeticKernel_specialization_isIrreducible N hN p L σ)

end HilbertModularity.Hypergeometric
