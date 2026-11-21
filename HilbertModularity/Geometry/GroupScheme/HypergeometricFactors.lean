/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricFamily
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Cyclotomic

/-! # Coefficient factors of the chosen Darmon family

The exponent label changes the primitive coefficient idempotent, while the
abelian scheme remains the single family selected from [DarmonFibres].
The construction and its arithmetic specialization use the same natural
projector, as in [TripathiGoswami, coefficient-label lemma].
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The actual scalar-extended Darmon Tate family splits equivariantly into its
embedding-labelled idempotent images. This natural isomorphism applies at every fibre. -/
def darmonTateDecomposition (K : Type) [Field K] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits) :
    GroupScheme.extendedTateLocalSystem K (darmonFamily N hN) p L ≅
      CategoryTheory.Limits.biproduct (fun σ : realCyclotomicField N →ₐ[ℚ] L =>
        GroupScheme.labelledTateLocalSystem K (darmonFamily N hN) p L
          (realCyclotomicField N) (darmonRealMultiplication N hN) hL σ) :=
  GroupScheme.labelledTateLocalSystemDecomposition K (darmonFamily N hN) p L
    (realCyclotomicField N) (darmonRealMultiplication N hN) hL

variable (K : Type) [Field K] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- The actual exponent-labelled idempotent image of the one Darmon Tate family.
For the manuscript this is used with a finite coefficient extension `L`. The
construction also works over any normed extension with the displayed actions. -/
def darmonLabelledTateFamily :
    Scheme.EtaleLocalSystem K (ProjectiveLine.punctured (realCyclotomicField N)) L :=
  labelledTateFamilyAtPrime K (darmonFamily N hN) p N m hm E hE w L
    (darmonRealMultiplication N hN)

/-- Arithmetic specialization is the same idempotent summand of the native Tate
module of the actual scheme-theoretic fibre. -/
def darmonLabelledTateFamily_arithmeticEquiv
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N)) :
    Representation.Equiv
      ((darmonLabelledTateFamily K N hN p m hm E hE w L).arithmeticRepresentation x)
      (GroupScheme.labelledTateSubrepresentation K (GroupScheme.fiber K (darmonFamily N hN) x).X p
        (realCyclotomicField N) L (splits_minpoly_above_coefficientPrime N E w L hE)
        (GroupScheme.fiberPointsAction K (AlgebraicClosure K) (darmonFamily N hN) x
          (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
        (GroupScheme.fiberPointsAction_realized K (AlgebraicClosure K) (darmonFamily N hN) x
          (𝓞 (realCyclotomicField N)) (darmonRealMultiplication N hN))
        (coefficientEmbeddingAbovePrime N m hm E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)).toRepresentation :=
  labelledTateFamilyAtPrime_arithmeticEquiv K (darmonFamily N hN) p N m hm E hE w L
    (darmonRealMultiplication N hN) x

/-- The labelled module is defined at the actual generic geometric point. -/
abbrev darmonGenericLabelledTateModule :=
  (darmonLabelledTateFamily (RatFunc (realCyclotomicField N)) N hN p m hm E hE w L).algebraicFunctor.obj (Scheme.etaleFiberPoint (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))

/-- The actual generic arithmetic fundamental group acts on the labelled summand. -/
def darmonGenericLabelledTateMonodromy :
    Representation L
      (Scheme.etaleFundamentalGroup (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      (darmonGenericLabelledTateModule N hN p m hm E hE w L) :=
  Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
    (ProjectiveLine.punctured (realCyclotomicField N))
    (darmonLabelledTateFamily (RatFunc (realCyclotomicField N)) N hN p m hm E hE w L).algebraicFunctor
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))

/-- Every exponent-labelled generic factor of the selected family has dimension two. -/
theorem finrank_darmonGenericLabelledTateModule :
    Module.finrank L (darmonGenericLabelledTateModule N hN p m hm E hE w L) = 2 :=
  finrank_darmonLabelledTateLocalSystem N hN p L
    (splits_minpoly_above_coefficientPrime N E w L hE)
    (coefficientEmbeddingAbovePrime N m hm E
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L)

end HilbertModularity.Hypergeometric
