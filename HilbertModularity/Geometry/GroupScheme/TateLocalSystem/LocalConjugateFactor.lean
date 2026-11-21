/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientTensor
public import HilbertModularity.NumberTheory.RealCyclotomicLabels

/-! # Actual idempotent factors of the local coefficient conjugates

The tensor-defined local coefficient conjugate is equivariantly the actual
embedding-idempotent Tate factor over the ramified completion. The completion
splits the real multiplication field by its proved normality, so no additional
splitting hypothesis is imposed. This identifies the two realizations of the
local label in [TripathiGoswami, ramified scalar label].
-/

@[expose] public noncomputable section
open CategoryTheory HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField TensorProduct
namespace AlgebraicGeometry.GroupScheme
variable (p k m : ℕ) [Fact p.Prime] (hm : m.Coprime (p ^ (k + 1)))

/-- The global multiplication embedding selected by the actual local coefficient automorphism. -/
def localConjugateTateLabel :
    realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] RealPrimePowerCompletion p k :=
  localTateCoefficientLabel p k (RealPrimePowerCompletion p k)
    (realPrimePowerCompletionAutomorphism p k m hm).toAlgHom

/-- The selected label is the original global power automorphism followed by completion. -/
theorem localConjugateTateLabel_apply (a : realCyclotomicField (p ^ (k + 1))) :
    localConjugateTateLabel p k m hm a =
      algebraMap _ (RealPrimePowerCompletion p k) (realPowerAutomorphism (p ^ (k + 1)) m hm a) :=
  realPrimePowerCompletionAutomorphism_algebraMap p k m hm a

/-- The local factor has exactly the prescribed exponent-labelled trace parameter. -/
@[simp] theorem localConjugateTateLabel_tau_one :
    localConjugateTateLabel p k m hm (tau (p ^ (k + 1)) 1) =
      algebraMap _ (RealPrimePowerCompletion p k) (tau (p ^ (k + 1)) m) := by
  rw [localConjugateTateLabel_apply, realPowerAutomorphism_tau_one]

/-- Every multiplication label in the actual completion is one of the native conjugate labels. -/
theorem exists_localConjugateTateLabel
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] RealPrimePowerCompletion p k) :
    ∃ m < p ^ (k + 1), ∃ hm : m.Coprime (p ^ (k + 1)),
      σ = localConjugateTateLabel p k m hm := by
  obtain ⟨m, hmN, hm, he⟩ := exists_powerEmbedding (p ^ (k + 1))
    (RealPrimePowerCompletion p k) σ
  refine ⟨m, hmN, hm, ?_⟩
  rw [he]
  apply AlgHom.ext
  intro a
  exact (localConjugateTateLabel_apply p k m hm a).symm

variable (K : Type) [Field K] {S : Scheme} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S)
  (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)

set_option maxHeartbeats 1000000 in
/-- The literal local scalar-conjugate representation is the actual exponent-labelled idempotent Tate factor. -/
def localConjugateTateFactorEquiv :
    (localConjugateTateRepresentation K A x p k φ m hm).ρ.Equiv
      (labelledTateSubrepresentation K (fiber K A x).X p
        (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k)
        (splits_minpoly_realPrimePowerCompletion p k)
        (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
        (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ)
        (localConjugateTateLabel p k m hm)).toRepresentation :=
  localCoefficientLabelledTateRepresentationEquiv p k (RealPrimePowerCompletion p k)
    (realPrimePowerCompletionAutomorphism p k m hm).toAlgHom K A x φ
    (splits_minpoly_realPrimePowerCompletion p k)

/-- The factor comparison is the actual idempotent projection on every pure conjugate tensor. -/
@[simp] theorem localConjugateTateFactorEquiv_tmul
    (a : RealPrimePowerCompletion p k) (v : rationalTate K (fiber K A x).X p) :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    ((localConjugateTateFactorEquiv p k m hm K A x φ)
      (a ⊗ₜ[RealPrimePowerCompletion p k] v) :
        RealPrimePowerCompletion p k ⊗[ℚ_[p]] rationalTate K (fiber K A x).X p) =
      labelledTateProjection K (fiber K A x).X p (realCyclotomicField (p ^ (k + 1)))
        (RealPrimePowerCompletion p k) (splits_minpoly_realPrimePowerCompletion p k)
        (fiberPointsAction K (AlgebraicClosure K) A x _ φ) (localConjugateTateLabel p k m hm)
        (a ⊗ₜ[ℚ_[p]] v) :=
  localCoefficientLabelledTateEquiv_tmul p k (RealPrimePowerCompletion p k)
    (realPrimePowerCompletionAutomorphism p k m hm).toAlgHom K A x φ
    (splits_minpoly_realPrimePowerCompletion p k) a v

/-- Every actual completed-coefficient idempotent factor is a native local scalar conjugate. -/
theorem exists_localConjugateTateFactorEquiv
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] RealPrimePowerCompletion p k) :
    ∃ m < p ^ (k + 1), ∃ hm : m.Coprime (p ^ (k + 1)), Nonempty
      ((localConjugateTateRepresentation K A x p k φ m hm).ρ.Equiv
        (labelledTateSubrepresentation K (fiber K A x).X p
          (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k)
          (splits_minpoly_realPrimePowerCompletion p k)
          (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
          (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ) σ).toRepresentation) := by
  obtain ⟨m, hmN, hm, rfl⟩ := exists_localConjugateTateLabel p k σ
  exact ⟨m, hmN, hm, ⟨localConjugateTateFactorEquiv p k m hm K A x φ⟩⟩

variable [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

set_option maxHeartbeats 1000000 in
/-- The actual m-labelled family arithmetic fibre is the literal native local scalar conjugate. -/
def labelledTateLocalSystemLocalConjugateEquiv :
    (Scheme.arithmeticFiberRepresentation K S
      (labelledTateLocalSystem K A p (RealPrimePowerCompletion p k) _ φ
        (splits_minpoly_realPrimePowerCompletion p k) (localConjugateTateLabel p k m hm)) x).Equiv
      (localConjugateTateRepresentation K A x p k φ m hm).ρ :=
  (labelledTateLocalSystem_arithmeticEquiv K A p (RealPrimePowerCompletion p k) x _ φ
    (splits_minpoly_realPrimePowerCompletion p k) (localConjugateTateLabel p k m hm)).trans
      (localConjugateTateFactorEquiv p k m hm K A x φ).symm

/-- The arithmetic fibre of every labelled local family is one of the actual native conjugates. -/
theorem exists_labelledTateLocalSystemLocalConjugateEquiv
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] RealPrimePowerCompletion p k) :
    ∃ m < p ^ (k + 1), ∃ hm : m.Coprime (p ^ (k + 1)), Nonempty
      ((Scheme.arithmeticFiberRepresentation K S
        (labelledTateLocalSystem K A p (RealPrimePowerCompletion p k) _ φ
          (splits_minpoly_realPrimePowerCompletion p k) σ) x).Equiv
        (localConjugateTateRepresentation K A x p k φ m hm).ρ) := by
  obtain ⟨m, hmN, hm, rfl⟩ := exists_localConjugateTateLabel p k σ
  exact ⟨m, hmN, hm, ⟨labelledTateLocalSystemLocalConjugateEquiv p k m hm K A x φ⟩⟩

end AlgebraicGeometry.GroupScheme
