/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalConjugateFactor
public import HilbertModularity.RepresentationTheory.ScalarConjugationInvariants

/-! # Determinants of the actual local RM labels

The native scalar-conjugate Tate representation and its actual embedding-idempotent
factor have conjugate determinants. A determinant valued in the rational p-adic
scalars is therefore the same at every local label. This is the label-transport
step in [TripathiGoswami, prime determinant]; it does not prove the determinant
formula for the original native representation.
-/

@[expose] public noncomputable section
open CategoryTheory HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField
namespace AlgebraicGeometry.GroupScheme
variable (p k m : ℕ) [Fact p.Prime] (hm : m.Coprime (p ^ (k + 1)))
  (K : Type) [Field K] {S : Scheme} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S)
  (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)
  [Module.Finite (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ)]

/-- Finite native Tate rank gives finite rank for each actual local coefficient conjugate. -/
instance localConjugateTateRepresentation_finite :
    Module.Finite (RealPrimePowerCompletion p k)
      (localConjugateTateRepresentation K A x p k φ m hm) := by
  change Module.Finite (RealPrimePowerCompletion p k)
    (Rep.scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
      (localCoefficientTateRep K A x p k φ))
  infer_instance

/-- The characteristic polynomial of the actual local Tate conjugate is the native polynomial
with its coefficients acted on by the actual local coefficient automorphism. -/
theorem charpoly_localConjugateTateRepresentation
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ((localConjugateTateRepresentation K A x p k φ m hm).ρ g).charpoly =
      ((localCoefficientTateRep K A x p k φ).ρ g).charpoly.map
        (realPrimePowerCompletionAutomorphism p k m hm).toRingHom :=
  Rep.charpoly_scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (localCoefficientTateRep K A x p k φ) g

/-- The determinant of the actual local Tate conjugate is the native determinant conjugated. -/
theorem det_localConjugateTateRepresentation
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det ((localConjugateTateRepresentation K A x p k φ m hm).ρ g) =
      realPrimePowerCompletionAutomorphism p k m hm
        (LinearMap.det ((localCoefficientTateRep K A x p k φ).ρ g)) :=
  Rep.det_scalarConjugate (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (localCoefficientTateRep K A x p k φ) g

/-- The actual embedding-idempotent Tate factor has the conjugate native determinant. -/
theorem det_localConjugateTateFactor
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det (M := (labelledTateSubrepresentation K (fiber K A x).X p
      (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k)
      (splits_minpoly_realPrimePowerCompletion p k)
      (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
      (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ)
      (localConjugateTateLabel p k m hm)).toSubmodule) ((labelledTateSubrepresentation K (fiber K A x).X p
      (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k)
      (splits_minpoly_realPrimePowerCompletion p k)
      (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
      (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ)
      (localConjugateTateLabel p k m hm)).toRepresentation g) =
      realPrimePowerCompletionAutomorphism p k m hm
        (LinearMap.det ((localCoefficientTateRep K A x p k φ).ρ g)) := by
  exact (localConjugateTateFactorEquiv p k m hm K A x φ).det_eq g |>.trans
    (det_localConjugateTateRepresentation p k m hm K A x φ g)


/-- Rational p-adic determinant values are unchanged at every native coefficient conjugate. -/
theorem det_localConjugateTateRepresentation_of_rational
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (d : ℚ_[p])
    (hd : LinearMap.det ((localCoefficientTateRep K A x p k φ).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) d) :
    LinearMap.det ((localConjugateTateRepresentation K A x p k φ m hm).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) d := by
  rw [det_localConjugateTateRepresentation, hd, AlgEquiv.commutes]

/-- Every actual idempotent label has the same determinant when the native determinant
comes from the rational p-adic scalars. -/
theorem det_labelledTateSubrepresentation_of_rational
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] RealPrimePowerCompletion p k)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (d : ℚ_[p])
    (hd : LinearMap.det ((localCoefficientTateRep K A x p k φ).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) d) :
    LinearMap.det (M := (labelledTateSubrepresentation K (fiber K A x).X p
      (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k)
      (splits_minpoly_realPrimePowerCompletion p k)
      (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
      (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ) σ).toSubmodule)
      ((labelledTateSubrepresentation K (fiber K A x).X p
      (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k)
      (splits_minpoly_realPrimePowerCompletion p k)
      (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
      (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ) σ).toRepresentation g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) d := by
  exact (exists_localConjugateTateFactorEquiv p k K A x φ σ).elim fun a h =>
    h.2.elim fun ha he => he.elim fun e =>
      (e.det_eq g).trans
        (det_localConjugateTateRepresentation_of_rational p k a ha K A x φ g d hd)

variable [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The same rational determinant belongs to the actual arithmetic fibre of every labelled
Tate local system, by its checked comparison with the native coefficient conjugate. -/
theorem det_labelledTateLocalSystem_of_rational
    (σ : realCyclotomicField (p ^ (k + 1)) →ₐ[ℚ] RealPrimePowerCompletion p k)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (d : ℚ_[p])
    (hd : LinearMap.det ((localCoefficientTateRep K A x p k φ).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) d) :
    LinearMap.det (Scheme.arithmeticFiberRepresentation K S
      (labelledTateLocalSystem K A p (RealPrimePowerCompletion p k) _ φ
        (splits_minpoly_realPrimePowerCompletion p k) σ) x g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) d := by
  obtain ⟨a, _, ha, ⟨e⟩⟩ := exists_labelledTateLocalSystemLocalConjugateEquiv p k K A x φ σ
  exact (e.det_eq g).symm.trans
    (det_localConjugateTateRepresentation_of_rational p k a ha K A x φ g d hd)

end AlgebraicGeometry.GroupScheme
