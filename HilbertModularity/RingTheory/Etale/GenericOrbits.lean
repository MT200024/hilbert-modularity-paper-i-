/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.Smooth.Idempotents
public import HilbertModularity.FieldTheory.AlgebraicClosure.EmbeddingOrbits
public import Mathlib.RingTheory.Etale.Finite

/-! # Galois orbits of generic fibres detected over the original base

For a finite étale algebra over an integrally closed base, the idempotent
selecting an arithmetic orbit in the generic fibre descends to the original algebra.
-/

@[expose] public section
open scoped TensorProduct
namespace Algebra.TensorProduct
variable (R S F : Type*) [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [Algebra R S] [Algebra.Etale R S] [Module.Finite R S]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- An idempotent in the original finite étale algebra detects a chosen Galois
orbit of points of its generic fibre. -/
theorem exists_idempotent_genericGaloisOrbit_indicator
    (φ : F ⊗[R] S →ₐ[F] AlgebraicClosure F) :
    ∃ e : S, IsIdempotentElem e ∧ ∀ ψ : F ⊗[R] S →ₐ[F] AlgebraicClosure F,
      ψ ((1 : F) ⊗ₜ[R] e) = 1 ↔
        ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, g.toAlgHom.comp φ = ψ := by
  have : IsArtinianRing (F ⊗[R] S) := isArtinian_of_tower F inferInstance
  obtain ⟨z, hz, hdetect⟩ := AlgHom.exists_idempotent_galoisOrbit_indicator F (F ⊗[R] S) φ
  obtain ⟨e, ⟨he, hez⟩, _⟩ := existsUnique_includeRight_idempotent R S F z hz
  refine ⟨e, he, fun ψ => ?_⟩
  change ψ ((includeRight : S →ₐ[R] F ⊗[R] S) e) = 1 ↔ _
  rw [hez]
  exact hdetect ψ

end Algebra.TensorProduct
