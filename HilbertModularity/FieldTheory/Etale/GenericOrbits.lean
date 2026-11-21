/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.Etale.Idempotents
public import HilbertModularity.RingTheory.Etale.GenericOrbits

/-! # Natural automorphisms and arithmetic generic-fibre orbits

Over a normal base, the generic-fibre orbit idempotents already belong to the
original finite étale algebra. Naturality therefore preserves each arithmetic
Galois orbit in its geometric fibre.
-/

@[expose] public section
open CategoryTheory Opposite
open scoped TensorProduct
namespace CommAlgCat.FiniteEtale
universe u v
variable (R : Type u) [CommRing R] [IsIntegrallyClosed R]
  (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

/-- A natural endomorphism of geometric fibres sends each point into its actual
arithmetic Galois orbit at the generic point. -/
theorem fiberEnd_mem_genericGaloisOrbit
    (α : End (fiber.{u} R (AlgebraicClosure F))) (A : FiniteEtale.{u} R)
    (φ : A.obj →ₐ[R] AlgebraicClosure F) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      (g.toAlgHom.restrictScalars R).comp φ = α.app (op A) φ := by
  let E := AlgHom.liftEquiv R F A.obj (AlgebraicClosure F)
  obtain ⟨e, he, hdetect⟩ :=
    Algebra.TensorProduct.exists_idempotent_genericGaloisOrbit_indicator R A.obj F (E φ)
  have hself : E φ ((1 : F) ⊗ₜ[R] e) = 1 :=
    (hdetect (E φ)).mpr ⟨1, by ext; rfl⟩
  have heφ : φ e = 1 := by
    simpa only [E, AlgHom.liftEquiv_tmul, one_smul] using hself
  have heαφ : DFunLike.coe (F := A.obj →ₐ[R] AlgebraicClosure F) (α.app (op A) φ) e = 1 :=
    (fiberEnd_preserves_idempotent R (AlgebraicClosure F) α A e he φ).trans heφ
  have hpoint : E (α.app (op A) φ) ((1 : F) ⊗ₜ[R] e) = 1 := by
    change (1 : F) • DFunLike.coe (F := A.obj →ₐ[R] AlgebraicClosure F)
      (α.app (op A) φ) e = 1
    simpa only [one_smul] using heαφ
  obtain ⟨g, hg⟩ := (hdetect (E (α.app (op A) φ))).mp hpoint
  refine ⟨g, ?_⟩
  apply AlgHom.ext
  intro a
  have h := AlgHom.congr_fun hg ((1 : F) ⊗ₜ[R] a)
  change g (E φ ((1 : F) ⊗ₜ[R] a)) = E (α.app (op A) φ) ((1 : F) ⊗ₜ[R] a) at h
  change g ((1 : F) • φ a) =
    (1 : F) • DFunLike.coe (F := A.obj →ₐ[R] AlgebraicClosure F) (α.app (op A) φ) a at h
  change g (φ a) =
    DFunLike.coe (F := A.obj →ₐ[R] AlgebraicClosure F) (α.app (op A) φ) a
  simpa only [one_smul] using h

end CommAlgCat.FiniteEtale
