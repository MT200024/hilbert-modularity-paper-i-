/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Transitivity of full Frobenius polynomials across three carriers

The special Tate space, good-model generic Tate space, and selected Jacobian
Tate space are abstract here. Each comparison constructs a basis on its target
from a supplied source basis. The two comparisons compose without unfolding
the dependent residue field or group-scheme model.
-/

public noncomputable section

namespace HilbertModularity.Examples

/-- Compose two basis-level reverse-characteristic-polynomial comparisons
before inserting the selected curve, model and coefficient field. -/
theorem charpolyRev_basis_transport_trans
    {R Vₛ Vₘ Vₐ ι : Type*} [Field R]
    [AddCommGroup Vₛ] [Module R Vₛ]
    [AddCommGroup Vₘ] [Module R Vₘ]
    [AddCommGroup Vₐ] [Module R Vₐ]
    [Fintype ι] [DecidableEq ι]
    (fₛ : Module.End R Vₛ) (fₘ : Module.End R Vₘ)
    (fₐ : Module.End R Vₐ)
    (hₛₘ : ∀ bₛ : Module.Basis ι R Vₛ,
      ∃ bₘ : Module.Basis ι R Vₘ,
        (LinearMap.toMatrix bₘ bₘ fₘ).charpolyRev =
          (LinearMap.toMatrix bₛ bₛ fₛ).charpolyRev)
    (hₘₐ : ∀ bₘ : Module.Basis ι R Vₘ,
      ∃ bₐ : Module.Basis ι R Vₐ,
        (LinearMap.toMatrix bₐ bₐ fₐ).charpolyRev =
          (LinearMap.toMatrix bₘ bₘ fₘ).charpolyRev)
    (bₛ : Module.Basis ι R Vₛ) :
    ∃ bₐ : Module.Basis ι R Vₐ,
      (LinearMap.toMatrix bₐ bₐ fₐ).charpolyRev =
        (LinearMap.toMatrix bₛ bₛ fₛ).charpolyRev := by
  obtain ⟨bₘ, hₘ⟩ := hₛₘ bₛ
  obtain ⟨bₐ, hₐ⟩ := hₘₐ bₘ
  exact ⟨bₐ, hₐ.trans hₘ⟩

/-- An equivariant linear equivalence transports a full reverse
characteristic polynomial from any chosen source basis. -/
theorem exists_charpolyRev_basis_of_conj
    {R Vₛ Vₙ ι : Type*} [Field R]
    [AddCommGroup Vₛ] [Module R Vₛ]
    [AddCommGroup Vₙ] [Module R Vₙ]
    [Fintype ι] [DecidableEq ι]
    (fₛ : Module.End R Vₛ) (fₙ : Module.End R Vₙ)
    (e : Vₛ ≃ₗ[R] Vₙ) (he : e.conj fₛ = fₙ)
    (bₛ : Module.Basis ι R Vₛ) (P : Polynomial R)
    (hP : (LinearMap.toMatrix bₛ bₛ fₛ).charpolyRev = P) :
    ∃ bₙ : Module.Basis ι R Vₙ,
      (LinearMap.toMatrix bₙ bₙ fₙ).charpolyRev = P := by
  refine ⟨bₛ.map e, ?_⟩
  have hm : LinearMap.toMatrix (bₛ.map e) (bₛ.map e) (e.conj fₛ) =
      LinearMap.toMatrix bₛ bₛ fₛ := by
    rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
    congr 1
    ext v
    change e.symm (e.conj fₛ (e v)) = fₛ v
    simp [LinearEquiv.conj_apply]
  have hfirst := congrArg (fun f =>
    (LinearMap.toMatrix (bₛ.map e) (bₛ.map e) f).charpolyRev) he.symm
  have hsecond := congrArg Matrix.charpolyRev hm
  exact (hfirst.trans hsecond).trans hP

end HilbertModularity.Examples
