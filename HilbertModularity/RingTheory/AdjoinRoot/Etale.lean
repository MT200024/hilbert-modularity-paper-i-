/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.FieldTheory.Separable

/-! # Étaleness of monic separable root algebras

A monic separable polynomial gives a standard étale presentation with
localizing polynomial one. The universal properties identify that presentation
with the actual root algebra.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {f : R[X]}

/-- Adjoining a root of a monic separable polynomial gives an étale algebra. -/
theorem etale_of_monic_of_separable (hm : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := (Polynomial.separable_def' f).mp hs
  let P : StandardEtalePair R :=
    { f := f
      monic_f := hm
      g := 1
      cond := ⟨b, a, 0, by simpa [mul_comm, add_comm] using hab⟩ }
  have hf : aeval (root f) f = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hx : P.HasMap (root f) := ⟨hf, by simp [P]⟩
  let φ : P.Ring →ₐ[R] AdjoinRoot f := P.lift (root f) hx
  let ψ : AdjoinRoot f →ₐ[R] P.Ring :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  have hφ : φ P.X = root f := P.lift_X (root f) hx
  have hψ : ψ (root f) = P.X :=
    AdjoinRoot.liftAlgHom_root f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  let e : P.Ring ≃ₐ[R] AdjoinRoot f := AlgEquiv.ofAlgHom φ ψ
    (by
      apply AdjoinRoot.algHom_ext
      exact (congrArg φ hψ).trans hφ)
    (by
      apply P.hom_ext
      exact (congrArg ψ hφ).trans hψ)
  exact Algebra.Etale.of_equiv e

end AdjoinRoot
