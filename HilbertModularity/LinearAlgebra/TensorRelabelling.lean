/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar extension after relabelling the coefficient ring

A semilinear identification becomes linear after changing the coefficient map
by the same ring isomorphism. This transports the specified real-multiplication
action to the action in [DarmonMestre, Proposition 2.1 and Section 4].
-/

public section

open scoped TensorProduct

namespace LinearEquiv

variable {R S F M N : Type*} [CommRing R] [CommRing S] [CommRing F]
  [Algebra R F] [Algebra S F]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (σ : R ≃+* S) (hσ : ∀ r, algebraMap S F (σ r) = algebraMap R F r)

local instance : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

local instance : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- The identity on the target coefficient ring is semilinear for compatible labels. -/
def coefficientRelabelling : F ≃ₛₗ[σ.toRingHom] F where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r a := by
    simp only [id_eq, Algebra.smul_def]
    change algebraMap R F r * a = algebraMap S F (σ r) * a
    rw [hσ]

/-- Relabel both tensorands along a ring isomorphism, preserving target scalars. -/
def baseChangeRelabelling (e : M ≃ₛₗ[σ.toRingHom] N) : (F ⊗[R] M) ≃ₗ[F] (F ⊗[S] N) := by
  let t := TensorProduct.congr (coefficientRelabelling σ hσ) e
  refine { t.toAddEquiv with map_smul' := ?_ }
  intro a x
  change t (a • x) = a • t x
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    change TensorProduct.congr (coefficientRelabelling σ hσ) e (a • (b ⊗ₜ[R] m)) =
      a • TensorProduct.congr (coefficientRelabelling σ hσ) e (b ⊗ₜ[R] m)
    simp only [TensorProduct.smul_tmul', TensorProduct.congr_tmul]
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The transport fixes the coefficient and applies the original semilinear map. -/
@[simp] theorem baseChangeRelabelling_tmul (e : M ≃ₛₗ[σ.toRingHom] N) (a : F) (m : M) :
    baseChangeRelabelling σ hσ e (a ⊗ₜ[R] m) = a ⊗ₜ[S] e m := by
  rfl

end LinearEquiv
