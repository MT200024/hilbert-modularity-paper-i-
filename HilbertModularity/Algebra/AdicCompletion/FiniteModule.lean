/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Generators of the completion of a finite module

The finite-module completion theorem gives algebraic generation by the
original module over the completed base ring. This allows completed scalar
actions to be compared on the original coefficients without a continuity
argument or a second extension of the module.
-/

public section

open scoped TensorProduct

namespace AdicCompletion

variable {R M : Type*} [CommRing R] (I : Ideal R)
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Induction using the original vectors and scalars in the completed base
ring, obtained from the canonical finite-module completion map. -/
theorem induction_on_of_finite (x : AdicCompletion I M)
    {P : AdicCompletion I M → Prop}
    (_zero : P 0)
    (smul_of : ∀ (r : AdicCompletion I R) (m : M), P (r • of I M m))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  obtain ⟨t, rfl⟩ := ofTensorProduct_surjective_of_finite I M x
  induction t using TensorProduct.inductionOn with
  | tmul r m => exact smul_of r m
  | add x y hx hy => simpa only [_root_.map_add] using add _ _ hx hy

/-- Completed-linear maps from a finite module's completion are determined
by their values on the original module. -/
theorem linearMap_ext_of_finite
    {N : Type*} [AddCommGroup N] [Module (AdicCompletion I R) N]
    {f g : AdicCompletion I M →ₗ[AdicCompletion I R] N}
    (h : ∀ m : M, f (of I M m) = g (of I M m)) : f = g := by
  apply LinearMap.ext
  intro x
  apply induction_on_of_finite I x (P := fun x => f x = g x)
  · simp only [_root_.map_zero]
  · intro r m
    simp only [_root_.map_smul, h m]
  · intro x y hx hy
    simp only [_root_.map_add, hx, hy]

end AdicCompletion
