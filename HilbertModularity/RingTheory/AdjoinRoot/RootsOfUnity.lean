/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Roots of unity acting on Kummer root algebras

The scaling action on a root of `X^n-a` is defined over an arbitrary
commutative coefficient ring. This extends the field-case construction in
[mathlib_5ed296525643] to the coordinate rings of the Euler family.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- The defining power relation for the actual Kummer root algebra over a commutative ring. -/
theorem root_X_pow_sub_C_pow (n : ℕ) (a : R) :
    root (X ^ n - C a) ^ n = of (X ^ n - C a) a := by
  have h : mk (X ^ n - C a) (X ^ n - C a) = 0 := mk_self
  rw [map_sub, map_pow, mk_X, mk_C] at h
  exact sub_eq_zero.mp h

/-- Roots of unity scale the adjoined coordinate through actual algebra endomorphisms. -/
def rootScalingEnd (n : ℕ) (a : R) :
    rootsOfUnity n R →* (AdjoinRoot (X ^ n - C a) →ₐ[R] AdjoinRoot (X ^ n - C a)) where
  toFun η := liftAlgHom (X ^ n - C a) (Algebra.ofId _ _)
    (((η : Rˣ) : R) • root (X ^ n - C a)) (by
      have hη := (mem_rootsOfUnity' n (η : Rˣ)).mp η.property
      change aeval _ _ = _
      rw [map_sub, map_pow, aeval_C, aeval_X, Algebra.smul_def, mul_pow,
        root_X_pow_sub_C_pow, algebraMap_eq, ← map_pow, hη, map_one, one_mul, sub_self])
  map_one' := by
    apply algHom_ext
    simp
  map_mul' ε η := by
    apply algHom_ext
    simp [mul_smul, smul_comm ((ε : Rˣ) : R)]

/-- The scaling endomorphisms form an action by algebra automorphisms. -/
def rootScaling (n : ℕ) (a : R) :
    rootsOfUnity n R →* (AdjoinRoot (X ^ n - C a) ≃ₐ[R] AdjoinRoot (X ^ n - C a)) :=
  (AlgEquiv.algHomUnitsEquiv R _).toMonoidHom.comp (rootScalingEnd n a).toHomUnits

set_option backward.isDefEq.respectTransparency.types false in
/-- The algebraic action sends the actual covering coordinate to its specified scalar multiple. -/
theorem rootScaling_root (n : ℕ) (a : R) (η : rootsOfUnity n R) :
    rootScaling n a η (root (X ^ n - C a)) = ((η : Rˣ) : R) • root (X ^ n - C a) := by
  dsimp [rootScaling, rootScalingEnd, AlgEquiv.algHomUnitsEquiv]
  exact liftAlgHom_root (X ^ n - C a) (Algebra.ofId R _) _ _

end AdjoinRoot
