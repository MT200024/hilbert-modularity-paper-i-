/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Reduction

/-! # Reduction of Tate modules at all finite levels

Surjectivity at level one lifts inductively to every torsion level. Together
with the exact projection kernel, this identifies each finite scalar reduction
with the actual torsion group, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- Divisibility of the point group makes every actual Tate projection surjective. -/
theorem projection_surjective (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    Function.Surjective (projection p A n) := by
  induction n with
  | zero =>
    intro x
    refine ⟨0, ?_⟩
    apply Subtype.ext
    change (0 : A) = (x : A)
    have hx := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    simpa only [pow_zero, one_nsmul] using hx.symm
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := ih (transition p A n x)
    let d : Torsion p A 1 := ⟨(x : A) - (projection p A (n + 1) y : A), by
      rw [AddSubgroup.torsionBy.nsmul_iff, pow_one, nsmul_sub,
        nsmul_projection]
      exact sub_eq_zero.mpr (congrArg Subtype.val hy).symm⟩
    obtain ⟨z, hz⟩ := projection_one_surjective p A hpdiv d
    refine ⟨y + (p : ℤ_[p]) ^ n • z, ?_⟩
    apply Subtype.ext
    change (projection p A (n + 1) y : A) + (projection p A (n + 1) ((p : ℤ_[p]) ^ n • z) : A) = (x : A)
    have hpow : (projection p A (n + 1) ((p : ℤ_[p]) ^ n • z) : A) = (projection p A 1 z : A) := by
      rw [show (p : ℤ_[p]) ^ n = ((p ^ n : ℕ) : ℤ_[p]) by simp, Nat.cast_smul_eq_nsmul]
      rw [map_nsmul]
      change p ^ n • (projection p A (n + 1) z : A) = _
      rw [show n + 1 = 1 + n by omega]
      exact pow_nsmul_projection p A 1 n z
    rw [hpow]
    have hz' : (projection p A 1 z : A) = (x : A) - (projection p A (n + 1) y : A) := congrArg Subtype.val hz
    rw [hz']
    rw [← add_sub_assoc, add_sub_cancel_left]

/-- Quotienting the actual Tate module by `p^n` gives the actual `p^n`-torsion. -/
def powerReductionEquiv (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    ((integral p A) ⧸
      ((Ideal.span {(p : ℤ_[p]) ^ n}) • (⊤ : Submodule ℤ_[p] (integral p A)))) ≃ₗ[ℤ_[p]]
        Torsion p A n :=
  (Submodule.quotEquivOfEq _ _ (ker_projection p A n).symm).trans
    ((projection p A n).quotKerEquivOfSurjective (projection_surjective p A hpdiv n))

attribute [local instance] torsionCoefficientAlgebra torsionCoefficientScalarTower

/-- Scalar reduction at any finite level is the actual torsion module. -/
def finiteLevelEquiv (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    (ZMod (p ^ n) ⊗[ℤ_[p]] integral p A) ≃ₗ[ZMod (p ^ n)] Torsion p A n :=
  LinearEquiv.ofBijective (residualProjection p A n)
    (residualProjection_bijective p A n (projection_surjective p A hpdiv n))

/-- The finite-level comparison evaluates the original compatible family. -/
@[simp]
theorem finiteLevelEquiv_tmul (hpdiv : Function.Surjective (fun a : A => p • a))
    (n : ℕ) (a : ZMod (p ^ n)) (x : integral p A) :
    finiteLevelEquiv p A hpdiv n (a ⊗ₜ[ℤ_[p]] x) = a • projection p A n x := rfl

end TateModule
