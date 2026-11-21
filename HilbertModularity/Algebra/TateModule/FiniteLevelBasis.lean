/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.TowerReduction
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Bases and sizes of actual finite Tate levels

An integral Tate basis reduces to a basis of each actual p-power torsion
module. Its cardinality is therefore the expected p-power determined by the
actual Tate rank, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

attribute [local instance] torsionCoefficientAlgebra torsionCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]
  [Module.Finite ℤ_[p] (integral p A)]

/-- A finite integral Tate basis reduces to an actual basis at every torsion level. -/
def finiteLevelBasis (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℤ_[p] (integral p A))) (ZMod (p ^ n)) (Torsion p A n) :=
  ((Module.finBasis ℤ_[p] (integral p A)).baseChange (ZMod (p ^ n))).map (finiteLevelEquiv p A hpdiv n)

/-- The finite-level basis vectors are the actual coordinates of the integral Tate basis. -/
@[simp]
theorem finiteLevelBasis_apply (hpdiv : Function.Surjective (fun a : A => p • a))
    (n : ℕ) (i : Fin (Module.finrank ℤ_[p] (integral p A))) :
    finiteLevelBasis p A hpdiv n i = projection p A n (Module.finBasis ℤ_[p] (integral p A) i) := by
  simp [finiteLevelBasis, Module.Basis.baseChange_apply]

/-- The actual p-power torsion cardinality is determined by the actual integral Tate rank. -/
theorem card_torsion (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    Nat.card (Torsion p A n) = p ^ (n * Module.finrank ℤ_[p] (integral p A)) := by
  rw [Nat.card_congr (finiteLevelBasis p A hpdiv n).equivFun.toEquiv]
  rw [Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin, ← pow_mul]

/-- The actual level-one torsion cardinality characterizes the integral Tate rank. -/
theorem finrank_eq_iff_card_torsion (hpdiv : Function.Surjective (fun a : A => p • a)) (d : ℕ) :
    Module.finrank ℤ_[p] (integral p A) = d ↔ Nat.card (Torsion p A 1) = p ^ d := by
  rw [card_torsion p A hpdiv 1, one_mul]
  exact ⟨fun h => congrArg (fun r => p ^ r) h,
    fun h => Nat.pow_right_injective (Fact.out : p.Prime).two_le h⟩

end TateModule
