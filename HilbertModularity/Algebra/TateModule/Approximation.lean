/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.TowerReduction
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite-level approximation by level-one Tate lifts

Lifts of all level-one torsion points generate every finite projection of the
actual Tate module. This is the algebraic approximation step in finite Tate
generation used in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- Choose an actual compatible Tate lift of each level-one torsion point. -/
def levelOneLift (hpdiv : Function.Surjective (fun a : A => p • a))
    (x : Torsion p A 1) : integral p A :=
  Classical.choose (projection_one_surjective p A hpdiv x)

@[simp]
theorem projection_levelOneLift (hpdiv : Function.Surjective (fun a : A => p • a))
    (x : Torsion p A 1) : projection p A 1 (levelOneLift p A hpdiv x) = x :=
  Classical.choose_spec (projection_one_surjective p A hpdiv x)

/-- The integral submodule spanned by lifts of all actual level-one torsion points. -/
def levelOneSpan (hpdiv : Function.Surjective (fun a : A => p • a)) :
    Submodule ℤ_[p] (integral p A) := Submodule.span ℤ_[p] (Set.range (levelOneLift p A hpdiv))

/-- Finitely many level-one torsion points give a finitely generated lifted submodule. -/
theorem levelOneSpan_fg [Finite (Torsion p A 1)]
    (hpdiv : Function.Surjective (fun a : A => p • a)) : (levelOneSpan p A hpdiv).FG :=
  Submodule.fg_span (Set.finite_range (levelOneLift p A hpdiv))

/-- The lifted submodule realizes every actual finite torsion coordinate. -/
theorem exists_levelOneSpan_projection
    (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) (x : Torsion p A n) :
    ∃ y ∈ levelOneSpan p A hpdiv, projection p A n y = x := by
  induction n with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    apply Subtype.ext
    change (0 : A) = (x : A)
    have hx := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    simpa only [pow_zero, one_nsmul] using hx.symm
  | succ n ih =>
    obtain ⟨y, hym, hy⟩ := ih (transition p A n x)
    let d : Torsion p A 1 := ⟨(x : A) - (projection p A (n + 1) y : A), by
      rw [AddSubgroup.torsionBy.nsmul_iff, pow_one, nsmul_sub, nsmul_projection]
      exact sub_eq_zero.mpr (congrArg Subtype.val hy).symm⟩
    let z := levelOneLift p A hpdiv d
    have hz : projection p A 1 z = d := projection_levelOneLift p A hpdiv d
    have hzm : z ∈ levelOneSpan p A hpdiv := Submodule.subset_span ⟨d, rfl⟩
    refine ⟨y + (p : ℤ_[p]) ^ n • z, Submodule.add_mem _ hym (Submodule.smul_mem _ _ hzm), ?_⟩
    apply Subtype.ext
    change (projection p A (n + 1) y : A) +
      (projection p A (n + 1) ((p : ℤ_[p]) ^ n • z) : A) = (x : A)
    have hpow : (projection p A (n + 1) ((p : ℤ_[p]) ^ n • z) : A) =
        (projection p A 1 z : A) := by
      rw [show (p : ℤ_[p]) ^ n = ((p ^ n : ℕ) : ℤ_[p]) by simp, Nat.cast_smul_eq_nsmul,
        map_nsmul]
      change p ^ n • (projection p A (n + 1) z : A) = _
      rw [show n + 1 = 1 + n by omega]
      exact pow_nsmul_projection p A 1 n z
    rw [hpow]
    have hz' : (projection p A 1 z : A) = (x : A) - (projection p A (n + 1) y : A) :=
      congrArg Subtype.val hz
    rw [hz', ← add_sub_assoc, add_sub_cancel_left]

/-- Agreement at a finite Tate level implies agreement at every lower level. -/
theorem projection_eq_of_le {k n : ℕ} (hkn : k ≤ n) {x y : integral p A}
    (h : projection p A n x = projection p A n y) : projection p A k x = projection p A k y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  apply Subtype.ext
  exact (pow_nsmul_projection p A k d x).symm.trans
    ((congrArg (fun z : Torsion p A (k + d) => p ^ d • (z : A)) h).trans
      (pow_nsmul_projection p A k d y))

end TateModule
