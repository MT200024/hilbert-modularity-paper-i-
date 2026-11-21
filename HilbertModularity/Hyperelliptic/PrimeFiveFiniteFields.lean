/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Explicit quadratic finite fields and the level-five Euler counts

The concrete arithmetic computations for [TripathiGoswami] use two quadratic
extensions and one Euler test per field element. All finite computations are
checked by the Lean kernel.
-/

@[expose] public section

namespace HilbertModularity.Hyperelliptic

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 11, r ^ 2 ≠ 2 + 0 * r) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 41, r ^ 2 ≠ 3 + 0 * r) := ⟨by decide⟩

/-- The quadratic extension of `𝔽₁₁` obtained by adjoining a square root of two. -/
abbrev QuadraticField11 := QuadraticAlgebra (ZMod 11) 2 0

/-- The quadratic extension of `𝔽₄₁` obtained by adjoining a square root of three. -/
abbrev QuadraticField41 := QuadraticAlgebra (ZMod 41) 3 0

instance instFieldQuadraticField11 : Field QuadraticField11 := inferInstance
instance instFieldQuadraticField41 : Field QuadraticField41 := inferInstance

instance instFintypeQuadraticField11 : Fintype QuadraticField11 :=
  Fintype.ofEquiv (ZMod 11 × ZMod 11) (QuadraticAlgebra.equivProd 2 0).symm

instance instFintypeQuadraticField41 : Fintype QuadraticField41 :=
  Fintype.ofEquiv (ZMod 41 × ZMod 41) (QuadraticAlgebra.equivProd 3 0).symm

instance instCharPQuadraticField11 : CharP QuadraticField11 11 :=
  charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective 11

instance instCharPQuadraticField41 : CharP QuadraticField41 41 :=
  charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective 41

/-- The first explicit quadratic field has the required cardinality. -/
theorem quadraticField11_card : Fintype.card QuadraticField11 = 121 := by
  simpa using Fintype.card_congr (QuadraticAlgebra.equivProd (2 : ZMod 11) 0)

/-- The second explicit quadratic field has the required cardinality. -/
theorem quadraticField41_card : Fintype.card QuadraticField41 = 1681 := by
  simpa using Fintype.card_congr (QuadraticAlgebra.equivProd (3 : ZMod 41) 0)

/-- The affine point count obtained from Euler's criterion on the branch values. -/
def primeFiveEulerCount (K : Type*) [Field K] [Fintype K] [DecidableEq K] : ℕ :=
  ∑ x : K, let v := (x + 2) * (x ^ 5 - 5 * x ^ 3 + 5 * x + 2 - 500)
    if v = 0 then 1 else if npowBinRec (Fintype.card K / 2) v = 1 then 2 else 0

/-- The binary-power implementation agrees with the usual Euler-criterion formula. -/
theorem primeFiveEulerCount_eq (K : Type*) [Field K] [Fintype K] [DecidableEq K] :
    primeFiveEulerCount K =
      ∑ x : K, let v := (x + 2) * (x ^ 5 - 5 * x ^ 3 + 5 * x + 2 - 500)
        if v = 0 then 1 else if v ^ (Fintype.card K / 2) = 1 then 2 else 0 := by
  have hpow (z : K) (n : ℕ) : npowBinRec n z = z ^ n := by
    induction n with
    | zero => simp [npowBinRec_zero]
    | succ n ih => rw [npowBinRec_succ, pow_succ, ih]
  simp only [primeFiveEulerCount, hpow]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel computation of the affine count over the field of 121 elements. -/
theorem primeFive_euler_count_121 : primeFiveEulerCount QuadraticField11 = 161 := by
  unfold primeFiveEulerCount
  rw [quadraticField11_card]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel computation of the affine count over the field of 1681 elements. -/
theorem primeFive_euler_count_1681 : primeFiveEulerCount QuadraticField41 = 1781 := by
  unfold primeFiveEulerCount
  rw [quadraticField41_card]
  decide +kernel

end HilbertModularity.Hyperelliptic
