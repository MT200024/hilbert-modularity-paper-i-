module

public import HilbertModularity.Examples.PrimeFiveHypergeometric
public import HilbertModularity.Hypergeometric.EulerSum
public import HilbertModularity.Hyperelliptic.PrimeFiveFiniteFields
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! # The oriented residue field and the McCarthy value at 19 -/

@[expose] public section
namespace HilbertModularity.PaperI.Nineteen
open HilbertModularity.Examples HilbertModularity.Hyperelliptic HilbertModularity.Hypergeometric

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 19, r^2 ≠ 2 + 0*r) := ⟨by decide⟩
abbrev K := QuadraticAlgebra (ZMod 19) 2 0
instance : Field K := inferInstance
instance : Fintype K := Fintype.ofEquiv (ZMod 19 × ZMod 19) (QuadraticAlgebra.equivProd 2 0).symm
instance : CharP K 19 := charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective 19

theorem card_field : Fintype.card K = 361 := by
  simpa using Fintype.card_congr (QuadraticAlgebra.equivProd (2 : ZMod 19) 0)

def generator : Kˣ := Units.mk0 (⟨2,1⟩ : K) (by decide)
def residueRoot : K := ⟨7,10⟩
theorem generator_pow_72 : (generator : K)^72 = residueRoot := by decide +kernel

/-- The residue-field Frobenius acts by inversion on the specified fifth root. -/
theorem residueFrobenius_inverts_root : residueRoot ^ 19 = residueRoot⁻¹ := by decide +kernel

theorem generator_order : orderOf generator = 360 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide +kernel)
  intro q hq hd
  have h : q = 2 ∨ q = 3 ∨ q = 5 := by
    have he : ∀ j : Fin 361, j.val.Prime → j.val ∣ 360 → j.val=2 ∨ j.val=3 ∨ j.val=5 := by decide +kernel
    exact he ⟨q,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)⟩ hq hd
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem exists_oriented_character : ∃ A : MulChar K ℂ, A generator = fifthRoot ∧ orderOf A = 5 := by
  have hg : orderOf generator = Fintype.card Kˣ := by rw [generator_order, Fintype.card_units, card_field]
  exact MulChar.exists_apply_eq_of_orderOf_eq_card hg fifthRoot_isPrimitiveRoot (by rw [Fintype.card_units, card_field]; decide)

def rootIndex (v : K) : Fin 6 :=
  if v = 1 then 0 else if v = residueRoot then 1 else if v = residueRoot^2 then 2
  else if v = residueRoot^3 then 3 else if v = residueRoot^4 then 4 else 5
def powerIndex (z : K) : Fin 6 := rootIndex (npowBinRec 72 z)
private theorem binary_pow (n : ℕ) (z : K) : npowBinRec n z = z ^ n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, pow_succ, ih]

def weight (x : K) := x * (1-125*x) / (1-x)
def multiplicities (j : Fin 6) := (Finset.univ.filter (fun x : K => powerIndex (weight x) = j)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The last entry counts the three branch values whose character is zero. -/
theorem multiplicities_eq : multiplicities = ![96,63,68,68,63,3] := by
  funext j
  fin_cases j <;> decide +kernel

noncomputable def charValue (ζ : ℂ) (j : Fin 6) : ℂ := if j.val < 5 then ζ^j.val else 0

private theorem charValue_index (A : MulChar K ℂ) (hA : A generator = fifthRoot) (z : K) :
    A z = charValue fifthRoot (powerIndex z) := by
  by_cases hz : z = 0
  · subst z
    rw [MulChar.map_zero]
    rw [show powerIndex 0 = 5 by decide]
    simp [charValue]
  let a := Units.mk0 z hz
  have htop : Subgroup.zpowers generator = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    simp only [Nat.card_eq_fintype_card, Fintype.card_zpowers, generator_order, Fintype.card_units, card_field])
  have hmem : a ∈ Subgroup.zpowers generator := htop ▸ trivial
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
  have hzn : (generator : K)^n = z := by simpa [a] using congrArg (fun t : Kˣ => (t : K)) hn
  have hmod (j : Fin 5) : rootIndex (residueRoot^j.val) = j.castSucc := by fin_cases j <;> decide
  have hord : orderOf residueRoot = 5 := by apply orderOf_eq_prime (p := 5) <;> decide
  rw [← hzn, map_pow, hA]
  unfold powerIndex
  rw [binary_pow, ← pow_mul, Nat.mul_comm, pow_mul, generator_pow_72,
    ← pow_mod_orderOf residueRoot n, hord, hmod ⟨n%5, Nat.mod_lt _ (by decide)⟩]
  change fifthRoot^n = (if n%5 < 5 then fifthRoot^(n%5) else 0)
  have hrem : n % 5 < 5 := Nat.mod_lt _ (by decide)
  simp only [hrem, ite_true]
  rw [fifthRoot_isPrimitiveRoot.eq_orderOf, pow_mod_orderOf]

/-- The field sum at the specified character orientation, for every nontrivial additive character. -/
theorem mccarthy_at_nineteen (A : MulChar K ℂ) (hA : A generator = fifthRoot)
    (θ : AddChar K ℂ) (hθ : θ ≠ 1) :
    rankTwoMcCarthySum θ A 125 = (-61 + 5 * (Real.sqrt 5 : ℂ)) / 2 := by
  have hn : A ≠ 1 := by
    intro h
    have h1 : A generator = 1 := h ▸ MulChar.one_apply_coe generator
    exact (fifthRoot_isPrimitiveRoot.ne_one (by decide)) (hA.symm.trans h1)
  have hsign : A (-1) = 1 := by
    rw [charValue_index A hA, show powerIndex (-1) = 0 by decide]
    simp [charValue]
  rw [rankTwoMcCarthySum_eq_eulerCharacterSum A hn θ hθ 125 (by decide), hsign]
  simp only [neg_one_mul]
  have hw (x : K) : A x * A⁻¹ (1-x) * A (1-125*x) = A (weight x) := by
    simp only [weight, div_eq_mul_inv, map_mul, ← MulChar.inv_apply']
    ring
  unfold eulerCharacterSum
  simp_rw [hw, charValue_index A hA]
  rw [← Finset.sum_fiberwise_of_maps_to' (t := (Finset.univ : Finset (Fin 6)))
    (fun (x : K) _ => Finset.mem_univ (powerIndex (weight x)))]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change -(∑ j : Fin 6, (multiplicities j : ℂ) * charValue fifthRoot j) = _
  rw [multiplicities_eq]
  norm_num [Fin.sum_univ_succ, charValue]
  have hsum := fifthRoot_isPrimitiveRoot.geom_sum_eq_zero (by decide)
  norm_num [Finset.sum_range_succ] at hsum
  linear_combination -68 * hsum + 5 * fifthRoot_add_fourth_pow

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem affine_counts : primeFiveEulerCount (ZMod 19) = 23 ∧ primeFiveEulerCount K = 421 := by
  unfold primeFiveEulerCount
  rw [card_field, ZMod.card]
  decide +kernel

theorem both_degree_two_traces :
    ((-5 - Real.sqrt 5)/2)^2 - 2*19 = (-61+5*Real.sqrt 5)/2 ∧
    ((5 + Real.sqrt 5)/2)^2 - 2*19 = (-61+5*Real.sqrt 5)/2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  constructor <;> linear_combination (1 / 4 : ℝ) * h

end HilbertModularity.PaperI.Nineteen
