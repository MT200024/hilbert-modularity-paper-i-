/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! # Eigenvalues of rank-two involutions -/

@[expose] public section

namespace HilbertModularity

open Matrix Polynomial

/-- An involution of determinant `-1` has a nonzero eigenvector for each sign `s = ±1`. -/
private lemma exists_eigenvector_of_involution {K : Type*} [Field K] (hK : (2 : K) ≠ 0)
    (c : Matrix (Fin 2) (Fin 2) K) (hc : c ^ 2 = 1) (hdet : c.det = -1) (s : K)
    (hs : s = 1 ∨ s = -1) : ∃ v : Fin 2 → K, v ≠ 0 ∧ c *ᵥ v = s • v := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  set M := c + s • (1 : Matrix (Fin 2) (Fin 2) K) with hM
  have hcM : c * M = s • M := by
    rw [hM, mul_add, mul_smul_comm, mul_one, ← sq, hc, smul_add, smul_smul, hs2, one_smul,
      add_comm]
  have hM0 : M ≠ 0 := by
    intro h0
    have hc' : c = -(s • (1 : Matrix (Fin 2) (Fin 2) K)) := eq_neg_of_add_eq_zero_left h0
    rw [hc', Matrix.det_fin_two] at hdet
    simp at hdet
    have : s * s = -1 := by linear_combination hdet
    apply hK
    linear_combination this - hs2
  have : ∃ j, M *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hM0
    ext i j
    have := congrFun (hall j) i
    simpa [Matrix.mulVec_single] using this
  obtain ⟨j, hj⟩ := this
  refine ⟨M *ᵥ Pi.single j 1, hj, ?_⟩
  rw [Matrix.mulVec_mulVec, hcM, Matrix.smul_mulVec]

/-- [TripathiGoswami], Lemma 5.4: if `c² = 1` and `det c = -1` for a `2 × 2` matrix over a field of
characteristic `≠ 2`, then every eigenvector of `c` has eigenvalue `1` or `-1`, and both
eigenvalues occur (so the two eigenlines are the only `c`-stable lines). -/
theorem involution_eigen {K : Type*} [Field K] (hK : (2 : K) ≠ 0)
    (c : Matrix (Fin 2) (Fin 2) K) (hc : c ^ 2 = 1) (hdet : c.det = -1) :
    (∀ (v : Fin 2 → K) (μ : K), v ≠ 0 → c *ᵥ v = μ • v → μ = 1 ∨ μ = -1) ∧
      (∃ v : Fin 2 → K, v ≠ 0 ∧ c *ᵥ v = v) ∧ (∃ v : Fin 2 → K, v ≠ 0 ∧ c *ᵥ v = -v) := by
  refine ⟨fun v μ hv h => ?_, ?_, ?_⟩
  · have h2 : c *ᵥ (c *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← sq, hc, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_smul, h, smul_smul] at h2
    have h3 : (μ * μ - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact mul_self_eq_one_iff.mp (sub_eq_zero.mp h4)
    · exact absurd h4 hv
  · obtain ⟨v, hv, h⟩ := exists_eigenvector_of_involution hK c hc hdet 1 (Or.inl rfl)
    exact ⟨v, hv, by simpa using h⟩
  · obtain ⟨v, hv, h⟩ := exists_eigenvector_of_involution hK c hc hdet (-1) (Or.inr rfl)
    exact ⟨v, hv, by simpa using h⟩

/-- A rank-two involution of determinant minus one admits a basis in which it
acts by the two distinct signs. -/
theorem exists_basis_of_involution {K : Type*} [Field K] (hK : (2 : K) ≠ 0)
    (c : Matrix (Fin 2) (Fin 2) K) (hc : c ^ 2 = 1) (hdet : c.det = -1) :
    ∃ b : Module.Basis (Fin 2) K (Fin 2 → K),
      c *ᵥ b 0 = b 0 ∧ c *ᵥ b 1 = -b 1 := by
  classical
  obtain ⟨_, ⟨v, hv, hcv⟩, ⟨w, hw, hcw⟩⟩ := involution_eigen hK c hc hdet
  have hμ : Function.Injective (![1, -1] : Fin 2 → K) := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply hK
      change (1 : K) = -1 at h
      linear_combination h
    · exfalso
      apply hK
      change (-1 : K) = 1 at h
      linear_combination -h
    · rfl
  have hli : LinearIndependent K (![v, w] : Fin 2 → Fin 2 → K) := by
    apply Module.End.eigenvectors_linearIndependent' (Matrix.toLinAlgEquiv' c) ![1, -1] hμ
    intro i
    fin_cases i
    · refine ⟨?_, hv⟩
      apply Module.End.mem_eigenspace_iff.mpr
      change c *ᵥ v = (1 : K) • v
      simpa only [one_smul] using hcv
    · refine ⟨?_, hw⟩
      apply Module.End.mem_eigenspace_iff.mpr
      change c *ᵥ w = (-1 : K) • w
      simpa only [neg_one_smul] using hcw
  refine ⟨basisOfPiSpaceOfLinearIndependent hli, ?_, ?_⟩
  · simpa only [coe_basisOfPiSpaceOfLinearIndependent, Matrix.cons_val_zero] using hcv
  · simpa only [coe_basisOfPiSpaceOfLinearIndependent, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hcw

end HilbertModularity
