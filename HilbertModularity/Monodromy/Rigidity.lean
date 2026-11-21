/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.UnipotentBasis
public import HilbertModularity.Monodromy.Matrices
public import Mathlib.LinearAlgebra.Trace

/-! # Rigidity of rank-two unipotent triples

We prove the simultaneous normal form used in
[TripathiGoswami, rigid triple lemma].
-/

@[expose] public section

namespace HilbertModularity.Monodromy

variable {K : Type*} [Field K]

/-- Two rank-two unipotents with no common nonzero fixed vector have the
standard simultaneous normal form. -/
theorem exists_basis_unipotent_pair
    (A B : Module.End K (Fin 2 → K))
    (hA : (A - 1) ^ 2 = 0) (hB : (B - 1) ^ 2 = 0) (hBne : B ≠ 1)
    (hirr : ∀ v, A v = v → B v = v → v = 0) :
    ∃ (b : Module.Basis (Fin 2) K (Fin 2 → K)) (τ : K),
      τ ≠ 2 ∧ LinearMap.toMatrix b b A = U0 ∧ LinearMap.toMatrix b b B = U1 τ := by
  have hex : ∃ w, (B - 1) w ≠ 0 := by
    by_contra! h
    apply hBne
    apply sub_eq_zero.mp
    apply LinearMap.ext
    intro w
    exact h w
  obtain ⟨w, hw⟩ := hex
  let v := (B - 1) w
  have hv : v ≠ 0 := hw
  have hBv : (B - 1) v = 0 := by
    have := congrArg (fun f : Module.End K (Fin 2 → K) => f w) hB
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using this
  have hAv : (A - 1) v ≠ 0 := by
    intro h
    apply hv
    exact hirr v (sub_eq_zero.mp h) (sub_eq_zero.mp hBv)
  obtain ⟨b, hb0, hb1⟩ := (A - 1).exists_basis_of_square_zero hA v hAv
  have hA0 : A (b 0) = b 0 := by
    have h := congrArg (fun f : Module.End K (Fin 2 → K) => f v) hA
    have hz : (A - 1) (b 0) = 0 := by
      rw [hb0]
      simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h
    exact sub_eq_zero.mp hz
  have hA1 : A (b 1) = b 0 + b 1 := by
    have h : A (b 1) - b 1 = b 0 := by
      change (A - 1) (b 1) = b 0
      rw [hb1, hb0]
    exact sub_eq_iff_eq_add.mp h
  have hB1 : B (b 1) = b 1 := by
    rw [hb1]
    exact sub_eq_zero.mp hBv
  obtain ⟨t, ht⟩ := b.exists_smul_of_square_zero (B - 1) hB
    (by change B (b 1) - b 1 = 0; rw [hB1, sub_self])
  have hB0 : B (b 0) = b 0 + t • b 1 := by
    change B (b 0) - b 0 = t • b 1 at ht
    exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hBne
    apply b.ext
    intro i
    fin_cases i
    · change B (b 0) = b 0
      simpa only [ht0, zero_smul, add_zero] using hB0
    · change B (b 1) = b 1
      exact hB1
  refine ⟨b, t + 2, by simpa using ht0, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hA0, hA1, U0]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hB0, hB1, U1]

/-- The simultaneous normal form is determined by the trace of the product. -/
theorem exists_basis_unipotent_pair_trace
    (A B : Module.End K (Fin 2 → K))
    (hA : (A - 1) ^ 2 = 0) (hB : (B - 1) ^ 2 = 0) (hBne : B ≠ 1)
    (hirr : ∀ v, A v = v → B v = v → v = 0) :
    ∃ b : Module.Basis (Fin 2) K (Fin 2 → K),
      LinearMap.toMatrix b b A = U0 ∧
      LinearMap.toMatrix b b B = U1 (LinearMap.trace K (Fin 2 → K) (A * B)) := by
  obtain ⟨b, τ, _, h0, h1⟩ := exists_basis_unipotent_pair A B hA hB hBne hirr
  have ht : LinearMap.trace K (Fin 2 → K) (A * B) = τ := by
    rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.toMatrix_mul, h0, h1,
      trace_U0_mul_U1]
  exact ⟨b, h0, ht.symm ▸ h1⟩

/-- Rank-two unipotent pairs with no common fixed vector and the same product
trace are simultaneously conjugate over the original coefficient field. -/
theorem exists_equiv_unipotent_pair
    (A B A' B' : Module.End K (Fin 2 → K))
    (hA : (A - 1) ^ 2 = 0) (hB : (B - 1) ^ 2 = 0) (hBne : B ≠ 1)
    (hirr : ∀ v, A v = v → B v = v → v = 0)
    (hA' : (A' - 1) ^ 2 = 0) (hB' : (B' - 1) ^ 2 = 0) (hBne' : B' ≠ 1)
    (hirr' : ∀ v, A' v = v → B' v = v → v = 0)
    (ht : LinearMap.trace K (Fin 2 → K) (A * B) =
      LinearMap.trace K (Fin 2 → K) (A' * B')) :
    ∃ e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K),
      e.toLinearMap.comp A = A'.comp e.toLinearMap ∧
      e.toLinearMap.comp B = B'.comp e.toLinearMap := by
  obtain ⟨b, h0, h1⟩ := exists_basis_unipotent_pair_trace A B hA hB hBne hirr
  obtain ⟨b', h0', h1'⟩ := exists_basis_unipotent_pair_trace A' B' hA' hB' hBne' hirr'
  refine ⟨b.equiv b' (Equiv.refl _), ?_, ?_⟩
  · exact b.equiv_comp_of_toMatrix_eq b' A A' (h0.trans h0'.symm)
  · apply b.equiv_comp_of_toMatrix_eq b' B B'
    rw [h1, h1', ht]

/-- The trace at infinity is the parameter of the standard triple. -/
theorem trace_Uinf (τ : K) : (Uinf τ).trace = τ := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, charpoly_Uinf]
  simp [Polynomial.coeff_one]

/-- In a product-one unipotent triple, the trace at infinity equals the trace
of the product of the two finite-cusp matrices. -/
theorem trace_third_eq_trace_product
    (A B C : Module.End K (Fin 2 → K))
    (hA : (A - 1) ^ 2 = 0) (hB : (B - 1) ^ 2 = 0) (hBne : B ≠ 1)
    (hirr : ∀ v, A v = v → B v = v → v = 0) (hprod : A * B * C = 1) :
    LinearMap.trace K (Fin 2 → K) C = LinearMap.trace K (Fin 2 → K) (A * B) := by
  obtain ⟨b, h0, h1⟩ := exists_basis_unipotent_pair_trace A B hA hB hBne hirr
  have hc : LinearMap.toMatrix b b C = Uinf (LinearMap.trace K (Fin 2 → K) (A * B)) := by
    apply Eq.symm
    apply Matrix.inv_eq_right_inv
    have h := congrArg (LinearMap.toMatrix b b) hprod
    simpa only [LinearMap.toMatrix_mul, LinearMap.toMatrix_one, h0, h1] using h
  rw [LinearMap.trace_eq_matrix_trace K b, hc, trace_Uinf]

end HilbertModularity.Monodromy
