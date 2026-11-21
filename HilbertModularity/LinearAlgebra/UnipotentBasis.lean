/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Bases for square-zero rank-two endomorphisms

These elementary basis constructions support the simultaneous normal form
of two unipotents in [TripathiGoswami, rigid triple lemma].
-/

@[expose] public section

namespace Module.End

variable {K : Type*} [Field K]

/-- A nonzero image vector of a square-zero rank-two endomorphism and its
preimage form a basis. -/
theorem exists_basis_of_square_zero (N : Module.End K (Fin 2 → K))
    (hN : N ^ 2 = 0) (v : Fin 2 → K) (hv : N v ≠ 0) :
    ∃ b : Module.Basis (Fin 2) K (Fin 2 → K), b 0 = N v ∧ b 1 = v := by
  classical
  have hNv : N (N v) = 0 := by
    have := congrArg (fun f : Module.End K (Fin 2 → K) => f v) hN
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using this
  have hi : LinearIndependent K ![N v, v] := by
    apply linearIndependent_fin2.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one] using
        (show v ≠ 0 from fun h => hv (by simp [h]))
    · intro a ha
      change a • v = N v at ha
      have h := congrArg N ha
      rw [map_smul, hNv] at h
      have ha0 : a = 0 := (smul_eq_zero.mp h).resolve_right hv
      exact hv (by simpa [ha0] using ha.symm)
  refine ⟨basisOfPiSpaceOfLinearIndependent hi, ?_, ?_⟩ <;>
    simp only [coe_basisOfPiSpaceOfLinearIndependent, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]

end Module.End

namespace Module.Basis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If a square-zero rank-two endomorphism kills the second basis vector,
its image of the first is a multiple of the second. -/
theorem exists_smul_of_square_zero (b : Basis (Fin 2) K V)
    (N : Module.End K V) (hN : N ^ 2 = 0) (h1 : N (b 1) = 0) :
    ∃ t : K, N (b 0) = t • b 1 := by
  have hr : b.repr (N (b 0)) 0 • b 0 + b.repr (N (b 0)) 1 • b 1 = N (b 0) := by
    simpa only [Fin.sum_univ_two] using b.sum_repr (N (b 0))
  have hs : N (N (b 0)) = 0 := by
    have := congrArg (fun f : Module.End K V => f (b 0)) hN
    simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using this
  have hm : b.repr (N (b 0)) 0 • N (b 0) = 0 := by
    simpa only [map_add, map_smul, h1, smul_zero, add_zero, hs] using congrArg N hr
  have ha : b.repr (N (b 0)) 0 = 0 := by
    have h := congrArg (fun v => b.repr v 0) hm
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero,
      Finsupp.zero_apply] at h
    exact (mul_self_eq_zero.mp h)
  exact ⟨b.repr (N (b 0)) 1, by simpa only [ha, zero_smul, zero_add] using hr.symm⟩

/-- Matching two bases intertwines endomorphisms with the same coordinate matrix. -/
theorem equiv_comp_of_toMatrix_eq {W ι : Type*} [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (b' : Basis ι K W)
    (A : Module.End K V) (A' : Module.End K W)
    (h : LinearMap.toMatrix b b A = LinearMap.toMatrix b' b' A') :
    (b.equiv b' (Equiv.refl _)).toLinearMap.comp A =
      A'.comp (b.equiv b' (Equiv.refl _)).toLinearMap := by
  apply (LinearMap.toMatrix b b').injective
  rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b',
    LinearMap.toMatrix_basis_equiv, one_mul, mul_one, h]

end Module.Basis
