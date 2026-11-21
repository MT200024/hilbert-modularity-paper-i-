/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.JordanChevalley
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-! # Finite-order semisimplification

A commuting semisimple part with nilpotent difference is precisely the additive
Jordan–Chevalley semisimple part. Its uniqueness is supplied by mathlib.
-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Finite order is independent of the choice of a commuting semisimple part,
by uniqueness of Jordan–Chevalley decomposition. -/
theorem isOfFinOrder_of_exists_semisimple_part
    [FiniteDimensional K V] [PerfectField K] {f : Module.End K V}
    (hf : ∃ s₀, s₀.IsSemisimple ∧ Commute f s₀ ∧ IsNilpotent (f - s₀) ∧ IsOfFinOrder s₀) (s : Module.End K V)
    (hs : s.IsSemisimple) (hc : Commute f s) (hn : IsNilpotent (f - s)) :
    IsOfFinOrder s := by
  obtain ⟨s₀, hs₀, hc₀, hn₀, ho₀⟩ := hf
  have h := isNilpotent_isSemisimple_unique hn hs hn₀ hs₀
    (hc.sub_left (Commute.refl s)) (hc₀.sub_left (Commute.refl s₀)) (by simp)
  rwa [h.2]

/-- A unipotent endomorphism has identity semisimple part. -/
theorem exists_finiteOrder_semisimple_part_of_unipotent (f : Module.End K V)
    (hf : IsNilpotent (f - 1)) : ∃ s, s.IsSemisimple ∧ Commute f s ∧ IsNilpotent (f - s) ∧ IsOfFinOrder s := by
  refine ⟨1, isSemisimple_id, Commute.one_right f, hf, ?_⟩
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩

/-- In characteristic zero, a finite-order endomorphism is its own semisimple part. -/
theorem exists_finiteOrder_semisimple_part_of_pow_eq_one [CharZero K]
    (f : Module.End K V) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    ∃ s, s.IsSemisimple ∧ Commute f s ∧ IsNilpotent (f - s) ∧ IsOfFinOrder s := by
  have hs : f.IsSemisimple := isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.mpr hn.ne') one_ne_zero).squarefree
    (by simpa using sub_eq_zero.mpr hf)
  refine ⟨f, hs, Commute.refl f, ?_, isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hf⟩⟩
  rw [sub_self]
  exact ⟨1, zero_pow Nat.one_ne_zero⟩

end Module.End
