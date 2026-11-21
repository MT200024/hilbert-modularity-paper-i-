/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PrimitiveRootLift
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

/-! # Compatible generators of finite-field character groups -/

namespace MulChar

variable {F C : Type*} [Field F] [Fintype F] [Field C]

omit [Fintype F] in
/-- Evaluation at a generator preserves the order of a multiplicative character. -/
theorem orderOf_apply_generator (χ : MulChar F C) {g : Fˣ}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : orderOf (χ g) = orderOf χ := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  rw [← pow_apply_coe, ← one_apply_coe g, ← eq_iff hg]

/-- A character of order `N` is the `(q-1)/N`th power of a generating character,
provided the coefficient field contains a primitive `(q-1)`th root of unity. -/
theorem exists_generator_pow_eq {N : ℕ} [NeZero N] (χ : MulChar F C)
    (hχ : orderOf χ = N) (hd : N ∣ Fintype.card F - 1)
    {ζ : C} (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1)) :
    ∃ ω : MulChar F C, orderOf ω = Fintype.card F - 1 ∧
      ω ^ ((Fintype.card F - 1) / N) = χ := by
  classical
  have : NeZero (Fintype.card F - 1) := ⟨by have := Fintype.one_lt_card (α := F); omega⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hvalue : IsPrimitiveRoot (χ g) N := by
    rw [← hχ, ← orderOf_apply_generator χ hg]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨η, hη, hpower⟩ := hζ.exists_primitiveRoot_pow_eq hvalue hd
  let ηu : Cˣ := (hη.isUnit (NeZero.ne _)).unit
  have hηu : ηu ∈ rootsOfUnity (Fintype.card Fˣ) C := by
    rw [mem_rootsOfUnity']
    simpa [ηu, Fintype.card_units] using hη.pow_eq_one
  let ω := ofRootOfUnity hηu hg
  have hω : ω g = η := by
    simpa [ω, ηu] using ofRootOfUnity_spec hηu hg
  refine ⟨ω, ?_, ?_⟩
  · rw [← orderOf_apply_generator ω hg, hω, ← hη.eq_orderOf]
  · apply (eq_iff hg _ _).mpr
    rw [pow_apply_coe, hω, hpower]

/-- Prescribing a primitive root at a generator constructs a character of that
exact order, whenever the order divides the size of the unit group. -/
theorem exists_apply_eq_of_orderOf_eq_card [DecidableEq F] {g : Fˣ}
    (hg : orderOf g = Fintype.card Fˣ) {N : ℕ} [NeZero N]
    {ζ : C} (hζ : IsPrimitiveRoot ζ N) (hd : N ∣ Fintype.card Fˣ) :
    ∃ χ : MulChar F C, χ g = ζ ∧ orderOf χ = N := by
  classical
  have hgen : ∀ x, x ∈ Subgroup.zpowers g := by
    have ht : Subgroup.zpowers g = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by simpa only [Nat.card_eq_fintype_card,
        Fintype.card_zpowers] using hg)
    simp [ht]
  let ζu : Cˣ := (hζ.isUnit (NeZero.ne N)).unit
  have hu : ζu ∈ rootsOfUnity (Fintype.card Fˣ) C := by
    rw [mem_rootsOfUnity']
    change ζ ^ Fintype.card Fˣ = 1
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ofRootOfUnity hu hgen, ?_, ?_⟩
  · simpa [ζu] using ofRootOfUnity_spec hu hgen
  · rw [← orderOf_apply_generator _ hgen, ofRootOfUnity_spec hu hgen]
    exact hζ.eq_orderOf.symm

end MulChar
