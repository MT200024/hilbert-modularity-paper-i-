/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-! # Reduction of cyclotomic roots at good primes -/

open Polynomial

/-- A primitive root in characteristic zero remains primitive under reduction
provided its order is nonzero in the target domain. -/
theorem IsPrimitiveRoot.map_of_order_ne_zero {R S : Type*}
    [CommRing R] [IsDomain R] [CharZero R] [CommRing S] [IsDomain S]
    {N : ℕ} [NeZero N] [NeZero (N : S)] {z : R} (hz : IsPrimitiveRoot z N)
    (f : R →+* S) : IsPrimitiveRoot (f z) N := by
  apply isRoot_cyclotomic_iff.mp
  have h := isRoot_cyclotomic_iff.mpr hz
  change (cyclotomic N S).eval (f z) = 0
  rw [← map_cyclotomic N f, eval_map_apply, h, map_zero]

/-- A ring map preserving a primitive root is injective on all roots of that order. -/
theorem IsPrimitiveRoot.eq_of_map_eq_on_roots {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S]
    {N : ℕ} [NeZero N] {ζ x y : R} (hζ : IsPrimitiveRoot ζ N)
    (f : R →+* S) (hfζ : IsPrimitiveRoot (f ζ) N)
    (hx : x ^ N = 1) (hy : y ^ N = 1) (hxy : f x = f y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  have hij := hfζ.pow_inj hi hj (by simpa only [map_pow] using hxy)
  rw [hij]

namespace HilbertModularity.Cyclotomic

open scoped NumberField

attribute [local instance] Ideal.Quotient.field

noncomputable section

/-- The chosen primitive root as an algebraic integer. -/
def rootInteger (N : ℕ) [NeZero N] : 𝓞 (cyclotomicField N) :=
  ⟨root N, (root_isPrimitiveRoot N).isIntegral (NeZero.pos N)⟩

theorem rootInteger_isPrimitiveRoot (N : ℕ) [NeZero N] :
    IsPrimitiveRoot (rootInteger N) N :=
  (root_isPrimitiveRoot N).of_map_of_injective
    (f := algebraMap (𝓞 (cyclotomicField N)) (cyclotomicField N))
    NumberField.RingOfIntegers.coe_injective

/-- The reduction of the chosen root has exact order at every prime not dividing `N`. -/
theorem rootInteger_reduction_isPrimitiveRoot (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P (rootInteger N)) N := by
  have : NeZero (N : 𝓞 (cyclotomicField N) ⧸ P) := ⟨by
    intro h
    apply hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using h⟩
  exact (rootInteger_isPrimitiveRoot N).map_of_order_ne_zero (Ideal.Quotient.mk P)

/-- The reduced root, as a unit of the residue field. -/
def residueRoot (N : ℕ) [NeZero N] (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) : (𝓞 (cyclotomicField N) ⧸ P)ˣ := by
  classical
  exact Units.mk0 _ ((rootInteger_reduction_isPrimitiveRoot N P hP).ne_zero (NeZero.ne N))

theorem residueRoot_orderOf (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) : orderOf (residueRoot N P hP) = N := by
  have h : IsPrimitiveRoot (residueRoot N P hP) N :=
    (rootInteger_reduction_isPrimitiveRoot N P hP).of_map_of_injective
      (f := Units.coeHom _) Units.val_injective
  exact h.eq_orderOf.symm

/-- The denominator divides the cardinality of the residue multiplicative group. -/
theorem dvd_residue_card_sub_one (N : ℕ) [NeZero N]
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsMaximal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P) :
    N ∣ Nat.card (𝓞 (cyclotomicField N) ⧸ P) - 1 := by
  classical
  let := Fintype.ofFinite (𝓞 (cyclotomicField N) ⧸ P)
  rw [Nat.card_eq_fintype_card, ← Fintype.card_units]
  simpa only [residueRoot_orderOf N P hP] using
    (orderOf_dvd_card (x := residueRoot N P hP))

end

end HilbertModularity.Cyclotomic
