/- Assembled by AxiomProver. -/

module

/-
Assembled with the assistance of AxiomProver, an automated formalization tool from Axiom Math.

# McCarthy's finite-field hypergeometric function

McCarthy's Gauss-sum normalization of `ₙ₊₁Fₙ^⋆` over a finite field (paper, §2.3,
equation (2.2)), its independence of the additive character, and the rank-two
specialization attached to the datum `HD_{p,m}` (paper, (2.3) and Proposition 2.2).
-/
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.MulChar.Duality

@[expose] public section

namespace HilbertModularity.Hypergeometric

open Finset

noncomputable section

variable {𝔽 C : Type*} [Field 𝔽] [Fintype 𝔽] [Field C]

/-- The finite group of multiplicative characters, enumerated by finite choice. -/
noncomputable instance instFintypeMulChar : Fintype (MulChar 𝔽 C) := Fintype.ofFinite _

/-- McCarthy's normalized finite-field hypergeometric function [McCarthyFF]
`ₙ₊₁Fₙ^⋆(A₀,…,Aₙ; B₁,…,Bₙ | x)_q` (paper, equation (2.2)), built from the Gauss sums
`g(χ) = ∑ₓ χ(x) θ(x)` for a fixed additive character `θ`. Multiplicative characters vanish
at `0`. The character `χ̄` is `χ⁻¹`; for complex values this is complex conjugation. -/
def mcCarthySum {n : ℕ} (θ : AddChar 𝔽 C) (A : Fin (n + 1) → MulChar 𝔽 C)
    (B : Fin n → MulChar 𝔽 C) (x : 𝔽) : C :=
  (1 / ((Fintype.card 𝔽 : C) - 1)) *
    ∑ χ : MulChar 𝔽 C,
      (∏ i, gaussSum (A i * χ) θ / gaussSum (A i) θ) *
      (∏ j, gaussSum (B j * χ)⁻¹ θ / gaussSum (B j)⁻¹ θ) *
      gaussSum χ⁻¹ θ * χ (-1) ^ (n + 1) * χ x

/-- Every nontrivial additive character is a unit multiplicative shift of a given one. -/
private lemma exists_unit_mulShift (θ θ' : AddChar 𝔽 ℂ) (hθ : θ ≠ 1) (hθ' : θ' ≠ 1) :
    ∃ a : 𝔽ˣ, θ' = θ.mulShift a := by
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hθ)
  have hbij : Function.Bijective θ.mulShift := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [AddChar.card_eq]
  obtain ⟨b, hb⟩ := hbij.2 θ'
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hθ' (by rw [← hb, AddChar.mulShift_zero])
  exact ⟨Units.mk0 b hb0, by simp [hb]⟩

omit [Fintype 𝔽] in
/-- A multiplicative character does not vanish at a unit. -/
private lemma inv_apply_unit_ne_zero (X : MulChar 𝔽 C) (a : 𝔽ˣ) : X⁻¹ (a : 𝔽) ≠ 0 := by
  intro h
  have : (X⁻¹ * X) (a : 𝔽) = 1 := by rw [inv_mul_cancel, MulChar.one_apply_coe]
  rw [MulChar.mul_apply, h, zero_mul] at this
  exact zero_ne_one this

/-- Shifting the additive character by `a` multiplies the ratio `g(XY)/g(X)` by `Y⁻¹(a)`. -/
private lemma ratio_mulShift (θ : AddChar 𝔽 C) (a : 𝔽ˣ) (X Y : MulChar 𝔽 C) :
    gaussSum (X * Y) (θ.mulShift a) / gaussSum X (θ.mulShift a) =
      Y⁻¹ (a : 𝔽) * (gaussSum (X * Y) θ / gaussSum X θ) := by
  rw [gaussSum_mulShift_eq, gaussSum_mulShift_eq, mul_inv, MulChar.mul_apply]
  have := inv_apply_unit_ne_zero X a
  field_simp

/-- McCarthy's function does not depend on the choice of nontrivial additive character
(McCarthy, §2; recalled in the paper after (2.2)). -/
theorem mcCarthySum_indep {n : ℕ} (θ θ' : AddChar 𝔽 ℂ) (hθ : θ ≠ 1) (hθ' : θ' ≠ 1)
    (A : Fin (n + 1) → MulChar 𝔽 ℂ) (B : Fin n → MulChar 𝔽 ℂ) (x : 𝔽) :
    mcCarthySum θ' A B x = mcCarthySum θ A B x := by
  obtain ⟨a, rfl⟩ := exists_unit_mulShift θ θ' hθ hθ'
  unfold mcCarthySum
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  simp only [mul_inv]
  simp only [ratio_mulShift]
  rw [gaussSum_mulShift_eq, inv_inv]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : χ⁻¹ (a : 𝔽) * χ (a : 𝔽) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
  have h2 : χ⁻¹ (a : 𝔽) ^ (n + 1) * χ (a : 𝔽) ^ n * χ (a : 𝔽) = 1 := by
    rw [mul_assoc, ← pow_succ, ← mul_pow, h1, one_pow]
  linear_combination (∏ i, gaussSum (A i * χ) θ / gaussSum (A i) θ) *
    (∏ j, gaussSum ((B j)⁻¹ * χ⁻¹) θ / gaussSum (B j)⁻¹ θ) * gaussSum χ⁻¹ θ *
    χ (-1) ^ (n + 1) * χ x * h2

/-- The rank-two function `₂F₁^⋆(A, A⁻¹; ε | x)_q` (paper, (2.3)): the finite-field
hypergeometric function of the datum `HD_{p,m}` when `A = A_{𝔓,m}`. -/
def rankTwoMcCarthySum (θ : AddChar 𝔽 C) (A : MulChar 𝔽 C) (x : 𝔽) : C :=
  mcCarthySum θ ![A, A⁻¹] ![1] x

/-- The finite-field hypergeometric function `𝓕_𝔓(HD_{p,m}; ξ)` of (2.3), for a
character `χ𝔓` of the residue field (of order `p` in the paper) and `x = ξ̄`. -/
def symmetricMcCarthySum (θ : AddChar 𝔽 C) (χ𝔓 : MulChar 𝔽 C) (m : ℕ) (x : 𝔽) : C :=
  rankTwoMcCarthySum θ (χ𝔓 ^ m) x

/-- The Gauss sum of the trivial character is `-1` (used in Proposition 2.2). -/
theorem gaussSum_one_eq_neg_one {D : Type*} [Field D]
    (θ : AddChar 𝔽 D) (hθ : θ ≠ 1) :
    gaussSum (1 : MulChar 𝔽 D) θ = -1 :=
  gaussSum_one_left hθ

/-- Every Gauss denominator is nonzero for a nontrivial additive character in
characteristic zero, including the trivial multiplicative character. -/
theorem gaussSum_ne_zero {D : Type*} [Field D] [CharZero D]
    (θ : AddChar 𝔽 D) (hθ : θ ≠ 1) (χ : MulChar 𝔽 D) :
    gaussSum χ θ ≠ 0 := by
  by_cases hχ : χ = 1
  · subst χ
    rw [gaussSum_one_eq_neg_one θ hθ]
    exact neg_ne_zero.mpr one_ne_zero
  · exact gaussSum_ne_zero_of_nontrivial
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hχ (AddChar.IsPrimitive.of_ne_one hθ)

/-- Explicit form of the rank-two function: since the lower character is trivial,
`g(ε) = -1` and `χ(-1)² = 1`, McCarthy's definition becomes
`-(1/(q-1)) ∑_χ g(Aχ) g(A⁻¹χ) g(χ̄)² χ(x) / (g(A) g(A⁻¹))`. -/
theorem rankTwoMcCarthySum_eq (θ : AddChar 𝔽 C) (hθ : θ ≠ 1) (A : MulChar 𝔽 C) (x : 𝔽) :
    rankTwoMcCarthySum θ A x = -(1 / ((Fintype.card 𝔽 : C) - 1)) *
      ∑ χ : MulChar 𝔽 C,
        gaussSum (A * χ) θ * gaussSum (A⁻¹ * χ) θ * gaussSum χ⁻¹ θ ^ 2 /
          (gaussSum A θ * gaussSum A⁻¹ θ) * χ x := by
  unfold rankTwoMcCarthySum mcCarthySum
  rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hχ : χ (-1) ^ 2 = 1 := by rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    mul_one, one_mul, inv_one, gaussSum_one_eq_neg_one θ hθ, hχ]
  ring

/-- The normalized finite sum of [GPRV] for the symmetric datum `(m/N, 1-m/N; 1, 1)`,
written in terms of a generator `ω` of the multiplicative character group.
The comparison theorem supplies the denominator and generator hypotheses. -/
def gprvSymmetricSum (θ : AddChar 𝔽 C) (ω : MulChar 𝔽 C) (N m : ℕ) (x : 𝔽) : C :=
  let k := (Fintype.card 𝔽 - 1) / N
  let g : ℤ → C := fun r => gaussSum (ω ^ r) θ
  (1 / (1 - (Fintype.card 𝔽 : C))) *
    ∑ r ∈ range (Fintype.card 𝔽 - 1),
      g (r + (m * k : ℕ)) * g (r + ((N - m) * k : ℕ)) * g (-r) ^ 2 /
        (g (m * k : ℕ) * g ((N - m) * k : ℕ)) * ω x ^ r

/-- [TripathiGoswami], Proposition 2.2 (McCarthy side, the displayed formula in its proof): writing
`χ = ω^r` for a generator `ω` of the character group and `A = ω^{m(q-1)/p}`,
`₂F₁^⋆(A, A⁻¹; ε | x)_q =
  -(1/(q-1)) ∑_{r=0}^{q-2} g(r + m(q-1)/p) g(r + (p-m)(q-1)/p) g(-r)² ω(x)^r
     / (g(m(q-1)/p) g((p-m)(q-1)/p))`, where `g(k) = g(ω^k)`. -/
theorem rankTwoMcCarthySum_eq_generator [CharZero C] [IsAlgClosed C] (θ : AddChar 𝔽 C) (hθ : θ ≠ 1) (ω : MulChar 𝔽 C)
    (hω : orderOf ω = Fintype.card 𝔽 - 1) (p m : ℕ) (hp : p ∣ Fintype.card 𝔽 - 1)
    (hm : m ≤ p) (x : 𝔽) (hx : x ≠ 0) :
    let k : ℕ := (Fintype.card 𝔽 - 1) / p
    let g : ℤ → C := fun r => gaussSum (ω ^ r) θ
    rankTwoMcCarthySum θ (ω ^ (m * k)) x = -(1 / ((Fintype.card 𝔽 : C) - 1)) *
      ∑ r ∈ range (Fintype.card 𝔽 - 1),
        g (r + (m * k : ℕ)) * g (r + ((p - m) * k : ℕ)) * g (-r) ^ 2 /
          (g (m * k : ℕ) * g ((p - m) * k : ℕ)) * ω x ^ r := by
  classical
  intro k g
  rw [rankTwoMcCarthySum_eq θ hθ]
  congr 1
  have hcard : Fintype.card (MulChar 𝔽 C) = Fintype.card 𝔽 - 1 := by
    classical
    rw [← Nat.card_eq_fintype_card, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity,
      Nat.card_eq_fintype_card, Fintype.card_units]
  have hinj : Set.InjOn (fun r : ℕ => ω ^ r) (range (Fintype.card 𝔽 - 1) : Set ℕ) := by
    rw [Finset.coe_range, ← hω]
    exact pow_injOn_Iio_orderOf
  have himg : (range (Fintype.card 𝔽 - 1)).image (fun r : ℕ => ω ^ r) = univ :=
    Finset.eq_univ_of_card _ (by rw [card_image_of_injOn hinj, card_range, hcard])
  rw [← himg, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpk : p * k = Fintype.card 𝔽 - 1 := Nat.mul_div_cancel' hp
  have hinv : (ω ^ (m * k))⁻¹ = ω ^ ((p - m) * k) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, ← add_mul, Nat.add_sub_cancel' hm, hpk, ← hω, pow_orderOf_eq_one]
  have hx' : (ω ^ r) x = ω x ^ r := MulChar.pow_apply_coe ω r (Units.mk0 x hx)
  simp only [g, zpow_add, zpow_neg, zpow_natCast]
  rw [hinv, hx', mul_comm (ω ^ (m * k)), mul_comm (ω ^ ((p - m) * k))]

/-- The rank-two McCarthy and GPRV finite sums agree with their exact displayed
normalizations, over any algebraically closed coefficient field of characteristic zero. -/
theorem rankTwoMcCarthySum_eq_gprvSymmetricSum [CharZero C] [IsAlgClosed C]
    (θ : AddChar 𝔽 C) (hθ : θ ≠ 1) (ω : MulChar 𝔽 C)
    (hω : orderOf ω = Fintype.card 𝔽 - 1) (N m : ℕ)
    (hN : N ∣ Fintype.card 𝔽 - 1) (hm : m ≤ N) (x : 𝔽) (hx : x ≠ 0) :
    rankTwoMcCarthySum θ (ω ^ (m * ((Fintype.card 𝔽 - 1) / N))) x = gprvSymmetricSum θ ω N m x := by
  rw [rankTwoMcCarthySum_eq_generator θ hθ ω hω N m hN hm x hx]
  unfold gprvSymmetricSum
  rw [← neg_sub (Fintype.card 𝔽 : C) 1, div_neg]

/-- The same comparison with a specified power-residue character and a compatible
character-group generator. The arithmetic construction of this character is separate. -/
theorem symmetricMcCarthySum_eq_gprvSymmetricSum [CharZero C] [IsAlgClosed C]
    (θ : AddChar 𝔽 C) (hθ : θ ≠ 1) (ω χ : MulChar 𝔽 C)
    (hω : orderOf ω = Fintype.card 𝔽 - 1) (N m : ℕ)
    (hN : N ∣ Fintype.card 𝔽 - 1) (hm : m ≤ N)
    (hχ : ω ^ ((Fintype.card 𝔽 - 1) / N) = χ) (x : 𝔽) (hx : x ≠ 0) :
    symmetricMcCarthySum θ χ m x = gprvSymmetricSum θ ω N m x := by
  rw [symmetricMcCarthySum, ← hχ, ← pow_mul, Nat.mul_comm]
  exact rankTwoMcCarthySum_eq_gprvSymmetricSum θ hθ ω hω N m hN hm x hx

/-- Exchanging `A ↔ A⁻¹` leaves the rank-two function unchanged (the convention switch
recorded after Proposition 2.2). -/
theorem rankTwoMcCarthySum_inv (θ : AddChar 𝔽 C) (A : MulChar 𝔽 C) (x : 𝔽) :
    rankTwoMcCarthySum θ A⁻¹ x = rankTwoMcCarthySum θ A x := by
  unfold rankTwoMcCarthySum mcCarthySum
  refine congrArg _ (Finset.sum_congr rfl fun χ _ => ?_)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    inv_inv, mul_one]
  ring

/-- Inverting the chosen power-residue character preserves the symmetric value. -/
theorem symmetricMcCarthySum_inv (θ : AddChar 𝔽 C) (χ : MulChar 𝔽 C) (m : ℕ) (x : 𝔽) :
    symmetricMcCarthySum θ χ⁻¹ m x = symmetricMcCarthySum θ χ m x := by
  simpa only [symmetricMcCarthySum, inv_pow] using rankTwoMcCarthySum_inv θ (χ ^ m) x

end

end HilbertModularity.Hypergeometric
