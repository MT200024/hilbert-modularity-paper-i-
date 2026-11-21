/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Frobenius
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Cyclotomic characters with extended coefficients

The character is the action on roots of unity. Taking an inverse Frobenius
element therefore inverts its value, as required by the geometric convention in
[TripathiGoswami, conventions on Frobenius and Tate twists].
-/

@[expose] public noncomputable section

open scoped NumberField Pointwise

namespace PadicInt

/-- Reduction modulo the first power of `p` is the usual residue-field map. -/
theorem cast_toZModPow_one (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p) (x.toZModPow 1) = x.toZMod := by
  have h := zmod_congr_of_sub_mem_max_ideal x (appr x 1) (zmodRepr x)
    (by simpa only [maximalIdeal_eq_span_p, pow_one] using appr_spec 1 x)
    (sub_zmodRepr_mem x)
  simpa only [toZModPow, toZMod, toZModHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, map_natCast] using h

end PadicInt

namespace modularCyclotomicCharacter

/-- Changing an equal conductor preserves the finite cyclotomic character. -/
theorem cast_of_eq {E : Type*} [Field E] {n m : ℕ} [NeZero n] [NeZero m]
    (hn : Nat.card (rootsOfUnity n E) = n) (hm : Nat.card (rootsOfUnity m E) = m)
    (h : n = m) (g : E ≃+* E) :
    ZMod.castHom h.symm.dvd (ZMod m)
      (modularCyclotomicCharacter E hn g : ZMod n) =
        (modularCyclotomicCharacter E hm g : ZMod m) := by
  subst m
  simp only [ZMod.castHom_self, RingHom.id_apply]

end modularCyclotomicCharacter

namespace cyclotomicCharacter

/-- Reduction of the integral cyclotomic character is its action on `p`-th roots. -/
theorem toZMod {E : Type*} [Field E] (p : ℕ) [Fact p.Prime]
    [∀ n, HasEnoughRootsOfUnity E (p ^ n)]
    (hp : Nat.card (rootsOfUnity p E) = p) (g : E ≃+* E) :
    (_root_.cyclotomicCharacter E p g : ℤ_[p]).toZMod =
      (modularCyclotomicCharacter E hp g : ZMod p) := by
  rw [← PadicInt.cast_toZModPow_one, cyclotomicCharacter.toZModPow]
  exact modularCyclotomicCharacter.cast_of_eq _ hp (pow_one p) g

/-- An automorphism acting by the same integral power on every `p`-power
root of unity has that integer as its cyclotomic character value. -/
theorem coe_eq_natCast_of_roots_action {E : Type*} [Field E]
    (p : ℕ) [Fact p.Prime] [∀ n, HasEnoughRootsOfUnity E (p ^ n)]
    (g : E ≃+* E) (q : ℕ)
    (h : ∀ n (ζ : E), ζ ^ p ^ n = 1 → g ζ = ζ ^ q) :
    (_root_.cyclotomicCharacter E p g : ℤ_[p]) = q := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro ζ hζ
  rw [h n ζ ((mem_rootsOfUnity' _ _).mp hζ), ZMod.val_natCast]
  exact pow_eq_pow_mod q ((mem_rootsOfUnity' _ _).mp hζ)

/-- An automorphism which inverts every `p`-power root of unity has completed
cyclotomic character `-1`. The condition concerns all powers, since its
reduction modulo `p` alone does not determine a `p`-adic unit. -/
theorem coe_eq_neg_one_of_roots_action {E : Type*} [Field E]
    (p : ℕ) [Fact p.Prime] [∀ n, HasEnoughRootsOfUnity E (p ^ n)]
    (g : E ≃+* E)
    (hg : ∀ n (ζ : E), ζ ^ p ^ n = 1 → g ζ * ζ = 1) :
    (_root_.cyclotomicCharacter E p g : ℤ_[p]) = -1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E (p ^ n)
  have h := hg n ζ hζ.pow_eq_one
  rw [_root_.cyclotomicCharacter.spec p g ζ hζ.pow_eq_one, ← pow_succ,
    hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff, Nat.cast_succ,
    ZMod.natCast_zmod_val] at h
  rw [map_neg, map_one, eq_neg_iff_add_eq_zero]
  exact h

/-- An automorphism realizing complex conjugation under an embedding inverts
every root of unity, so its completed cyclotomic character is `-1`. The
embedding condition specifies the actual real place. See
[TripathiGoswamiRevised, Lemma `prime-absolute-irred`]. -/
theorem coe_eq_neg_one_of_complexConjugation {E : Type*} [Field E]
    (p : ℕ) [Fact p.Prime] [∀ n, HasEnoughRootsOfUnity E (p ^ n)]
    (ι : E →+* ℂ) (g : E ≃+* E)
    (hg : ∀ x, ι (g x) = star (ι x)) :
    (_root_.cyclotomicCharacter E p g : ℤ_[p]) = -1 := by
  apply coe_eq_neg_one_of_roots_action p g
  intro n ζ hζ
  have hn : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  have hnorm : ‖ι ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by
    rw [← map_pow, hζ, map_one]) hn
  have hnonzero : ι ζ ≠ 0 := by
    intro hzero
    simp [hzero] at hnorm
  apply ι.injective
  rw [map_mul, hg ζ, map_one]
  change (starRingEnd ℂ) (ι ζ) * ι ζ = 1
  rw [← Complex.inv_eq_conj hnorm]
  exact inv_mul_cancel₀ hnonzero

end cyclotomicCharacter

namespace Field

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

/-- The continuous integral cyclotomic character of the absolute Galois group. -/
def cyclotomicCharacter : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* ℤ_[p]ˣ where
  __ := (_root_.cyclotomicCharacter (AlgebraicClosure K) p).comp
    (MulSemiringAction.toRingAut (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K))
  continuous_toFun := _root_.cyclotomicCharacter.continuous p K (AlgebraicClosure K)

/-- The integral character is characterized by its action on every power-order root. -/
theorem cyclotomicCharacter_spec [CharZero K] (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (n : ℕ) (ζ : AlgebraicClosure K) (hζ : ζ ^ p ^ n = 1) :
    g ζ = ζ ^ ((cyclotomicCharacter K p g : ℤ_[p]).toZModPow n).val := by
  exact _root_.cyclotomicCharacter.spec p g.toRingEquiv ζ hζ

variable (L : Type*) [NormedField L] [Algebra ℚ_[p] L]
  [ContinuousSMul ℚ_[p] L]

/-- Extend the cyclotomic character from the `p`-adic integers to a normed
coefficient field with continuous `ℚ_[p]`-scalar action. -/
def cyclotomicCharacterWithCoefficients : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* Lˣ where
  __ := (Units.map ((algebraMap ℚ_[p] L).comp (PadicInt.Coe.ringHom (p := p))).toMonoidHom).comp
    (cyclotomicCharacter K p).toMonoidHom
  continuous_toFun := by
    apply Continuous.of_coeHom_comp
    exact (continuous_algebraMap ℚ_[p] L).comp
      ((show Continuous (fun x : ℤ_[p] => (x : ℚ_[p])) from continuous_subtype_val).comp
        ((show Continuous (fun x : ℤ_[p]ˣ => (x : ℤ_[p])) from Units.continuous_val).comp
          (cyclotomicCharacter K p).continuous))

/-- Coefficient extension is the usual embedding of the integral character. -/
@[simp] theorem cyclotomicCharacterWithCoefficients_coe (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (cyclotomicCharacterWithCoefficients K p L g : L) =
      algebraMap ℚ_[p] L ((cyclotomicCharacter K p g : ℤ_[p]) : ℚ_[p]) := rfl

/-- Arithmetic power action gives the expected arithmetic cyclotomic value. -/
theorem cyclotomicCharacterWithCoefficients_eq_natCast [CharZero K]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (q : ℕ)
    (h : ∀ n (ζ : AlgebraicClosure K), ζ ^ p ^ n = 1 → g ζ = ζ ^ q) :
    (cyclotomicCharacterWithCoefficients K p L g : L) = q := by
  rw [cyclotomicCharacterWithCoefficients_coe]
  have hc := _root_.cyclotomicCharacter.coe_eq_natCast_of_roots_action p g.toRingEquiv q h
  change (cyclotomicCharacter K p g : ℤ_[p]) = q at hc
  rw [hc, PadicInt.coe_natCast, map_natCast]

/-- A residue-field power action on algebraic integers determines the
cyclotomic character. The prime and its inertia action are actual ideals and
automorphisms of the algebraic closure. -/
theorem cyclotomicCharacterWithCoefficients_eq_natCast_of_quotient_action [CharZero K]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsPrime]
    (hp : (p : 𝓞 (AlgebraicClosure K)) ∉ Q)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (q : ℕ)
    (hg : ∀ b : 𝓞 (AlgebraicClosure K),
      Ideal.Quotient.mk Q (g • b) = (Ideal.Quotient.mk Q b) ^ q) :
    (cyclotomicCharacterWithCoefficients K p L g : L) = q := by
  apply cyclotomicCharacterWithCoefficients_eq_natCast K p L g q
  intro n y hy
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (p ^ n)
  let ζO : 𝓞 (AlgebraicClosure K) :=
    ⟨ζ, hζ.isIntegral (NeZero.pos (p ^ n))⟩
  let yO : 𝓞 (AlgebraicClosure K) :=
    ⟨y, IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) (by rw [hy]; exact isIntegral_one)⟩
  have hζO : IsPrimitiveRoot ζO (p ^ n) :=
    hζ.of_map_of_injective (f := algebraMap (𝓞 (AlgebraicClosure K)) (AlgebraicClosure K))
      NumberField.RingOfIntegers.coe_injective
  have hpN : ((p ^ n : ℕ) : 𝓞 (AlgebraicClosure K)) ∉ Q := by
    intro h
    apply hp
    exact (inferInstance : Q.IsPrime).mem_of_pow_mem n (by simpa only [Nat.cast_pow] using h)
  have h := Ideal.smul_root_eq_pow_of_quotient_action Q g q hg hpN hζO
    (show yO ^ p ^ n = 1 from Subtype.ext hy)
  exact congrArg Subtype.val h

/-- The cyclotomic character is trivial on inertia away from `p`. -/
theorem cyclotomicCharacterWithCoefficients_eq_one_on_inertia [CharZero K]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsPrime]
    (hp : (p : 𝓞 (AlgebraicClosure K)) ∉ Q)
    (g : Q.inertia (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :
    cyclotomicCharacterWithCoefficients K p L g = 1 := by
  apply Units.ext
  have h := cyclotomicCharacterWithCoefficients_eq_natCast_of_quotient_action K p L Q hp g 1
    (fun b => by
      rw [pow_one, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact (Ideal.mem_inertia.mp g.property) b)
  simpa only [Nat.cast_one, Units.val_one] using h

/-- Inverting an arithmetic Frobenius action gives the inverse norm in the
geometric convention. The power action hypothesis is stated explicitly. -/
theorem cyclotomicCharacterWithCoefficients_inv_eq_inv_natCast [CharZero K]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (q : ℕ)
    (h : ∀ n (ζ : AlgebraicClosure K), ζ ^ p ^ n = 1 → g ζ = ζ ^ q) :
    (cyclotomicCharacterWithCoefficients K p L g⁻¹ : L) = (q : L)⁻¹ := by
  rw [map_inv, Units.val_inv_eq_inv_val,
    cyclotomicCharacterWithCoefficients_eq_natCast K p L g q h]

/-- At a geometric Frobenius lift over a prime away from `p`, the extended
cyclotomic character is the inverse of the residue-field norm. The Frobenius
condition is equality with the canonical residue automorphism. -/
theorem cyclotomicCharacterWithCoefficients_geometricFrobenius [NumberField K]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P]
    (hp : (p : 𝓞 K) ∉ P)
    (g : MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Q)
    (hg : Ideal.Quotient.stabilizerHom Q P
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) g⁻¹ =
        Ideal.Quotient.arithmeticFrobenius P Q) :
    (cyclotomicCharacterWithCoefficients K p L g : L) = (Nat.card (𝓞 K ⧸ P) : L)⁻¹ := by
  have hpQ : (p : 𝓞 (AlgebraicClosure K)) ∉ Q := by
    intro h
    apply hp
    apply (Ideal.mem_of_liesOver Q P (p : 𝓞 K)).mpr
    simpa only [map_natCast] using h
  have hact (b : 𝓞 (AlgebraicClosure K)) :
      Ideal.Quotient.mk Q ((g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)⁻¹ • b) =
        (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 K ⧸ P) := by
    have h := congrArg (fun f : (𝓞 (AlgebraicClosure K) ⧸ Q) ≃ₐ[𝓞 K ⧸ P]
      (𝓞 (AlgebraicClosure K) ⧸ Q) => f (Ideal.Quotient.mk Q b)) hg
    simpa only [Ideal.Quotient.stabilizerHom_apply,
      Ideal.Quotient.arithmeticFrobenius_apply, Subgroup.smul_def, Subgroup.coe_inv] using h
  have h := cyclotomicCharacterWithCoefficients_eq_natCast_of_quotient_action
    K p L Q hpQ (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)⁻¹ _ hact
  have hi := congrArg (fun x : L => x⁻¹) h
  simpa only [map_inv, Units.val_inv_eq_inv_val, inv_inv] using hi

end Field
