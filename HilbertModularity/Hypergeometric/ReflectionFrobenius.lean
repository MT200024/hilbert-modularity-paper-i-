/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ReflectionCharacter
public import HilbertModularity.Hypergeometric.SpecializationInvolution
public import HilbertModularity.NumberTheory.Frobenius

/-! # Computing the quadratic reflection character

We compute the global character on an automorphism with a specified power
action on a square root of the cyclotomic generator. This is the algebraic
step in identifying its arithmetic Frobenius values in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace MulChar

/-- A finite-field character of exact order `N` takes the value `(-1)^k`
at minus one when the odd field cardinality is `N*k+1`. -/
theorem apply_neg_one_of_order {F C : Type*} [Field F] [Fintype F] [Field C]
    (χ : MulChar F C) (N : ℕ) [NeZero N] (hχ : orderOf χ = N)
    (k : ℕ) (hcard : Fintype.card F = N * k + 1) (hodd : Odd (Fintype.card F)) :
    χ (-1) = (-1 : C) ^ k := by
  classical
  rcases Nat.even_or_odd N with hNeven | hNodd
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hgorder : orderOf (g : F) = Fintype.card F - 1 := by
      rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg,
        Nat.card_eq_fintype_card, Fintype.card_units]
    have hgp : IsPrimitiveRoot (g : F) (Fintype.card F - 1) := by
      rw [← hgorder]
      exact IsPrimitiveRoot.orderOf _
    have hχg : IsPrimitiveRoot (χ g) N := by
      rw [← hχ, ← MulChar.orderOf_apply_generator χ hg]
      exact IsPrimitiveRoot.orderOf _
    have hqpos : 0 < Fintype.card F - 1 := by
      have := Fintype.one_lt_card (α := F)
      omega
    have hqhalf : Fintype.card F - 1 = ((Fintype.card F - 1) / 2) * 2 := by
      obtain ⟨j, hj⟩ := hodd
      omega
    have hNhalf : N = (N / 2) * 2 := by obtain ⟨j, hj⟩ := hNeven; omega
    have hgneg : (g : F) ^ ((Fintype.card F - 1) / 2) = -1 :=
      (IsPrimitiveRoot.pow hqpos hgp hqhalf).eq_neg_one_of_two_right
    have hχneg : (χ g) ^ (N / 2) = -1 :=
      (IsPrimitiveRoot.pow (NeZero.pos N) hχg hNhalf).eq_neg_one_of_two_right
    have hhalf : (Fintype.card F - 1) / 2 = (N / 2) * k := by
      have hc : Fintype.card F - 1 = N * k := by omega
      rw [hc, Nat.mul_comm N k, Nat.mul_div_assoc k (even_iff_two_dvd.mp hNeven),
        Nat.mul_comm]
    rw [← hgneg, map_pow, hhalf, pow_mul, hχneg]
  · have hk : Even k := by
      simpa only [hcard, Nat.odd_add_one, Nat.odd_mul, hNodd, true_and,
        Nat.not_odd_iff_even] using hodd
    rw [HilbertModularity.Hypergeometric.character_neg_one_of_odd_power χ N hNodd
      (by simpa only [hχ] using pow_orderOf_eq_one χ), hk.neg_one_pow]

end MulChar

namespace HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N]

/-- The trace of a half-root is a square root of the real radicand. -/
theorem halfRoot_trace_sq (w : Qbar) (hw : w ^ 2 = zeta N) :
    (w + w⁻¹) ^ 2 = algebraMap (realCyclotomicField N) Qbar (reflectionRadicand N) := by
  have hw0 : w ≠ 0 := by
    intro h
    apply (zeta_isPrimitiveRoot N).ne_zero (NeZero.ne N)
    rw [← hw, h]
    simp
  change (w + w⁻¹) ^ 2 = 2 + ((zeta N) ^ 1 + ((zeta N)⁻¹) ^ 1)
  simp only [pow_one]
  calc
    _ = 2 + (w ^ 2 + (w ^ 2)⁻¹) := by field_simp [hw0]; ring
    _ = _ := by rw [hw]

/-- A half-root trace is nonzero at the manuscript levels. -/
theorem halfRoot_trace_ne_zero (hN : 3 ≤ N) (w : Qbar) (hw : w ^ 2 = zeta N) :
    w + w⁻¹ ≠ 0 := by
  intro h
  apply (map_ne_zero (algebraMap (realCyclotomicField N) Qbar)).mpr
    (reflectionRadicand_ne_zero N hN)
  rw [← halfRoot_trace_sq N w hw, h]
  simp

/-- The global character is the sign with which the automorphism acts on a
half-root. Root-choice independence makes this independent of the chosen radical. -/
theorem reflectionCharacter_apply_of_halfRoot (hN : 3 ≤ N)
    (w : Qbar) (hw : w ^ 2 = zeta N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar) (ε : Qbarˣ)
    (hε : ε ^ 2 = 1) (hgw : g w = (ε : Qbar) * w) :
    reflectionCharacter N hN g = ε := by
  have heq := Galois.quadraticCharacter_root_independent (reflectionRadicand N)
    (reflectionRoot N) (w + w⁻¹) (reflectionRoot_ne_zero N hN)
    (halfRoot_trace_ne_zero N hN w hw) (reflectionRoot_sq N) (halfRoot_trace_sq N w hw)
  change Galois.quadraticCharacter _ _ _ _ g = ε
  rw [heq]
  apply Units.ext
  change g (w + w⁻¹) / (w + w⁻¹) = (ε : Qbar)
  apply (div_eq_iff (halfRoot_trace_ne_zero N hN w hw)).mpr
  rw [map_add, map_inv₀, hgw]
  have hε' : (ε : Qbar) ^ 2 = 1 := congrArg Units.val hε
  rcases sq_eq_one_iff.mp hε' with h | h <;> rw [h] <;> simp [mul_add]

/-- At an even level, every square root of a primitive level root has
`N`th power minus one. -/
theorem halfRoot_pow_of_even (hN : 3 ≤ N) (heven : Even N)
    (w : Qbar) (hw : w ^ 2 = zeta N) : w ^ N = -1 := by
  have hsq : (w ^ N) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul, hw, (zeta_isPrimitiveRoot N).pow_eq_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · obtain ⟨k, hk⟩ := heven
    have hk2 : N = 2 * k := by omega
    have hp : (zeta N) ^ k = 1 := by
      calc
        _ = (w ^ 2) ^ k := congrArg (fun z : Qbar => z ^ k) hw.symm
        _ = w ^ N := by rw [← pow_mul, ← hk2]
        _ = 1 := h
    exact ((zeta_isPrimitiveRoot N).pow_ne_one_of_pos_of_lt (by omega : k ≠ 0)
      (by omega : k < N) hp).elim
  · exact h

/-- A power action of odd degree `q=N*k+1` has reflection sign `(-1)^k`.
This computes the character once the arithmetic Frobenius power action is supplied. -/
theorem reflectionCharacter_apply_of_power (hN : 3 ≤ N)
    (w : Qbar) (hw : w ^ 2 = zeta N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar) (q k : ℕ)
    (hq : q = N * k + 1) (hqodd : Odd q) (hg : g w = w ^ q) :
    reflectionCharacter N hN g = (-1 : Qbarˣ) ^ k := by
  have hsq : (w ^ N) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul, hw, (zeta_isPrimitiveRoot N).pow_eq_one]
  have hp : (w ^ N) ^ k = (-1 : Qbar) ^ k := by
    rcases Nat.even_or_odd N with heven | hodd
    · rw [halfRoot_pow_of_even N hN heven w hw]
    · have hk : Even k := by
        simpa only [hq, Nat.odd_add_one, Nat.odd_mul, hodd, true_and,
          Nat.not_odd_iff_even] using hqodd
      obtain ⟨j, hj⟩ := hk
      have hj2 : k = 2 * j := by omega
      rw [hj2, pow_mul, hsq, one_pow, pow_mul, neg_one_sq, one_pow]
  apply reflectionCharacter_apply_of_halfRoot N hN w hw g ((-1 : Qbarˣ) ^ k)
  · apply Units.ext
    change ((-1 : Qbar) ^ k) ^ 2 = 1
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, neg_one_sq, one_pow]
  · change g w = (-1 : Qbar) ^ k * w
    rw [hg, hq, pow_add, pow_one, pow_mul, hp]

open scoped NumberField
open IsDedekindDomain
attribute [local instance] Ideal.Quotient.field

variable (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)

/-- The canonical residue field is finite. -/
local instance instFintypeReflectionFrobeniusResidue :
    Fintype (𝓞 (cyclotomicField N) ⧸ P.asIdeal) := Fintype.ofFinite _

private theorem residue_card_eq_level_mul
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) :
    Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) =
      N * ((Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1) / N) + 1 := by
  have hd := Nat.div_mul_cancel (dvd_residue_card_sub_one N P.asIdeal hP)
  rw [Nat.mul_comm] at hd
  have hpos : 0 < Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  omega

/-- The canonical residue-character sign is the explicit parity of its
power-residue exponent, at every odd residue cardinality. -/
theorem reflectionSign_eq_neg_one_pow (m : ℕ)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal))) :
    reflectionSign N P hP m =
      (-1 : Qbarˣ) ^ (((Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1) / N) * m) := by
  classical
  let χ := powerResidueMulChar N P.asIdeal hP
  let k := (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) - 1) / N
  have hneg : χ (-1) = (-1 : Qbar) ^ k :=
    MulChar.apply_neg_one_of_order χ N (powerResidueMulChar_orderOf N P.asIdeal hP) k
      (by simpa only [k, Nat.card_eq_fintype_card] using residue_card_eq_level_mul N P hP)
      (by simpa only [Nat.card_eq_fintype_card] using hodd)
  have hp : (χ ^ m) (-1) = χ (-1) ^ m := by
    simpa only [Units.val_neg, Units.val_one] using
      χ.pow_apply_coe m (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ)
  apply Units.ext
  rw [coe_reflectionSign]
  change (χ ^ m) (-1) = (-1 : Qbar) ^ (k * m)
  rw [hp, hneg, ← pow_mul]

/-- The global quadratic character, raised to the actual label, equals the
canonical finite-field reflection sign under the arithmetic power action. -/
theorem reflectionCharacter_pow_eq_reflectionSign (hN : 3 ≤ N)
    (w : Qbar) (hw : w ^ 2 = zeta N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : g w = w ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)) (m : ℕ) :
    reflectionCharacter N hN g ^ m = reflectionSign N P hP m := by
  rw [reflectionCharacter_apply_of_power N hN w hw g _ _
      (residue_card_eq_level_mul N P hP) hodd hg,
    reflectionSign_eq_neg_one_pow N P hP m hodd, ← pow_mul]

/-- Exact arithmetic McCarthy values transform by the specified global
quadratic character whenever its arithmetic power-action hypothesis holds. -/
theorem mccarthyValue_complement_eq_global_character (hN : 3 ≤ N)
    (w : Qbar) (hw : w ^ 2 = zeta N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : g w = w ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal))
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN g ^ m : Qbarˣ) : Qbar) * mccarthyValue N P hP m θ ξ hξ := by
  rw [mccarthyValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_pow_eq_reflectionSign N P hP hN w hw g hodd hg m]

/-- The same global-character value gives the exact GPRV finite-sum reflection. -/
theorem gprvValue_complement_eq_global_character (hN : 3 ≤ N)
    (w : Qbar) (hw : w ^ 2 = zeta N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : g w = w ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal))
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    gprvValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN g ^ m : Qbarˣ) : Qbar) * gprvValue N P hP m θ ξ hξ := by
  rw [gprvValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_pow_eq_reflectionSign N P hP hN w hw g hodd hg m]

/-- The arithmetic residue power action lifts to a half-root away from `2N`,
using the actual prime quotient of the algebraic integer ring. -/
theorem halfRoot_power_action_of_residue
    (w : Qbar) (hw : w ^ 2 = zeta N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar) (q : ℕ)
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hg : ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q (g • b) = (Ideal.Quotient.mk Q b) ^ q) :
    g w = w ^ q := by
  have : NeZero (2 * N) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne N)⟩
  have hwunity : w ^ (2 * N) = 1 := by
    rw [pow_mul, hw, (zeta_isPrimitiveRoot N).pow_eq_one]
  let v : 𝓞 Qbar := ⟨w, IsIntegral.of_pow (NeZero.pos (2 * N)) (by
    rw [hwunity]
    exact isIntegral_one)⟩
  let ζ : 𝓞 Qbar := ⟨zeta (2 * N),
    (zeta_isPrimitiveRoot (2 * N)).isIntegral (NeZero.pos (2 * N))⟩
  have hζ : IsPrimitiveRoot ζ (2 * N) :=
    (zeta_isPrimitiveRoot (2 * N)).of_map_of_injective
      (f := algebraMap (𝓞 Qbar) Qbar) NumberField.RingOfIntegers.coe_injective
  have hv : v ^ (2 * N) = 1 := by
    apply NumberField.RingOfIntegers.ext
    exact hwunity
  have h := Ideal.smul_root_eq_pow_of_quotient_action Q g q hg
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hQ) hζ hv
  exact congrArg (fun b : 𝓞 Qbar => (b : Qbar)) h

/-- A genuine arithmetic residue Frobenius action yields the canonical
primewise reflection sign of the global character. -/
theorem reflectionCharacter_pow_eq_reflectionSign_of_residue (hN : 3 ≤ N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q (g • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)) (m : ℕ) :
    reflectionCharacter N hN g ^ m = reflectionSign N P hP m := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (zeta N) zero_lt_two
  apply reflectionCharacter_pow_eq_reflectionSign N P hP hN w hw g hodd
  exact halfRoot_power_action_of_residue N w hw g _ Q hQ hg

/-- The global quadratic character is trivial on the actual inertia subgroup
at every algebraic prime away from `2N`. -/
theorem reflectionCharacter_inertia_eq_one (hN : 3 ≤ N)
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (g : Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar)) :
    reflectionCharacter N hN g = 1 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (zeta N) zero_lt_two
  have hg : ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q ((g : Qbar ≃ₐ[realCyclotomicField N] Qbar) • b) =
      (Ideal.Quotient.mk Q b) ^ 1 := by
    intro b
    rw [pow_one, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact (Ideal.mem_inertia.mp g.property) b
  have hgw := halfRoot_power_action_of_residue N w hw g 1 Q hQ hg
  apply reflectionCharacter_apply_of_halfRoot N hN w hw g 1 (by simp)
  simpa only [pow_one, Units.val_one, one_mul] using hgw

/-- Geometric Frobenius gives the identical sign: its inverse has the
arithmetic residue action, and the global character has order dividing two. -/
theorem reflectionCharacter_pow_eq_reflectionSign_of_geometric_residue (hN : 3 ≤ N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q (g⁻¹ • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)) (m : ℕ) :
    reflectionCharacter N hN g ^ m = reflectionSign N P hP m := by
  have h := reflectionCharacter_pow_eq_reflectionSign_of_residue
    N P hP hN g⁻¹ Q hQ hodd hg m
  have hs := congrArg (fun χ : (Qbar ≃ₐ[realCyclotomicField N] Qbar) →* Qbarˣ => χ g)
    (reflectionCharacter_sq N hN)
  change reflectionCharacter N hN g ^ 2 = 1 at hs
  have hi : (reflectionCharacter N hN g)⁻¹ = reflectionCharacter N hN g :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  simpa only [map_inv, hi] using h

/-- The McCarthy reflection identity with the actual global character at a
geometric residue Frobenius, uniformly in every good parameter. -/
theorem mccarthyValue_complement_eq_geometric_character (hN : 3 ≤ N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q (g⁻¹ • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal))
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN g ^ m : Qbarˣ) : Qbar) * mccarthyValue N P hP m θ ξ hξ := by
  rw [mccarthyValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_pow_eq_reflectionSign_of_geometric_residue N P hP hN g Q hQ hodd hg m]

/-- The GPRV normalization has the same global-character reflection formula
at a geometric residue Frobenius. -/
theorem gprvValue_complement_eq_geometric_character (hN : 3 ≤ N)
    (g : Qbar ≃ₐ[realCyclotomicField N] Qbar)
    (Q : Ideal (𝓞 Qbar)) [Q.IsPrime] (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (hg : ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q (g⁻¹ • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal))
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    gprvValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN g ^ m : Qbarˣ) : Qbar) * gprvValue N P hP m θ ξ hξ := by
  rw [gprvValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_pow_eq_reflectionSign_of_geometric_residue N P hP hN g Q hQ hodd hg m]

end HilbertModularity.Cyclotomic
