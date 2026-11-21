/- Assembled by AxiomProver. -/

module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Symmetric rank-two hypergeometric parameters

The numerator parameters are `m / N` and `1 - m / N`, and the denominator
parameters are `1, 1`. Their rational representatives are retained alongside
the datum in `ℚ / ℤ`. Parameters in the open unit interval are nonintegral;
coprimality supplies the Euler-curve irreducibility condition.

## Main definitions

* `numeratorParameters`, `denominatorParameters`: rational representatives.
* `symmetricDatum`: the pair of parameter multisets modulo the integers.

## References

[TripathiGoswami], §§2.1 and 2.4, the genericity and `(Irr)` checks.
-/

namespace HilbertModularity.Hypergeometric

/-- The two rational numerator parameters, with multiplicity. -/
def numeratorParameters (N m : ℕ) : Multiset ℚ :=
  {(m : ℚ) / N, 1 - (m : ℚ) / N}

/-- Rational denominator representatives for the symmetric rank-two family. -/
def denominatorParameters : Multiset ℚ := {1, 1}

/-- The symmetric rank-two hypergeometric datum in `ℚ / ℤ`. -/
def symmetricDatum (N m : ℕ) :
    Multiset (AddCircle (1 : ℚ)) × Multiset (AddCircle (1 : ℚ)) :=
  ((numeratorParameters N m).map ((↑) : ℚ → AddCircle (1 : ℚ)),
    denominatorParameters.map ((↑) : ℚ → AddCircle (1 : ℚ)))

/-- A rational number strictly between zero and one is nonzero modulo the integers. -/
lemma mod_one_ne_zero {a : ℚ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    (a : AddCircle (1 : ℚ)) ≠ 0 := by
  rw [ne_eq, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  have hn₀ : (0 : ℤ) < n := by exact_mod_cast (hn ▸ ha₀)
  have hn₁ : n < (1 : ℤ) := by exact_mod_cast (hn ▸ ha₁)
  omega

/-- Numerator and denominator multisets have no common class modulo the integers. -/
theorem symmetricDatum_generic {N m : ℕ} (hm₀ : 0 < m) (hmN : m < N) :
    ∀ a ∈ (symmetricDatum N m).1, ∀ b ∈ (symmetricDatum N m).2, a ≠ b := by
  have hN : (0 : ℚ) < N := by exact_mod_cast (lt_trans hm₀ hmN)
  have ha₀ : (0 : ℚ) < (m : ℚ) / N := div_pos (by exact_mod_cast hm₀) hN
  have ha₁ : (m : ℚ) / N < 1 := (div_lt_one hN).mpr (by exact_mod_cast hmN)
  intro a ha b hb
  have hb₀ : b = 0 := by
    simpa [symmetricDatum, denominatorParameters, AddCircle.coe_period] using hb
  have ha' : a = (((m : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) ∨
      a = ((1 - (m : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) := by
    simpa [symmetricDatum, numeratorParameters] using ha
  subst b
  rcases ha' with rfl | rfl
  · exact mod_one_ne_zero ha₀ ha₁
  · exact mod_one_ne_zero (by linarith) (by linarith)

/-- The three scaled Euler-curve differences are integers whose common gcd
with the denominator is one. These are the differences `N(d-b)`, `N(b-c)`
and `N(a-d)` for `(a,b,c,d) = (m/N, 1-m/N, 1, 1)`. -/
theorem symmetricParameters_irreducible {N m : ℕ} (hN : N ≠ 0)
    (hm : m.Coprime N) :
    ∃ u v w : ℤ,
      (N : ℚ) * (1 - (1 - (m : ℚ) / N)) = u ∧
      (N : ℚ) * ((1 - (m : ℚ) / N) - 1) = v ∧
      (N : ℚ) * ((m : ℚ) / N - 1) = w ∧
      Nat.gcd (Int.gcd u v) (Int.gcd w N) = 1 := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  refine ⟨m, -(m : ℤ), (m : ℤ) - N, ?_, ?_, ?_, ?_⟩
  · push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring
  · push_cast
    field_simp
  · simp only [Int.gcd, Int.natAbs_natCast, Int.natAbs_neg, Nat.gcd_self]
    apply Nat.dvd_one.mp
    rw [← hm.gcd_eq_one]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))

/-- The numerator multiset modulo integers is the pair of opposite classes. -/
theorem symmetricDatum_fst (N m : ℕ) :
    (symmetricDatum N m).1 =
      {(((m : ℚ) / N : ℚ) : AddCircle (1 : ℚ)), -(((m : ℚ) / N : ℚ) : AddCircle (1 : ℚ))} := by
  simp [symmetricDatum, numeratorParameters, AddCircle.coe_period]

/-- Both denominator parameters are zero modulo integers. -/
theorem symmetricDatum_snd (N m : ℕ) :
    (symmetricDatum N m).2 = {0, 0} := by
  simp [symmetricDatum, denominatorParameters, AddCircle.coe_period]

/-- Coprimality gives exact additive order to the first numerator parameter. -/
theorem numeratorParameter_addOrderOf {N m : ℕ} [NeZero N] (hm : m.Coprime N) :
    addOrderOf (((m : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) = N := by
  simpa only [mul_one] using
    (AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℚ)) (NeZero.pos N) hm.gcd_eq_one)

/-- Multiplication by an integer preserves both parameter multisets exactly
when its residue class is one of the two signs. -/
theorem symmetricDatum_map_zsmul_eq_iff {N m : ℕ} [NeZero N]
    (hm : m.Coprime N) (k : ℤ) :
    ((symmetricDatum N m).1.map (fun a => k • a) = (symmetricDatum N m).1 ∧
      (symmetricDatum N m).2.map (fun a => k • a) = (symmetricDatum N m).2) ↔
      (k : ZMod N) = 1 ∨ (k : ZMod N) = -1 := by
  let a : AddCircle (1 : ℚ) := ((m : ℚ) / N : ℚ)
  have ha : addOrderOf a = N := numeratorParameter_addOrderOf hm
  have hplus : k • a = a ↔ (k : ZMod N) = 1 := by
    have h := zsmul_eq_zsmul_iff_modEq (x := a) (m := k) (n := 1)
    rw [ha] at h
    simpa only [one_zsmul, Int.cast_one] using
      h.trans (ZMod.intCast_eq_intCast_iff k 1 N).symm
  have hminus : k • a = -a ↔ (k : ZMod N) = -1 := by
    have h := zsmul_eq_zsmul_iff_modEq (x := a) (m := k) (n := -1)
    rw [ha] at h
    simpa only [neg_one_zsmul, Int.cast_neg, Int.cast_one] using
      h.trans (ZMod.intCast_eq_intCast_iff k (-1) N).symm
  rw [symmetricDatum_fst, symmetricDatum_snd]
  change (({a, -a} : Multiset _).map (fun b => k • b) = {a, -a} ∧
    ({0, 0} : Multiset (AddCircle (1 : ℚ))).map (fun b => k • b) = {0, 0}) ↔ _
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, smul_zero, zsmul_neg,
    and_true]
  rw [← hplus, ← hminus]
  constructor
  · intro h
    have hm : k • a ∈ a ::ₘ {-a} := by rw [← h]; simp
    simpa using hm
  · rintro (h | h)
    · rw [h]
    · rw [h, neg_neg]
      exact Multiset.pair_comm _ _

/-- [TripathiGoswami], §1.3: the stabilizer of the two actual parameter
multisets in the unit group modulo the denominator is `{1, -1}`. -/
theorem symmetricDatum_stabilizer_iff {N m : ℕ} [NeZero N]
    (hm : m.Coprime N) (h : (ZMod N)ˣ) :
    ((symmetricDatum N m).1.map (fun a => ((h : ZMod N).val : ℤ) • a) =
        (symmetricDatum N m).1 ∧
      (symmetricDatum N m).2.map (fun a => ((h : ZMod N).val : ℤ) • a) =
        (symmetricDatum N m).2) ↔ h = 1 ∨ h = -1 := by
  rw [symmetricDatum_map_zsmul_eq_iff hm]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl) <;> simp

end HilbertModularity.Hypergeometric
