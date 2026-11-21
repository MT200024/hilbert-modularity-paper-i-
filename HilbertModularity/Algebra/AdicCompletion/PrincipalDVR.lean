/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.AdicCompletion.IdealPower
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Completion at a principal maximal ideal

The native completion of a domain at a nonzero principal maximal ideal is
a discrete valuation ring. Its principal generator remains regular, and
adic separatedness gives the unit-times-power factorization. This supplies
the integral RM-prime coefficient ring in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace IsLocalRing

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- A separated local ring with principal maximal ideal has unit-times-power factorization. -/
theorem exists_unit_mul_pow_of_isHausdorff
    [IsHausdorff (maximalIdeal S) S] (a : S)
    (ha : maximalIdeal S = Ideal.span {a}) {x : S} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Sˣ), x = u * a ^ n := by
  classical
  have hex : ∃ n : ℕ, x ∉ (maximalIdeal S) ^ n := by
    by_contra! h
    apply hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal S) S) x
    intro n
    simpa [SModEq.zero] using h n
  let n := Nat.find hex
  have hn : x ∉ (maximalIdeal S) ^ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    apply hn
    simp [h]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmem : x ∈ (maximalIdeal S) ^ k := by
    apply Classical.not_not.mp
    exact Nat.find_min hex (by omega)
  rw [ha, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  have hdunit : IsUnit d := by
    by_contra hdunit
    have hdmem : d ∈ maximalIdeal S := hdunit
    rw [ha, Ideal.mem_span_singleton] at hdmem
    obtain ⟨c, hc⟩ := hdmem
    apply hn
    rw [hk, ha, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, by rw [hd, hc, pow_succ, mul_assoc]⟩
  obtain ⟨u, rfl⟩ := hdunit
  exact ⟨k, u, by simpa only [mul_comm] using hd⟩

end IsLocalRing

namespace AdicCompletion

variable {R : Type*} [CommRing R]

/-- Completion at a finitely generated maximal ideal is a local ring. -/
theorem isLocalRing_of_isMaximal (I : Ideal R) [I.IsMaximal] (hI : I.FG) :
    IsLocalRing (AdicCompletion I R) := by
  have := isMaximal_map_of_le I I le_rfl hI
  have := isAdicComplete_self I hI
  exact isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap R (AdicCompletion I R)))

/-- A nonzero principal generator in a domain remains regular in its native completion. -/
theorem algebraMap_mul_eq_zero_iff [IsDomain R] (a : R) (ha : a ≠ 0)
    (x : AdicCompletion (Ideal.span {a}) R) :
    algebraMap R (AdicCompletion (Ideal.span {a}) R) a * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply ext_evalₐ
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (Ideal.span {a}) (n + 1) x)
    have hmul := congrArg (evalₐ (Ideal.span {a}) (n + 1)) h
    rw [_root_.map_mul, _root_.map_zero] at hmul
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ (n + 1)) a *
      evalₐ (Ideal.span {a}) (n + 1) x = 0 at hmul
    rw [← hr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmul
    obtain ⟨d, hd⟩ := hmul
    have hrdiv : a ^ n ∣ r := by
      refine ⟨d, ?_⟩
      apply mul_left_cancel₀ ha
      simpa only [pow_succ', mul_assoc] using hd
    rw [← factor_evalₐ (Ideal.span {a}) (Nat.le_succ n) x, ← hr]
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ n) r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hrdiv
  · rintro rfl
    exact mul_zero _

/-- Every nonzero element of the principal-prime completion is a unit times a generator power. -/
theorem exists_unit_mul_pow (a : R) [(Ideal.span {a}).IsMaximal]
    {x : AdicCompletion (Ideal.span {a}) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (Ideal.span {a}) R)ˣ),
      x = u * (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) ^ n := by
  let := isLocalRing_of_isMaximal (Ideal.span {a}) (Submodule.fg_span_singleton _)
  have := isAdicComplete_self (Ideal.span {a}) (Submodule.fg_span_singleton _)
  have hm := isMaximal_map_of_le (Ideal.span {a}) (Ideal.span {a}) le_rfl
    (Submodule.fg_span_singleton _)
  have hmax := (IsLocalRing.eq_maximalIdeal hm).symm
  have : IsHausdorff (IsLocalRing.maximalIdeal (AdicCompletion (Ideal.span {a}) R))
      (AdicCompletion (Ideal.span {a}) R) := by
    rw [hmax]
    infer_instance
  apply IsLocalRing.exists_unit_mul_pow_of_isHausdorff _ _ hx
  simpa only [Ideal.map_span, Set.image_singleton] using hmax

/-- Completion at a nonzero principal maximal ideal of a domain is a domain. -/
theorem isDomain_of_isMaximal_span [IsDomain R] (a : R) (ha : a ≠ 0)
    [(Ideal.span {a}).IsMaximal] : IsDomain (AdicCompletion (Ideal.span {a}) R) := by
  let S := AdicCompletion (Ideal.span {a}) R
  let := isLocalRing_of_isMaximal (Ideal.span {a}) (Submodule.fg_span_singleton _)
  have hpowers (n : ℕ) (y : S) : (algebraMap R S a) ^ n * y = 0 → y = 0 := by
    induction n with
    | zero => simpa only [pow_zero, one_mul] using (id : y = 0 → y = 0)
    | succ n ih =>
      intro h
      rw [pow_succ', mul_assoc] at h
      exact ih ((algebraMap_mul_eq_zero_iff a ha _).mp h)
  have : NoZeroDivisors S := ⟨fun {x y} h => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      obtain ⟨n, u, rfl⟩ := exists_unit_mul_pow a hx
      rw [mul_assoc, u.mul_right_eq_zero] at h
      exact hpowers n y h⟩
  exact (isDomain_iff_noZeroDivisors_and_nontrivial S).mpr ⟨inferInstance, inferInstance⟩

/-- The native completion at a nonzero principal maximal ideal of a domain is a DVR. -/
theorem isDiscreteValuationRing_of_isMaximal_span [IsDomain R] (a : R) (ha : a ≠ 0)
    [(Ideal.span {a}).IsMaximal] :
    letI := isDomain_of_isMaximal_span a ha
    IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R) := by
  let := isDomain_of_isMaximal_span a ha
  let := isLocalRing_of_isMaximal (Ideal.span {a}) (Submodule.fg_span_singleton _)
  let S := AdicCompletion (Ideal.span {a}) R
  have haS : algebraMap R S a ≠ 0 := by
    intro h
    have hz : algebraMap R S a * 1 = 0 := by rw [h, zero_mul]
    exact one_ne_zero ((algebraMap_mul_eq_zero_iff a ha 1).mp hz)
  have hm := isMaximal_map_of_le (Ideal.span {a}) (Ideal.span {a}) le_rfl
    (Submodule.fg_span_singleton _)
  have hirr : Irreducible (algebraMap R S a) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ haS (by
      simpa only [Ideal.map_span, Set.image_singleton] using (IsLocalRing.eq_maximalIdeal hm).symm)
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨algebraMap R S a, hirr, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu⟩ := exists_unit_mul_pow a hx
  exact ⟨n, ⟨u, by simpa only [mul_comm] using hu.symm⟩⟩

end AdicCompletion
