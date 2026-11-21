/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem

/-! # Coefficient places away from a geometric prime

A place above two or three suffices for every geometric prime. This choice
removes the residue characteristic of an initial comparison from subsequent
all-place trace deductions.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

namespace HilbertModularForms

omit [NumberField F] in
/-- At a geometric prime, one of the rational primes two and three is a unit. -/
theorem two_or_three_away_from_prime
    (P : Ideal (𝓞 F)) [P.IsMaximal] :
    (2 : 𝓞 F) ∉ P ∨ (3 : 𝓞 F) ∉ P := by
  by_contra h
  simp only [not_or, not_not] at h
  have h1 : (1 : 𝓞 F) ∈ P := by
    convert P.sub_mem h.2 h.1 using 1; norm_num
  exact Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)
    ((Ideal.eq_top_iff_one P).mpr h1)

end HilbertModularForms

/-- A coefficient number field has a finite place above each rational prime. -/
theorem NumberFieldCompatibleSystem.exists_place_of_prime
    (D : NumberFieldCompatibleSystem F E)
    (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), D.residueCharacteristic w = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hspan : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    intro h
    have hmem : (p : ℤ) ∈ (⊥ : Ideal ℤ) := by
      rw [← h]
      exact Ideal.subset_span (by simp)
    exact hp0 (by simpa using hmem)
  have hQbot : Q ≠ ⊥ := by
    have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hOver
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hspan Q
  let w : HeightOneSpectrum (𝓞 E) :=
    { asIdeal := Q
      isPrime := hQ.isPrime
      ne_bot := hQbot }
  have heq : Ideal.span {(D.residueCharacteristic w : ℤ)} =
      Ideal.span {(p : ℤ)} :=
    (D.coefficientPrime w).over.trans hOver.over.symm
  have hmem : (p : ℤ) ∈ Ideal.span {(D.residueCharacteristic w : ℤ)} := by
    rw [heq]
    exact Ideal.subset_span (by simp)
  have hdvd : D.residueCharacteristic w ∣ p := by
    exact_mod_cast (Ideal.mem_span_singleton.mp hmem)
  exact ⟨w, (Nat.prime_dvd_prime_iff_eq (D.residueCharacteristic_prime w) hp).mp hdvd⟩

/-- One of two fixed coefficient places lies away from any geometric prime. -/
theorem NumberFieldCompatibleSystem.exists_place_away_from_prime
    (D : NumberFieldCompatibleSystem F E)
    (P : Ideal (𝓞 F)) [P.IsMaximal] :
    ∃ w : HeightOneSpectrum (𝓞 E),
      (D.residueCharacteristic w : 𝓞 F) ∉ P := by
  obtain ⟨w₂, hw₂⟩ := D.exists_place_of_prime 2 Nat.prime_two
  obtain ⟨w₃, hw₃⟩ := D.exists_place_of_prime 3 Nat.prime_three
  rcases HilbertModularForms.two_or_three_away_from_prime P with h₂ | h₃
  · exact ⟨w₂, by simpa only [hw₂, Nat.cast_ofNat] using h₂⟩
  · exact ⟨w₃, by simpa only [hw₃, Nat.cast_ofNat] using h₃⟩

end HilbertModularity
