/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTraceAtEveryGoodPrime

/-! # Algebraic Frobenius polynomials after promotion

At a prime good for both systems, choose a coefficient completion away from its
residue characteristic. Promotion compares the actual actions there. Since the
canonical embedding of the common coefficient number field is injective, the
comparison descends to an equality in that number field. This is the algebraic
polynomial form of [TripathiGoswami, Lemma “Promotion from one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

omit [NumberField E] in
/-- The residue characteristic of a fixed coefficient place is intrinsic to
that place, even when recorded separately by two systems. -/
theorem residueCharacteristic_eq_of_same_coefficientPlace
    (w : HeightOneSpectrum (𝓞 E))
    (p r : ℕ) (hp : p.Prime) (hr : r.Prime)
    (hwp : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    (hwr : w.asIdeal.LiesOver (Ideal.span {(r : ℤ)})) : p = r := by
  have heq : (Ideal.span {(p : ℤ)} : Ideal ℤ) = Ideal.span {(r : ℤ)} :=
    hwp.over.trans hwr.over.symm
  have hmem : (p : ℤ) ∈ (Ideal.span {(r : ℤ)} : Ideal ℤ) := by
    rw [← heq]
    exact Ideal.subset_span (by simp)
  have hdvd : r ∣ p := by
    exact_mod_cast (Ideal.mem_span_singleton.mp hmem)
  exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hdvd |>.symm

/-- One coefficient place can be chosen away from the geometric prime for
both the manuscript system and the independently supplied eigenform actions. -/
theorem EigenformCohomologicalActions.exists_common_place_away_from_prime
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (P : Ideal (𝓞 F)) [P.IsMaximal] :
    ∃ w : HeightOneSpectrum (𝓞 E),
      (D.residueCharacteristic w : 𝓞 F) ∉ P ∧
      (ρ.residueCharacteristic w : 𝓞 F) ∉ P := by
  obtain ⟨w, hw⟩ := D.exists_place_away_from_prime P
  have heq : ρ.residueCharacteristic w = D.residueCharacteristic w :=
    residueCharacteristic_eq_of_same_coefficientPlace w
      (ρ.residueCharacteristic w) (D.residueCharacteristic w)
      (ρ.residueCharacteristic_prime w) (D.residueCharacteristic_prime w)
      (ρ.coefficientPrime w) (D.coefficientPrime w)
  exact ⟨w, hw, by simpa only [heq] using hw⟩

/-- At every geometric prime good for the two systems, the manuscript
system's common algebraic Frobenius polynomial is the independently defined
Hecke polynomial with roots scaled by the one algebraic comparison character.
The Frobenius lift is retained in the statement; independence of its choice
requires the character to be unramified. -/
theorem EigenformCohomologicalActions.algebraic_heckePolynomial_of_promotedComparison
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (D.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hρ : q ∉ ρ.bad) (hφ : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    ρ.polynomial q = (φ.heckePolynomial q hφ).scaleRoots
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) := by
  obtain ⟨w, hwD, hwρ⟩ := D.exists_common_place_away_from_prime ρ P
  let S := D.toCompatibleSystem
  have he₀ : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)) := by
    simpa only [S, D.toCompatibleSystem_action] using e₀
  obtain ⟨e⟩ := ρ.promote_characterComparison S.system χ w₀ he₀ w
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let ι := algebraMap E (w.adicCompletion E)
  have : Infinite (w.adicCompletion E) := Infinite.of_injective ι ι.injective
  apply Polynomial.map_injective ι ι.injective
  calc
    (ρ.polynomial q).map ι = (ρ.action w g).charpoly :=
      (ρ.frobenius_charpoly w q hρ P hP hwρ Q).symm
    _ = (((Representation.ofCharacter (χ.local w)).tprod (D.action w)) g).charpoly := by
      simpa only [S, D.toCompatibleSystem_action] using e.charpoly_eq g
    _ = ((φ.heckePolynomial q hφ).scaleRoots (χ.toMonoidHom g : E)).map ι :=
      Representation.charpoly_characterTensor_eq_map_scaleRoots ι (D.action w)
        (χ.local w) g (φ.heckePolynomial q hφ) (χ.toMonoidHom g : E)
        (D.frobenius_charpoly w q hφ P hP hwD Q) (by
          rw [χ.local_eq_composition]
          rfl)

end HilbertModularity.HilbertModularForms
