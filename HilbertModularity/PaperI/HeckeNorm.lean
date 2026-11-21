module

public import HilbertModularity.PaperI.Automorphy

/-! # The norm term in the Hecke polynomial -/
public noncomputable section

namespace HilbertModularity.PaperI
open AlgebraicGeometry IsDedekindDomain Polynomial HilbertModularity.Cyclotomic
open HilbertModularity.Hypergeometric HilbertModularity.HilbertModularForms LocalSpecialization
open scoped NumberField
attribute [local instance] Ideal.Quotient.field realFieldAlgebra

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (m : ℕ) (hm : 0 < m) (hmP : m < p)

/-- The Euler polynomial has constant term equal to the residue norm. -/
theorem euler_polynomial_constant_of_pullbacks
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (geo : HasConductorPullbacks p hp m hm hmP ξ)
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField p))) (hq : q ∉ (eulerFamily p hp m hm hmP ξ).bad)
    (hpq : (p : 𝓞 (realCyclotomicField p)) ∉ q.asIdeal) :
    ((eulerFamily p hp m hm hmP ξ).polynomial q).coeff 0 =
      Nat.card (𝓞 (realCyclotomicField p) ⧸ q.asIdeal) := by
  let K := realCyclotomicField p
  let E := cyclotomicField p
  let L := FullConductorCompletion p
  let w := primeAboveConductor p
  let S := eulerFamily p hp m hm hmP ξ
  have hbelow : S.residueCharacteristic w = p := by
    simpa only [S, eulerFamily, chosenCommonEulerCompatibleSystem_eq_common,
      commonEulerCompatibleSystem_residueCharacteristic] using
      (NumberField.primeBelow_eq_of_liesOver E w p)
  let : Algebra.IsIntegral (𝓞 K) (𝓞 (AlgebraicClosure K)) := Algebra.IsIntegral.tower_top ℤ
  obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (AlgebraicClosure K)) q.asIdeal
  let := hQ
  let := hQq
  let g := NumberField.geometricFrobenius K (AlgebraicClosure K) q.asIdeal Q
  let b := Pi.basisFun L (Fin 2)
  have hpoly := S.frobenius_charpoly w q hq q.asIdeal rfl (by simpa only [hbelow] using hpq) Q
  have hd := euler_frobenius_det_of_pullbacks p hp m hm hmP ξ geo q.asIdeal Q hpq
  apply (algebraMap E L).injective
  change algebraMap E L ((S.polynomial q).coeff 0) = _
  rw [← Polynomial.coeff_map, ← hpoly, ← LinearMap.charpoly_toMatrix _ b, Matrix.charpoly_fin_two]
  simpa [LinearMap.det_toMatrix, g] using hd

/-- Under the labelled geometric comparison, one eigenform gives the norm-normalized
Hecke polynomial and the finite-field identities of Theorem 1.1 at every eligible prime. -/
theorem exists_norm_hecke_traces_of_cubic_of_pullbacks
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ (B : ℤ) - A)
    (geo : HasConductorPullbacks p hp m hm hmP (darmonRationalParameter p ξ₀)) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B), letI := hB
    ∃ (jF : (cyclotomicField p) →+* B) (j : B →+* Qbar), j.comp jF = (cyclotomicField p).val.toRingHom ∧
    ∃ (level : FiniteLevel (realCyclotomicField p)) (μ : AdditiveQuotientMeasure (realCyclotomicField p)) (ψ : AlgebraicGoodPrimeEigenform level μ B),
      ψ.complexEmbedding = B.val.toRingHom ∧
      ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField p))) (hP : (p : 𝓞 (cyclotomicField p)) ∉ P.asIdeal)
        (hx : P.GoodUnit (algebraMap (realCyclotomicField p) (cyclotomicField p) (darmonRationalParameter p ξ₀).val))
        (θ : AddChar (𝓞 (cyclotomicField p) ⧸ P.asIdeal) Qbar), θ ≠ 1 →
      ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField p))) (_hOver : P.asIdeal.LiesOver q.asIdeal),
        let norm := Nat.card (𝓞 (realCyclotomicField p) ⧸ q.asIdeal)
        let f := P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField p))
        let value := mccarthyValue p P hP m θ (algebraMap (realCyclotomicField p) (cyclotomicField p) (darmonRationalParameter p ξ₀).val) hx
        ∃ (hψ : q ∉ ψ.form.bad) (α β : Qbar),
          (X - C α) * (X - C β) = X ^ 2 - C (j (ψ.heckeCoefficient q hψ)) * X + C (norm : Qbar) ∧
          value = α ^ f + β ^ f ∧ (f = 1 → value = j (ψ.heckeCoefficient q hψ)) ∧
          (f = 2 → value = (j (ψ.heckeCoefficient q hψ)) ^ 2 - 2 * (norm : Qbar)) := by
  let ξ := darmonRationalParameter p ξ₀
  let K := realCyclotomicField p
  let F := cyclotomicField p
  obtain ⟨B, hNumberField, jF, level, μ, ψ, _, hψ, _, _, hpoly, _⟩ :=
    exists_chosenEuler_allPlaceEigenform_of_cubic p hp m hm hmP ξ₀ hξ hA hB hAB hdeep
  let := hNumberField
  let : Algebra F B := jF.toAlgebra
  let : Algebra F Qbar := F.val.toRingHom.toAlgebra
  let : Algebra.IsAlgebraic F B := Algebra.IsAlgebraic.tower_top (K := ℚ) (L := F) (A := B)
  let j : B →ₐ[F] Qbar := IsAlgClosed.lift
  have hj : j.toRingHom.comp jF = F.val.toRingHom := by
    ext a
    exact j.commutes a
  refine ⟨B, hNumberField, jF, j.toRingHom, hj, level, μ, ψ, hψ, ?_⟩
  intro P hP hx θ hθ q hOver
  let : P.asIdeal.LiesOver q.asIdeal := hOver
  let U := eulerFamily p hp m hm hmP ξ
  let S := chosenCommonEulerCompatibleSystemExtended p m (Fact.out : p.Prime) hp hm hmP ξ B
  have hbad := chosenCommonEulerCompatibleSystem_bad_subset p m (Fact.out : p.Prime) hp hm hmP ξ
  have hqU : q ∉ U.bad :=
    LocalSpecialization.not_mem_of_goodUnit_of_subset_badPrimesBelow ξ.val p U.bad hbad q P hx hP
  have hq : q ∉ S.bad := by
    simpa only [S, chosenCommonEulerCompatibleSystemExtended_eq_extendCoefficients,
      NumberFieldCompatibleSystem.extendCoefficients_bad] using hqU
  obtain ⟨hψq, hpolyq⟩ := hpoly q hqU
  have hHecke : (S.polynomial q).map (RingHom.id B) = ψ.heckePolynomial q hψq := by
    simpa only [S, chosenCommonEulerCompatibleSystemExtended_eq_extendCoefficients,
      NumberFieldCompatibleSystem.extendCoefficients_polynomial, RingHom.algebraMap_toAlgebra,
      Polynomial.map_id] using hpolyq
  obtain ⟨α, β, hab, hv, h1, h2⟩ :=
    Cyclotomic.exists_mccarthyValue_eq_compatibleEigenform_roots_at_good_prime
      p S ψ (RingHom.id B) j.toRingHom P hP m hm hmP θ hθ (algebraMap K F ξ.val)
      hx q hq hψq hHecke (by
        intro v hv ιv hιv Q _ _ _
        have hi : ιv.comp j.toRingHom =
            (algebraMap (v.adicCompletion B) (AlgebraicClosure (v.adicCompletion B))).comp
              (algebraMap B (v.adicCompletion B)) := by
          simpa only [RingHom.comp_id] using hιv
        simpa only [S, RingHom.comp_id] using
          chosenCommonEulerCompatibleSystemExtended_endpoint_trace p m (Fact.out : p.Prime)
            hp hm hmP ξ B j.toRingHom (by simpa only [RingHom.algebraMap_toAlgebra] using hj)
            P hP hx q hq v hv ιv hi Q)
  have hpq : (p : 𝓞 K) ∉ q.asIdeal := fun h => hP (by
    simpa using (Ideal.mem_of_liesOver P.asIdeal q.asIdeal (p : 𝓞 K)).mp h)
  let norm := Nat.card (𝓞 K ⧸ q.asIdeal)
  have hconst : (U.polynomial q).coeff 0 = (norm : F) :=
    euler_polynomial_constant_of_pullbacks p hp m hm hmP ξ geo q hqU hpq
  have cn : (norm : B) * ψ.centralCoefficient q hψq = (norm : B) := by
    have hc : (ψ.heckePolynomial q hψq).coeff 0 = jF ((U.polynomial q).coeff 0) := by
      rw [← hpolyq, Polynomial.coeff_map]
    rw [hconst, map_natCast] at hc
    have hshape := ψ.heckePolynomial_map q hψq (RingHom.id B)
    simp only [Polynomial.map_id, RingHom.id_apply] at hshape
    rw [hshape] at hc
    simpa [norm] using hc
  have cm : (norm : Qbar) * j (ψ.centralCoefficient q hψq) = (norm : Qbar) := by
    simpa using congrArg (fun a : B => j a) cn
  refine ⟨hψq, α, β, ?_, hv, h1, ?_⟩
  · rw [hab, ψ.heckePolynomial_map]
    change X ^ 2 - C (j (ψ.heckeCoefficient q hψq)) * X +
      C ((norm : Qbar) * j (ψ.centralCoefficient q hψq)) = _
    rw [cm]
    rfl
  · intro hf
    have hd := h2 hf
    change _ = (j (ψ.heckeCoefficient q hψq)) ^ 2 -
      2 * ((norm : Qbar) * j (ψ.centralCoefficient q hψq)) at hd
    rw [cm] at hd
    exact hd

end HilbertModularity.PaperI
