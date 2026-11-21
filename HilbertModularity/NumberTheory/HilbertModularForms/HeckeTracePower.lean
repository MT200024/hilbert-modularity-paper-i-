/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.PromotionPowerTrace
public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeTraceAlgebraicCharacter

/-! # Degree-two Hecke traces under compatible-system promotion

For a degree-two Frobenius power, the trace is `a² - 2δ`, where `a` and `δ`
are the trace and determinant of the original degree-one Frobenius. The
determinant comes from the independent central Hecke coefficient. This is the
power-trace identity of [TripathiGoswami, §1.1 and Lemma “Promotion from
one realization”], rather than the symmetric-square identity `a² - δ`.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The geometric-Frobenius square has trace `a_q² - 2 Nq ω_q` at each
coefficient completion. -/
theorem EigenformCompatibleSystem.frobenius_trace_sq
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (S : EigenformCompatibleSystem φ)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
      ((S.system.action w
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ 2) =
      (algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq)) ^ 2 -
        2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
          algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq)) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let A := S.system.action w g
  let b := Pi.basisFun (w.adicCompletion E) (Fin 2)
  let M := LinearMap.toMatrix b b A
  have ht : M.trace =
      algebraMap E (w.adicCompletion E) (φ.heckeCoefficient q hq) := by
    simpa only [M, ← LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b]
      using S.frobenius_trace w q hq P hP hp Q
  have hd : M.det =
      (Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
        algebraMap E (w.adicCompletion E) (φ.centralCoefficient q hq) := by
    simpa only [M, ← LinearMap.det_toMatrix b]
      using S.frobenius_det w q hq P hP hp Q
  have hmatrix := two_mul_det_eq_sq_trace_sub_trace_sq M
  rw [ht, hd] at hmatrix
  rw [LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
    ← LinearMap.toMatrix_pow]
  change (M ^ 2).trace = _
  linear_combination hmatrix

/-- One-place comparison carries the degree-two Hecke power trace to every
coefficient completion outside a single finite exceptional set. -/
theorem EigenformCompatibleSystem.heckeTrace_sq_of_characterComparisonGood
    (φ : AlgebraicGoodPrimeEigenform level μ E)
    (S : EigenformCompatibleSystem φ)
    (ρ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (S.system.action w₀)))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad S.system χ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        ((ρ.action w (NumberField.geometricFrobenius F
          (AlgebraicClosure F) P Q)) ^ 2) =
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
          w.adicCompletion E) ^ 2 *
        ((algebraMap E (w.adicCompletion E)
          (φ.heckeCoefficient q (by
            have h := ρ.good_of_not_mem_characterComparisonBad S.system χ w₀ w q hq
            rw [← S.bad_eq]
            exact h.2.1))) ^ 2 -
          2 * ((Nat.card (𝓞 F ⧸ q.asIdeal) : w.adicCompletion E) *
            algebraMap E (w.adicCompletion E)
              (φ.centralCoefficient q (by
                have h := ρ.good_of_not_mem_characterComparisonBad S.system χ w₀ w q hq
                rw [← S.bad_eq]
                exact h.2.1)))) := by
  have hgood := ρ.good_of_not_mem_characterComparisonBad S.system χ w₀ w q hq
  have hform : q ∉ φ.form.bad := by
    rw [← S.bad_eq]
    exact hgood.2.1
  have hp : (S.system.residueCharacteristic w : 𝓞 F) ∉ P :=
    hP.symm ▸ hgood.2.2.2.2.2.2
  rw [ρ.frobenius_powerTrace_eq_of_characterGood S.system χ w₀ w e q hq P hP Q 2,
    S.frobenius_trace_sq w q hform P hP hp Q]

end HilbertModularity.HilbertModularForms
