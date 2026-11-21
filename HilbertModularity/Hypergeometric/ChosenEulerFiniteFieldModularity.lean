/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FiniteFieldHilbertModularity
public import HilbertModularity.Hypergeometric.ChosenEulerAllPlaceModularity
public import HilbertModularity.Hypergeometric.GaloisRealizationCoefficientExtension
public import HilbertModularity.Hypergeometric.CompatibleTraceAtEveryPrime
public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimeDescent

/-! # Finite-field traces of the chosen Euler family

The all-place eigenform is chosen once from the same-family Skinner–Wiles
input. Its polynomial is the one attached to the selected Euler quotient.
The normalized trace already proved for that quotient then gives the
McCarthy value at every eligible cyclotomic prime, including residue degree
two. This is the finite-field deduction in
[TripathiGoswamiRevised, Theorem `thm:intro-main`].
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain Polynomial
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic HilbertModularForms LocalSpecialization

attribute [local instance] Ideal.Quotient.field

/-- One spherical eigenform gives the root-power and degree-one/two
McCarthy formulas at *every* good-unit prime of the chosen Euler family.
The only supplied arithmetic inputs are the same-family Skinner–Wiles
checklist and its covariant coordinate equivalence. In particular the
selected system, local polynomial comparison, normalized trace, auxiliary
coefficient place and absolute Frobenius prime are constructed internally. -/
theorem exists_chosenEuler_mccarthyEigenform_of_skinnerWiles
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ ℚ_[N] L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [CharP (𝒪[L] ⧸ 𝓂[L]) N]
    (ι : cyclotomicField N →+* L)
    (hcoeff : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ρ : Representation L (AbsoluteGalois (realCyclotomicField N)) (Fin 2 → L))
    (e : ρ.Equiv (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
      (darmonLabelledTateFamily (realCyclotomicField N)
        N (le_trans (by decide : 3 ≤ 5) h5) N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN)
        (cyclotomicField N) (normalClosure_realCyclotomicField_le_cyclotomicField N)
        w L)))
    (M : Type*) [Field M] [NumberField M]
    [Algebra (realCyclotomicField N) M]
    (H : SkinnerWilesWeightTwoInput N ρ M) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (jF : cyclotomicField N →+* B) (j : B →+* Qbar),
        j.comp jF = (cyclotomicField N).val.toRingHom ∧
        ∃ (level : FiniteLevel (realCyclotomicField N))
          (μ : AdditiveQuotientMeasure (realCyclotomicField N))
          (ψ : AlgebraicGoodPrimeEigenform level μ B),
          ψ.complexEmbedding = B.val.toRingHom ∧
          (∃ b : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ b) ∧
          (Set.range ψ.form.central_character).Finite ∧
          ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
            (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
            (hx : P.GoodUnit
              (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val))
            (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
            (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
            [P.asIdeal.LiesOver q.asIdeal],
            ∃ (hψ : q ∉ ψ.form.bad) (α β : Qbar),
              (X - C α) * (X - C β) = (ψ.heckePolynomial q hψ).map j ∧
              mccarthyValue N P hP m θ
                (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) hx =
                α ^ P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) +
                  β ^ P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) ∧
              (P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) = 1 →
                mccarthyValue N P hP m θ
                  (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) hx =
                  j (ψ.heckeCoefficient q hψ)) ∧
              (P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) = 2 →
                mccarthyValue N P hP m θ
                  (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) hx =
                  j (ψ.heckeCoefficient q hψ) ^ 2 -
                    2 * ((Nat.card (𝓞 (realCyclotomicField N) ⧸ q.asIdeal) : Qbar) *
                      j (ψ.centralCoefficient q hψ))) := by
  obtain ⟨B, hB, jF, level, μ, ψ, T, hψ, hb, hc, hpoly, _hall⟩ :=
    exists_chosenEuler_allPlaceEigenform_of_skinnerWiles
      N m hN h5 hmPos hmN w L ι hcoeff ξ ρ e M H
  let := hB
  let : Algebra (cyclotomicField N) B := jF.toAlgebra
  let : Algebra (cyclotomicField N) Qbar :=
    (cyclotomicField N).val.toRingHom.toAlgebra
  let : Algebra.IsAlgebraic (cyclotomicField N) B :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := cyclotomicField N) (A := B)
  let j : B →ₐ[cyclotomicField N] Qbar := IsAlgClosed.lift
  have hj : j.toRingHom.comp jF = (cyclotomicField N).val.toRingHom := by
    ext a
    exact j.commutes a
  let S₀ := chosenCommonEulerCompatibleSystem N m hN h5 hmPos hmN ξ
  let S := chosenCommonEulerCompatibleSystemExtended N m hN h5 hmPos hmN ξ B
  have hbad : S₀.bad ⊆ badPrimesBelow
      (K := realCyclotomicField N)
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) N :=
    chosenCommonEulerCompatibleSystem_bad_subset N m hN h5 hmPos hmN ξ
  refine ⟨B, hB, jF, j.toRingHom, hj, level, μ, ψ, hψ, hb, hc, ?_⟩
  intro P hP hx θ hθ q _
  have hq₀ : q ∉ S₀.bad :=
    LocalSpecialization.not_mem_of_goodUnit_of_subset_badPrimesBelow
      ξ.val N S₀.bad hbad q P hx hP
  have hq : q ∉ S.bad := by
    simpa only [S, chosenCommonEulerCompatibleSystemExtended_eq_extendCoefficients,
      NumberFieldCompatibleSystem.extendCoefficients_bad] using hq₀
  obtain ⟨hψq, hpolyq⟩ := hpoly q hq₀
  have hHecke : (S.polynomial q).map (RingHom.id B) =
      ψ.heckePolynomial q hψq := by
    simpa only [S, chosenCommonEulerCompatibleSystemExtended_eq_extendCoefficients,
      NumberFieldCompatibleSystem.extendCoefficients_polynomial,
      RingHom.algebraMap_toAlgebra, Polynomial.map_id] using hpolyq
  refine ⟨hψq, ?_⟩
  apply Cyclotomic.exists_mccarthyValue_eq_compatibleEigenform_roots_at_good_prime
    N S ψ (RingHom.id B) j.toRingHom P hP m hmPos hmN θ hθ
    (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) hx
    q hq hψq hHecke
  intro v hv ιv hιv Q _ _ _
  have hιv : ιv.comp j.toRingHom =
      (algebraMap (v.adicCompletion B) (AlgebraicClosure (v.adicCompletion B))).comp
        (algebraMap B (v.adicCompletion B)) := by
    simpa only [RingHom.comp_id] using hιv
  have htrace := chosenCommonEulerCompatibleSystemExtended_endpoint_trace
    N m hN h5 hmPos hmN ξ B j.toRingHom
    (by simpa only [RingHom.algebraMap_toAlgebra] using hj)
    P hP hx q hq v hv ιv hιv Q
  simpa only [S, RingHom.comp_id] using htrace

/-- The chosen-family deduction satisfies the manuscript's finite-field
modularity definition. The same-family lifting input and covariant coordinates
remain explicit until the deep-cusp application constructs them. -/
theorem finiteFieldHilbertModularAt_of_skinnerWiles
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ ℚ_[N] L]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [CharP (𝒪[L] ⧸ 𝓂[L]) N]
    (ι : cyclotomicField N →+* L)
    (hcoeff : (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) = ι)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ρ : Representation L (AbsoluteGalois (realCyclotomicField N)) (Fin 2 → L))
    (e : ρ.Equiv (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
      (darmonLabelledTateFamily (realCyclotomicField N)
        N (le_trans (by decide : 3 ≤ 5) h5) N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN)
        (cyclotomicField N) (normalClosure_realCyclotomicField_le_cyclotomicField N)
        w L)))
    (M : Type*) [Field M] [NumberField M]
    [Algebra (realCyclotomicField N) M]
    (H : SkinnerWilesWeightTwoInput N ρ M) :
    FiniteFieldHilbertModularAt N m ξ.val := by
  obtain ⟨B, hB, jF, j, hj, level, μ, ψ, hψ, _hb, _hc, htrace⟩ :=
    exists_chosenEuler_mccarthyEigenform_of_skinnerWiles
      N m hN h5 hmPos hmN w L ι hcoeff ξ ρ e M H
  let := hB
  refine ⟨B, hB, jF, j, hj, level, μ, ψ, hψ, ?_⟩
  intro P hP hx θ hθ q _
  obtain ⟨hq, α, β, hroots, hvalue, _h1, _h2⟩ := htrace P hP hx θ hθ q
  exact ⟨hq, α, β, hroots, hvalue⟩

end HilbertModularity.Hypergeometric
