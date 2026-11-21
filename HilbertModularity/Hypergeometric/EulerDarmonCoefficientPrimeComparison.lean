/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationGenericMonodromy

/-! # The chosen Euler–Darmon comparison at arbitrary odd coefficient primes

The conductor N and the coefficient characteristic p are independent. The
same generic family and fixed exponent label are retained when applying the
local monodromy, Hodge–Tate and finite-ramification inputs. One finite algebraic
character works at every nonsingular fibre for the chosen coefficient place.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic HilbertModularForms

/-- The selected prime-conductor family has one algebraic finite comparison
character at any odd coefficient prime. The coefficient prime need not divide
the conductor. This is the arbitrary-place portion of
[TripathiGoswamiRevised, Theorem `thm:RMgeneral`]. The composite-conductor
and dyadic cases remain separate applications. -/
theorem exists_algebraic_character_comparing_selectedEuler_at_prime
    (N m p : ℕ) [NeZero N] [Fact N.Prime] [Fact p.Prime]
    (hp : p ≠ 2)
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := R.placeDescent N m 𝒞 p L ι
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        letI : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E'.subtype.comp (algebraMap E E') = (algebraMap (w.adicCompletion E) L).comp
            (algebraMap E (w.adicCompletion E)) ∧
          ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
            Nonempty (((Representation.ofCharacter
              ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
                  (darmonCohomologicalFamily (realCyclotomicField N)
                    N (le_trans (by decide : 3 ≤ 5) h5) p m
                    (eulerExponent_coprime_of_prime N m hN hmPos hmN)
                    E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation
                    (realCyclotomicField N) ξ D.localSystem)) := by
  let h3 : 3 ≤ N := le_trans (by decide : 3 ≤ 5) h5
  let hmcp : m.Coprime N :=
    eulerExponent_coprime_of_prime N m hN hmPos hmN
  let D := R.placeDescent N m 𝒞 p L ι
  obtain ⟨F_gen, ⟨ePath⟩⟩ :=
    exists_genericLocalSystem_of_commonRealEulerQuotient N m p 𝒞 R L ι ξ₀
  obtain ⟨hlocal, hirred⟩ :=
    commonRealEulerQuotient_generic_localMonodromy N m p hN h5 hmPos hmN
      E hE w L 𝒞 R ι hι ξ₀ F_gen ⟨ePath⟩
  obtain ⟨eGeom⟩ :=
    darmonCohomologicalFamily_geometricEquiv_of_localMonodromy
      N h3 p m hmcp E hE w L hp F_gen hlocal hirred
  let : IsScalarTower ℚ ℚ_[p] L :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[p] (w.adicCompletion E) L
  obtain ⟨hHT, hmult⟩ :=
    commonRealEulerQuotientRealization_labelledHodgeTate
      N m p hN h5 hmPos hmN 𝒞 R L ι ξ₀
  have hunram :
      ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
        (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N)))),
        Q.IsMaximal → Q.LiesOver q.asIdeal →
        ∀ g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N),
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois
            (realCyclotomicField N)) →
          q ∉ properEulerBadPrimes N p hN ξ₀ →
          puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L
            ξ₀ D.localSystem g = 1 := by
    intro q Q hQ hOver g hg hq
    let : Q.IsMaximal := hQ
    let : Q.LiesOver q.asIdeal := hOver
    exact D.normalizedDeterminant_inertia_eq_one N m p L ι hN h5 hmPos
      hmN 𝒞 ξ₀ q Q g hg hq
  exact exists_algebraic_character_comparing_darmon_localSystems_of_weights_zero_one
    N h3 p m hmcp E hE w L h5 ξ₀ D.localSystem F_gen ePath eGeom
    (properEulerBadPrimes N p hN ξ₀) hunram hHT hmult

/-- The fixed chosen prime-conductor Euler family has one finite algebraic
comparison character at any odd coefficient prime, uniformly in all nonsingular
fibres. The coefficient embedding and exponent label remain fixed. -/
theorem exists_algebraic_character_comparing_chosenEuler_at_prime
    (N m p : ℕ) [NeZero N] [Fact N.Prime] [Fact p.Prime]
    (hp : p ≠ 2)
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent N m 𝒞 p L ι
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        letI : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E'.subtype.comp (algebraMap E E') = (algebraMap (w.adicCompletion E) L).comp
            (algebraMap E (w.adicCompletion E)) ∧
          ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
            Nonempty (((Representation.ofCharacter
              ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
                  (darmonCohomologicalFamily (realCyclotomicField N)
                    N (le_trans (by decide : 3 ≤ 5) h5) p m
                    (eulerExponent_coprime_of_prime N m hN hmPos hmN)
                    E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation
                    (realCyclotomicField N) ξ D.localSystem)) := by
  let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hmPos hmN
  let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hmPos hmN
  exact exists_algebraic_character_comparing_selectedEuler_at_prime
    N m p hp hN h5 hmPos hmN E hE w L 𝒞 R ι hι ξ₀

end HilbertModularity.Hypergeometric
