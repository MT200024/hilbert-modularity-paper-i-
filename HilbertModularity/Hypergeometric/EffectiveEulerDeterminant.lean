/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EffectiveEulerRealization
public import HilbertModularity.Hypergeometric.GaloisRealizationHodgeTate
public import HilbertModularity.Hypergeometric.DarmonWeightComparison

/-! # The determinant of the chosen effective Euler realization

The determinant assertion in [TripathiGoswamiRevised, Proposition 2.5]
follows from the actual quotient's labelled weights and finite ramification.
The effective κ twist has square one and the fibre has rank two, so it
leaves this determinant unchanged, including at even conductors.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

variable (N m p : ℕ) [NeZero N] [Fact p.Prime]
  (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [Algebra ℚ L]
  (ι : cyclotomicField N →+* L)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

omit [Algebra ℚ L] in
/-- The actual raw Euler determinant times the cyclotomic character has
one finite exponent on the entire arithmetic Galois group. Its Hodge and
ramification hypotheses are supplied by the chosen quotient; no determinant
or comparison premise is required. -/
theorem finite_order_chosenRawEulerNormalizedDeterminant :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 p L ι
    ∃ n : ℕ, 0 < n ∧ ∀ g,
      (puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ
        D.localSystem g) ^ n = 1 := by
  classical
  let K := realCyclotomicField N
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  let F := D.localSystem
  let ρ := puncturedFiberCoordinateRepresentation K L ξ F
  let : IsModuleTopology ℚ_[p] (Fin (Module.finrank L (F.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K)
        (ProjectiveLine.puncturedPoint K ξ)))) → L) :=
    isModuleTopologyOfFiniteDimensional
  have hd := chosenCoprimeRawEulerRealization_rank_two
    N m h3 hm hmN hcop p L ι ξ
  have hw := commonRealEulerQuotientRealization_labelledHodgeTate_of_coprime
    N m p h3 hm hmN hcop 𝒞 R L ι ξ
  have hu : ∀ (q : HeightOneSpectrum (𝓞 K))
      (Q : Ideal (𝓞 (AlgebraicClosure K))), Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois K,
        g ∈ Q.inertia _ → q ∉ properEulerBadPrimesOfConductor N p ξ →
          puncturedFiberNormalizedDeterminant K p L ξ F g = 1 := by
    intro q Q hQ hQq g hg hq
    let : Q.IsMaximal := hQ
    let : Q.LiesOver q.asIdeal := hQq
    exact D.normalizedDeterminant_inertia_eq_one_of_coprime
      N m p L ι h3 hm hmN hcop 𝒞 ξ q Q g hg hq
  obtain ⟨n, hn, hpow⟩ := finite_order_normalizedDeterminant_of_weights_zero_one p ι
    ρ (continuous_puncturedFiberCoordinateRepresentation K L ξ F)
    (by simpa using hd) (properEulerBadPrimesOfConductor N p ξ)
    (by simpa only [ρ, puncturedFiberCoordinateRepresentation_normalizedDeterminant] using hu)
    hw.1 hw.2
  dsimp only [ρ] at hpow
  rw [puncturedFiberCoordinateRepresentation_normalizedDeterminant] at hpow
  exact ⟨n, hn, hpow⟩

/-- For every coprime conductor and every coefficient prime, the chosen
effective cohomological determinant is a finite-order continuous character
times the inverse cyclotomic character. The fixed κ normalization occurs
exactly once in the action and cancels in rank two. This proves the actual
selected-family determinant conclusion of Proposition 2.5; it adds no
literature admission and uses no purity or Darmon-comparison hypothesis. -/
theorem exists_finite_character_chosenEffectiveEuler_determinant :
    ∃ ψ : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ψ ∧ IsOfFinOrder ψ ∧
        (chosenEffectiveEulerAction N m p h3 hm hmN hcop L ι ξ).determinantCharacter =
          ψ * (Field.cyclotomicCharacterWithCoefficients
            (realCyclotomicField N) p L).toMonoidHom⁻¹ := by
  let K := realCyclotomicField N
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  let F := D.localSystem
  let ρ := puncturedFiberArithmeticRepresentation K ξ F
  let ψ := puncturedFiberNormalizedDeterminant K p L ξ F
  have hd := chosenEffectiveEulerAction_rank_two N m p h3 hm hmN hcop L ι ξ
  have hdet : (chosenEffectiveEulerAction N m p h3 hm hmN hcop L ι ξ
      ).determinantCharacter = ρ.determinantCharacter := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    simp only [Representation.determinantCharacter_coe]
    have ha : chosenEffectiveEulerAction N m p h3 hm hmN hcop L ι ξ g =
        (gprvKappaLocal N h3 m L g : L) • ρ g := by
      ext v
      exact chosenEffectiveEulerAction_apply N m p h3 hm hmN hcop L ι ξ g v
    rw [ha, LinearMap.det_smul, hd]
    have hκ := congrArg (fun u : Lˣ => (u : L))
      (gprvKappaLocal_apply_sq N h3 m L g)
    change (gprvKappaLocal N h3 m L g : L) ^ 2 = 1 at hκ
    rw [hκ, one_mul]
  obtain ⟨n, hn, hpow⟩ := finite_order_chosenRawEulerNormalizedDeterminant
    N m p h3 hm hmN hcop L ι ξ
  refine ⟨ψ, continuous_puncturedFiberNormalizedDeterminant K p L ξ F, ?_, ?_⟩
  · apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply MonoidHom.ext
    intro g
    exact hpow g
  · rw [hdet]
    dsimp only [ψ]
    rw [puncturedFiberNormalizedDeterminant_eq]
    apply MonoidHom.ext
    intro g
    change ρ.determinantCharacter g =
      (ρ.determinantCharacter g * Field.cyclotomicCharacterWithCoefficients K p L g) *
        (Field.cyclotomicCharacterWithCoefficients K p L g)⁻¹
    exact (mul_inv_cancel_right _ _).symm

end HilbertModularity.Hypergeometric
