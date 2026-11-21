/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EffectiveEulerCompatibleSystem
public import Mathlib.Analysis.Complex.Basic

/-! # Coefficient field and purity of the effective Euler polynomials

These are the cited coefficient and weight properties of the GPRV motive,
kept separate from the proved construction of its compatible system.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

variable (N m : ℕ) [NeZero N]
  (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

/-- **Named literature input.** For `(m/N, 1-m/N); (1,1)`, the
upper and lower sums are integral, the parameters are generic, and the
coprimality hypothesis supplies `(Irr)` by [GPRV, Lemma 8.5, p.30].
Their stabilizer is `{1,-1}`. [GPRV, Theorem 9.2 and its proof (76),
pp.40–41] therefore gives coefficient field contained in `K_N`, without
asserting equality at every specialization. Its proof supplies the real
coefficient action on the new part of the same quotient.

Exactly two parameters are integral, so [GPRV, Theorem 8.25(1), p.37]
gives weight `2-1=1`. [GPRV, Lemma 9.3, p.40] has `δ=0` for these
parameters, hence introduces no norm power. The effective realization
includes the single finite `κ_N^m` factor from Definition 8.8 and Lemma 9.4.
Thus the roots of its geometric-Frobenius polynomial have squared complex
norm equal to the residue cardinality. The sign convention is `det(X-Frob)`
on cohomology, with no Tate twist.

The system-to-original-fibre equivalence is proved in
`chosenEffectiveEulerCompatibleSystem_actionEquiv`. This admission records
only these cited coefficient/purity properties of its common polynomial,
not a comparison character, modularity, or a numerical example value.
Purity is stated at the system's good primes; no assertion at its exceptional
primes is inferred from this interface. -/
theorem chosenEffectiveEulerCompatibleSystem_polynomial_properties
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).bad) :
    ∃ P : Polynomial (realCyclotomicField N),
      (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).polynomial q =
        P.map (algebraMap (realCyclotomicField N) (cyclotomicField N)) ∧
      ∀ (σ : cyclotomicField N →+* ℂ) (z : ℂ),
        (((chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).polynomial q
          ).map σ).eval z = 0 →
        ‖z‖ ^ 2 = (Nat.card (𝓞 (realCyclotomicField N) ⧸ q.asIdeal) : ℝ) := by
  sorry

/-- The common Frobenius polynomial descends to the real cyclotomic field;
no equality with the minimal coefficient field is asserted. -/
theorem chosenEffectiveEulerCompatibleSystem_exists_real_polynomial
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).bad) :
    ∃ P : Polynomial (realCyclotomicField N),
      (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).polynomial q =
        P.map (algebraMap (realCyclotomicField N) (cyclotomicField N)) := by
  obtain ⟨P, hP, _⟩ := chosenEffectiveEulerCompatibleSystem_polynomial_properties
    N m h3 hm hmN hcop ξ q hq
  exact ⟨P, hP⟩

/-- Every complex root has the weight-one squared norm, independently of
the chosen embedding of the system's coefficient field. -/
theorem chosenEffectiveEulerCompatibleSystem_root_norm_sq
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).bad)
    (σ : cyclotomicField N →+* ℂ) (z : ℂ)
    (hz : (((chosenEffectiveEulerCompatibleSystem N m h3 hm hmN hcop ξ).polynomial q
      ).map σ).eval z = 0) :
    ‖z‖ ^ 2 = (Nat.card (𝓞 (realCyclotomicField N) ⧸ q.asIdeal) : ℝ) := by
  obtain ⟨_, _, h⟩ := chosenEffectiveEulerCompatibleSystem_polynomial_properties
    N m h3 hm hmN hcop ξ q hq
  exact h σ z hz

end HilbertModularity.Hypergeometric
