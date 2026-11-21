/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeGoodReduction
public import HilbertModularity.Geometry.GroupScheme.HyperellipticGoodReduction
public import HilbertModularity.Hyperelliptic.PlusGoodSpecialization
public import HilbertModularity.NumberTheory.LocalSpecialization.Rational

/-! # Good reduction at the manuscript's odd good-unit primes

Apply the standard hyperelliptic Jacobian criterion to the actual selected
plus fibre, using its pointed Jacobian property and its integral plus equation.
The reduced polynomial is proved separable from the good-unit hypotheses.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic GroupScheme Hyperelliptic

attribute [local instance] Ideal.Quotient.field

/-- The same plus Jacobian used in the compatible system has good reduction
at every good-unit prime away from `2p`. No replacement Jacobian or changed
RM label is chosen. See [DarmonRigid, Proposition 1.15, proof, p. 426] and
[MilneJacobian2021, Corollary 12.3, proof, p. 39]. -/
theorem primePlusFiber_not_mem_badPrimes_of_goodUnit
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (P : HeightOneSpectrum (𝓞 (realCyclotomicField p)))
    (h2 : (2 : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (hpc : (p : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal)
    (hξ : P.GoodUnit ξ.val) :
    P ∉ primePlusFiberBadPrimes p hp ξ := by
  let t₀ := P.localElement ξ.val hξ.valuation_eq_one.le
  let f₀ := plusPolynomial p t₀
  have hodd := (primePlusData p hp).p_odd
  have hdegree : f₀.natDegree = 2 * ((p + 1) / 2) := by
    rw [(plusPolynomial_isMonicOfDegree p (by omega) t₀).natDegree_eq]
    obtain ⟨k, hk⟩ := hodd
    omega
  have hgeneric : f₀.map (algebraMap (P.valuationSubringAtPrime
      (realCyclotomicField p)) (realCyclotomicField p)) =
      plusPolynomial p ξ.val := by
    rw [plusPolynomial_map]
    rfl
  have hsep : (f₀.map (P.localResidue (K := realCyclotomicField p))).Separable := by
    rw [plusPolynomial_map]
    exact plusPolynomial_specialization_separable p hodd P h2 hpc ξ.val hξ
  let hJ := (primePlusFiberJacobian p hp ξ).transport (Iso.refl _)
  obtain ⟨B, hproper, hsmooth, hconnected, ⟨e⟩⟩ :=
    exists_hyperellipticJacobian_goodReduction_of_separable
      (realCyclotomicField p) P ((p + 1) / 2) (by omega)
      (plusPolynomial p ξ.val) (plusPolynomial_evenDegree p hodd ξ.val)
      f₀ (plusPolynomial_isMonicOfDegree p (by omega) t₀).monic
      hdegree hgeneric h2 hsep _ (primePlusFiber p hp ξ) hJ
  let := hproper
  let := hsmooth
  let := hconnected
  exact primePlusFiber_not_mem_badPrimes_of_goodReduction p hp ξ P B e

/-- For a rational parameter, the actual bad-reduction set is contained in
exactly the manuscript's excluded set. The good-unit conditions themselves
exclude primes above two, so the conclusion introduces no extra prime. -/
theorem primePlusFiberBadPrimes_subset_of_rational_parameter
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (x : ℚ) (hx : ξ.val = algebraMap ℚ (realCyclotomicField p) x) :
    primePlusFiberBadPrimes p hp ξ ⊆ LocalSpecialization.badPrimesAbove ξ.val p := by
  intro P hP
  by_contra hgood
  obtain ⟨hξ, hpc⟩ :=
    (LocalSpecialization.not_mem_badPrimesAbove_iff ξ.val p P).mp hgood
  have h2 : (2 : 𝓞 (realCyclotomicField p)) ∉ P.asIdeal :=
    LocalSpecialization.two_not_mem_of_rational_goodUnit P x (hx ▸ hξ)
  exact primePlusFiber_not_mem_badPrimes_of_goodUnit p hp ξ P h2 hpc hξ hP

end HilbertModularity.Hypergeometric
