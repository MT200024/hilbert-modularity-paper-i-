/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.PlusCurve
public import HilbertModularity.NumberTheory.LocalSpecialization

/-! # Good specializations of the plus curve

The actual branch polynomial remains separable at every good-unit prime away
from `2p`. This is the discriminant step used in [DarmonRigid, Proposition
1.15, proof, printed p. 426], without the Fermat-equation specialization.
-/

public noncomputable section

open Polynomial AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hyperelliptic

attribute [local instance] Ideal.Quotient.field

/-- The integral plus equation commutes with every coefficient homomorphism. -/
theorem plusPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (t : R) :
    (plusPolynomial p t).map f = plusPolynomial p (f t) := by
  simp only [plusPolynomial, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_sub,
    Chebyshev.map_C, Polynomial.map_C, map_sub, map_mul, map_ofNat]

/-- The completed plus curve is smooth over any field away from `2p` and
the two singular parameters. -/
theorem plusCurveToSpec_smooth_of_characteristic
    {k : Type*} [Field k] (p : ℕ) (hp : Odd p)
    (h2 : (2 : k) ≠ 0) (hpc : (p : k) ≠ 0)
    (t : k) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Smooth (plusCurveToSpec p hp t) := by
  exact AlgebraicGeometry.Hyperelliptic.smooth_toSpec _ _ _
    (plusPolynomial_separable p hp h2 hpc t ht0 ht1) h2

/-- At a good-unit prime away from `2p`, the displayed reduced plus polynomial
is separable. The parameter uses the canonical local specialization map. -/
theorem plusPolynomial_specialization_separable
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (hp : Odd p) (P : HeightOneSpectrum (𝓞 K))
    (h2 : (2 : 𝓞 K) ∉ P.asIdeal) (hpc : (p : 𝓞 K) ∉ P.asIdeal)
    (t : K) (ht : P.GoodUnit t) :
    (plusPolynomial p (P.specialization t ht.valuation_eq_one.le)).Separable := by
  have h2k : (2 : 𝓞 K ⧸ P.asIdeal) ≠ 0 := by
    exact fun h => h2 ((Ideal.Quotient.eq_zero_iff_mem).mp (by rw [map_ofNat]; exact h))
  have hpk : (p : 𝓞 K ⧸ P.asIdeal) ≠ 0 := by
    exact fun h => hpc ((Ideal.Quotient.eq_zero_iff_mem).mp (by simpa using h))
  exact plusPolynomial_separable p hp h2k hpk _
    ht.specialization_ne_zero_one.1 ht.specialization_ne_zero_one.2

/-- The completed curve defined by the reduced plus equation is smooth.
Identification with the special fibre of an integral model is a separate
base-change assertion; this theorem does not assert good reduction of a
Jacobian by itself. -/
theorem plusCurve_specialization_smooth
    {K : Type*} [Field K] [NumberField K]
    (p : ℕ) (hp : Odd p) (P : HeightOneSpectrum (𝓞 K))
    (h2 : (2 : 𝓞 K) ∉ P.asIdeal) (hpc : (p : 𝓞 K) ∉ P.asIdeal)
    (t : K) (ht : P.GoodUnit t) :
    Smooth (plusCurveToSpec p hp (P.specialization t ht.valuation_eq_one.le)) := by
  apply AlgebraicGeometry.Hyperelliptic.smooth_toSpec _ _ _
    (plusPolynomial_specialization_separable p hp P h2 hpc t ht)
  exact fun h => h2 ((Ideal.Quotient.eq_zero_iff_mem).mp (by rw [map_ofNat]; exact h))

end HilbertModularity.Hyperelliptic
