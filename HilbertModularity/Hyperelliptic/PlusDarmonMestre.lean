/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.PlusCurve

/-! # Darmon–Mestre's parameter for the plus curve

The curve `C₂(s)` in [DarmonMestre, §4, printed p. 309] has affine equation
`y² = (x + 2)(f(x) - 2s)`. The revised manuscript uses `s = 2t - 1` to compare
this equation with its plus family. The polynomial and projective-curve
identities below make that substitution exact; they make no assertion about
the separately selected abelian schemes or their integral Tate lattices.
-/

public noncomputable section

open Polynomial AlgebraicGeometry

namespace HilbertModularity.Hyperelliptic

variable {K : Type*} [Field K]

/-- The branch polynomial of `C₂(s)` for a specified Darmon–Mestre polynomial `f`.
See [DarmonMestre, §4, printed p. 309]. -/
def darmonMestrePlusPolynomial (f : K[X]) (s : K) : K[X] :=
  (X + 2) * (f - C (2 * s))

/-- The substitution `s = 2t - 1` identifies the Darmon–Mestre equation
with the plus-family equation, using the Chebyshev form of `f`. See
[TripathiGoswamiRevised, Lemma `RMtorsion`, proof] and
[DarmonMestre, §4, printed p. 309]. -/
theorem darmonMestrePlusPolynomial_eq_plusPolynomial (p : ℕ) (t : K) :
    darmonMestrePlusPolynomial (Chebyshev.C K p) (2 * t - 1) =
      plusPolynomial p t := by
  rw [darmonMestrePlusPolynomial, plusPolynomial,
    show (2 : K) * (2 * t - 1) = 4 * t - 2 by ring]

/-- The manuscript's cyclotomic `f(x) = x g(x² - 2)` gives the same polynomial.
This uses the already proved cyclotomic–Chebyshev identification. -/
theorem darmonMestreCyclotomicPolynomial_eq_plusPolynomial [CharZero K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (t : K) :
    darmonMestrePlusPolynomial (cyclotomicChebyshevPolynomial ζ p) (2 * t - 1) =
      plusPolynomial p t := by
  rw [cyclotomicChebyshevPolynomial_eq_chebyshev hp hp2 hζ]
  exact darmonMestrePlusPolynomial_eq_plusPolynomial p t

/-- The projective completion of `C₂(2t-1)` with the cyclotomic `f` is the
same projective double cover as the plus curve. This compares curves, not
their chosen Jacobian or Galois representations. -/
theorem darmonMestreCyclotomicCurve_eq_plusCurve [CharZero K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (t : K) :
    AlgebraicGeometry.Hyperelliptic.curve
      (darmonMestrePlusPolynomial (cyclotomicChebyshevPolynomial ζ p) (2 * t - 1))
      ((p + 1) / 2)
      (by
        rw [darmonMestreCyclotomicPolynomial_eq_plusPolynomial hp hp2 hζ t]
        exact plusPolynomial_evenDegree p (hp.odd_of_ne_two hp2) t) =
      plusCurve p (hp.odd_of_ne_two hp2) t := by
  simp only [darmonMestreCyclotomicPolynomial_eq_plusPolynomial hp hp2 hζ t]
  rfl

end HilbertModularity.Hyperelliptic
