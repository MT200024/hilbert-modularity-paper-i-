/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricExistence
public import HilbertModularity.Hyperelliptic.PlusDarmonMestre

/-! # The selected plus Jacobian in Darmon–Mestre's parameter

The substitution `s = 2t - 1` identifies the Chebyshev equation for
`C₂(s)` in [DarmonMestre, §4, printed p. 309] with the actual plus curve.
The pointed Jacobian property therefore transports to the same selected
family `B`, without changing its integral real multiplication. This does not
identify that RM action with Darmon–Mestre's auxiliary action.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open HilbertModularity.Cyclotomic HilbertModularity.Hyperelliptic

namespace HilbertModularity.Hypergeometric

private theorem hyperellipticToSpec_congr {K : Type*} [Field K]
    {f g : K[X]} (h : f = g) (n : ℕ)
    (hf : f.natDegree = 2 * n) (hg : g.natDegree = 2 * n) :
    Over.mk (Hyperelliptic.toSpec f n hf) =
      Over.mk (Hyperelliptic.toSpec g n hg) := by
  cases h
  rfl

/-- The Chebyshev `C₂(2t-1)` completion as a curve over its coefficient field.
See [DarmonMestre, §4, printed p. 309]. -/
def darmonMestreChebyshevCurveToSpec {K : Type*} [Field K]
    (p : ℕ) (hp : Odd p) (t : K) :
    Hyperelliptic.curve
        (darmonMestrePlusPolynomial (Chebyshev.C K p) (2 * t - 1))
        ((p + 1) / 2)
        (by
          rw [darmonMestrePlusPolynomial_eq_plusPolynomial]
          exact plusPolynomial_evenDegree p hp t) ⟶
      Spec (CommRingCat.of K) :=
  Hyperelliptic.toSpec
    (darmonMestrePlusPolynomial (Chebyshev.C K p) (2 * t - 1))
    ((p + 1) / 2)
    (by
      rw [darmonMestrePlusPolynomial_eq_plusPolynomial]
      exact plusPolynomial_evenDegree p hp t)

/-- The model equality is over the coefficient field, including the map to
its spectrum, so it transports the pointed Jacobian property. -/
theorem darmonMestreChebyshevCurveToSpec_eq_plusCurveToSpec
    {K : Type*} [Field K] (p : ℕ) (hp : Odd p) (t : K) :
    Over.mk (darmonMestreChebyshevCurveToSpec p hp t) =
      Over.mk (plusCurveToSpec p hp t) := by
  unfold darmonMestreChebyshevCurveToSpec plusCurveToSpec plusCurve
  exact hyperellipticToSpec_congr
    (darmonMestrePlusPolynomial_eq_plusPolynomial p t) ((p + 1) / 2) _ _

/-- Transport of the pointed Jacobian property under the exact parameter
substitution, keeping the target abelian variety fixed. -/
def darmonMestrePointedJacobianOfPlusJacobian {K : Type*} [Field K]
    (p : ℕ) (hp : Odd p) (t : K)
    (J : CommGrp (Over (Spec (CommRingCat.of K))))
    (hJ : GroupScheme.PlusCurveJacobian K p hp t J) :
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
        Over.mk (darmonMestreChebyshevCurveToSpec p hp t),
      GroupScheme.PointedCurveJacobian K
        (Over.mk (darmonMestreChebyshevCurveToSpec p hp t)) b J := by
  let e := eqToIso (darmonMestreChebyshevCurveToSpec_eq_plusCurveToSpec p hp t)
  exact ⟨plusBranchOver p hp t ≫ e.inv, hJ.transport e⟩

/-- The generic Jacobian of Darmon–Mestre's Chebyshev curve is the selected
plus-family generic fibre, with its original RM and Tate actions. -/
def primePlusDarmonMestreGenericJacobian (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of
        (RatFunc (realCyclotomicField p))))) ⟶
        Over.mk (darmonMestreChebyshevCurveToSpec p (primePlusData p hp).p_odd
          (plusGenericParameter (realCyclotomicField p))),
      GroupScheme.PointedCurveJacobian (RatFunc (realCyclotomicField p))
        (Over.mk (darmonMestreChebyshevCurveToSpec p (primePlusData p hp).p_odd
          (plusGenericParameter (realCyclotomicField p)))) b
        (GroupScheme.fiber (RatFunc (realCyclotomicField p))
          (primePlusFamily p hp)
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField p))) :=
  darmonMestrePointedJacobianOfPlusJacobian p (primePlusData p hp).p_odd
    (plusGenericParameter (realCyclotomicField p)) _ (primePlusGenericJacobian p hp)

/-- The same selected arithmetic fibre is the pointed Jacobian of the
specialized Chebyshev curve. The RM action remains the one on `primePlusFamily`.
-/
def primePlusDarmonMestreRationalFiberJacobian (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (darmonMestreChebyshevCurveToSpec p
          (primePlusData p hp).p_odd ξ.val),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (darmonMestreChebyshevCurveToSpec p
          (primePlusData p hp).p_odd ξ.val)) b
        (GroupScheme.fiber (realCyclotomicField p) (primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) :=
  darmonMestrePointedJacobianOfPlusJacobian p (primePlusData p hp).p_odd
    ξ.val _ (primePlusRationalFiberJacobian p hp ξ)

end HilbertModularity.Hypergeometric
