/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberLocalParameters
public import Mathlib.RingTheory.Etale.Locus

/-! # The branch polynomial as a local étale coordinate

The map on affine lines used here sends the coordinate on the target to the
actual branch polynomial `u P(u)`. Its derivative is invertible at each
crossing. The standard étale criterion is kept as an explicit literature
interface; the application to the manuscript's polynomial is proved below.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The relative polynomial Jacobian criterion, with no field assumption on
the coefficient ring.  For the map `R[t] → R[u]`, `t ↦ H(u)`, invertibility
of `H'(u)` at the chosen prime makes the map étale there.  Indeed the
presentation `R[t,u]/(H(u)-t)` is standard étale on that open; see
[src_stacks_standard_etale, Tags 00UB and 00UC].  This is a literature
interface about polynomial maps, independent of the double cover. -/
theorem polynomial_derivative_isEtaleAt {R : Type*} [CommRing R]
    (H : R[X]) (𝔭 : Ideal R[X]) [𝔭.IsPrime]
    (hder : H.derivative ∉ 𝔭) :
    letI : Algebra R[X] R[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt R[X] 𝔭 := by
  sorry

/-- Polynomial Jacobian criterion for the map of affine lines `t ↦ H(u)` at
a simple zero `x`. This is the standard étale presentation criterion of the
[src_stacks_standard_etale, Tags 00UB and 00UC]: after restricting to the open where
`H'(u)` is invertible, the presentation `k[t,u]/(H(u)-t)` is standard étale, after dividing `H(u)-t` by the nonzero leading
coefficient of `H`. The derivative hypothesis ensures `H` is nonconstant.
The criterion is an external literature input, not a claim about the scaled
double cover. -/
theorem polynomial_simpleRoot_isEtaleAt (H : k[X]) (x : k)
    (_hx : H.eval x = 0) (hsimple : H.derivative.eval x ≠ 0) :
    letI : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
    letI : Algebra k[X] k[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt k[X] (RingHom.ker (evalRingHom x)) := by
  let : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
  apply polynomial_derivative_isEtaleAt
  change H.derivative.eval x ≠ 0
  exact hsimple

/-- At every actual residue crossing, `t = u P(u)` is an étale coordinate.
The only admitted step is the general polynomial Jacobian criterion above;
simple roots of this particular branch polynomial were proved separately. -/
theorem reducedLocalFiniteComponent_isEtaleCoordinate
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0) :
    let H := finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))
    letI : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
    letI : Algebra (ZMod p)[X] (ZMod p)[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt (ZMod p)[X] (RingHom.ker (evalRingHom x)) := by
  exact polynomial_simpleRoot_isEtaleAt _ x hx
    (reducedLocalFiniteComponent_simple_roots p hx)

/-- At the zero crossing the coordinate change in the whole family uses
`z = u P(u)²`.  Its derivative at zero is `P(0)²`, so it is étale when the
other branch roots are nonzero. -/
theorem zeroNodePolynomial_derivative_eval_zero (P : k[X]) :
    ((X * P ^ 2).derivative).eval 0 = (P.eval 0) ^ 2 := by
  simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

theorem zeroNodePolynomial_isEtaleAt (P : k[X]) (hP : P.eval 0 ≠ 0) :
    let H := X * P ^ 2
    letI : (RingHom.ker (evalRingHom (0 : k))).IsPrime := RingHom.ker_isPrime _
    letI : Algebra k[X] k[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt k[X] (RingHom.ker (evalRingHom (0 : k))) := by
  apply polynomial_simpleRoot_isEtaleAt
  · simp
  · rw [zeroNodePolynomial_derivative_eval_zero]
    exact pow_ne_zero _ hP

/-- The nonzero cyclotomic branch roots stay away from the extra crossing
at zero. This unit check is used in the relative zero-node chart. -/
theorem localScaledRootPolynomial_reduction_eval_zero_ne_zero
    (p : ℕ) [Fact p.Prime] :
    (((localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)).eval (0 : ZMod p)) ≠ 0 := by
  rw [localScaledRootPolynomial_reduction_split]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  exact sub_ne_zero.mpr (fun he =>
    zero_not_mem_residueRootSet p (he.symm ▸ hx))

/-- The extra zero crossing of the actual reduced cyclotomic polynomial has
the required étale coordinate `u P(u)²`. -/
theorem reducedLocalZeroNodePolynomial_isEtaleAt (p : ℕ) [Fact p.Prime] :
    let P := (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)
    let H := X * P ^ 2
    letI : (RingHom.ker (evalRingHom (0 : ZMod p))).IsPrime := RingHom.ker_isPrime _
    letI : Algebra (ZMod p)[X] (ZMod p)[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt (ZMod p)[X]
      (RingHom.ker (evalRingHom (0 : ZMod p))) := by
  exact zeroNodePolynomial_isEtaleAt _
    (localScaledRootPolynomial_reduction_eval_zero_ne_zero p)

/-- The point of the coefficient affine line specializing to `x` under a
residue map.  This prime retains the whole DVR coefficient ring, so it can be
used for an étale coordinate on the family rather than only on its fibre. -/
def residuePointPrime {R : Type*} [CommRing R] (f : R →+* k) (x : k) :
    Ideal R[X] :=
  RingHom.ker ((evalRingHom x).comp (Polynomial.mapRingHom f))

instance residuePointPrime_isPrime {R : Type*} [CommRing R]
    (f : R →+* k) (x : k) : (residuePointPrime f x).IsPrime :=
  RingHom.ker_isPrime _

/-- The standard polynomial étale criterion is valid at a point of the
*whole* family whenever the derivative is nonzero after reduction.  This
deduction from the general Jacobian criterion uses no smoothness assumption
on the total space. -/
theorem polynomial_residueDerivative_isEtaleAt {R : Type*} [CommRing R]
    (f : R →+* k) (H : R[X]) (x : k)
    (hder : (H.map f).derivative.eval x ≠ 0) :
    letI : Algebra R[X] R[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt R[X] (residuePointPrime f x) := by
  apply polynomial_derivative_isEtaleAt H (residuePointPrime f x)
  change ((evalRingHom x).comp (Polynomial.mapRingHom f)) H.derivative ≠ 0
  simpa [residuePointPrime, Polynomial.evalRingHom, Polynomial.derivative_map] using hder

/-- The relative affine-line coordinate `u P(u)` at any nonzero residue
crossing of the actual cyclotomic family.  Unlike the fibre-only coordinate,
the prime here lies in the integral coefficient polynomial ring. -/
theorem localFiniteComponent_isEtaleCoordinateOnFamily
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0) :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let H : R[X] := X * P
    letI : Algebra R[X] R[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt R[X]
      (residuePointPrime (Cyclotomic.realLocalReduction p) x) := by
  let P := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
  have hder : ((X * P).map (Cyclotomic.realLocalReduction p)).derivative.eval x ≠ 0 := by
    simpa only [finiteComponentPolynomial_eq, Polynomial.map_mul, Polynomial.map_X] using
      reducedLocalFiniteComponent_simple_roots p hx
  exact polynomial_residueDerivative_isEtaleAt
    (Cyclotomic.realLocalReduction p) (X * P) x hder

/-- The alternative coordinate `u P(u)²` is étale on the whole family at
the zero crossing.  Its unit derivative explains why the quadratic chart
with smoothing thickness `T²` is a genuine étale local chart there. -/
theorem localZeroNodePolynomial_isEtaleCoordinateOnFamily (p : ℕ) [Fact p.Prime] :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let H : R[X] := X * P ^ 2
    letI : Algebra R[X] R[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt R[X]
      (residuePointPrime (Cyclotomic.realLocalReduction p) (0 : ZMod p)) := by
  let P := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
  have hP : (P.map (Cyclotomic.realLocalReduction p)).eval (0 : ZMod p) ≠ 0 := by
    exact localScaledRootPolynomial_reduction_eval_zero_ne_zero p
  have hder : ((X * P ^ 2).map (Cyclotomic.realLocalReduction p)).derivative.eval
      (0 : ZMod p) ≠ 0 := by
    simp only [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_pow]
    rw [zeroNodePolynomial_derivative_eval_zero]
    exact pow_ne_zero _ hP
  exact polynomial_residueDerivative_isEtaleAt
    (Cyclotomic.realLocalReduction p) (X * P ^ 2) 0 hder

/-- An element of the coefficient affine line whose residue is nonzero is a
unit in the local ring at the corresponding whole-family point. This is the
localization fact needed to turn the node product identities into charts. -/
theorem residuePointPrime_isUnit_of_eval_ne_zero {R : Type*} [CommRing R]
    (f : R →+* k) (H : R[X]) (x : k)
    (hH : (H.map f).eval x ≠ 0) :
    letI : (residuePointPrime f x).IsPrime := residuePointPrime_isPrime f x
    IsUnit (algebraMap R[X] (Localization.AtPrime (residuePointPrime f x)) H) := by
  let : (residuePointPrime f x).IsPrime := residuePointPrime_isPrime f x
  apply (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime (residuePointPrime f x)) (residuePointPrime f x) H).2
  change ((evalRingHom x).comp (Polynomial.mapRingHom f)) H ≠ 0
  simpa [Polynomial.evalRingHom] using hH

/-- At a nonzero residue crossing, the affine coordinate `u` is invertible
in the local ring of the whole family. Thus `-4Tu` differs from `-4T` by a
unit at that node. -/
theorem residuePointPrime_X_isUnit_of_ne_zero {R : Type*} [CommRing R]
    (f : R →+* k) (x : k) (hx : x ≠ 0) :
    letI : (residuePointPrime f x).IsPrime := residuePointPrime_isPrime f x
    IsUnit (algebraMap R[X] (Localization.AtPrime (residuePointPrime f x)) X) := by
  apply residuePointPrime_isUnit_of_eval_ne_zero f X x
  simpa using hx

/-- At the zero crossing of the actual family, `P(u)` is a unit in the
whole-family local coefficient ring. Together with the étale coordinate
`uP(u)²`, this justifies the chart with smoothing parameter `-4T²`. -/
theorem localScaledRootPolynomial_isUnit_atZeroNode (p : ℕ) [Fact p.Prime] :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let 𝔭 := residuePointPrime (Cyclotomic.realLocalReduction p) (0 : ZMod p)
    letI : 𝔭.IsPrime := residuePointPrime_isPrime _ _
    IsUnit (algebraMap R[X] (Localization.AtPrime 𝔭) P) := by
  let P := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
  apply residuePointPrime_isUnit_of_eval_ne_zero
    (Cyclotomic.realLocalReduction p) P 0
  exact localScaledRootPolynomial_reduction_eval_zero_ne_zero p

end HilbertModularity.Hyperelliptic
