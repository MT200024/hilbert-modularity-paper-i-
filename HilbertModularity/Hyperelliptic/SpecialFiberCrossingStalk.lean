/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingLocalization
public import HilbertModularity.Hyperelliptic.SpecialFiberNodeEquation

/-! # The local algebra at an actual finite crossing

The finite chart localized at a branch crossing has the explicit split-node
quadratic presentation. The separate localization theorem certifies that this
is the stalk of the actual chart at its rational crossing prime.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

/-- The evaluation kernel is the maximal ideal of a rational point of the
coefficient line. -/
instance evalRingHom_ker_isPrime {k : Type*} [Field k] (x : k) :
    (RingHom.ker (evalRingHom x)).IsPrime :=
  RingHom.ker_isPrime _

/-- At a simple zero of the component polynomial, the local algebra of the
actual finite quadratic chart has equation `y * (y - 2*t) = 0`, with `t` the
standard parameter on the base line. -/
def finiteCrossing_localNodeEquiv
    {k : Type*} [Field k] (P : k[X]) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0)
    (hsimple : (finiteComponentPolynomial P).derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    QuadraticAlgebra S
      (algebraMap k[X] S (finiteBranchPolynomial P 0))
      (algebraMap k[X] S 0) ≃ₐ[S]
        QuadraticAlgebra S 0
          (2 * algebraMap k[X] S (X - C x)) := by
  rw [finiteBranchPolynomial_zero, map_pow, map_zero]
  exact squareBranch_localNodeEquiv (finiteComponentPolynomial P) x hx hsimple S

/-- For each cyclotomic crossing, this is the split-node presentation of the
actual local finite chart, whose localization prime is identified by
`finiteCrossing_baseChange_isLocalization_atPrime`. -/
def reducedLocalFiniteCrossing_localNodeEquiv
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0)
    (S : Type*) [CommRing S] [Algebra (ZMod p)[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    QuadraticAlgebra S
      (algebraMap (ZMod p)[X] S
        (finiteBranchPolynomial
          ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
            (Cyclotomic.realLocalReduction p)) 0))
      (algebraMap (ZMod p)[X] S 0) ≃ₐ[S]
        QuadraticAlgebra S 0
          (2 * algebraMap (ZMod p)[X] S (X - C x)) :=
  finiteCrossing_localNodeEquiv _ x hx
    (reducedLocalFiniteComponent_simple_roots p hx) S

/-- The canonical coefficient local ring gives the nodal presentation of the
actual crossing stalk. The finite chart localization is certified separately
by `finiteCrossing_stalk_isLocalization_atPrime`. -/
def finiteCrossing_stalkNodeEquiv
    {k : Type*} [Field k] (P : k[X]) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0)
    (hsimple : (finiteComponentPolynomial P).derivative.eval x ≠ 0) :
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    QuadraticAlgebra S
      (algebraMap k[X] S (finiteBranchPolynomial P 0))
      (algebraMap k[X] S 0) ≃ₐ[S]
        QuadraticAlgebra S 0
          (2 * algebraMap k[X] S (X - C x)) := by
  letI : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
  exact finiteCrossing_localNodeEquiv P x hx hsimple _

/-- The model identified by `finiteCrossing_stalkNodeEquiv` really localizes
the finite chart at its rational crossing prime. -/
theorem finiteCrossing_stalk_isLocalization_atPrime
    {k : Type*} [Field k] (P : k[X]) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0) :
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    IsLocalization.AtPrime
      (QuadraticAlgebra S
        (algebraMap k[X] S (finiteBranchPolynomial P 0))
        (algebraMap k[X] S 0))
      (RingHom.ker (finiteCrossingEvaluation P x).toRingHom) := by
  let : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
  exact finiteCrossing_baseChange_isLocalization_atPrime P x hx _

end HilbertModularity.Hyperelliptic
