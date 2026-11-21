/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberLocalNormalForm

/-! # Nodal equation at a simple crossing of the special fibre

Translating the square-root generator gives the equation `y * (y - 2*t) = 0`,
where `t` is the local coordinate on the base. At an actual cyclotomic
crossing, the branch polynomial differs from `t` by a unit, so this equation
applies to the localized finite chart. A scheme-theoretic node criterion is
still needed to identify its completed local ring.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

/-- Translating the square root gives the quadratic presentation with
relation `y² = 2*t*y`. The new generator maps back to `w + t`. -/
def squareBranchNodeEquiv {S : Type*} [CommRing S] (t : S) :
    QuadraticAlgebra S (t ^ 2) 0 ≃ₐ[S] QuadraticAlgebra S 0 (2 * t) :=
  (QuadraticAlgebra.changeGeneratorEquiv (t ^ 2) 0 (1 : Sˣ) t
    (by simp) (by simp)).symm

/-- The two branches in the translated presentation have zero product. -/
theorem nodeEquation {S : Type*} [CommRing S] (t : S) :
    (QuadraticAlgebra.omega : QuadraticAlgebra S 0 (2 * t)) *
      (QuadraticAlgebra.omega -
        algebraMap S (QuadraticAlgebra S 0 (2 * t)) (2 * t)) = 0 := by
  apply QuadraticAlgebra.ext <;>
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- At a simple branch zero, the actual localized square-branch algebra has
the translated quadratic presentation `y² = 2*t*y`. -/
def squareBranch_localNodeEquiv
    {k : Type*} [Field k] (H : k[X]) (x : k)
    (hx : H.eval x = 0) (hsimple : H.derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    QuadraticAlgebra S ((algebraMap k[X] S H) ^ 2) 0 ≃ₐ[S]
      QuadraticAlgebra S 0 (2 * algebraMap k[X] S (X - C x)) :=
  (squareBranch_localNormalFormEquiv H x hx hsimple S).trans
    (squareBranchNodeEquiv (algebraMap k[X] S (X - C x)))

/-- The actual cyclotomic finite crossing has the zero-product nodal
presentation after localizing at its residue root. -/
def reducedLocalFiniteComponent_localNodeEquiv
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0)
    (S : Type*) [CommRing S] [Algebra (ZMod p)[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    QuadraticAlgebra S
      ((algebraMap (ZMod p)[X] S
        (finiteComponentPolynomial
          ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
            (Cyclotomic.realLocalReduction p)))) ^ 2) 0 ≃ₐ[S]
      QuadraticAlgebra S 0 (2 * algebraMap (ZMod p)[X] S (X - C x)) :=
  squareBranch_localNodeEquiv _ x hx
    (reducedLocalFiniteComponent_simple_roots p hx) S

end HilbertModularity.Hyperelliptic
