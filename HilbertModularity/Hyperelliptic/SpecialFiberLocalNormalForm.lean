/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberLocalParameters
public import HilbertModularity.Geometry.QuadraticLocalization

/-! # A local normal form for a simple square-branch crossing

After localizing at a simple zero of the branch polynomial, its quotient by
the linear factor is a unit. Changing the quadratic generator by this unit
identifies the actual square-branch chart with the quadratic chart whose
branch is the square of the local coordinate. The two factors in the latter
chart multiply to zero. A completed-local-ring node criterion is still needed
to turn this algebraic normal form into a Scheme nodality assertion.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

/-- Scaling the quadratic generator removes a unit factor from a square branch. -/
def squareBranchScaleEquiv {S : Type*} [CommRing S] (t : S) (u : Sˣ) :
    QuadraticAlgebra S ((t * (u : S)) ^ 2) 0 ≃ₐ[S]
      QuadraticAlgebra S (t ^ 2) 0 :=
  QuadraticAlgebra.changeGeneratorEquiv (t ^ 2) 0 u 0 (by ring) (by ring)

/-- The scaled normal-form map sends the old square root to the unit times
the normal-form square root. -/
theorem squareBranchScaleEquiv_omega {S : Type*} [CommRing S] (t : S) (u : Sˣ) :
    squareBranchScaleEquiv t u
      (QuadraticAlgebra.omega : QuadraticAlgebra S ((t * (u : S)) ^ 2) 0) =
      (u : S) • (QuadraticAlgebra.omega : QuadraticAlgebra S (t ^ 2) 0) := by
  simp [squareBranchScaleEquiv, QuadraticAlgebra.changeGeneratorEquiv_apply,
    QuadraticAlgebra.changeGenerator_omega]

/-- At a simple zero, the localized square-branch chart is the quadratic
chart of the square of the standard local coordinate. -/
theorem squareBranch_localNormalForm
    {k : Type*} [Field k] (H : k[X]) (x : k)
    (hx : H.eval x = 0) (hsimple : H.derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    Nonempty (QuadraticAlgebra S ((algebraMap k[X] S H) ^ 2) 0 ≃ₐ[S]
      QuadraticAlgebra S ((algebraMap k[X] S (X - C x)) ^ 2) 0) := by
  obtain ⟨u, hu⟩ := branch_localParameter_factor H x hx hsimple S
  refine ⟨?_⟩
  rw [hu]
  exact squareBranchScaleEquiv (algebraMap k[X] S (X - C x)) u

/-- A chosen algebra equivalence for the local square-branch chart. -/
noncomputable def squareBranch_localNormalFormEquiv
    {k : Type*} [Field k] (H : k[X]) (x : k)
    (hx : H.eval x = 0) (hsimple : H.derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    QuadraticAlgebra S ((algebraMap k[X] S H) ^ 2) 0 ≃ₐ[S]
      QuadraticAlgebra S ((algebraMap k[X] S (X - C x)) ^ 2) 0 :=
  Classical.choice (squareBranch_localNormalForm H x hx hsimple S)

/-- The actual cyclotomic finite-chart crossing has this unit-scaled
quadratic normal form at each of its residue roots. -/
theorem reducedLocalFiniteComponent_localNormalForm
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0)
    (S : Type*) [CommRing S] [Algebra (ZMod p)[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    Nonempty (QuadraticAlgebra S
        ((algebraMap (ZMod p)[X] S
          (finiteComponentPolynomial
            ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
              (Cyclotomic.realLocalReduction p)))) ^ 2) 0 ≃ₐ[S]
        QuadraticAlgebra S ((algebraMap (ZMod p)[X] S (X - C x)) ^ 2) 0) :=
  squareBranch_localNormalForm _ x hx
    (reducedLocalFiniteComponent_simple_roots p hx) S

end HilbertModularity.Hyperelliptic
