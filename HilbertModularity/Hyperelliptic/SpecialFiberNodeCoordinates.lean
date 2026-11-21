/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberEtaleCoordinate
public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingStalk

/-! # Coordinates at the actual square-branch crossings

The special-fibre equation is `W² = t²`. The linear coordinates
`U = W - t` and `V = W + t` have `UV = 0`. When two is invertible,
`W = (U + V)/2` and `t = (V - U)/2`. These identities apply to the
localized chart at each actual simple residue root; the separate étale
coordinate theorem identifies `t = u P(u)` as a local parameter.
-/

public noncomputable section

open Polynomial
open scoped QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

/-- The two linear coordinates on the square-branch quadratic chart. -/
def nodeMinus {S : Type*} [CommRing S] (t : S) : QuadraticAlgebra S (t ^ 2) 0 :=
  QuadraticAlgebra.omega - algebraMap S _ t

/-- The second linear coordinate on the square-branch quadratic chart. -/
def nodePlus {S : Type*} [CommRing S] (t : S) : QuadraticAlgebra S (t ^ 2) 0 :=
  QuadraticAlgebra.omega + algebraMap S _ t

/-- The two node coordinates multiply to zero on the actual square-branch chart. -/
theorem nodeMinus_mul_nodePlus {S : Type*} [CommRing S] (t : S) :
    nodeMinus t * nodePlus t = 0 := by
  calc
    _ = (QuadraticAlgebra.omega : QuadraticAlgebra S (t ^ 2) 0) ^ 2 -
        (algebraMap S (QuadraticAlgebra S (t ^ 2) 0) t) ^ 2 := by
          simp only [nodeMinus, nodePlus]
          ring
    _ = 0 := by
      simp only [pow_two]
      rw [QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_pow]
      simp only [pow_two, map_zero, zero_mul, add_zero, sub_self]

/-- The inverse linear transformation recovers the square-root generator. -/
theorem nodeCoordinates_recover_omega {S : Type*} [CommRing S]
    (t half : S) (hhalf : (2 : S) * half = 1) :
    algebraMap S (QuadraticAlgebra S (t ^ 2) 0) half *
        (nodeMinus t + nodePlus t) = QuadraticAlgebra.omega := by
  simp only [nodeMinus, nodePlus]
  have h : (algebraMap S (QuadraticAlgebra S (t ^ 2) 0) (2 * half)) = 1 := by
    rw [hhalf, map_one]
  calc
    _ = algebraMap S (QuadraticAlgebra S (t ^ 2) 0) (2 * half) *
        QuadraticAlgebra.omega := by
          noncomm_ring
          simp only [two_smul, map_add, add_mul]
    _ = _ := by rw [h, one_mul]

/-- The inverse linear transformation recovers the base parameter. -/
theorem nodeCoordinates_recover_parameter {S : Type*} [CommRing S]
    (t half : S) (hhalf : (2 : S) * half = 1) :
    algebraMap S (QuadraticAlgebra S (t ^ 2) 0) half *
        (nodePlus t - nodeMinus t) = algebraMap S _ t := by
  simp only [nodeMinus, nodePlus]
  have h : (algebraMap S (QuadraticAlgebra S (t ^ 2) 0) (2 * half)) = 1 := by
    rw [hhalf, map_one]
  calc
    _ = algebraMap S (QuadraticAlgebra S (t ^ 2) 0) (2 * half) *
        algebraMap S _ t := by
          noncomm_ring
          simp only [two_smul, map_add, add_mul]
    _ = _ := by rw [h, one_mul]

/-- The first coordinate on the actual crossing stalk is `W-uP(u)`. -/
def finiteCrossing_stalkNodeU
    {k : Type*} [Field k] (P : k[X]) (x : k) :
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    QuadraticAlgebra S
      (algebraMap k[X] S (finiteBranchPolynomial P 0))
      (algebraMap k[X] S 0) := by
  let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
  exact QuadraticAlgebra.omega -
    algebraMap S
      (QuadraticAlgebra S
        (algebraMap k[X] S (finiteBranchPolynomial P 0))
        (algebraMap k[X] S 0))
      (algebraMap k[X] S (finiteComponentPolynomial P))

/-- The second coordinate on the actual crossing stalk is `W+uP(u)`. -/
def finiteCrossing_stalkNodeV
    {k : Type*} [Field k] (P : k[X]) (x : k) :
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    QuadraticAlgebra S
      (algebraMap k[X] S (finiteBranchPolynomial P 0))
      (algebraMap k[X] S 0) := by
  let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
  exact QuadraticAlgebra.omega +
    algebraMap S
      (QuadraticAlgebra S
        (algebraMap k[X] S (finiteBranchPolynomial P 0))
        (algebraMap k[X] S 0))
      (algebraMap k[X] S (finiteComponentPolynomial P))

/-- The actual square-branch stalk equation factors as
`(W-uP(u)) (W+uP(u)) = 0`. -/
theorem finiteCrossing_stalk_nodeCoordinates
    {k : Type*} [Field k] (P : k[X]) (x : k) :
    finiteCrossing_stalkNodeU P x * finiteCrossing_stalkNodeV P x = 0 := by
  let : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
  let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
  let t := algebraMap k[X] S (finiteComponentPolynomial P)
  apply QuadraticAlgebra.ext <;>
    simp [finiteCrossing_stalkNodeU, finiteCrossing_stalkNodeV,
      finiteBranchPolynomial_zero, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul] ; ring

end HilbertModularity.Hyperelliptic
