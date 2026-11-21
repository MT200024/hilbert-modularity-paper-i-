/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberFamilyNodeCoordinates
public import HilbertModularity.Hyperelliptic.SpecialFiberEtaleCoordinate

/-! # Applying the family node coordinates at residue crossings

The product `-4TX` on the finite chart has thickness `T` at a nonzero
crossing because `X` is a unit there. At zero, `P(X)` is a unit and the
alternate coordinate has thickness `T²`. These are statements about the
actual local coefficient ring of the family, not regularity claims for the
total space.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- At a nonzero residue crossing, the actual finite-chart branch equation
becomes a node equation with smoothing parameter `-4T` after dividing one
coordinate by the unit `X`. -/
theorem familyNonzeroNode_atResiduePoint {R : Type*} [CommRing R]
    (f : R →+* k) (P : R[X]) (T : R) (x : k) (hx : x ≠ 0) :
    letI : (residuePointPrime f x).IsPrime := residuePointPrime_isPrime f x
    let A := Localization.AtPrime (residuePointPrime f x)
    ∃ u : Aˣ, (u : A) = algebraMap R[X] A X ∧
      algebraMap R[X] A (finiteBranchPolynomial P T) =
        (algebraMap R[X] A (X * P)) ^ 2 -
          4 * algebraMap R[X] A (C T) * (u : A) ∧
      let B := QuadraticAlgebra A
        ((algebraMap R[X] A (X * P)) ^ 2 -
          4 * algebraMap R[X] A (C T) * (u : A)) 0
      familyNodeMinus (algebraMap R[X] A (X * P))
          (algebraMap R[X] A (C T)) (u : A) *
        (familyNodePlus (algebraMap R[X] A (X * P))
          (algebraMap R[X] A (C T)) (u : A) *
          algebraMap A B (↑u⁻¹ : A)) =
        algebraMap A B (-(4 * algebraMap R[X] A (C T))) := by
  let : (residuePointPrime f x).IsPrime := residuePointPrime_isPrime f x
  let A := Localization.AtPrime (residuePointPrime f x)
  obtain ⟨u, hu⟩ := residuePointPrime_X_isUnit_of_ne_zero f x hx
  refine ⟨u, hu, ?_, ?_⟩
  · rw [finiteBranchPolynomial_eq_nodeEquation]
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    rw [hu]
  · exact familyNonzeroNode_product _ _ u

/-- At the zero residue crossing the factor `P(u)` is a unit, so multiplying
the square-root coordinate by it gives an isomorphism of the local quadratic
algebra with a node chart. Its smoothing parameter is exactly `-4T²`, not
`-4T`. -/
theorem familyZeroNode_atResiduePoint {R : Type*} [CommRing R]
    (f : R →+* k) (P : R[X]) (T : R)
    (hP0 : (P.map f).eval 0 ≠ 0) :
    letI : (residuePointPrime f (0 : k)).IsPrime :=
      residuePointPrime_isPrime f 0
    let A := Localization.AtPrime (residuePointPrime f (0 : k))
    let u := algebraMap R[X] A X
    let t := algebraMap R[X] A (C T)
    ∃ q : Aˣ, (q : A) = algebraMap R[X] A P ∧
      Nonempty (familyZeroNodeAlgebra (q : A) u t ≃ₐ[A]
        QuadraticAlgebra A (algebraMap R[X] A (finiteBranchPolynomial P T)) 0) ∧
      familyZeroNodeMinus (q : A) u t * familyZeroNodePlus (q : A) u t =
        algebraMap A _ (-(4 * t ^ 2)) := by
  let : (residuePointPrime f (0 : k)).IsPrime := residuePointPrime_isPrime f 0
  let A := Localization.AtPrime (residuePointPrime f (0 : k))
  let u : A := algebraMap R[X] A X
  let t : A := algebraMap R[X] A (C T)
  obtain ⟨q, hq⟩ := residuePointPrime_isUnit_of_eval_ne_zero f P 0 hP0
  refine ⟨q, hq, ?_, ?_⟩
  · have hbranch : algebraMap R[X] A (finiteBranchPolynomial P T) =
        (u * (q : A)) ^ 2 - 4 * t * u := by
      rw [finiteBranchPolynomial_eq_nodeEquation]
      simp only [map_sub, map_pow, map_mul, map_ofNat]
      rw [hq]
    rw [hbranch]
    exact ⟨familyZeroNodeCoordinateEquiv q u t⟩
  · exact familyZeroNodeMinus_mul_familyZeroNodePlus (q : A) u t

/-- The zero node of the *cyclotomic scaled family* has the actual local
quadratic chart whose two coordinates multiply to `-4T²`. The general
construction above supplies the algebra equivalence; the only arithmetic
input here is the previously proved nonvanishing of `P(0)` modulo the
chosen prime. -/
theorem cyclotomicZeroNode_localChart (p : ℕ) [Fact p.Prime]
    (T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)) :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let 𝔭 := residuePointPrime (Cyclotomic.realLocalReduction p) (0 : ZMod p)
    letI : 𝔭.IsPrime := residuePointPrime_isPrime _ _
    let A := Localization.AtPrime 𝔭
    let u := algebraMap R[X] A X
    let t := algebraMap R[X] A (C T)
    ∃ q : Aˣ, (q : A) = algebraMap R[X] A P ∧
      Nonempty (familyZeroNodeAlgebra (q : A) u t ≃ₐ[A]
        QuadraticAlgebra A (algebraMap R[X] A (finiteBranchPolynomial P T)) 0) := by
  let P := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
  obtain ⟨q, hq, he, _⟩ := familyZeroNode_atResiduePoint
    (Cyclotomic.realLocalReduction p) P T
      (localScaledRootPolynomial_reduction_eval_zero_ne_zero p)
  exact ⟨q, hq, he⟩

/-- At each nonzero cyclotomic crossing, the actual local finite-chart
equation has a unit `u`, equal to the affine coordinate, for which the node
coordinates multiply to `-4T` after dividing by `u`. -/
theorem cyclotomicNonzeroNode_localChart (p : ℕ) [Fact p.Prime]
    (T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p))
    (x : ZMod p) (hx : x ∈ residueRootSet p) :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let 𝔭 := residuePointPrime (Cyclotomic.realLocalReduction p) x
    letI : 𝔭.IsPrime := residuePointPrime_isPrime _ _
    let A := Localization.AtPrime 𝔭
    ∃ u : Aˣ, (u : A) = algebraMap R[X] A X ∧
      algebraMap R[X] A (finiteBranchPolynomial P T) =
        (algebraMap R[X] A (X * P)) ^ 2 -
          4 * algebraMap R[X] A (C T) * (u : A) ∧
      let B := QuadraticAlgebra A
        ((algebraMap R[X] A (X * P)) ^ 2 -
          4 * algebraMap R[X] A (C T) * (u : A)) 0
      familyNodeMinus (algebraMap R[X] A (X * P))
          (algebraMap R[X] A (C T)) (u : A) *
        (familyNodePlus (algebraMap R[X] A (X * P))
          (algebraMap R[X] A (C T)) (u : A) *
          algebraMap A B (↑u⁻¹ : A)) =
        algebraMap A B (-(4 * algebraMap R[X] A (C T))) := by
  have hxn : x ≠ 0 := by
    intro h
    exact zero_not_mem_residueRootSet p (h ▸ hx)
  exact familyNonzeroNode_atResiduePoint
    (Cyclotomic.realLocalReduction p)
      (localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)) T x hxn

end HilbertModularity.Hyperelliptic
