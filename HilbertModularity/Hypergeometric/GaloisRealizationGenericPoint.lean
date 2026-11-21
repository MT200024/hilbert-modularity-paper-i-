/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationOpenQuotient

/-! # The generic point of the Euler cover

The actual function field of the exponent-`m` Euler cover supplies a generic
branch-open point. Its reflection orbit gives rational invariant elements of
that field before choosing an ℓ-adic coefficient place. This construction is
point-level data; the smooth proper quotient and its cohomology are separate.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The actual generic point of the branch-open Euler cover. -/
def genericOpenEulerPoint (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    OpenEulerPoint N m (algebraMap K (CoverFunctionField N m t) t) := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let x := coverFunctionFieldX N m t
  let y := coverFunctionFieldRoot N m t
  have htcoeff : algebraMap (BaseRing t) (CoverFunctionField N m t)
      (algebraMap K[X] (BaseRing t) (C t)) =
      algebraMap K (CoverFunctionField N m t) t := by
    rw [← IsScalarTower.algebraMap_apply K[X] (BaseRing t)
      (CoverFunctionField N m t)]
    exact (IsScalarTower.algebraMap_apply K K[X]
      (CoverFunctionField N m t) t).symm
  have hx : x ≠ 0 := by
    have hu := (isUnit_xCoordinate t).map
      (algebraMap (BaseRing t) (CoverFunctionField N m t))
    have heq : algebraMap (BaseRing t) (CoverFunctionField N m t)
        (xCoordinate t) = x := by
      simp [xCoordinate, x, coverFunctionFieldX,
        IsScalarTower.algebraMap_apply K[X] (BaseRing t)
          (CoverFunctionField N m t)]
    exact heq ▸ hu.ne_zero
  have hy : y ≠ 0 := by
    have hu := (isUnit_radicand N m t).map
      (algebraMap (BaseRing t) (CoverFunctionField N m t))
    have hpow : y ^ N = algebraMap (BaseRing t) (CoverFunctionField N m t)
        (radicand N m t) := by
      simp [y, coverFunctionFieldRoot, ← map_pow, coverRoot_pow,
        IsScalarTower.algebraMap_apply (BaseRing t) (CoverRing N m t)
          (CoverFunctionField N m t)]
    intro h
    apply hu.ne_zero
    rw [← hpow, h, zero_pow hN]
  have h1x : 1 - x ≠ 0 := by
    have hu := (isUnit_oneMinusX t).map
      (algebraMap (BaseRing t) (CoverFunctionField N m t))
    have heq : algebraMap (BaseRing t) (CoverFunctionField N m t)
        (oneMinusX t) = 1 - x := by
      simp [oneMinusX, x, coverFunctionFieldX,
        IsScalarTower.algebraMap_apply K[X] (BaseRing t)
          (CoverFunctionField N m t)]
    exact heq ▸ hu.ne_zero
  have h1tx : 1 - (algebraMap K (CoverFunctionField N m t) t) * x ≠ 0 := by
    have hu := (isUnit_oneMinusTX t).map
      (algebraMap (BaseRing t) (CoverFunctionField N m t))
    have heq : algebraMap (BaseRing t) (CoverFunctionField N m t)
        (oneMinusTX t) = 1 - (algebraMap K (CoverFunctionField N m t) t) * x := by
      simp [oneMinusTX, x, coverFunctionFieldX, htcoeff,
        IsScalarTower.algebraMap_apply K[X] (BaseRing t)
          (CoverFunctionField N m t)]
    exact heq ▸ hu.ne_zero
  refine ⟨x, y, hx, hy, h1x, h1tx, ?_⟩
  have hpow : y ^ N = algebraMap (BaseRing t) (CoverFunctionField N m t)
      (radicand N m t) := by
    simp [y, coverFunctionFieldRoot, ← map_pow, coverRoot_pow,
      IsScalarTower.algebraMap_apply (BaseRing t) (CoverRing N m t)
        (CoverFunctionField N m t)]
  simpa [radicand, branchPolynomial, x, coverFunctionFieldX, htcoeff,
    map_mul, map_pow, map_sub,
    IsScalarTower.algebraMap_apply K[X] (BaseRing t)
      (CoverFunctionField N m t)] using hpow

@[simp] theorem genericOpenEulerPoint_x (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericOpenEulerPoint N m t hN hmPos hm hcop).x =
      coverFunctionFieldX N m t := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rfl

@[simp] theorem genericOpenEulerPoint_y (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericOpenEulerPoint N m t hN hmPos hm hcop).y =
      coverFunctionFieldRoot N m t := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rfl

/-- The reflection orbit of the actual generic Euler point. It is chosen in
the function field before any coefficient place or Galois representation. -/
def genericOpenEulerReflectionOrbit (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    OpenEulerReflectionQuotient N m (Nat.le_of_lt hm)
      ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht) := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact openEulerReflectionQuotientMk N m (Nat.le_of_lt hm)
    ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht)
    (genericOpenEulerPoint N m t hN hmPos hm hcop)

/-- The two explicit rational reflection invariants evaluated at the actual
generic point of the exponent-`m` Euler curve. -/
def genericReflectionInvariantCoordinates (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    CoverFunctionField N m t × CoverFunctionField N m t := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact openEulerReflectionCoordinates
    (genericOpenEulerPoint N m t hN hmPos hm hcop)

@[simp] theorem genericReflectionInvariantCoordinates_fst (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).1 =
      reflectionInvariantX (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  unfold genericReflectionInvariantCoordinates
  simp only [openEulerReflectionCoordinates_fst, genericOpenEulerPoint_x]

@[simp] theorem genericReflectionInvariantCoordinates_snd (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).2 =
      reflectionInvariantY (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) (coverFunctionFieldRoot N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  unfold genericReflectionInvariantCoordinates
  simp only [openEulerReflectionCoordinates_snd, genericOpenEulerPoint_x,
    genericOpenEulerPoint_y]

/-- The generic invariant coordinates descend through the point-level
reflection orbit. This does not assert that the orbit represents a scheme. -/
theorem genericReflectionInvariantCoordinates_orbit (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    openEulerReflectionQuotientCoordinates N m (Nat.le_of_lt hm)
        ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht)
        (genericOpenEulerReflectionOrbit N m t hN hmPos hm hcop ht) =
      genericReflectionInvariantCoordinates N m t hN hmPos hm hcop := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact openEulerReflectionQuotientCoordinates_mk N m (Nat.le_of_lt hm)
    ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht)
    (genericOpenEulerPoint N m t hN hmPos hm hcop)

end HilbertModularity.Hypergeometric.EulerCover
