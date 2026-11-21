/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationGenericPoint

/-! # Invariant coordinates in the generic Euler function field

The reflection formulas of [GPRV, Proposition 9.5] produce two rational
coordinates in the actual Euler function field before choosing a coefficient
place. Their generated intermediate field is a candidate for the function field
of the quotient. Identifying it with the fixed field requires a field
automorphism and is a separate assertion.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The base coordinate satisfies a quadratic relation over its reflection
invariant coordinate. -/
theorem reflectionInvariantX_quadratic {F : Type*} [Field F]
    {t x : F} (ht : t ≠ 0) (hx : x ≠ 0) :
    x ^ 2 - reflectionInvariantX t x * x + t⁻¹ = 0 := by
  rw [reflectionInvariantX_eq]
  field_simp
  ring

/-- The covering coordinate satisfies a quadratic relation after adjoining
the base coordinate and its reflection invariant companion. -/
theorem reflectionInvariantY_quadratic {F : Type*} [Field F]
    {t x y : F} (ht : t ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    y ^ 2 - reflectionInvariantY t x y * y -
      (1 - x) * (1 - t * x) / (t * x) = 0 := by
  rw [reflectionInvariantY_eq]
  field_simp
  ring

/-- The explicitly generated field of the two rational reflection
invariants, inside the actual generic Euler function field. This definition
does not assert that it is the full fixed field of the involution. -/
def genericReflectionInvariantField (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    IntermediateField K (CoverFunctionField N m t) := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact IntermediateField.adjoin K
    ({(genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).1,
       (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).2} :
      Set (CoverFunctionField N m t))

/-- The explicit generators of the rational invariant field. -/
theorem genericReflectionInvariantField_eq_adjoin (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionInvariantField N m t hN hmPos hm hcop =
      IntermediateField.adjoin K
        ({(genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).1,
           (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).2} :
          Set (CoverFunctionField N m t)) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  unfold genericReflectionInvariantField
  exact (rfl)

/-- The first explicit coordinate belongs to the generated intermediate field. -/
theorem genericReflectionInvariantX_mem (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).1 ∈
      genericReflectionInvariantField N m t hN hmPos hm hcop := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  apply IntermediateField.subset_adjoin
  simp

/-- The second explicit coordinate belongs to the generated intermediate field. -/
theorem genericReflectionInvariantY_mem (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).2 ∈
      genericReflectionInvariantField N m t hN hmPos hm hcop := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  apply IntermediateField.subset_adjoin
  simp

end HilbertModularity.Hypergeometric.EulerCover
