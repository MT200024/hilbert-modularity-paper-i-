/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationReflectionFixedField

/-! # Rational Euler invariants lie in the reflection fixed field

The two coordinates of the actual generic Euler point from [GPRV,
Proposition 9.5] are fixed by its function-field reflection. Thus the field
they generate lies in the fixed field. This does not identify the function
field of the selected smooth proper quotient.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The first explicit rational coordinate is fixed by the actual Euler reflection. -/
theorem genericReflectionInvariantX_fixed (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht)
        (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).1 =
      (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).1 := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let F := CoverFunctionField N m t
  let x := coverFunctionFieldX N m t
  let y := coverFunctionFieldRoot N m t
  let u := algebraMap K F t
  have hu : u ≠ 0 := (map_ne_zero (algebraMap K F)).mpr ht
  have hx := (genericOpenEulerPoint N m t hN hmPos hm hcop).x_ne_zero
  have hx' : x ≠ 0 := by simpa [x] using hx
  rw [genericReflectionInvariantCoordinates_fst]
  change (genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht)
      (reflectionInvariantX u x) = reflectionInvariantX u x
  rw [genericReflectionFunctionFieldEquiv_apply,
    map_reflectionInvariantX,
    genericReflectionFunctionFieldHom_const,
    genericReflectionFunctionFieldHom_x]
  exact reflectionInvariantX_reflect hu hx'

/-- The second explicit rational coordinate is fixed by the actual Euler reflection. -/
theorem genericReflectionInvariantY_fixed (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht)
        (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).2 =
      (genericReflectionInvariantCoordinates N m t hN hmPos hm hcop).2 := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let F := CoverFunctionField N m t
  let x := coverFunctionFieldX N m t
  let y := coverFunctionFieldRoot N m t
  let u := algebraMap K F t
  have hu : u ≠ 0 := (map_ne_zero (algebraMap K F)).mpr ht
  have hx := (genericOpenEulerPoint N m t hN hmPos hm hcop).x_ne_zero
  have hy := (genericOpenEulerPoint N m t hN hmPos hm hcop).y_ne_zero
  have h1x := (genericOpenEulerPoint N m t hN hmPos hm hcop).one_sub_x_ne_zero
  have h1tx := (genericOpenEulerPoint N m t hN hmPos hm hcop).one_sub_tx_ne_zero
  have hx' : x ≠ 0 := by simpa [x] using hx
  have hy' : y ≠ 0 := by simpa [y] using hy
  have h1x' : 1 - x ≠ 0 := by simpa [x] using h1x
  have h1tx' : 1 - u * x ≠ 0 := by simpa [u, x] using h1tx
  rw [genericReflectionInvariantCoordinates_snd]
  change (genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht)
      (reflectionInvariantY u x y) = reflectionInvariantY u x y
  rw [genericReflectionFunctionFieldEquiv_apply,
    map_reflectionInvariantY,
    genericReflectionFunctionFieldHom_const,
    genericReflectionFunctionFieldHom_x,
    genericReflectionFunctionFieldHom_root]
  exact reflectionInvariantY_reflect hu hx' hy' h1x' h1tx'

/-- The explicitly generated invariant-coordinate field is contained in the
actual fixed field of the generic reflection. -/
theorem genericReflectionInvariantField_le_fixedField (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionInvariantField N m t hN hmPos hm hcop :
      Set (CoverFunctionField N m t)) ⊆
      FixedPoints.subfield
        (Subgroup.zpowers
          (genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht))
        (CoverFunctionField N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let F := CoverFunctionField N m t
  let r : RingAut F := genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht
  let : MulSemiringAction (RingAut F) F := RingAut.applyMulSemiringAction
  let S : Subfield F := FixedPoints.subfield (Subgroup.zpowers r) F
  have hcoord (a : F) (ha : r a = a) :
      a ∈ S := by
    change ∀ g : Subgroup.zpowers r, g • a = a
    intro g
    exact smul_eq_self_of_mem_zpowers g.property ha
  have hconst (a : K) : algebraMap K F a ∈ S := by
    apply hcoord
    rw [genericReflectionFunctionFieldEquiv_apply]
    exact genericReflectionFunctionFieldHom_const N m t hN hmPos hm hcop ht a
  intro a ha
  rw [genericReflectionInvariantField_eq_adjoin] at ha
  refine IntermediateField.adjoin_induction K (p := fun z _ => z ∈ S)
    ?_ ?_ ?_ ?_ ?_ ha
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hcoord _ (genericReflectionInvariantX_fixed N m t hN hmPos hm hcop ht)
    · rw [hz]
      exact hcoord _ (genericReflectionInvariantY_fixed N m t hN hmPos hm hcop ht)
  · exact hconst
  · intro x y hx hy ihx ihy
    exact S.add_mem ihx ihy
  · intro x hx ih
    exact S.inv_mem ih
  · intro x y hx hy ihx ihy
    exact S.mul_mem ihx ihy

end HilbertModularity.Hypergeometric.EulerCover
