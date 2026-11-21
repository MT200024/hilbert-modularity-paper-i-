/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicUnramified
public import Mathlib.RepresentationTheory.Basic

/-! # Absolute inertia at cyclotomic coefficient primes

In the fixed algebraic closure, inertia away from the conductor fixes the
cyclotomic coefficient field pointwise. This compares the actual inertia
subgroups used when restricting an arithmetic representation to that field.
-/

@[expose] public noncomputable section

open scoped NumberField

namespace HilbertModularity.Cyclotomic

variable (p k q : ℕ) [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p)
  (P : Ideal (𝓞 Qbar)) [P.IsPrime] [P.LiesOver (Ideal.span {(q : ℤ)})]

include hq hqp in
/-- Absolute inertia away from the conductor fixes the actual cyclotomic field pointwise. -/
theorem absoluteInertia_le_cyclotomic_fixingSubgroup :
    Ideal.inertia (Qbar ≃ₐ[ℚ] Qbar) P ≤ (cyclotomicField (p ^ (k + 1))).fixingSubgroup := by
  let : IsGalois ℚ (cyclotomicField (p ^ (k + 1))) :=
    IsCyclotomicExtension.isGalois {p ^ (k + 1)} ℚ _
  let Q := P.under (𝓞 (cyclotomicField (p ^ (k + 1))))
  let : Q.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.tower_bot P Q _
  intro σ hσ
  have h := Ideal.restrictNormal_mem_inertia (L := cyclotomicField (p ^ (k + 1))) P σ hσ
  change σ.restrictNormal (cyclotomicField (p ^ (k + 1))) ∈
    Ideal.inertia (cyclotomicField (p ^ (k + 1)) ≃ₐ[ℚ] cyclotomicField (p ^ (k + 1))) Q at h
  rw [inertia_cyclotomic_primePower_eq_bot p k q hq hqp Q, Subgroup.mem_bot] at h
  exact (IntermediateField.mem_fixingSubgroup_iff (cyclotomicField (p ^ (k + 1))) σ).mpr
    ((AlgEquiv.restrictNormal_eq_one_iff (cyclotomicField (p ^ (k + 1))) σ).mp h)

include hq hqp in
/-- Restricting absolute inertia over the cyclotomic field gives exactly rational absolute inertia. -/
theorem map_absoluteInertia_cyclotomic :
    (Ideal.inertia (Qbar ≃ₐ[cyclotomicField (p ^ (k + 1))] Qbar) P).map
      (AlgEquiv.restrictScalarsHom ℚ) = Ideal.inertia (Qbar ≃ₐ[ℚ] Qbar) P := by
  rw [Ideal.map_inertia_restrictScalars]
  exact inf_eq_left.mpr (absoluteInertia_le_cyclotomic_fixingSubgroup p k q hq hqp P)

include hq hqp in
/-- Restricting absolute inertia over the real cyclotomic field also gives exactly rational inertia. -/
theorem map_absoluteInertia_realCyclotomic :
    (Ideal.inertia (Qbar ≃ₐ[realCyclotomicField (p ^ (k + 1))] Qbar) P).map
      (AlgEquiv.restrictScalarsHom ℚ) = Ideal.inertia (Qbar ≃ₐ[ℚ] Qbar) P := by
  rw [Ideal.map_inertia_restrictScalars]
  apply inf_eq_left.mpr
  intro σ hσ
  have h := absoluteInertia_le_cyclotomic_fixingSubgroup p k q hq hqp P hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
  intro x hx
  exact h x (realCyclotomicField_le (p ^ (k + 1)) hx)

include hq hqp in
/-- The full and real cyclotomic fields have the same absolute inertia subgroup inside a common
algebraic closure, with the canonical restriction homomorphism. -/
theorem map_absoluteInertia_cyclotomic_to_real :
    let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
      (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
    let : IsScalarTower (realCyclotomicField (p ^ (k + 1)))
        (cyclotomicField (p ^ (k + 1))) Qbar := IsScalarTower.of_algebraMap_eq fun _ => rfl
    (Ideal.inertia (Qbar ≃ₐ[cyclotomicField (p ^ (k + 1))] Qbar) P).map
      (AlgEquiv.restrictScalarsHom (realCyclotomicField (p ^ (k + 1)))) =
        Ideal.inertia (Qbar ≃ₐ[realCyclotomicField (p ^ (k + 1))] Qbar) P := by
  let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
    (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
  let : IsScalarTower (realCyclotomicField (p ^ (k + 1)))
      (cyclotomicField (p ^ (k + 1))) Qbar := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Subgroup.map_injective (AlgEquiv.restrictScalarsHom_injective ℚ)
  rw [Subgroup.map_map, map_absoluteInertia_realCyclotomic p k q hq hqp P]
  exact map_absoluteInertia_cyclotomic p k q hq hqp P

include hq hqp in
/-- Triviality of a representation on actual inertia can be checked after restriction from the
real coefficient field to the full cyclotomic field, away from the conductor. -/
theorem unramified_cyclotomic_restriction_iff
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (ρ : Representation R (Qbar ≃ₐ[realCyclotomicField (p ^ (k + 1))] Qbar) V) :
    let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
      (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
    let : IsScalarTower (realCyclotomicField (p ^ (k + 1)))
        (cyclotomicField (p ^ (k + 1))) Qbar := IsScalarTower.of_algebraMap_eq fun _ => rfl
    (∀ σ ∈ Ideal.inertia (Qbar ≃ₐ[realCyclotomicField (p ^ (k + 1))] Qbar) P, ρ σ = 1) ↔
      ∀ σ ∈ Ideal.inertia (Qbar ≃ₐ[cyclotomicField (p ^ (k + 1))] Qbar) P,
        ρ (σ.restrictScalars (realCyclotomicField (p ^ (k + 1)))) = 1 := by
  let : Algebra (realCyclotomicField (p ^ (k + 1))) (cyclotomicField (p ^ (k + 1))) :=
    (IntermediateField.inclusion (realCyclotomicField_le (p ^ (k + 1)))).toRingHom.toAlgebra
  let : IsScalarTower (realCyclotomicField (p ^ (k + 1)))
      (cyclotomicField (p ^ (k + 1))) Qbar := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have he := map_absoluteInertia_cyclotomic_to_real p k q hq hqp P
  constructor
  · intro h σ hσ
    apply h
    rw [← he]
    exact ⟨σ, hσ, rfl⟩
  · intro h σ hσ
    rw [← he] at hσ
    obtain ⟨τ, hτ, rfl⟩ := hσ
    exact h τ hτ

end HilbertModularity.Cyclotomic
