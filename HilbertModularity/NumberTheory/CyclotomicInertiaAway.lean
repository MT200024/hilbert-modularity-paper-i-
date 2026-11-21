/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicInertia
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-! # Cyclotomic inertia away from a general conductor

The pinned mathlib ramification-index theorem applies to composite as well
as prime-power conductors. Its index-one conclusion gives trivial finite
Galois inertia, and hence the absolute inertia restriction needed for the
selected Euler family.
-/

public noncomputable section

open scoped NumberField

namespace HilbertModularity.Cyclotomic

/-- A rational prime not dividing the conductor has trivial inertia in
`Q(ζ_N)/Q`. This applies the index-one theorem in pinned mathlib
`Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal`. -/
theorem inertia_cyclotomic_eq_bot_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (P : Ideal (𝓞 (cyclotomicField N))) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    Ideal.inertia (cyclotomicField N ≃ₐ[ℚ] cyclotomicField N) P = ⊥ := by
  let : IsGalois ℚ (cyclotomicField N) :=
    IsCyclotomicExtension.isGalois {N} ℚ _
  let : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime ((Nat.cast_ne_zero.mpr hq.ne_zero) : (q : ℤ) ≠ 0)).mpr
      ((Int.prime_iff_natAbs_prime (k := (q : ℤ))).mpr hq)
  let : Fact q.Prime := ⟨hq⟩
  apply Subgroup.card_eq_one.mp
  rw [Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(q : ℤ)}) P]
  exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
    (m := N) q (cyclotomicField N) hqN

/-- Absolute rational inertia away from `N` fixes `Q(ζ_N)` pointwise,
also when `N` is composite. -/
theorem absoluteInertia_le_cyclotomic_fixingSubgroup_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (P : Ideal (𝓞 Qbar)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    Ideal.inertia (Qbar ≃ₐ[ℚ] Qbar) P ≤
      (cyclotomicField N).fixingSubgroup := by
  let : IsGalois ℚ (cyclotomicField N) :=
    IsCyclotomicExtension.isGalois {N} ℚ _
  let Q := P.under (𝓞 (cyclotomicField N))
  let : Q.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.tower_bot P Q _
  intro σ hσ
  have h := Ideal.restrictNormal_mem_inertia (L := cyclotomicField N) P σ hσ
  change σ.restrictNormal (cyclotomicField N) ∈
    Ideal.inertia (cyclotomicField N ≃ₐ[ℚ] cyclotomicField N) Q at h
  rw [inertia_cyclotomic_eq_bot_of_not_dvd N q hq hqN Q, Subgroup.mem_bot] at h
  exact (IntermediateField.mem_fixingSubgroup_iff (cyclotomicField N) σ).mpr
    ((AlgEquiv.restrictNormal_eq_one_iff (cyclotomicField N) σ).mp h)

/-- Cyclotomic absolute inertia maps onto rational absolute inertia away
from every prime divisor of the general conductor. -/
theorem map_absoluteInertia_cyclotomic_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (P : Ideal (𝓞 Qbar)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    (Ideal.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar) P).map
      (AlgEquiv.restrictScalarsHom ℚ) =
      Ideal.inertia (Qbar ≃ₐ[ℚ] Qbar) P := by
  rw [Ideal.map_inertia_restrictScalars]
  exact inf_eq_left.mpr
    (absoluteInertia_le_cyclotomic_fixingSubgroup_of_not_dvd N q hq hqN P)

/-- Real cyclotomic absolute inertia has the same rational image away
from the general conductor. -/
theorem map_absoluteInertia_realCyclotomic_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (P : Ideal (𝓞 Qbar)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    (Ideal.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar) P).map
      (AlgEquiv.restrictScalarsHom ℚ) =
      Ideal.inertia (Qbar ≃ₐ[ℚ] Qbar) P := by
  rw [Ideal.map_inertia_restrictScalars]
  apply inf_eq_left.mpr
  intro σ hσ
  have h := absoluteInertia_le_cyclotomic_fixingSubgroup_of_not_dvd
    N q hq hqN P hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at h ⊢
  intro x hx
  exact h x (realCyclotomicField_le N hx)

/-- Restriction of absolute inertia from the full to the real cyclotomic
field is onto at every rational prime not dividing `N`. -/
theorem map_absoluteInertia_cyclotomic_to_real_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (P : Ideal (𝓞 Qbar)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(q : ℤ)})] :
    letI : Algebra (realCyclotomicField N) (cyclotomicField N) :=
      (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra
    letI : IsScalarTower (realCyclotomicField N) (cyclotomicField N) Qbar :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    (Ideal.inertia (Qbar ≃ₐ[cyclotomicField N] Qbar) P).map
      (AlgEquiv.restrictScalarsHom (realCyclotomicField N)) =
      Ideal.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar) P := by
  let : Algebra (realCyclotomicField N) (cyclotomicField N) :=
    (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra
  let : IsScalarTower (realCyclotomicField N) (cyclotomicField N) Qbar :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Subgroup.map_injective (AlgEquiv.restrictScalarsHom_injective ℚ)
  rw [Subgroup.map_map, map_absoluteInertia_realCyclotomic_of_not_dvd N q hq hqN P]
  exact map_absoluteInertia_cyclotomic_of_not_dvd N q hq hqN P

end HilbertModularity.Cyclotomic
