/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.Parameters
public import HilbertModularity.NumberTheory.CyclotomicEmbeddings

/-! # The coefficient field of symmetric hypergeometric parameters

The stabilizer calculation of [TripathiGoswami, §1.3] identifies the fixed
field of the parameter datum with the real cyclotomic field.
-/

@[expose] public section

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic

/-- A cyclotomic automorphism preserves the symmetric parameter multisets if
and only if it is the identity or algebraic conjugation. -/
theorem automorphism_preserves_symmetricDatum_iff {N m : ℕ} [NeZero N]
    (hm : m.Coprime N) (σ : cyclotomicField N ≃ₐ[ℚ] cyclotomicField N) :
    ((symmetricDatum N m).1.map (fun a =>
        (((root_isPrimitiveRoot N).autToPow ℚ σ : ZMod N).val : ℤ) • a) =
          (symmetricDatum N m).1 ∧
      (symmetricDatum N m).2.map (fun a =>
        (((root_isPrimitiveRoot N).autToPow ℚ σ : ZMod N).val : ℤ) • a) =
          (symmetricDatum N m).2) ↔ σ = 1 ∨ σ = conjugation N := by
  rw [symmetricDatum_stabilizer_iff hm, autToPow_eq_sign_iff]

/-- [TripathiGoswami], §1.3: the fixed field of the stabilizer of both
parameter multisets is exactly the real cyclotomic field. -/
theorem fixed_by_parameter_stabilizer_iff {N m : ℕ} [NeZero N]
    (hm : m.Coprime N) (x : cyclotomicField N) :
    (∀ σ : cyclotomicField N ≃ₐ[ℚ] cyclotomicField N,
      ((symmetricDatum N m).1.map (fun a =>
          (((root_isPrimitiveRoot N).autToPow ℚ σ : ZMod N).val : ℤ) • a) =
            (symmetricDatum N m).1 ∧
        (symmetricDatum N m).2.map (fun a =>
          (((root_isPrimitiveRoot N).autToPow ℚ σ : ZMod N).val : ℤ) • a) =
            (symmetricDatum N m).2) → σ x = x) ↔
      (x : Qbar) ∈ realCyclotomicField N := by
  simp only [automorphism_preserves_symmetricDatum_iff hm]
  constructor
  · intro h
    exact (conjugation_eq_self_iff N x).mp (h (conjugation N) (Or.inr rfl))
  · intro hx σ hσ
    rcases hσ with rfl | rfl
    · rfl
    · exact (conjugation_eq_self_iff N x).mpr hx

end HilbertModularity.Hypergeometric
