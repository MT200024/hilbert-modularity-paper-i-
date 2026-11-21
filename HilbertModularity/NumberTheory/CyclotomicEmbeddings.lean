/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic
public import Mathlib.NumberTheory.Cyclotomic.Gal

@[expose] public section

/-! # Coefficient embeddings labelled by powers of the cyclotomic root -/

namespace IsPrimitiveRoot

/-- An automorphism inverting a primitive root has cyclotomic exponent minus one. -/
theorem autToPow_eq_neg_one_of_apply_eq_inv {K E : Type*} [Field K] [Field E]
    [Algebra K E] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (g : E ≃ₐ[K] E) (hg : g ζ = ζ⁻¹) : hζ.autToPow K g = -1 := by
  have hpow : ζ ^ ((hζ.autToPow K g : ZMod N).val + 1) = 1 := by
    rw [pow_succ, hζ.autToPow_spec K, hg, inv_mul_cancel₀ (hζ.ne_zero (NeZero.ne N))]
  have hz := (ZMod.natCast_eq_zero_iff _ N).mpr (hζ.dvd_of_pow_eq_one _ hpow)
  apply Units.ext
  change (hζ.autToPow K g : ZMod N) = -1
  apply eq_neg_of_add_eq_zero_left
  simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using hz

end IsPrimitiveRoot

namespace HilbertModularity.Cyclotomic

noncomputable section

/-- The cyclotomic automorphism specified by a coprime power of the chosen root. -/
def powerAutomorphism (N m : ℕ) [NeZero N] (hm : m.Coprime N) :
    cyclotomicField N ≃ₐ[ℚ] cyclotomicField N :=
  rootEquiv N ((root N) ^ m) ((root_isPrimitiveRoot N).pow_of_coprime m hm)

@[simp] theorem powerAutomorphism_root (N m : ℕ) [NeZero N] (hm : m.Coprime N) :
    powerAutomorphism N m hm (root N) = (root N) ^ m := rootEquiv_root _ _ _

/-- Power automorphisms commute with conjugation and therefore preserve its fixed field. -/
theorem conjugation_powerAutomorphism (N m : ℕ) [NeZero N] (hm : m.Coprime N)
    (x : cyclotomicField N) :
    conjugation N (powerAutomorphism N m hm x) =
      powerAutomorphism N m hm (conjugation N x) := by
  have h : (conjugation N).toAlgHom.comp (powerAutomorphism N m hm).toAlgHom =
      (powerAutomorphism N m hm).toAlgHom.comp (conjugation N).toAlgHom := by
    apply ((root_isPrimitiveRoot N).powerBasis ℚ).algHom_ext
    change conjugation N (powerAutomorphism N m hm (root N)) =
      powerAutomorphism N m hm (conjugation N (root N))
    rw [powerAutomorphism_root, map_pow, conjugation_root, map_inv₀,
      powerAutomorphism_root, inv_pow]
  exact AlgHom.congr_fun h x

/-- The labelled embedding of the real cyclotomic field into itself. -/
def powerEmbedding (N m : ℕ) [NeZero N] (hm : m.Coprime N) :
    realCyclotomicField N →ₐ[ℚ] realCyclotomicField N :=
  AlgHom.codRestrict
    (((cyclotomicField N).val.comp (powerAutomorphism N m hm).toAlgHom).comp
      (IntermediateField.inclusion (realCyclotomicField_le N)))
    (realCyclotomicField N).toSubalgebra (fun x => by
      apply (conjugation_eq_self_iff N _).mp
      change conjugation N (powerAutomorphism N m hm
        (IntermediateField.inclusion (realCyclotomicField_le N) x)) =
        powerAutomorphism N m hm (IntermediateField.inclusion (realCyclotomicField_le N) x)
      rw [conjugation_powerAutomorphism, conjugation_inclusion])

/-- The labelled embedding sends the first trace parameter to the prescribed power trace. -/
@[simp] theorem powerEmbedding_tau_one (N m : ℕ) [NeZero N] (hm : m.Coprime N) :
    powerEmbedding N m hm (tau N 1) = tau N m := by
  apply Subtype.ext
  have ht : IntermediateField.inclusion (realCyclotomicField_le N) (tau N 1) =
      root N + (root N)⁻¹ := by
    apply Subtype.ext
    simp [tau, root]
  change ((powerAutomorphism N m hm
    (IntermediateField.inclusion (realCyclotomicField_le N) (tau N 1)) :
      cyclotomicField N) : Qbar) = _
  rw [ht, map_add, map_inv₀, powerAutomorphism_root, ← inv_pow]
  rfl

/-- The labelled real-cyclotomic embedding is an automorphism. -/
def realPowerAutomorphism (N m : ℕ) [NeZero N] (hm : m.Coprime N) :
    realCyclotomicField N ≃ₐ[ℚ] realCyclotomicField N :=
  AlgEquiv.ofBijective (powerEmbedding N m hm)
    ⟨(powerEmbedding N m hm).injective,
      LinearMap.surjective_of_injective (f := (powerEmbedding N m hm).toLinearMap)
        (powerEmbedding N m hm).injective⟩

@[simp] theorem realPowerAutomorphism_tau_one (N m : ℕ) [NeZero N] (hm : m.Coprime N) :
    realPowerAutomorphism N m hm (tau N 1) = tau N m :=
  powerEmbedding_tau_one N m hm

/-- The coefficient embedding into a fixed field containing the real cyclotomic field.
In particular this applies to the manuscript's number field containing its Galois closure. -/
def coefficientEmbedding (N m : ℕ) [NeZero N] (hm : m.Coprime N)
    (E : IntermediateField ℚ Qbar) (hE : realCyclotomicField N ≤ E) :
    realCyclotomicField N →ₐ[ℚ] E :=
  (IntermediateField.inclusion hE).comp (powerEmbedding N m hm)

@[simp] theorem coefficientEmbedding_tau_one (N m : ℕ) [NeZero N] (hm : m.Coprime N)
    (E : IntermediateField ℚ Qbar) (hE : realCyclotomicField N ≤ E) :
    coefficientEmbedding N m hm E hE (tau N 1) = IntermediateField.inclusion hE (tau N m) := by
  simp [coefficientEmbedding]

/-- Algebraic conjugation corresponds to minus one under the cyclotomic
Galois character. -/
theorem autToPow_conjugation (N : ℕ) [NeZero N] :
    (root_isPrimitiveRoot N).autToPow ℚ (conjugation N) = -1 :=
  (root_isPrimitiveRoot N).autToPow_eq_neg_one_of_apply_eq_inv _ (conjugation_root N)

/-- The two sign exponents correspond exactly to identity and conjugation. -/
theorem autToPow_eq_sign_iff (N : ℕ) [NeZero N]
    (σ : cyclotomicField N ≃ₐ[ℚ] cyclotomicField N) :
    ((root_isPrimitiveRoot N).autToPow ℚ σ = 1 ∨
      (root_isPrimitiveRoot N).autToPow ℚ σ = -1) ↔
      σ = 1 ∨ σ = conjugation N := by
  rw [← autToPow_conjugation N, ← map_one ((root_isPrimitiveRoot N).autToPow ℚ)]
  exact or_congr ((root_isPrimitiveRoot N).autToPow_injective ℚ).eq_iff
    ((root_isPrimitiveRoot N).autToPow_injective ℚ).eq_iff

end

end HilbertModularity.Cyclotomic
