/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Quadratic Galois characters from square roots

A nonzero square root of a base-field element defines the actual character
`σ ↦ σ(u)/u`. Its image has order dividing two and is locally constant for
the Krull topology. This supplies a concrete finite-character construction
for the reflection comparison in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped Topology

namespace Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem quadraticRatio_sq (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) (σ : L ≃ₐ[K] L) :
    (σ u / u) ^ 2 = 1 := by
  rw [div_pow, ← map_pow, hsq, σ.commutes]
  exact div_self (by rw [← hsq]; exact pow_ne_zero _ hu)

private theorem quadraticRatio_fixed (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) (σ τ : L ≃ₐ[K] L) :
    σ (τ u / u) = τ u / u := by
  rcases sq_eq_one_iff.mp (quadraticRatio_sq a u hu hsq τ) with h | h <;>
    rw [h] <;> simp

/-- The genuine quadratic character attached to a nonzero square root. -/
def quadraticCharacter (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) : (L ≃ₐ[K] L) →* Lˣ where
  toFun σ := Units.mk0 (σ u / u) (div_ne_zero ((map_ne_zero σ).mpr hu) hu)
  map_one' := by apply Units.ext; simp [hu]
  map_mul' σ τ := by
    apply Units.ext
    change σ (τ u) / u = (σ u / u) * (τ u / u)
    calc
      _ = σ (τ u / u) * (σ u / u) := by
        rw [map_div₀]
        field_simp [hu, (map_ne_zero σ).mpr hu]
      _ = _ := by rw [quadraticRatio_fixed a u hu hsq σ τ, mul_comm]

@[simp]
theorem coe_quadraticCharacter (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) (σ : L ≃ₐ[K] L) :
    (quadraticCharacter a u hu hsq σ : L) = σ u / u := rfl

/-- Every value of the quadratic character has square one. -/
theorem quadraticCharacter_apply_sq (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) (σ : L ≃ₐ[K] L) :
    quadraticCharacter a u hu hsq σ ^ 2 = 1 := by
  apply Units.ext
  exact quadraticRatio_sq a u hu hsq σ

/-- The character itself has order dividing two in the character group. -/
theorem quadraticCharacter_sq (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) : quadraticCharacter a u hu hsq ^ 2 = 1 := by
  apply MonoidHom.ext
  intro σ
  exact quadraticCharacter_apply_sq a u hu hsq σ

/-- The image is contained in the two signs, hence is finite. -/
theorem quadraticCharacter_finite_range (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) : Set.Finite (Set.range (quadraticCharacter a u hu hsq)) := by
  apply ((Set.finite_singleton (-1 : Lˣ)).insert 1).subset
  rintro v ⟨σ, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases sq_eq_one_iff.mp (quadraticRatio_sq a u hu hsq σ) with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

/-- Changing the chosen square root does not change the character. -/
theorem quadraticCharacter_root_independent (a : K) (u v : L)
    (hu : u ≠ 0) (hv : v ≠ 0) (hsu : u ^ 2 = algebraMap K L a)
    (hsv : v ^ 2 = algebraMap K L a) :
    quadraticCharacter a u hu hsu = quadraticCharacter a v hv hsv := by
  ext σ
  simp only [coe_quadraticCharacter]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsu.trans hsv.symm) with h | h
  · rw [h]
  · rw [h, map_neg, neg_div_neg_eq]

/-- A square root already in the base field gives the trivial character. -/
theorem quadraticCharacter_eq_one_of_root (a : K) (u : L) (hu : u ≠ 0)
    (hsq : u ^ 2 = algebraMap K L a) (b : K) (hb : algebraMap K L b = u) :
    quadraticCharacter a u hu hsq = 1 := by
  ext σ
  change σ u / u = 1
  rw [← hb, σ.commutes]
  exact div_self (by simpa only [hb] using hu)

/-- Algebraic Galois automorphisms give locally constant quadratic characters
for the actual Krull topology. -/
theorem quadraticCharacter_isLocallyConstant [Algebra.IsIntegral K L]
    (a : K) (u : L) (hu : u ≠ 0) (hsq : u ^ 2 = algebraMap K L a) :
    IsLocallyConstant (quadraticCharacter a u hu hsq) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro σ
  have ho := (stabilizer_isOpen_of_isIntegral (K := K) u).preimage
    (continuous_const.mul continuous_id : Continuous fun τ => σ⁻¹ * τ)
  have hn := ho.mem_nhds (show σ⁻¹ * σ ∈
    MulAction.stabilizer (L ≃ₐ[K] L) u by simp)
  filter_upwards [hn] with τ hτ
  change (σ⁻¹ * τ) u = u at hτ
  have heq : τ u = σ u := by simpa using congrArg σ hτ
  apply Units.ext
  change τ u / u = σ u / u
  rw [heq]

end Galois
