/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # Projectors for finite characters

The weighted average of a finite abelian group action projects to a chosen
one-dimensional character when the group order is invertible in the
coefficient field. This is used for the fixed deck character of the Euler
cover in [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

namespace Representation

variable {L G V : Type*} [Field L] [CommGroup G] [Fintype G]
  [AddCommGroup V] [Module L V]

/-- The normalized character-weighted average of a finite abelian group action. -/
def characterProjector (χ : G →* Lˣ) (ρ : Representation L G V) : V →ₗ[L] V :=
  ((Fintype.card G : L)⁻¹) •
    ∑ g : G, ((χ g : L)⁻¹) • ρ g

/-- Every vector in the projector image transforms by the chosen character. -/
theorem characterProjector_eigen (χ : G →* Lˣ) (ρ : Representation L G V)
    (h : G) (v : V) :
    ρ h (characterProjector χ ρ v) =
      (χ h : L) • characterProjector χ ρ v := by
  classical
  have hρ (g : G) : ρ h (ρ g v) = ρ (h * g) v := by
    calc
      ρ h (ρ g v) = (ρ h * ρ g) v := rfl
      _ = ρ (h * g) v := by rw [map_mul]
  have hc (g : G) : (χ g : L)⁻¹ = (χ h : L) * (χ (h * g) : L)⁻¹ := by
    simp [map_mul, mul_inv_rev, mul_comm]
  have hs : (∑ g : G, ((χ g : L)⁻¹) • ρ (h * g) v) =
      (χ h : L) • ∑ g : G, ((χ g : L)⁻¹) • ρ g v := by
    rw [Finset.smul_sum]
    apply Fintype.sum_equiv (Equiv.mulLeft h)
    intro g
    change ((χ g : L)⁻¹) • ρ (h * g) v =
      (χ h : L) • ((χ (h * g) : L)⁻¹) • ρ (h * g) v
    rw [smul_smul, ← hc g]
  simp only [characterProjector, LinearMap.smul_apply, LinearMap.sum_apply]
  change ρ h (((Fintype.card G : L)⁻¹) •
    ∑ g : G, ((χ g : L)⁻¹) • ρ g v) =
      (χ h : L) • (((Fintype.card G : L)⁻¹) •
        ∑ g : G, ((χ g : L)⁻¹) • ρ g v)
  rw [map_smul, map_sum]
  simp_rw [map_smul, hρ]
  rw [hs]
  simp only [smul_smul]
  simp [mul_comm]

/-- A vector already transforming by the character is fixed by the average. -/
theorem characterProjector_eq_self_of_eigen (χ : G →* Lˣ) (ρ : Representation L G V)
    (hcard : (Fintype.card G : L) ≠ 0) (v : V)
    (hv : ∀ g : G, ρ g v = (χ g : L) • v) :
    characterProjector χ ρ v = v := by
  classical
  simp only [characterProjector, LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [hv, smul_smul]
  simp only [inv_mul_cancel₀ (Units.ne_zero _), one_smul, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul L]
  simp [smul_smul, hcard]

/-- The normalized character average is an idempotent endomorphism. -/
theorem characterProjector_idempotent (χ : G →* Lˣ) (ρ : Representation L G V)
    (hcard : (Fintype.card G : L) ≠ 0) :
    (characterProjector χ ρ).comp (characterProjector χ ρ) =
      characterProjector χ ρ := by
  ext v
  exact characterProjector_eq_self_of_eigen χ ρ hcard _
    (fun g => characterProjector_eigen χ ρ g v)

/-- A linear operator commuting with a finite group action preserves every
character projector. -/
theorem characterProjector_comm (χ : G →* Lˣ) (ρ : Representation L G V)
    (f : V →ₗ[L] V) (hf : ∀ g : G, (ρ g).comp f = f.comp (ρ g)) :
    (characterProjector χ ρ).comp f = f.comp (characterProjector χ ρ) := by
  classical
  apply LinearMap.ext
  intro v
  simp only [characterProjector, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact congrArg (fun h : V →ₗ[L] V => h v) (hf g)

end Representation
