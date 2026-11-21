/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.RankTwoDuality

/-! # Determinants from rank-two alternating pairings

The multiplier of a nondegenerate alternating pairing on a two-dimensional
space is the determinant. This is the algebraic application of the polarized
Tate pairing used in [TripathiGoswami, Lemma RMtorsion].
-/

public noncomputable section

namespace HilbertModularity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every alternating form in dimension two is a scalar multiple of the
coordinate alternating form. -/
theorem alternatingForm_eq_rankTwo
    (b : Module.Basis (Fin 2) K V) (B : V →ₗ[K] Module.Dual K V)
    (halt : ∀ v, B v v = 0) (v w : V) :
    B v w = B (b 0) (b 1) * rankTwoAlternatingEquiv b v w := by
  have hv (u : V) : u = b.repr u 0 • b 0 + b.repr u 1 • b 1 := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp
  have hskew : B (b 1) (b 0) = -B (b 0) (b 1) := by
    have h := halt (b 0 + b 1)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  conv_lhs => rw [hv v, hv w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, halt, hskew, rankTwoAlternatingEquiv_apply]
  ring

/-- A nondegenerate alternating form has a nonzero coefficient in any
two-dimensional basis. -/
theorem alternatingForm_basis_ne_zero
    (b : Module.Basis (Fin 2) K V) (B : V →ₗ[K] Module.Dual K V)
    (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) : B (b 0) (b 1) ≠ 0 := by
  intro hz
  have h := hnd (b 0) (fun w => by
    rw [alternatingForm_eq_rankTwo b B halt, hz, zero_mul])
  exact b.ne_zero 0 h

/-- The similitude multiplier on a rank-two nondegenerate alternating space
is its determinant. The pairing is supplied independently of the conclusion. -/
theorem det_eq_of_alternating_similitude
    (b : Module.Basis (Fin 2) K V) (B : V →ₗ[K] Module.Dual K V)
    (halt : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (f : V →ₗ[K] V) (c : K)
    (hscale : ∀ v w, B (f v) (f w) = c * B v w) :
    (LinearMap.toMatrix b b f).det = c := by
  have h := hscale (b 0) (b 1)
  rw [alternatingForm_eq_rankTwo b B halt,
    rankTwoAlternatingEquiv_map] at h
  have hunit : rankTwoAlternatingEquiv b (b 0) (b 1) = 1 := by simp
  rw [hunit, mul_one, mul_comm c] at h
  exact mul_left_cancel₀ (alternatingForm_basis_ne_zero b B halt hnd) h

/-- Eliminate the existence of a pairing before specializing to a geometric
carrier, keeping the determinant application independent of its construction. -/
theorem det_eq_of_exists_alternating_similitude
    {G : Type*} (b : Module.Basis (Fin 2) K V)
    (ρ : G → V →ₗ[K] V) (χ : G → K)
    (h : ∃ B : V →ₗ[K] Module.Dual K V,
      (∀ v, B v v = 0) ∧ (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      ∀ g v w, B (ρ g v) (ρ g w) = χ g * B v w) (g : G) :
    (LinearMap.toMatrix b b (ρ g)).det = χ g := by
  obtain ⟨B, halt, hnd, hscale⟩ := h
  exact det_eq_of_alternating_similitude b B halt hnd (ρ g) (χ g) (hscale g)

/-- Basis-free determinant form of the rank-two pairing argument. -/
theorem linearMap_det_eq_of_exists_alternating_similitude
    {G : Type*} (hr : Module.finrank K V = 2)
    (ρ : G → V →ₗ[K] V) (χ : G → K)
    (h : ∃ B : V →ₗ[K] Module.Dual K V,
      (∀ v, B v v = 0) ∧ (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      ∀ g v w, B (ρ g v) (ρ g w) = χ g * B v w) (g : G) :
    LinearMap.det (ρ g) = χ g := by
  let : Module.Finite K V := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  let b := Module.finBasisOfFinrankEq K V hr
  simpa only [LinearMap.det_toMatrix] using
    det_eq_of_exists_alternating_similitude b ρ χ h g

end HilbertModularity
