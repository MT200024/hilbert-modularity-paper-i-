/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.Duality
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! # Rank-two alternating duality

A choice of basis identifies a rank-two space with its dual by the alternating
pairing. Determinant-one operators preserve this identification. This is the
linear-algebra step in [TripathiGoswami, proof of RMgeneral, Step 2].
-/

public noncomputable section

namespace HilbertModularity

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

/-- The alternating pairing in a rank-two basis identifies the space with its dual. -/
def rankTwoAlternatingEquiv (b : Module.Basis (Fin 2) K V) : V ≃ₗ[K] Module.Dual K V where
  toFun v := b.repr v 0 • b.coord 1 - b.repr v 1 • b.coord 0
  invFun f := f (b 1) • b 0 - f (b 0) • b 1
  map_add' v w := by simp [add_smul]; abel
  map_smul' a v := by simp [mul_smul, smul_sub]
  left_inv v := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [Module.Basis.coord_apply]
  right_inv f := by
    apply b.ext
    intro i
    fin_cases i <;> simp [Module.Basis.coord_apply]

@[simp] theorem rankTwoAlternatingEquiv_apply
    (b : Module.Basis (Fin 2) K V) (v w : V) :
    rankTwoAlternatingEquiv b v w = b.repr v 0 * b.repr w 1 - b.repr v 1 * b.repr w 0 := (rfl)

/-- Applying an operator to both arguments scales the alternating form by its determinant. -/
theorem rankTwoAlternatingEquiv_map
    (b : Module.Basis (Fin 2) K V) (f : V →ₗ[K] V) (v w : V) :
    rankTwoAlternatingEquiv b (f v) (f w) =
      (LinearMap.toMatrix b b f).det * rankTwoAlternatingEquiv b v w := by
  have hc (u : V) : b.repr (f u) =
      b.repr u 0 • b.repr (f (b 0)) + b.repr u 1 • b.repr (f (b 1)) := by
    have hu : u = b.repr u 0 • b 0 + b.repr u 1 • b 1 := by
      apply b.repr.injective
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hu]
    simp
  simp only [rankTwoAlternatingEquiv_apply, hc v, hc w, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Matrix.det_fin_two, LinearMap.toMatrix_apply]
  ring

/-- A determinant-one operator intertwines the alternating identification with
its contragredient. Only the selected group element needs determinant one. -/
theorem rankTwoAlternatingEquiv_intertwines
    (b : Module.Basis (Fin 2) K V) (ρ : Representation K G V) (g : G)
    (hg : (LinearMap.toMatrix b b (ρ g)).det = 1) (v : V) :
    rankTwoAlternatingEquiv b (ρ g v) = ρ.dual g (rankTwoAlternatingEquiv b v) := by
  ext w
  have h := rankTwoAlternatingEquiv_map b (ρ g) v (ρ g⁻¹ w)
  have hi : ρ g (ρ g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hg, one_mul, hi] at h
  exact h

/-- The dual operator has the original matrix in the alternating dual basis. -/
theorem toMatrix_dual_rankTwoAlternatingEquiv
    (b : Module.Basis (Fin 2) K V) (ρ : Representation K G V) (g : G)
    (hg : (LinearMap.toMatrix b b (ρ g)).det = 1) :
    LinearMap.toMatrix (b.map (rankTwoAlternatingEquiv b))
      (b.map (rankTwoAlternatingEquiv b)) (ρ.dual g) = LinearMap.toMatrix b b (ρ g) := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext v
  change (rankTwoAlternatingEquiv b).symm
    (ρ.dual g (rankTwoAlternatingEquiv b v)) = ρ g v
  rw [← rankTwoAlternatingEquiv_intertwines b ρ g hg, LinearEquiv.symm_apply_apply]

end HilbertModularity
