/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Reduction
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-! # Isogeny invariance of rational Tate modules

A surjective additive point map with kernel killed by a nonzero integer has a
multiplication quasi-inverse. Its actual rational Tate map is therefore an
isomorphism. This is the isogeny invariance used in [TripathiGoswami]; no
existence of a geometric isogeny is asserted here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Descend multiplication through a surjective point map whose kernel it kills. -/
def isogenyInverse (f : A →+ B) (hf : Function.Surjective f) (m : ℕ)
    (hk : ∀ x, f x = 0 → m • x = 0) : B →+ A :=
  f.liftOfSurjective hf ⟨m • AddMonoidHom.id A, hk⟩

/-- The point-level quasi-inverse composed with the original map is multiplication. -/
@[simp]
theorem isogenyInverse_apply (f : A →+ B) (hf : Function.Surjective f) (m : ℕ)
    (hk : ∀ x, f x = 0 → m • x = 0) (x : A) :
    isogenyInverse f hf m hk (f x) = m • x := by
  simp [isogenyInverse]

/-- The other composite is also multiplication on the point group. -/
@[simp]
theorem apply_isogenyInverse (f : A →+ B) (hf : Function.Surjective f) (m : ℕ)
    (hk : ∀ x, f x = 0 → m • x = 0) (y : B) :
    f (isogenyInverse f hf m hk y) = m • y := by
  obtain ⟨x, rfl⟩ := hf y
  rw [isogenyInverse_apply, map_nsmul]

variable (p : ℕ) [Fact p.Prime]

/-- A bounded kernel contributes no nonzero compatible Tate family. -/
theorem map_injective_of_bounded_kernel (f : A →+ B) (m : ℕ) (hm : m ≠ 0)
    (hk : ∀ x, f x = 0 → m • x = 0) : Function.Injective (map p f) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hx : map p f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hmx : (m : ℤ_[p]) • (x - y) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    apply Subtype.ext
    funext n
    apply Subtype.ext
    apply hk
    exact congrArg (fun y : integral p B => (projection p B n y : B)) hx
  exact (smul_eq_zero.mp hmx).resolve_left (Nat.cast_ne_zero.mpr hm)

/-- A point-level multiplication composite induces the same composite on actual Tate modules. -/
theorem map_comp_eq_nsmul (f : A →+ B) (g : B →+ A) (m : ℕ)
    (h : ∀ x, g (f x) = m • x) (x : integral p A) :
    map p g (map p f x) = m • x := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact h (projection p A n x)

/-- The multiplication composite persists after rationalization of the actual Tate map. -/
theorem rationalMap_comp_eq_nsmul (f : A →+ B) (g : B →+ A) (m : ℕ)
    (h : ∀ x, g (f x) = m • x) (x : rational p A) :
    rationalMap p g (rationalMap p f x) = m • x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add, nsmul_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
    rw [rationalMap_tmul, rationalMap_tmul, map_comp_eq_nsmul p f g m h]
    exact map_nsmul (TensorProduct.mk ℤ_[p] ℚ_[p] (integral p A) a) m x

/-- A point isogeny induces an isomorphism of the actual rational Tate modules. -/
def rationalIsogenyEquiv (f : A →+ B) (hf : Function.Surjective f) (m : ℕ) (hm : m ≠ 0)
    (hk : ∀ x, f x = 0 → m • x = 0) : rational p A ≃ₗ[ℚ_[p]] rational p B :=
  { rationalMap p f with
    invFun := fun y => (m : ℚ_[p])⁻¹ • rationalMap p (isogenyInverse f hf m hk) y
    left_inv := by
      intro x
      change (m : ℚ_[p])⁻¹ • rationalMap p (isogenyInverse f hf m hk) (rationalMap p f x) = x
      rw [rationalMap_comp_eq_nsmul p f (isogenyInverse f hf m hk) m
        (isogenyInverse_apply f hf m hk)]
      rw [← Nat.cast_smul_eq_nsmul ℚ_[p], inv_smul_smul₀ (Nat.cast_ne_zero.mpr hm)]
    right_inv := by
      intro y
      change rationalMap p f ((m : ℚ_[p])⁻¹ • rationalMap p (isogenyInverse f hf m hk) y) = y
      rw [map_smul, rationalMap_comp_eq_nsmul p (isogenyInverse f hf m hk) f m
        (apply_isogenyInverse f hf m hk)]
      rw [← Nat.cast_smul_eq_nsmul ℚ_[p], inv_smul_smul₀ (Nat.cast_ne_zero.mpr hm)] }

/-- A finite point kernel gives an injective map on actual integral Tate modules. -/
theorem map_injective_of_finite_kernel (f : A →+ B) [Finite f.ker] :
    Function.Injective (map p f) :=
  map_injective_of_bounded_kernel p f (Nat.card f.ker) (Nat.ne_of_gt Nat.card_pos) (by
    intro x hx
    exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : f.ker))))

/-- Surjective point maps with finite kernel preserve the actual rational Tate module. -/
def rationalFiniteKernelEquiv (f : A →+ B) [Finite f.ker] (hf : Function.Surjective f) :
    rational p A ≃ₗ[ℚ_[p]] rational p B :=
  rationalIsogenyEquiv p f hf (Nat.card f.ker) (Nat.ne_of_gt Nat.card_pos) (by
    intro x hx
    exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : f.ker))))

end TateModule
