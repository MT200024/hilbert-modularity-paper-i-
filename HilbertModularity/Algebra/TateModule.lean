/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Covariant Tate modules

The integral Tate module is the inverse limit of the `pⁿ`-torsion groups, with
transition maps multiplication by `p`. Its scalar action uses the compatible
reductions of a `p`-adic integer. This is the algebraic construction underlying
the covariant realization in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- The finite-level `pⁿ`-torsion group. -/
abbrev Torsion (n : ℕ) := AddSubgroup.torsionBy A (p ^ n : ℕ)

instance torsionZModModule (n : ℕ) : Module (ZMod (p ^ n)) (Torsion p A n) :=
  AddSubgroup.torsionBy.zmodModule

instance torsionPadicModule (n : ℕ) : Module ℤ_[p] (Torsion p A n) :=
  Module.compHom (Torsion p A n) (PadicInt.toZModPow n)

/-- Multiplication by `p` lowers the torsion level by one. -/
def transitionAddHom (n : ℕ) : Torsion p A (n + 1) →+ Torsion p A n where
  toFun x := ⟨p • (x : A), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← mul_nsmul, ← pow_succ']
    exact AddSubgroup.torsionBy.nsmul_iff.mp x.property⟩
  map_zero' := Subtype.ext (nsmul_zero p)
  map_add' x y := Subtype.ext (nsmul_add _ _ _)

/-- The torsion transition respects the compatible `p`-adic scalar actions. -/
def transition (n : ℕ) : Torsion p A (n + 1) →ₗ[ℤ_[p]] Torsion p A n where
  __ := transitionAddHom p A n
  map_smul' r x := by
    change transitionAddHom p A n (r.toZModPow (n + 1) • x) =
      r.toZModPow n • transitionAddHom p A n x
    have h : ((r.toZModPow (n + 1)).val : ZMod (p ^ n)) = r.toZModPow n := by
      rw [← ZMod.cast_eq_val]
      exact PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) r
    rw [← h, ← ZMod.natCast_zmod_val (r.toZModPow (n + 1))]
    simp only [Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- Compatible torsion families, as a submodule of the product of the finite levels. -/
def integral : Submodule ℤ_[p] (∀ n, Torsion p A n) where
  carrier := {x | ∀ n, transition p A n (x (n + 1)) = x n}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy n
    simp only [Pi.add_apply, map_add, hx n, hy n]
  smul_mem' := by
    intro r x hx n
    simp only [Pi.smul_apply, map_smul, hx n]

/-- Evaluation at a finite torsion level. -/
def projection (n : ℕ) : integral p A →ₗ[ℤ_[p]] Torsion p A n :=
  (LinearMap.proj n).comp (integral p A).subtype

/-- The finite-level coordinates of a Tate vector satisfy the transition equation. -/
theorem transition_projection (n : ℕ) (x : integral p A) :
    transition p A n (projection p A (n + 1) x) = projection p A n x :=
  x.property n

/-- The rational Tate module, obtained by extending scalars to `ℚ_p`. -/
abbrev rational := ℚ_[p] ⊗[ℤ_[p]] integral p A

variable {A} {B C : Type*} [AddCommGroup B] [AddCommGroup C]

/-- An additive map carries torsion points covariantly to torsion points. -/
def torsionMapAddHom (f : A →+ B) (n : ℕ) : Torsion p A n →+ Torsion p B n where
  toFun x := ⟨f x, by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.mp x.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f _ _)

/-- The finite-level covariant map is linear for the `p`-adic scalar action. -/
def torsionMap (f : A →+ B) (n : ℕ) : Torsion p A n →ₗ[ℤ_[p]] Torsion p B n where
  __ := torsionMapAddHom p f n
  map_smul' r x := by
    change torsionMapAddHom p f n (r.toZModPow n • x) =
      r.toZModPow n • torsionMapAddHom p f n x
    exact ZMod.map_smul (torsionMapAddHom p f n) _ _

/-- Covariance commutes with multiplication by `p` between torsion levels. -/
theorem torsionMap_transition (f : A →+ B) (n : ℕ) (x : Torsion p A (n + 1)) :
    torsionMap p f n (transition p A n x) =
      transition p B n (torsionMap p f (n + 1) x) :=
  Subtype.ext (map_nsmul f _ _)

/-- The map on integral Tate modules induced by an additive map. -/
def map (f : A →+ B) : integral p A →ₗ[ℤ_[p]] integral p B where
  toFun x := ⟨fun n => torsionMap p f n (x.val n), by
    intro n
    rw [← torsionMap_transition, x.property n]⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (torsionMap p f n) _ _
  map_smul' r x := by
    apply Subtype.ext
    funext n
    exact map_smul (torsionMap p f n) _ _

/-- Covariance is the usual pointwise map on every torsion coordinate. -/
@[simp]
theorem projection_map (f : A →+ B) (n : ℕ) (x : integral p A) :
    projection p B n (map p f x) = torsionMap p f n (projection p A n x) := rfl

@[simp]
theorem map_id : map p (AddMonoidHom.id A) = LinearMap.id := by
  ext x n
  rfl

/-- The integral Tate construction is covariantly functorial. -/
@[simp]
theorem map_comp (f : A →+ B) (g : B →+ C) :
    map p (g.comp f) = (map p g).comp (map p f) := by
  ext x n
  rfl

/-- The induced map on rational Tate modules. -/
def rationalMap (f : A →+ B) : rational p A →ₗ[ℚ_[p]] rational p B :=
  (map p f).baseChange ℚ_[p]

/-- Rational covariance acts on the torsion factor of pure tensors. -/
@[simp]
theorem rationalMap_tmul (f : A →+ B) (c : ℚ_[p]) (x : integral p A) :
    rationalMap p f (c ⊗ₜ x) = c ⊗ₜ map p f x := rfl

end TateModule
