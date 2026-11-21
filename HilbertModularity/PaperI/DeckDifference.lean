module
public import HilbertModularity.RepresentationTheory.CharacterTwist
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Two reflection eigenspaces on the same labelled cover -/
@[expose] public noncomputable section
namespace HilbertModularity.PaperI
variable {L G H : Type*} [Field L] [Group G] [AddCommGroup H] [Module L H]

structure DihedralAction (L H : Type*) [Field L] [AddCommGroup H] [Module L H] where
  delta : H ≃ₗ[L] H
  reflection : H ≃ₗ[L] H
  involution : ∀ v, reflection (reflection v) = v
  conjugate : ∀ v, reflection (delta v) = delta.symm (reflection v)

namespace Deck
variable (d : DihedralAction L H)
def difference := d.delta.toLinearMap - d.delta.symm.toLinearMap
def realOperator := d.delta.toLinearMap + d.delta.symm.toLinearMap
theorem difference_apply (v : H) : difference d v = d.delta v - d.delta.symm v := rfl

theorem reflection_difference (v : H) : d.reflection (difference d v) = - difference d (d.reflection v) := by
  have hi : d.reflection (d.delta.symm v) = d.delta (d.reflection v) := by
    have h := congrArg d.delta (d.conjugate (d.delta.symm v))
    simpa using h.symm
  rw [difference_apply, difference_apply, map_sub, d.conjugate, hi, neg_sub]

theorem difference_square (τ : L) (label : ∀ v, realOperator d v = τ • v) (v : H) :
    difference d (difference d v) = (τ^2-4) • v := by
  have eq : realOperator d (realOperator d v) = τ^2 • v := by rw [label, label, smul_smul, pow_two]
  have h : difference d (difference d v) = realOperator d (realOperator d v) - (v+v+v+v) := by
    simp only [difference_apply, realOperator, LinearMap.add_apply, LinearEquiv.coe_coe, map_sub,
      map_add, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    abel
  rw [h, eq, sub_smul]
  congr 1
  module

def space (s : L) := Module.End.eigenspace d.reflection.toLinearMap s
theorem mem_space (s : L) (v : H) : v ∈ space d s ↔ d.reflection v = s • v := Module.End.mem_eigenspace_iff
theorem difference_mem (s : L) (v : space d s) : difference d v ∈ space d (-s) := by
  rw [mem_space, reflection_difference, (mem_space d s v).mp v.property, map_smul, neg_smul]

def exchange (τ : L) (label : ∀ v, realOperator d v = τ • v) (ht : τ^2-4 ≠ 0) :
    space d (-1) ≃ₗ[L] space d 1 where
  toFun v := ⟨difference d v, by simpa using difference_mem d (-1) v⟩
  invFun w := ⟨(τ^2-4)⁻¹ • difference d w, (space d (-1)).smul_mem _ (difference_mem d 1 w)⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' a v := Subtype.ext (map_smul _ _ _)
  left_inv v := by
    apply Subtype.ext
    change (τ^2-4)⁻¹ • difference d (difference d v) = _
    rw [difference_square d τ label, smul_smul, inv_mul_cancel₀ ht, one_smul]
  right_inv w := by
    apply Subtype.ext
    change difference d ((τ^2-4)⁻¹ • difference d w) = _
    rw [map_smul, difference_square d τ label, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem trace_discriminant (a : L) (ha : a ≠ 0) : (a+a⁻¹)^2-4 = (a-a⁻¹)^2 := by field_simp [ha]; ring
end Deck

variable {E P C : Type*} [AddCommGroup E] [Module L E] [AddCommGroup P] [Module L P]
  [AddCommGroup C] [Module L C]

/-- Pullback data on a common cohomology space with the specified deck label. -/
structure QuotientPullbacks (ρE : Representation L G E) (ρC : Representation L G C)
    (ρP : Representation L G P) (χ : G →* Lˣ) (a : L) (H : Type*)
    [AddCommGroup H] [Module L H] where
  deck : DihedralAction L H
  galois : Representation L G H
  label : ∀ v, Deck.realOperator deck v = (a+a⁻¹) • v
  euler : E ≃ₗ[L] Deck.space deck (-1)
  complement : C ≃ₗ[L] Deck.space deck (-1)
  plus : P ≃ₗ[L] Deck.space deck 1
  euler_natural : ∀ g v, (euler (ρE g v) : H) = galois g (euler v)
  complement_natural : ∀ g v, (complement (ρC g v) : H) = galois g (complement v)
  plus_natural : ∀ g v, (plus (ρP g v) : H) = galois g (plus v)
  rotation_galois : ∀ g,
    (χ g = 1 ∧ ∀ v, deck.delta (galois g v) = galois g (deck.delta v)) ∨
    (χ g = -1 ∧ ∀ v, deck.delta (galois g v) = galois g (deck.delta.symm v))

namespace QuotientPullbacks
variable {ρE : Representation L G E} {ρC : Representation L G C} {ρP : Representation L G P}
  {χ : G →* Lˣ} {a : L} (D : QuotientPullbacks ρE ρC ρP χ a H)

theorem difference_galois (g : G) (v : H) :
    Deck.difference D.deck (D.galois g v) = (χ g : L) • D.galois g (Deck.difference D.deck v) := by
  rcases D.rotation_galois g with ⟨h,hc⟩ | ⟨h,hr⟩
  · have hi : D.deck.delta.symm (D.galois g v) = D.galois g (D.deck.delta.symm v) := by
      apply D.deck.delta.injective
      simp only [LinearEquiv.apply_symm_apply, hc]
    simp only [Deck.difference_apply, hc, hi, map_sub, h, Units.val_one, one_smul]
  · have hi : D.deck.delta.symm (D.galois g v) = D.galois g (D.deck.delta v) := by
      apply D.deck.delta.injective
      simp only [LinearEquiv.apply_symm_apply, hr, LinearEquiv.symm_apply_apply]
    simp [Deck.difference_apply, hr, hi, h, map_sub]

def eulerComplement : ρE.Equiv ρC := by
  apply Representation.Equiv.mk (D.euler.trans D.complement.symm)
  intro g
  ext v
  apply D.complement.injective
  apply Subtype.ext
  change (D.complement (D.complement.symm (D.euler (ρE g v))) : H) =
    (D.complement (ρC g (D.complement.symm (D.euler v))) : H)
  rw [D.complement.apply_symm_apply, D.euler_natural, D.complement_natural, D.complement.apply_symm_apply]

def complementTwist (ha : a ≠ 0) (hne : a ≠ a⁻¹) : ρC.Equiv (ρP.characterTwist χ) := by
  have ht : (a+a⁻¹)^2-4 ≠ 0 := by rw [Deck.trace_discriminant a ha]; exact pow_ne_zero _ (sub_ne_zero.mpr hne)
  let T := Deck.exchange D.deck (a+a⁻¹) D.label ht
  apply Representation.Equiv.mk ((D.complement.trans T).trans D.plus.symm)
  intro g
  ext v
  apply D.plus.injective
  apply Subtype.ext
  change (D.plus (D.plus.symm (T (D.complement (ρC g v)))) : H) =
    (D.plus ((χ g : L) • ρP g (D.plus.symm (T (D.complement v)))) : H)
  rw [D.plus.apply_symm_apply, map_smul]
  change Deck.difference D.deck (D.complement (ρC g v)) =
    (χ g : L) • (D.plus (ρP g (D.plus.symm (T (D.complement v)))) : H)
  rw [D.complement_natural, D.plus_natural, D.plus.apply_symm_apply]
  exact D.difference_galois g (D.complement v)

end QuotientPullbacks
end HilbertModularity.PaperI
