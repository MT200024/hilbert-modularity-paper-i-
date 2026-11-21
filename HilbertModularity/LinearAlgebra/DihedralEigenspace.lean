/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.LinearCombination

/-! # Dihedral eigenspaces

The real operator on a reflection quotient is `δ + δ⁻¹`, even though `δ` itself
does not generally descend. The algebra below isolates the eigenspace comparison
used with the quotient in [GPRV, Proposition 9.5 and Theorem 9.2]. It does not
assert that any geometric reflection or transfer map exists.
-/

public noncomputable section

namespace HilbertModularity

/-- Two linear automorphisms with the reflection relation `sδs = δ⁻¹`. -/
structure DihedralAction (L V : Type*) [Field L] [AddCommGroup V] [Module L V] where
  delta : V ≃ₗ[L] V
  reflection : V ≃ₗ[L] V
  reflection_sq : ∀ v, reflection (reflection v) = v
  reflection_delta_reflection :
    ∀ v, reflection (delta (reflection v)) = delta.symm v

namespace DihedralAction

variable {L V : Type*} [Field L] [AddCommGroup V] [Module L V]
variable (d : DihedralAction L V)

/-- The operator that is invariant under reflection. -/
def realOperator : Module.End L V :=
  (d.delta : Module.End L V) + (d.delta.symm : Module.End L V)

/-- The fixed subspace of the reflection. -/
def fixedSpace : Submodule L V :=
  Module.End.eigenspace (d.reflection : Module.End L V) 1

/-- The `a`-eigenspace of the deck operator. -/
def deckEigenspace (a : L) : Submodule L V :=
  Module.End.eigenspace (d.delta : Module.End L V) a

/-- The real-operator eigenspace inside the reflection-fixed subspace. -/
def realEigenspace (a : L) : Submodule L V :=
  d.fixedSpace ⊓ Module.End.eigenspace d.realOperator (a + a⁻¹)

theorem mem_fixedSpace_iff (v : V) :
    v ∈ d.fixedSpace ↔ d.reflection v = v := by
  rw [fixedSpace, Module.End.mem_eigenspace_iff]
  change d.reflection v = (1 : L) • v ↔ d.reflection v = v
  simp only [one_smul]

theorem mem_deckEigenspace_iff (a : L) (v : V) :
    v ∈ d.deckEigenspace a ↔ d.delta v = a • v := by
  change v ∈ Module.End.eigenspace (d.delta : Module.End L V) a ↔ _
  exact Module.End.mem_eigenspace_iff

theorem mem_realEigenspace_iff (a : L) (v : V) :
    v ∈ d.realEigenspace a ↔
      d.reflection v = v ∧ d.realOperator v = (a + a⁻¹) • v := by
  change v ∈ d.fixedSpace ⊓ Module.End.eigenspace d.realOperator (a + a⁻¹) ↔ _
  rw [Submodule.mem_inf, d.mem_fixedSpace_iff, Module.End.mem_eigenspace_iff]

private theorem reflection_delta (v : V) :
    d.reflection (d.delta v) = d.delta.symm (d.reflection v) := by
  simpa only [d.reflection_sq] using d.reflection_delta_reflection (d.reflection v)

private theorem delta_reflection (v : V) :
    d.delta (d.reflection v) = d.reflection (d.delta.symm v) := by
  have h := congrArg d.reflection (d.reflection_delta_reflection v)
  simpa only [d.reflection_sq] using h

private theorem symm_reflection (v : V) :
    d.delta.symm (d.reflection v) = d.reflection (d.delta v) := by
  simpa only [d.reflection_sq] using
    (d.reflection_delta_reflection (d.reflection v)).symm

private theorem symm_eigen {a : L} (ha : a ≠ 0) {v : V}
    (hv : d.delta v = a • v) : d.delta.symm v = a⁻¹ • v := by
  apply d.delta.injective
  rw [d.delta.apply_symm_apply, map_smul, hv, smul_smul, inv_mul_cancel₀ ha,
    one_smul]

theorem realOperator_apply (v : V) :
    d.realOperator v = d.delta v + d.delta.symm v := (rfl)

theorem realOperator_reflection (v : V) :
    d.realOperator (d.reflection v) = d.reflection (d.realOperator v) := by
  change d.delta (d.reflection v) + d.delta.symm (d.reflection v) =
    d.reflection (d.delta v + d.delta.symm v)
  rw [d.delta_reflection, d.symm_reflection, map_add]
  abel

private theorem deck_eigen_reflection {a : L} (ha : a ≠ 0) {v : V}
    (hv : d.delta v = a • v) :
    d.delta (d.reflection v) = a⁻¹ • d.reflection v := by
  rw [d.delta_reflection, d.symm_eigen ha hv, map_smul]

private theorem forward_mem {a : L} (ha : a ≠ 0) {v : V}
    (hv : v ∈ d.deckEigenspace a) :
    v + d.reflection v ∈ d.realEigenspace a := by
  have hdelta : d.delta v = a • v :=
    Module.End.mem_eigenspace_iff.mp hv
  have hsymm := d.symm_eigen ha hdelta
  have hdelta_s := d.deck_eigen_reflection ha hdelta
  have hsymm_s : d.delta.symm (d.reflection v) = a • d.reflection v := by
    apply d.delta.injective
    rw [d.delta.apply_symm_apply, map_smul, hdelta_s, smul_smul,
      mul_inv_cancel₀ ha, one_smul]
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    change d.reflection (v + d.reflection v) = (1 : L) • (v + d.reflection v)
    rw [map_add, d.reflection_sq, one_smul, add_comm]
  · apply Module.End.mem_eigenspace_iff.mpr
    change d.realOperator (v + d.reflection v) = (a + a⁻¹) • (v + d.reflection v)
    change d.delta (v + d.reflection v) + d.delta.symm (v + d.reflection v) =
      (a + a⁻¹) • (v + d.reflection v)
    rw [map_add, map_add, hdelta, hsymm, hdelta_s, hsymm_s, add_smul]
    simp only [smul_add]
    abel

private theorem inverse_mem {a : L} (ha : a ≠ 0) {w : V}
    (hw : w ∈ d.realEigenspace a) :
    (a - a⁻¹)⁻¹ • (d.delta w - a⁻¹ • w) ∈ d.deckEigenspace a := by
  have heig : d.realOperator w = (a + a⁻¹) • w :=
    Module.End.mem_eigenspace_iff.mp hw.2
  have hquad : d.delta (d.delta w) = (a + a⁻¹) • d.delta w - w := by
    have hq' : d.delta (d.delta w) + w = (a + a⁻¹) • d.delta w := by
      have h := congrArg d.delta heig
      rw [d.realOperator_apply, map_add, d.delta.apply_symm_apply,
        map_smul] at h
      exact h
    exact (eq_sub_iff_add_eq).2 hq'
  have hnum : d.delta (d.delta w - a⁻¹ • w) =
      a • (d.delta w - a⁻¹ • w) := by
    rw [map_sub, map_smul, hquad, add_smul, smul_sub, smul_smul,
      mul_inv_cancel₀ ha, one_smul]
    abel
  apply Module.End.mem_eigenspace_iff.mpr
  change d.delta ((a - a⁻¹)⁻¹ • (d.delta w - a⁻¹ • w)) =
    a • ((a - a⁻¹)⁻¹ • (d.delta w - a⁻¹ • w))
  rw [map_smul, hnum, smul_comm]

/-- The reflection-sum map identifies a non-self-inverse deck eigenspace with
the matching real eigenspace. No semisimplicity or dimension assumption occurs. -/
def deckEigenspaceEquiv (a : L) (ha : a ≠ 0) (hne : a ≠ a⁻¹) :
    d.deckEigenspace a ≃ₗ[L] d.realEigenspace a where
  toFun v := ⟨v + d.reflection v, d.forward_mem ha v.property⟩
  invFun w := ⟨(a - a⁻¹)⁻¹ • (d.delta w - a⁻¹ • w),
    d.inverse_mem ha w.property⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    abel
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul, smul_add]
  left_inv v := by
    apply Subtype.ext
    have hv : d.delta (v : V) = a • (v : V) :=
      Module.End.mem_eigenspace_iff.mp v.property
    have hs := d.deck_eigen_reflection ha hv
    have hn : d.delta ((v : V) + d.reflection v) -
        a⁻¹ • ((v : V) + d.reflection v) = (a - a⁻¹) • (v : V) := by
      rw [map_add, hv, hs, smul_add, sub_smul]
      abel
    change (a - a⁻¹)⁻¹ •
      (d.delta ((v : V) + d.reflection v) - a⁻¹ • ((v : V) + d.reflection v)) = v
    have hdiff : a - a⁻¹ ≠ 0 := sub_ne_zero.mpr hne
    rw [hn, smul_smul, inv_mul_cancel₀ hdiff, one_smul]
  right_inv w := by
    apply Subtype.ext
    have hfixed : d.reflection (w : V) = (w : V) := by
      have h := Module.End.mem_eigenspace_iff.mp w.property.1
      change d.reflection (w : V) = (1 : L) • (w : V) at h
      simpa only [one_smul] using h
    have heig : d.realOperator (w : V) = (a + a⁻¹) • (w : V) :=
      Module.End.mem_eigenspace_iff.mp w.property.2
    have hsymm : d.delta.symm (w : V) =
        (a + a⁻¹) • w - d.delta w := by
      rw [d.realOperator_apply] at heig
      exact eq_sub_of_add_eq' heig
    have hn : (d.delta (w : V) - a⁻¹ • w) +
        d.reflection (d.delta (w : V) - a⁻¹ • w) =
        (a - a⁻¹) • (w : V) := by
      rw [map_sub, map_smul, d.reflection_delta, hfixed, hsymm, sub_smul,
        add_smul]
      abel
    change (a - a⁻¹)⁻¹ • (d.delta (w : V) - a⁻¹ • w) +
      d.reflection ((a - a⁻¹)⁻¹ • (d.delta (w : V) - a⁻¹ • w)) = w
    rw [map_smul, ← smul_add, hn, smul_smul]
    have hdiff : a - a⁻¹ ≠ 0 := sub_ne_zero.mpr hne
    rw [inv_mul_cancel₀ hdiff, one_smul]

theorem deckEigenspaceEquiv_apply (a : L) (ha : a ≠ 0) (hne : a ≠ a⁻¹)
    (v : d.deckEigenspace a) :
    ((d.deckEigenspaceEquiv a ha hne v : d.realEigenspace a) : V) =
      v + d.reflection v := (rfl)

theorem deckEigenspaceEquiv_symm_apply (a : L) (ha : a ≠ 0)
    (hne : a ≠ a⁻¹) (w : d.realEigenspace a) :
    (((d.deckEigenspaceEquiv a ha hne).symm w : d.deckEigenspace a) : V) =
      (a - a⁻¹)⁻¹ • (d.delta w - a⁻¹ • w) := (rfl)

private theorem symm_commutes (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta v)) (v : V) :
    d.delta.symm (T v) = T (d.delta.symm v) := by
  apply d.delta.injective
  rw [d.delta.apply_symm_apply, hdelta, d.delta.apply_symm_apply]

private theorem symm_reverses (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta.symm v)) (v : V) :
    d.delta.symm (T v) = T (d.delta v) := by
  apply d.delta.injective
  rw [d.delta.apply_symm_apply, hdelta, d.delta.symm_apply_apply]

theorem real_commutes_of_commutes (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta v)) (v : V) :
    d.realOperator (T v) = T (d.realOperator v) := by
  change d.delta (T v) + d.delta.symm (T v) =
    T (d.delta v + d.delta.symm v)
  rw [hdelta, d.symm_commutes T hdelta, map_add]

theorem real_commutes_of_reverses (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta.symm v)) (v : V) :
    d.realOperator (T v) = T (d.realOperator v) := by
  change d.delta (T v) + d.delta.symm (T v) =
    T (d.delta v + d.delta.symm v)
  rw [hdelta, d.symm_reverses T hdelta, map_add]
  abel

/-- A linear map commuting with the deck operator acts on each deck eigenspace. -/
def deckMap (a : L) (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta v)) :
    d.deckEigenspace a →ₗ[L] d.deckEigenspace a where
  toFun v := ⟨T v, by
    apply Module.End.mem_eigenspace_iff.mpr
    change d.delta (T v) = a • T v
    rw [hdelta, show d.delta (v : V) = a • v from
      Module.End.mem_eigenspace_iff.mp v.property, map_smul]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- A map commuting with reflection and the real operator acts on the fixed
real eigenspace. -/
def realMap (a : L) (T : Module.End L V)
    (hreflection : ∀ v, d.reflection (T v) = T (d.reflection v))
    (hreal : ∀ v, d.realOperator (T v) = T (d.realOperator v)) :
    d.realEigenspace a →ₗ[L] d.realEigenspace a where
  toFun w := ⟨T w, by
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      change d.reflection (T w) = (1 : L) • T w
      rw [hreflection, show d.reflection (w : V) = (1 : L) • w from
        Module.End.mem_eigenspace_iff.mp w.property.1, map_smul]
    · apply Module.End.mem_eigenspace_iff.mpr
      change d.realOperator (T w) = (a + a⁻¹) • T w
      rw [hreal, show d.realOperator (w : V) = (a + a⁻¹) • w from
        Module.End.mem_eigenspace_iff.mp w.property.2, map_smul]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- The reflection sum intertwines a map commuting with both generators. -/
theorem deckEigenspaceEquiv_commuting (a : L) (ha : a ≠ 0) (hne : a ≠ a⁻¹)
    (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta v))
    (hreflection : ∀ v, d.reflection (T v) = T (d.reflection v))
    (v : d.deckEigenspace a) :
    d.deckEigenspaceEquiv a ha hne (d.deckMap a T hdelta v) =
      d.realMap a T hreflection (real_commutes_of_commutes d T hdelta)
        (d.deckEigenspaceEquiv a ha hne v) := by
  apply Subtype.ext
  change T v + d.reflection (T v) = T (v + d.reflection v)
  rw [hreflection, map_add]

/-- If `T` inverts the deck operator, the stable action on the `a`-eigenspace
is `s ∘ T`, not `T`. -/
def reflectedDeckMap (a : L) (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta.symm v)) :
    d.deckEigenspace a →ₗ[L] d.deckEigenspace a where
  toFun v := ⟨d.reflection (T v), by
    apply Module.End.mem_eigenspace_iff.mpr
    change d.delta (d.reflection (T v)) = a • d.reflection (T v)
    rw [d.delta_reflection, d.symm_reverses T hdelta,
      show d.delta (v : V) = a • v from
        Module.End.mem_eigenspace_iff.mp v.property, map_smul, map_smul]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- Reflection-corrected deck action intertwines the ordinary fixed-space
action when `T` commutes with `s` and inverts `δ`. -/
theorem deckEigenspaceEquiv_reversing (a : L) (ha : a ≠ 0) (hne : a ≠ a⁻¹)
    (T : Module.End L V)
    (hdelta : ∀ v, d.delta (T v) = T (d.delta.symm v))
    (hreflection : ∀ v, d.reflection (T v) = T (d.reflection v))
    (v : d.deckEigenspace a) :
    d.deckEigenspaceEquiv a ha hne (d.reflectedDeckMap a T hdelta v) =
      d.realMap a T hreflection (real_commutes_of_reverses d T hdelta)
        (d.deckEigenspaceEquiv a ha hne v) := by
  apply Subtype.ext
  change d.reflection (T v) + d.reflection (d.reflection (T v)) =
    T (v + d.reflection v)
  rw [d.reflection_sq, map_add, ← hreflection]
  abel

end DihedralAction

end HilbertModularity
