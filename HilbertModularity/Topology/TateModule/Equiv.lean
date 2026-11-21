/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Topology.TateModule.Maps

/-! # Tate-module equivalences from compatible torsion equivalences -/

@[expose] public noncomputable section
open scoped TensorProduct

namespace TateModule
variable (p : ℕ) [Fact p.Prime] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  (e : ∀ n, Torsion p A n ≃ₗ[ℤ_[p]] Torsion p B n)
  (he : ∀ n v, transition p B n (e (n + 1) v) = e n (transition p A n v))

/-- Compatible equivalences on every torsion level induce an equivalence of integral Tate modules.
No equivalence on the full groups of points is required. -/
def equivOfTorsion : integral p A ≃ₗ[ℤ_[p]] integral p B where
  toLinearMap := mapOfTorsion p (fun n => (e n).toLinearMap) he
  invFun w := ⟨fun n => (e n).symm (w.val n), by
    intro n
    apply (e n).injective
    rw [← he]
    simpa only [LinearEquiv.apply_symm_apply] using w.property n⟩
  left_inv v := by
    apply Subtype.ext
    funext n
    exact (e n).symm_apply_apply _
  right_inv w := by
    apply Subtype.ext
    funext n
    exact (e n).apply_symm_apply _

/-- The induced equivalence acts by the specified equivalence at each torsion level. -/
@[simp]
theorem equivOfTorsion_projection (v : integral p A) (n : ℕ) :
    projection p B n (equivOfTorsion p e he v) = e n (projection p A n v) := rfl

/-- The inverse equivalence acts by the inverse at each torsion level. -/
@[simp]
theorem equivOfTorsion_symm_projection (w : integral p B) (n : ℕ) :
    projection p A n ((equivOfTorsion p e he).symm w) =
      (e n).symm (projection p B n w) := rfl

/-- The compatible torsion equivalences extend to the rational Tate modules. -/
def rationalEquivOfTorsion : rational p A ≃ₗ[ℚ_[p]] rational p B :=
  LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ (equivOfTorsion p e he)

/-- The rational equivalence preserves the coefficient and applies the integral equivalence. -/
@[simp]
theorem rationalEquivOfTorsion_tmul (c : ℚ_[p]) (v : integral p A) :
    rationalEquivOfTorsion p e he (c ⊗ₜ v) = c ⊗ₜ equivOfTorsion p e he v := rfl

variable [TopologicalSpace A] [TopologicalSpace B]

/-- Continuous torsion equivalences give a continuous forward map on the inverse limit. -/
theorem continuous_equivOfTorsion (h : ∀ n, Continuous (e n)) :
    Continuous (equivOfTorsion p e he) :=
  continuous_mapOfTorsion p (fun n => (e n).toLinearMap) he h

/-- Continuity of the inverse torsion maps gives continuity of the inverse-limit inverse. -/
theorem continuous_equivOfTorsion_symm (h : ∀ n, Continuous (e n).symm) :
    Continuous (equivOfTorsion p e he).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (h n).comp ((continuous_apply n).comp continuous_subtype_val)

/-- The rationalized map is continuous for the Tate scalar-extension topology. -/
theorem continuous_rationalEquivOfTorsion (h : ∀ n, Continuous (e n)) :
    Continuous (rationalEquivOfTorsion p e he) :=
  continuous_baseChange_map p (equivOfTorsion p e he).toLinearMap
    (continuous_equivOfTorsion p e he h)

end TateModule
