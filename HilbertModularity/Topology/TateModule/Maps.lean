/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Topology.TateModule

/-! # Maps of Tate modules from compatible maps at every torsion level -/

@[expose] public noncomputable section

namespace TateModule

variable (p : ℕ) [Fact p.Prime] {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (f : ∀ n, Torsion p A n →ₗ[ℤ_[p]] Torsion p B n)
  (hf : ∀ n v, transition p B n (f (n + 1) v) = f n (transition p A n v))

/-- Compatible linear maps of torsion levels induce a map on the ordinary integral Tate modules. -/
def mapOfTorsion : integral p A →ₗ[ℤ_[p]] integral p B where
  toFun v := ⟨fun n => f n (v.val n), by
    intro n
    rw [hf, v.property n]⟩
  map_add' v w := by
    apply Subtype.ext
    funext n
    exact map_add (f n) _ _
  map_smul' r v := by
    apply Subtype.ext
    funext n
    exact map_smul (f n) _ _

/-- The induced Tate map has exactly the prescribed finite-level coordinates. -/
@[simp]
theorem mapOfTorsion_projection (v : integral p A) (n : ℕ) :
    projection p B n (mapOfTorsion p f hf v) = f n (projection p A n v) := rfl

/-- Composition of compatible maps is computed at every finite torsion level. -/
theorem mapOfTorsion_comp
    (g : ∀ n, Torsion p B n →ₗ[ℤ_[p]] Torsion p C n)
    (hg : ∀ n v, transition p C n (g (n + 1) v) = g n (transition p B n v)) :
    mapOfTorsion p (fun n => (g n).comp (f n))
      (fun n v => (hg n (f (n + 1) v)).trans (congrArg (g n) (hf n v))) =
      (mapOfTorsion p g hg).comp (mapOfTorsion p f hf) := by
  apply LinearMap.ext
  intro v
  rfl

variable [TopologicalSpace A] [TopologicalSpace B]

/-- Continuous maps at every finite level give a continuous map of integral inverse limits. -/
theorem continuous_mapOfTorsion (hcont : ∀ n, Continuous (f n)) :
    Continuous (mapOfTorsion p f hf) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (hcont n).comp ((continuous_apply n).comp continuous_subtype_val)

end TateModule

namespace TateModule
variable (p : ℕ) [Fact p.Prime] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [TopologicalSpace A] [TopologicalSpace B]

/-- A continuous integral Tate map extends continuously to rational coefficients. -/
theorem continuous_baseChange_map (f : integral p A →ₗ[ℤ_[p]] integral p B)
    (hf : Continuous f) : Continuous (f.baseChange ℚ_[p]) := by
  apply (continuous_linearMap_iff p A _).mpr
  exact (continuous_toRational p B).comp hf

end TateModule
