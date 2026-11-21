/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # The topology of the rational Tate module

The rational Tate module carries the finest topological `Q_p`-module topology
for which the map from the integral inverse limit is continuous. The universal
property below characterizes this topological extension of scalars.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- The canonical map from the integral Tate module to its rational scalar extension. -/
def toRational : integral p A →ₗ[ℤ_[p]] rational p A :=
  TensorProduct.mk ℤ_[p] ℚ_[p] (integral p A) 1

variable [TopologicalSpace A]

/-- The topological scalar-extension topology of the rational Tate module. -/
instance rationalTopologicalSpace : TopologicalSpace (rational p A) :=
  sInf {t | @ContinuousSMul ℚ_[p] (rational p A) _ _ t ∧
    @ContinuousAdd (rational p A) t _ ∧
    @Continuous (integral p A) (rational p A) _ t (toRational p A)}

instance rationalContinuousSMul : ContinuousSMul ℚ_[p] (rational p A) :=
  continuousSMul_sInf fun _ h => h.1

instance rationalContinuousAdd : ContinuousAdd (rational p A) :=
  continuousAdd_sInf fun _ h => h.2.1

instance rationalIsTopologicalAddGroup : IsTopologicalAddGroup (rational p A) where
  continuous_neg := by
    have h := (continuous_id.const_smul (-1 : ℚ_[p]) :
      Continuous (fun x : rational p A => (-1 : ℚ_[p]) • x))
    simp only [neg_one_smul] at h
    exact h

/-- The integral lattice map is continuous by construction. -/
theorem continuous_toRational : Continuous (toRational p A) :=
  continuous_sInf_rng.mpr fun _ h => h.2.2

/-- A rational linear map is continuous exactly when its restriction to the
integral Tate module is continuous. -/
theorem continuous_linearMap_iff {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul ℚ_[p] W]
    (f : rational p A →ₗ[ℚ_[p]] W) :
    Continuous f ↔ Continuous (fun x => f (toRational p A x)) := by
  constructor
  · intro h
    exact h.comp (continuous_toRational p A)
  · intro h
    rw [continuous_iff_le_induced]
    exact sInf_le ⟨continuousSMul_induced f, continuousAdd_induced f,
      continuous_induced_rng.mpr h⟩

end TateModule
