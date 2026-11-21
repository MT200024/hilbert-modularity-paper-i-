/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Approximation
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Finite generation of actual Tate modules

Finite level-one torsion and divisibility suffice: the span of chosen lifts
is finitely generated and compact over `Z_p`, hence closed. Its finite-level
approximations converge to every compatible family. This proves finite
Tate generation without an assumed lattice, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open Filter Topology

namespace TateModule

variable (p : ℕ) [Fact p.Prime]

/-- Reduction of a p-adic coefficient modulo `p^n` is continuous for the discrete topology. -/
theorem continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow n : ℤ_[p] → ZMod (p ^ n)) := by
  let : UniformSpace (ZMod (p ^ n)) := ⊥
  apply UniformContinuous.continuous
  apply IsUniformAddGroup.uniformContinuous_iff_isOpen_ker.mpr
  change IsOpen (RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) : Set ℤ_[p])
  rw [PadicInt.ker_toZModPow]
  have hr : (p : ℝ) ^ (-(n : ℤ)) ≠ 0 :=
    ne_of_gt (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _)
  convert IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p]) hr using 1
  ext x
  simp only [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow]
  rfl

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- The actual inverse-limit Tate module has continuous p-adic scalar multiplication. -/
instance integralContinuousSMul : ContinuousSMul ℤ_[p] (integral p A) where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro n
    change Continuous (fun z : ℤ_[p] × integral p A =>
      PadicInt.toZModPow n z.1 • projection p A n z.2)
    have h : Continuous (fun z : ℤ_[p] × integral p A =>
        (PadicInt.toZModPow n z.1, projection p A n z.2)) :=
      ((continuous_toZModPow p n).comp continuous_fst).prodMk
        ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))
    exact (continuous_of_discreteTopology : Continuous
      (fun z : ZMod (p ^ n) × Torsion p A n => z.1 • z.2)).comp h

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- The finitely generated lifted submodule is all of the actual Tate inverse limit. -/
theorem levelOneSpan_eq_top [Finite (Torsion p A 1)]
    (hpdiv : Function.Surjective (fun a : A => p • a)) : levelOneSpan p A hpdiv = ⊤ := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  apply top_unique
  intro x _
  let y : ℕ → integral p A := fun n =>
    Classical.choose (exists_levelOneSpan_projection p A hpdiv n (projection p A n x))
  have hym (n : ℕ) : y n ∈ levelOneSpan p A hpdiv :=
    (Classical.choose_spec (exists_levelOneSpan_projection p A hpdiv n (projection p A n x))).1
  have hye (n : ℕ) : projection p A n (y n) = projection p A n x :=
    (Classical.choose_spec (exists_levelOneSpan_projection p A hpdiv n (projection p A n x))).2
  have hlim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_subtype_rng]
    apply tendsto_pi_nhds.mpr
    intro k
    have he : ∀ᶠ n in atTop, projection p A k (y n) = projection p A k x := by
      filter_upwards [eventually_ge_atTop k] with n hn
      exact projection_eq_of_le p A hn (hye n)
    exact tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
  have hc : IsClosed (levelOneSpan p A hpdiv : Set (integral p A)) :=
    (Submodule.isCompact_of_fg (levelOneSpan_fg p A hpdiv)).isClosed
  exact hc.mem_of_tendsto hlim (Eventually.of_forall hym)

end TateModule

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- Finite level-one torsion and p-divisibility imply finite generation of the actual integral Tate module. -/
theorem integral_finite_of_finite_torsion [Finite (Torsion p A 1)]
    (hpdiv : Function.Surjective (fun a : A => p • a)) : Module.Finite ℤ_[p] (integral p A) := by
  rw [Module.finite_def, ← levelOneSpan_eq_top p A hpdiv]
  exact levelOneSpan_fg p A hpdiv

end TateModule
