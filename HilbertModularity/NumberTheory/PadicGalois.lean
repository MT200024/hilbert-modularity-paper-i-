/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linarith

/-! # The Galois action on the p-adic complex numbers

Automorphisms of the algebraic closure of `ℚ_[p]` preserve the spectral norm.
They therefore extend uniquely to the actual completed field `ℂ_[p]`.
-/

@[expose] public noncomputable section

open UniformSpace
open scoped Topology


variable (p : ℕ) [Fact p.Prime]

namespace PadicAlgCl

/-- Every algebraic Galois automorphism preserves the p-adic norm. -/
theorem norm_galois (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

/-- Algebraic Galois automorphisms are isometries for the p-adic metric. -/
theorem isometry_galois (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Isometry g := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm, ← map_sub, norm_galois]

/-- Each algebraic element has a locally constant orbit map in the Krull topology. -/
theorem eventually_galois_eq (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : PadicAlgCl p) : ∀ᶠ h in 𝓝 g, h x = g x := by
  have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) x).preimage
    (continuous_const.mul continuous_id : Continuous fun h => g⁻¹ * h)
  have hn := ho.mem_nhds (show g⁻¹ * g ∈
    MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x by simp)
  filter_upwards [hn] with h hh
  change (g⁻¹ * h) x = x at hh
  have := congrArg g hh
  simpa using this

end PadicAlgCl

namespace PadicComplex

set_option backward.isDefEq.respectTransparency false in
/-- The extension of an algebraic Galois automorphism to the completed field. -/
def galoisEquiv (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℂ_[p] ≃ₐ[ℚ_[p]] ℂ_[p] :=
  { Completion.mapRingEquiv g.toRingEquiv (PadicAlgCl.isometry_galois p g).continuous
      (PadicAlgCl.isometry_galois p g.symm).continuous with
    commutes' r := by
      change Completion.mapRingHom g.toRingHom _ (algebraMap ℚ_[p] (PadicAlgCl p) r) = _
      rw [Completion.mapRingHom_coe]
      exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (g.commutes r) }

/-- The completed action extends the given algebraic action. -/
@[simp]
theorem galoisEquiv_coe (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    galoisEquiv p g (x : ℂ_[p]) = (g x : ℂ_[p]) :=
  Completion.mapRingHom_coe (PadicAlgCl.isometry_galois p g).continuous x

/-- An automorphism over an embedded local field fixes its image in the completion. -/
theorem galoisEquiv_coe_algebraMap_of_restrictScalars
    {K : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (a : K) :
    galoisEquiv p (g.restrictScalars ℚ_[p]) (algebraMap K (PadicAlgCl p) a : ℂ_[p]) =
      (algebraMap K (PadicAlgCl p) a : ℂ_[p]) := by
  rw [galoisEquiv_coe]
  exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (g.commutes a)

/-- The completed action remains isometric. -/
theorem isometry_galoisEquiv (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Isometry (galoisEquiv p g) :=
  (PadicAlgCl.isometry_galois p g).completion_map

/-- Extension to the completion respects multiplication of Galois automorphisms. -/
theorem galoisEquiv_mul (g h : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    galoisEquiv p (g * h) = galoisEquiv p g * galoisEquiv p h := by
  ext x
  refine Completion.induction_on x ?_ fun x => ?_
  · exact isClosed_eq (isometry_galoisEquiv p (g * h)).continuous
      ((isometry_galoisEquiv p g).continuous.comp (isometry_galoisEquiv p h).continuous)
  · simp

/-- Extension of the identity is the identity. -/
@[simp]
theorem galoisEquiv_one : galoisEquiv p 1 = 1 := by
  ext x
  refine Completion.induction_on x ?_ fun x => ?_
  · exact isClosed_eq (isometry_galoisEquiv p 1).continuous continuous_id
  · simp

/-- The absolute Galois group acts by algebra automorphisms on `ℂ_[p]`. -/
def galoisAction : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* (ℂ_[p] ≃ₐ[ℚ_[p]] ℂ_[p]) where
  toFun := galoisEquiv p
  map_one' := galoisEquiv_one p
  map_mul' := galoisEquiv_mul p

/-- The completed Galois action is jointly continuous for the Krull and p-adic topologies. -/
theorem continuous_galoisAction :
    Continuous fun y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) × ℂ_[p] =>
      galoisEquiv p y.1 y.2 := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, z⟩
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨a, ha⟩ := Completion.denseRange_coe.exists_dist_lt z (by linarith : 0 < ε / 4)
  have hg := (continuous_fst.tendsto (g, z)).eventually
    (PadicAlgCl.eventually_galois_eq p g a)
  have hz : ∀ᶠ y : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) × ℂ_[p] in 𝓝 (g, z),
      dist y.2 z < ε / 2 :=
    (Metric.tendsto_nhds.mp (continuous_snd.tendsto (g, z))) _ (by linarith)
  filter_upwards [hg, hz] with y hy hyz
  have ht := dist_triangle (galoisEquiv p y.1 y.2)
    (galoisEquiv p y.1 (a : ℂ_[p])) (galoisEquiv p g z)
  rw [(isometry_galoisEquiv p y.1).dist_eq] at ht
  have he : galoisEquiv p y.1 (a : ℂ_[p]) = galoisEquiv p g (a : ℂ_[p]) := by
    simpa using congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) hy
  rw [he, (isometry_galoisEquiv p g).dist_eq] at ht
  have ht' := dist_triangle y.2 z (a : ℂ_[p])
  rw [dist_comm (a : ℂ_[p]) z] at ht
  linarith

end PadicComplex
