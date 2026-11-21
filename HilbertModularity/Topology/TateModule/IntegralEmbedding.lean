/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Topology.TateModule.FiniteFree

/-! # The actual integral Tate module as a compact open lattice

The canonical map from compatible integral Tate families to the rational Tate
module is an open embedding. Its image is compact and open, using the actual
finite integral and rational coordinates of [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]
  [TopologicalSpace A] [DiscreteTopology A] [Module.Finite ℤ_[p] (integral p A)]

/-- Rational coordinates of an integral Tate vector are its integral coordinates embedded in `Q_p`. -/
theorem rationalCoordinate_toRational (x : integral p A)
    (i : Fin (Module.finrank ℤ_[p] (integral p A))) :
    rationalCoordinateEquiv p A (toRational p A x) i =
      ((integralCoordinateEquiv p A).symm x i : ℚ_[p]) := by
  change ((Module.finBasis ℤ_[p] (integral p A)).baseChange ℚ_[p]).repr
    ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) i = ((Module.finBasis ℤ_[p] (integral p A)).repr x i : ℚ_[p])
  rw [Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

/-- The canonical actual integral-to-rational Tate map is an open embedding. -/
theorem isOpenEmbedding_toRational : Topology.IsOpenEmbedding (toRational p A) := by
  let I := Fin (Module.finrank ℤ_[p] (integral p A))
  have hpi : Topology.IsOpenEmbedding (fun c : I → ℤ_[p] => fun i => (c i : ℚ_[p])) :=
    Topology.IsOpenEmbedding.piMap (fun _ => PadicInt.isOpenEmbedding_coe)
  have hc := (rationalCoordinateEquiv p A).toHomeomorph.symm.isOpenEmbedding.comp
    (hpi.comp (integralCoordinateEquiv p A).toHomeomorph.symm.isOpenEmbedding)
  have he : (fun x => (rationalCoordinateEquiv p A).symm
      (fun i => ((integralCoordinateEquiv p A).symm x i : ℚ_[p]))) = toRational p A := by
    funext x
    apply (rationalCoordinateEquiv p A).injective
    funext i
    simpa using (rationalCoordinate_toRational p A x i).symm
  change Topology.IsOpenEmbedding (fun x => (rationalCoordinateEquiv p A).symm
    (fun i => ((integralCoordinateEquiv p A).symm x i : ℚ_[p]))) at hc
  rw [he] at hc
  exact hc

/-- The actual integral Tate image is compact in its rational realization. -/
theorem isCompact_range_toRational : IsCompact (Set.range (toRational p A)) :=
  isCompact_range (continuous_toRational p A)

/-- The actual integral Tate image is open in its rational realization. -/
theorem isOpen_range_toRational : IsOpen (Set.range (toRational p A)) :=
  (isOpenEmbedding_toRational p A).isOpen_range

end TateModule
