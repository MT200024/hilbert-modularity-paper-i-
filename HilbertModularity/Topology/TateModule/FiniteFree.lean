/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Topology.TateModule
public import HilbertModularity.Topology.TateModule.FiniteGeneration
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Compactness.LocallyCompact

/-! # The finite free topology of actual Tate modules

For discrete point groups with finite integral Tate module, the inverse-limit
topology agrees with finite p-adic coordinates. The universal rational Tate
topology is the ordinary module topology and has finite rational coordinates.
These are the topological realizations used in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]
  [TopologicalSpace A] [DiscreteTopology A] [Module.Finite ℤ_[p] (integral p A)]

/-- Finite integral Tate coordinates give a linear homeomorphism for the actual inverse-limit topology. -/
def integralCoordinateEquiv :
    (Fin (Module.finrank ℤ_[p] (integral p A)) → ℤ_[p]) ≃L[ℤ_[p]] integral p A := by
  let e := (Module.finBasis ℤ_[p] (integral p A)).equivFun.symm
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  let h := e.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap
  exact { e with continuous_toFun := hc, continuous_invFun := h.continuous_invFun }

/-- The actual inverse-limit topology is the finite p-adic module topology. -/
instance integralIsModuleTopology : IsModuleTopology ℤ_[p] (integral p A) :=
  IsModuleTopology.iso (integralCoordinateEquiv p A)

/-- The actual finite integral Tate module is compact. -/
instance integralCompactSpace : CompactSpace (integral p A) :=
  Module.Finite.compactSpace ℤ_[p] (integral p A)

/-- The universal rational Tate topology is the ordinary rational module topology. -/
instance rationalIsModuleTopology : IsModuleTopology ℚ_[p] (rational p A) := by
  apply IsModuleTopology.of_continuous_id
  let : TopologicalSpace (rational p A) := moduleTopology ℚ_[p] (rational p A)
  let : IsModuleTopology ℚ_[p] (rational p A) := ⟨rfl⟩
  let : ContinuousAdd (rational p A) := IsModuleTopology.toContinuousAdd ℚ_[p] (rational p A)
  let : ContinuousSMul ℤ_[p] (rational p A) := ⟨by
    change Continuous (fun z : ℤ_[p] × rational p A => (z.1 : ℚ_[p]) • z.2)
    exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd⟩
  apply (continuous_linearMap_iff p A (LinearMap.id : rational p A →ₗ[ℚ_[p]] rational p A)).mpr
  exact IsModuleTopology.continuous_of_linearMap (toRational p A)

/-- Actual rational Tate vectors have the usual finite p-adic coordinate topology. -/
def rationalCoordinateEquiv :
    rational p A ≃L[ℚ_[p]] (Fin (Module.finrank ℤ_[p] (integral p A)) → ℚ_[p]) := by
  let e := ((Module.finBasis ℤ_[p] (integral p A)).baseChange ℚ_[p]).equivFun
  exact { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

/-- The actual rational Tate topology is Hausdorff. -/
instance rationalT2Space : T2Space (rational p A) :=
  (rationalCoordinateEquiv p A).toHomeomorph.symm.t2Space

/-- The actual rational Tate topology is locally compact. -/
instance rationalLocallyCompactSpace : LocallyCompactSpace (rational p A) :=
  (rationalCoordinateEquiv p A).toHomeomorph.isClosedEmbedding.locallyCompactSpace

end TateModule
