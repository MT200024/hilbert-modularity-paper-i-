/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarConjugation
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Continuous coefficient conjugation

The actual tensor-defined coefficient conjugate is semilinearly homeomorphic
to the original module when the coefficient automorphism is a homeomorphism.
This preserves the continuous action of the same Galois group, as used for the
local coefficient labels in [TripathiGoswami].
-/

@[expose] public noncomputable section
namespace Rep
variable {K G : Type*} [Field K] [Monoid G]
  [TopologicalSpace K]
  (σ : K ≃+* K) (V : Rep K G)
  [TopologicalSpace V] [IsModuleTopology K V]
  [TopologicalSpace (scalarConjugate σ V)] [IsModuleTopology K (scalarConjugate σ V)]
  (hσ : Continuous σ) (hσi : Continuous σ.symm)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The canonical tensor conjugation equivalence respects the actual module topologies. -/
def scalarConjugateContinuousEquiv :
    ContinuousLinearEquiv (σ : K →+* K) (σ' := (σ.symm : K →+* K)) V (scalarConjugate σ V) := by
  letI : ContinuousAdd V := IsModuleTopology.toContinuousAdd K V
  letI : ContinuousAdd (scalarConjugate σ V) := IsModuleTopology.toContinuousAdd K _
  exact
    { scalarConjugateEquiv σ V with
      continuous_toFun := IsModuleTopology.continuous_of_linearMapₛₗ hσ
        (scalarConjugateEquiv σ V).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMapₛₗ hσi
        (scalarConjugateEquiv σ V).symm.toLinearMap }

include hσ hσi in
/-- A continuous Galois action remains continuous after actual coefficient conjugation. -/
theorem continuous_scalarConjugate [TopologicalSpace G]
    (hρ : Continuous fun y : G × V => V.ρ y.1 y.2) :
    Continuous fun y : G × scalarConjugate σ V => (scalarConjugate σ V).ρ y.1 y.2 := by
  let e := scalarConjugateContinuousEquiv σ V hσ hσi
  have h := e.continuous.comp
    (hρ.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  apply h.congr
  intro y
  change scalarConjugateEquiv σ V (V.ρ y.1 ((scalarConjugateEquiv σ V).symm y.2)) = _
  rw [scalarConjugateEquiv_apply_action, LinearEquiv.apply_symm_apply]

end Rep

namespace Rep
variable {K G H : Type*} [Field K] [Monoid G] [Monoid H]
  [TopologicalSpace K] [TopologicalSpace G] [TopologicalSpace H]

/-- Restriction along a continuous group homomorphism preserves the continuous coefficient-conjugate action. -/
theorem continuous_scalarConjugate_comp (σ : K ≃+* K) (V : Rep K G)
    (f : H →* G) (hf : Continuous f) :
    letI : TopologicalSpace (scalarConjugate σ V) := moduleTopology K _
    letI : TopologicalSpace (scalarConjugate σ (Rep.of (V.ρ.comp f))) := moduleTopology K _
    (Continuous fun y : G × scalarConjugate σ V => (scalarConjugate σ V).ρ y.1 y.2) →
      Continuous fun y : H × scalarConjugate σ (Rep.of (V.ρ.comp f)) =>
        (scalarConjugate σ (Rep.of (V.ρ.comp f))).ρ y.1 y.2 := by
  intro h
  let : TopologicalSpace (scalarConjugate σ V) := moduleTopology K _
  change Continuous (fun y : H × scalarConjugate σ V =>
    (scalarConjugate σ V).ρ (f y.1) y.2)
  change Continuous (fun y : G × scalarConjugate σ V =>
    (scalarConjugate σ V).ρ y.1 y.2) at h
  have hp : Continuous (fun y : H × scalarConjugate σ V => (f y.1, y.2)) :=
    (hf.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def] using h.comp hp

end Rep
