/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.TateModule.Reduction
public import HilbertModularity.RepresentationTheory.DualLattice

/-! # Reduction of integral dual Tate representations

Finite free dual base change and the actual torsion comparison identify the
reduced integral contragredient with the dual of the actual torsion action.
This supplies the covariant/dual convention used in [TripathiGoswami]; it
does not assert an etale-cohomology comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

attribute [local instance] torsionCoefficientAlgebra torsionCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G] [AddCommGroup A]
  [DistribMulAction G A] [Module.Finite ℤ_[p] (integral p A)]

/-- Reduction of the integral Tate dual is the contragredient actual torsion action. -/
def residualDualRepresentationEquiv
    (hpdiv : Function.Surjective (fun a : A => p • a)) :
    ((representation p G A).dual.baseChange (ZMod (p ^ 1))).Equiv
      (torsionRepresentation p G A 1).dual := by
  let e := residualRepresentationEquiv p G A hpdiv
  let d : (((representation p G A).baseChange (ZMod (p ^ 1))).dual).Equiv
      (torsionRepresentation p G A 1).dual :=
    .mk e.toLinearEquiv.symm.dualMap (by
      intro g
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      exact congrArg φ (e.symm.toIntertwiningMap.isIntertwining
        (torsionRepresentation p G A 1)
        ((representation p G A).baseChange (ZMod (p ^ 1))) g⁻¹ x).symm)
  exact (Representation.dualBaseChangeEquiv (ZMod (p ^ 1)) (representation p G A)).trans d

/-- The residual duality pairing on lifted compatible families is reduction of the integral pairing. -/
theorem residualDualRepresentationEquiv_tmul
    (hpdiv : Function.Surjective (fun a : A => p • a))
    (a : ZMod (p ^ 1)) (φ : Module.Dual ℤ_[p] (integral p A)) (x : integral p A) :
    residualDualRepresentationEquiv p G A hpdiv (a ⊗ₜ[ℤ_[p]] φ)
      (projection p A 1 x) = a * PadicInt.toZModPow 1 (φ x) := by
  change Representation.dualBaseChangeEquiv (ZMod (p ^ 1)) (representation p G A)
    (a ⊗ₜ[ℤ_[p]] φ) ((residualRepresentationEquiv p G A hpdiv).symm
      (projection p A 1 x)) = _
  have hx : (residualRepresentationEquiv p G A hpdiv).symm (projection p A 1 x) =
      (1 : ZMod (p ^ 1)) ⊗ₜ[ℤ_[p]] x := by
    apply (residualRepresentationEquiv p G A hpdiv).injective
    simp
  rw [hx, Representation.dualBaseChangeEquiv_tmul]
  rfl

end TateModule
