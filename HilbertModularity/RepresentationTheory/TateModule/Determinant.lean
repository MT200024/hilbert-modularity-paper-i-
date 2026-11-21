/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Topology.TateModule.FiniteFree
public import HilbertModularity.Algebra.TateModule.FiniteLevelBasis
public import HilbertModularity.RepresentationTheory.TateModule.TowerReduction
public import HilbertModularity.RepresentationTheory.DeterminantCharacter

/-! # Continuous determinant characters of actual Tate actions

The established finite coordinate topologies make the actual integral,
rational and finite-level determinant characters continuous. Their values
are related by the actual coefficient maps, as in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

attribute [local instance] torsionCoefficientAlgebra torsionCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G] [AddCommGroup A]
  [DistribMulAction G A] [TopologicalSpace G] [ContinuousInv G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]
  [Module.Finite ℤ_[p] (integral p A)]

/-- The actual integral Tate determinant as a continuous unit-valued character. -/
def integralDeterminantCharacter : G →ₜ* ℤ_[p]ˣ :=
  Representation.continuousDeterminantCharacter (Module.finBasis ℤ_[p] (integral p A))
    (fun _ => IsModuleTopology.continuous_of_linearMap _) (representation p G A)
    (continuous_representation p G A)

/-- The actual rational Tate determinant as a continuous unit-valued character. -/
def rationalDeterminantCharacter : G →ₜ* ℚ_[p]ˣ :=
  Representation.continuousDeterminantCharacter
    ((Module.finBasis ℤ_[p] (integral p A)).baseChange ℚ_[p])
    (fun _ => IsModuleTopology.continuous_of_linearMap _) (rationalRepresentation p G A)
    (continuous_rationalRepresentation p G A)

/-- The actual finite-level torsion determinant as a continuous character. -/
def finiteLevelDeterminantCharacter
    (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) : G →ₜ* (ZMod (p ^ n))ˣ :=
  Representation.continuousDeterminantCharacter (finiteLevelBasis p A hpdiv n)
    (fun _ => continuous_of_discreteTopology) (torsionRepresentation p G A n)
    (continuous_torsionRepresentation p G A n)

/-- Rationalizing the actual integral character gives the actual rational character. -/
theorem rationalDeterminantCharacter_apply (g : G) :
    rationalDeterminantCharacter p G A g =
      Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom (integralDeterminantCharacter p G A g) := by
  apply Units.ext
  exact det_rationalRepresentation p G A g

/-- Reducing the actual integral character gives the actual finite-level character. -/
theorem finiteLevelDeterminantCharacter_apply
    (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) (g : G) :
    finiteLevelDeterminantCharacter p G A hpdiv n g =
      Units.map (PadicInt.toZModPow n).toMonoidHom (integralDeterminantCharacter p G A g) := by
  apply Units.ext
  exact det_finiteLevelRepresentation p G A hpdiv n g

end TateModule
