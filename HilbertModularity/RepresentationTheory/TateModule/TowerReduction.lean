/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.TowerReduction
public import HilbertModularity.RepresentationTheory.TateModule.Reduction

/-! # Equivariant Tate reduction at every finite level

The actual p-power torsion action is obtained by scalar reduction of the
integral Tate representation, and determinants specialize accordingly.
This is the integral reduction step used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

attribute [local instance] torsionCoefficientAlgebra torsionCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (G A : Type*) [Monoid G] [AddCommGroup A]
  [DistribMulAction G A]

/-- Reduction of the actual covariant Tate action is the actual action on `p^n`-torsion. -/
def finiteLevelRepresentationEquiv (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    ((representation p G A).baseChange (ZMod (p ^ n))).Equiv (torsionRepresentation p G A n) :=
  .mk (finiteLevelEquiv p A hpdiv n) (by
    intro g
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    | tmul a x =>
      change finiteLevelEquiv p A hpdiv n (a ⊗ₜ[ℤ_[p]] representation p G A g x) =
        torsionRepresentation p G A n g (finiteLevelEquiv p A hpdiv n (a ⊗ₜ[ℤ_[p]] x))
      rw [finiteLevelEquiv_tmul, finiteLevelEquiv_tmul, map_smul]
      rfl)

/-- The equivariant residual identification evaluates the original compatible family at level n. -/
@[simp]
theorem finiteLevelRepresentationEquiv_tmul
    (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ)
    (a : ZMod (p ^ n)) (x : integral p A) :
    finiteLevelRepresentationEquiv p G A hpdiv n (a ⊗ₜ[ℤ_[p]] x) =
      a • projection p A n x := rfl

variable [Module.Finite ℤ_[p] (integral p A)]

/-- The determinant on actual geometric torsion is the residual image of the integral Tate determinant. -/
theorem det_finiteLevelRepresentation
    (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) (g : G) :
    LinearMap.det (torsionRepresentation p G A n g) =
      PadicInt.toZModPow n (LinearMap.det (representation p G A g)) := by
  let e := finiteLevelRepresentationEquiv p G A hpdiv n
  have he : e.toLinearEquiv.toLinearMap ∘ₗ
      ((representation p G A).baseChange (ZMod (p ^ n))) g ∘ₗ
        e.toLinearEquiv.symm.toLinearMap = torsionRepresentation p G A n g := by
    apply LinearMap.ext
    intro x
    change e (((representation p G A).baseChange (ZMod (p ^ n))) g (e.symm x)) =
      torsionRepresentation p G A n g x
    simpa using e.toIntertwiningMap.isIntertwining
      ((representation p G A).baseChange (ZMod (p ^ n))) (torsionRepresentation p G A n) g (e.symm x)
  rw [← he, LinearMap.det_conj]
  exact LinearMap.det_baseChange (representation p G A g)

/-- An exact integral-valued rational Tate determinant specializes to the actual torsion determinant. -/
theorem det_finiteLevelRepresentation_eq_of_rational
    (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) (g : G) (a : ℤ_[p])
    (h : LinearMap.det (rationalRepresentation p G A g) = algebraMap ℤ_[p] ℚ_[p] a) :
    LinearMap.det (torsionRepresentation p G A n g) = PadicInt.toZModPow n a := by
  rw [det_finiteLevelRepresentation p G A hpdiv n g]
  congr 1
  apply Subtype.ext
  exact (det_rationalRepresentation p G A g).symm.trans h

end TateModule
