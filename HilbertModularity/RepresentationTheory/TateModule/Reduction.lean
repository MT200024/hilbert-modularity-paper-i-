/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Reduction
public import HilbertModularity.RepresentationTheory.TateModule
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Equivariant reduction of the actual Tate module

The finite torsion action is constructed on the actual torsion subgroup.
The scalar-reduction equivalence intertwines this action with the reduction of
the compatible-family Tate representation, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

attribute [local instance] torsionCoefficientAlgebra torsionCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (G A : Type*) [Monoid G] [AddCommGroup A]
  [DistribMulAction G A]

/-- The actual action on finite torsion, over its natural finite coefficient ring. -/
def torsionRepresentation (n : ℕ) : Representation (ZMod (p ^ n)) G (Torsion p A n) where
  toFun g :=
    { __ := torsionMapAddHom p (DistribSMul.toAddMonoidHom A g) n
      map_smul' r x := ZMod.map_smul (torsionMapAddHom p (DistribSMul.toAddMonoidHom A g) n) r x }
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact one_smul G (x : A)
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact mul_smul g h (x : A)

omit [Fact p.Prime] in
@[simp]
theorem torsionRepresentation_apply (n : ℕ) (g : G) (x : Torsion p A n) :
    (torsionRepresentation p G A n g x : A) = g • (x : A) := rfl

/-- Reduction of the actual covariant Tate action is the actual action on `p`-torsion. -/
def residualRepresentationEquiv (hpdiv : Function.Surjective (fun a : A => p • a)) :
    ((representation p G A).baseChange (ZMod (p ^ 1))).Equiv (torsionRepresentation p G A 1) :=
  .mk (residualEquiv p A hpdiv) (by
    intro g
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    | tmul a x =>
      change residualEquiv p A hpdiv (a ⊗ₜ[ℤ_[p]] representation p G A g x) =
        torsionRepresentation p G A 1 g (residualEquiv p A hpdiv (a ⊗ₜ[ℤ_[p]] x))
      rw [residualEquiv_tmul, residualEquiv_tmul, map_smul]
      rfl)

/-- The equivariant residual identification evaluates the original compatible family at level one. -/
@[simp]
theorem residualRepresentationEquiv_tmul
    (hpdiv : Function.Surjective (fun a : A => p • a))
    (a : ZMod (p ^ 1)) (x : integral p A) :
    residualRepresentationEquiv p G A hpdiv (a ⊗ₜ[ℤ_[p]] x) =
      a • projection p A 1 x := rfl

section Determinant

variable [Module.Finite ℤ_[p] (integral p A)]

/-- The actual rational Tate determinant is the image of its actual integral determinant. -/
theorem det_rationalRepresentation (g : G) :
    LinearMap.det (rationalRepresentation p G A g) =
      algebraMap ℤ_[p] ℚ_[p] (LinearMap.det (representation p G A g)) :=
  LinearMap.det_baseChange (representation p G A g)

/-- The determinant on actual geometric torsion is the residual image of the integral Tate determinant. -/
theorem det_torsionRepresentation
    (hpdiv : Function.Surjective (fun a : A => p • a)) (g : G) :
    LinearMap.det (torsionRepresentation p G A 1 g) =
      PadicInt.toZModPow 1 (LinearMap.det (representation p G A g)) := by
  let e := residualRepresentationEquiv p G A hpdiv
  have he : e.toLinearEquiv.toLinearMap ∘ₗ
      ((representation p G A).baseChange (ZMod (p ^ 1))) g ∘ₗ
        e.toLinearEquiv.symm.toLinearMap = torsionRepresentation p G A 1 g := by
    apply LinearMap.ext
    intro x
    change e (((representation p G A).baseChange (ZMod (p ^ 1))) g (e.symm x)) =
      torsionRepresentation p G A 1 g x
    simpa using e.toIntertwiningMap.isIntertwining
      ((representation p G A).baseChange (ZMod (p ^ 1))) (torsionRepresentation p G A 1) g (e.symm x)
  rw [← he, LinearMap.det_conj]
  exact LinearMap.det_baseChange (representation p G A g)

/-- An exact integral-valued rational Tate determinant specializes to the actual torsion determinant. -/
theorem det_torsionRepresentation_eq_of_rational
    (hpdiv : Function.Surjective (fun a : A => p • a)) (g : G) (a : ℤ_[p])
    (h : LinearMap.det (rationalRepresentation p G A g) = algebraMap ℤ_[p] ℚ_[p] a) :
    LinearMap.det (torsionRepresentation p G A 1 g) = PadicInt.toZModPow 1 a := by
  rw [det_torsionRepresentation p G A hpdiv g]
  congr 1
  apply Subtype.ext
  exact (det_rationalRepresentation p G A g).symm.trans h

end Determinant

variable [TopologicalSpace A] [TopologicalSpace G] [ContinuousSMul G A]

omit [Fact p.Prime] in
/-- Continuity of the point action gives continuity on each finite torsion vector. -/
theorem continuous_torsionRepresentation (n : ℕ) (x : Torsion p A n) :
    Continuous (fun g => torsionRepresentation p G A n g x) :=
  Continuous.subtype_mk (continuous_id.smul continuous_const) _

end TateModule
