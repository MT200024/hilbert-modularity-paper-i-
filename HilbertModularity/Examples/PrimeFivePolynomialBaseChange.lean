/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMBlockFactorization
public import HilbertModularity.RepresentationTheory.DualLattice
public import Mathlib.RingTheory.TensorProduct.Free

/-! # Scalar extension of the worked reverse characteristic polynomial

The counted genus-two polynomial is initially over the conductor adic field.
Entrywise base change of a Frobenius matrix preserves its reverse characteristic
polynomial under the coefficient map, so its literal coefficients can be used
in the comparison field.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Examples

/-- Reverse characteristic polynomials commute with entrywise ring maps.
This is the determinant formula and `RingHom.map_det`. -/
theorem charpolyRev_map
    {R S n : Type*} [CommRing R] [CommRing S]
    [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (f : R →+* S) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  let F : R[X] →+* S[X] := Polynomial.mapRingHom f
  let N : Matrix n n R[X] := 1 - (X : R[X]) • M.map C
  have hN : (1 - (X : S[X]) • (M.map f).map C : Matrix n n S[X]) =
      F.mapMatrix N := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [N,
        F,
        Matrix.sub_apply,
        Matrix.smul_apply,
        Matrix.map_apply]
    · simp [N,
        F,
        hij,
        Matrix.sub_apply,
        Matrix.smul_apply,
        Matrix.map_apply]
  change (1 - (X : S[X]) • (M.map f).map C : Matrix n n S[X]).det =
    F (1 - (X : R[X]) • M.map C : Matrix n n R[X]).det
  rw [hN]
  exact (RingHom.map_det F N).symm

/-- Extend a cohomological dual representation to a larger coefficient
field. The basis is extended first, then transported through the canonical
equivariant dual/base-change equivalence; the reverse polynomial is the
coefficient image of the original. -/
theorem dualTate_charpolyRev_baseChange
    {K L G V ι : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation K G V) (g : G)
    (b : Module.Basis ι K (Module.Dual K V)) :
    let e := Representation.dualBaseChangeEquiv L ρ
    let bL := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
    (LinearMap.toMatrix bL bL ((ρ.baseChange L).dual g)).charpolyRev =
      ((LinearMap.toMatrix b b (ρ.dual g)).charpolyRev).map (algebraMap K L) := by
  let e := Representation.dualBaseChangeEquiv L ρ
  let bL := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
  have hm : LinearMap.toMatrix bL bL ((ρ.baseChange L).dual g) =
      LinearMap.toMatrix (Algebra.TensorProduct.basis L b) (Algebra.TensorProduct.basis L b)
        ((ρ.dual.baseChange L) g) :=
    toMatrix_map_representationEquiv e (Algebra.TensorProduct.basis L b) g
  dsimp only
  rw [hm]
  change (LinearMap.toMatrix (Algebra.TensorProduct.basis L b) (Algebra.TensorProduct.basis L b)
      ((ρ.dual g).baseChange L)).charpolyRev = _
  rw [LinearMap.toMatrix_baseChange]
  exact charpolyRev_map (LinearMap.toMatrix b b (ρ.dual g)) (algebraMap K L)

end HilbertModularity.Examples
