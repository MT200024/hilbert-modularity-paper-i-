/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.Inertia
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Rational-function inertia fixes algebraic constants

The difference between an algebraic constant and its inertia translate lies
in the chosen prime. If nonzero, this difference has an integral inverse, so
it cannot belong to that prime.
-/

@[expose] public noncomputable section
namespace RatFunc
variable (K : Type*) [Field K]

/-- Actual affine inertia fixes every constant algebraic over the ground field. -/
theorem affineInertia_fixes_algebraic_constants (a : K)
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
    (hg : g ∈ affineInertia K a) (z : AlgebraicClosure (RatFunc K))
    (hz : IsIntegral K z) : g z = z := by
  apply sub_eq_zero.mp
  by_contra hn
  have hd : IsIntegral K (g z - z) := (hz.map (g.restrictScalars K)).sub hz
  let w : affineIntegralClosure K := ⟨g z - z, hd.tower_top⟩
  let v : affineIntegralClosure K := ⟨(g z - z)⁻¹, hd.inv.tower_top⟩
  have hw : w ∈ affinePrimeAbove K a :=
    (mem_affineInertia K a g).mp hg ⟨z, hz.tower_top⟩
  have huv : w * v = 1 := Subtype.ext (mul_inv_cancel₀ hn)
  have hu : IsUnit w := isUnit_iff_exists_inv.mpr ⟨v, huv⟩
  exact (affinePrimeAbove K a).notMem_of_isUnit hu hw

end RatFunc
