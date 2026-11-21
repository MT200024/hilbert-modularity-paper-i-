/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.CuspInertia
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # A common orientation for the three cusp generators

[DarmonFibres, §1, printed p. 2] fixes one compatible system of primitive
roots of unity before defining the three local monodromies. The uniformizers
at zero, one and infinity are respectively `X`, `X - 1` and `X⁻¹`.
This records that normalization on the actual rational-function Galois group;
it does not assert a product relation or generation by the selected loops.
-/

public section

namespace AlgebraicGeometry.ProjectiveLine

variable (K : Type*) [Field K]

/-- Three inertia generators have the same orientation when their actions on
roots of the local parameters use one compatible system of primitive roots.
Membership in the relevant conjugates of inertia is a separate hypothesis. -/
def HasCommonCuspOrientation
    (γ : Fin 3 → AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K]
      AlgebraicClosure (RatFunc K))
    (ζ : ℕ → AlgebraicClosure (RatFunc K)) : Prop :=
  (∀ n : ℕ, 0 < n → IsPrimitiveRoot (ζ n) n) ∧
  (∀ n m : ℕ, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧
  ∀ (i : Fin 3) (n : ℕ), 0 < n →
    ∀ r : AlgebraicClosure (RatFunc K),
      r ^ n = algebraMap (RatFunc K) _
        (![RatFunc.X, RatFunc.X - 1, RatFunc.X⁻¹] i) →
      γ i r = ζ n * r

end AlgebraicGeometry.ProjectiveLine
