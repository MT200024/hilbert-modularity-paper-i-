/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.InertiaConjugacy
public import HilbertModularity.Geometry.ProjectiveLine.GenericFundamentalGroup

/-! # Actual affine inertia in the punctured-line fundamental group

The generic arithmetic Galois action sends inertia above a coordinate prime
into the actual finite étale fundamental group. Different choices of the prime
in the algebraic normalization give conjugate subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K]

/-- The image of actual rational-function inertia in the generic finite étale fundamental group. -/
def puncturedAffineInertia (a : K) :
    Subgroup (Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)) :=
  (RatFunc.affineInertia K a).map
    (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K))

variable [CharZero K]

/-- Inertia in the actual punctured-line fundamental group is independent of the
chosen prime above a coordinate up to conjugacy. -/
theorem puncturedAffineInertia_conjugate (a : K) (P : Ideal (RatFunc.affineIntegralClosure K))
    [P.IsPrime] [P.LiesOver (RatFunc.affinePrime K a)] :
    ∃ g : Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K),
      (Ideal.inertia
        (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) P).map
          (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)) =
        (puncturedAffineInertia K a).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := RatFunc.affineInertia_conjugate K a P
  let q := Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)
  refine ⟨q g, ?_⟩
  rw [hg]
  change ((RatFunc.affineInertia K a).map (MulAut.conj g).toMonoidHom).map q =
    ((RatFunc.affineInertia K a).map q).map (MulAut.conj (q g)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro σ
  change q (g * σ * g⁻¹) = q g * q σ * (q g)⁻¹
  simp only [map_mul, map_inv]

end AlgebraicGeometry.ProjectiveLine
