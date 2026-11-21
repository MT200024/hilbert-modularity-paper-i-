/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.PointedAutomorphism
public import HilbertModularity.Geometry.ProjectiveInvolution
public import Mathlib.Tactic.NormNum

/-! # The actual fundamental-group action of the parameter complement

For the cusp comparison in [TripathiGoswami, lem:involution], the parameter `1/2` is fixed by the actual automorphism `t ↦ 1 - t` of the
punctured projective line. Its pointed fundamental-group automorphism fixes
all arithmetic loops. Identification of its geometric cusp action remains
separate from this construction.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

universe u
variable (K : Type u) [Field K] [CharZero K]

/-- The canonical rational base parameter fixed by the complement automorphism. -/
def midpointParameter : Parameter K := ⟨1 / 2, by norm_num⟩

/-- The complement fixes the midpoint parameter. -/
@[simp]
theorem complement_midpointParameter :
    complementParameter K (midpointParameter K) = midpointParameter K := by
  apply Subtype.ext
  change 1 - (1 : K) / 2 = 1 / 2
  norm_num

/-- The actual complement scheme morphism fixes the midpoint section. -/
theorem puncturedPoint_midpoint_complement :
    puncturedPoint K (midpointParameter K) ≫ (puncturedComplementIso K).hom =
      puncturedPoint K (midpointParameter K) := by
  rw [puncturedPoint_complement, complement_midpointParameter]

/-- The actual parameter complement acts continuously on the pointed fundamental group. -/
def complementFundamentalAutomorphism :
    Scheme.etaleFundamentalGroup K (puncturedPoint K (midpointParameter K)) ≃ₜ*
      Scheme.etaleFundamentalGroup K (puncturedPoint K (midpointParameter K)) :=
  Scheme.etaleFundamentalGroupPointedAutomorphism K (puncturedComplementIso K)
    (puncturedPoint K (midpointParameter K)) (puncturedPoint_midpoint_complement K)

/-- The complement fundamental-group automorphism fixes all arithmetic loops at the midpoint. -/
theorem complementFundamentalAutomorphism_galois
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Scheme.etaleFundamentalGroupPointedAutomorphism K (puncturedComplementIso K)
      (puncturedPoint K (midpointParameter K)) (puncturedPoint_midpoint_complement K)
      (Scheme.galoisToEtaleFundamentalGroup K (puncturedPoint K (midpointParameter K)) g) =
        Scheme.galoisToEtaleFundamentalGroup K (puncturedPoint K (midpointParameter K)) g :=
  Scheme.etaleFundamentalGroupPointedAutomorphism_galois K (puncturedComplementIso K)
    (puncturedPoint K (midpointParameter K)) (puncturedPoint_midpoint_complement K) g

end AlgebraicGeometry.ProjectiveLine
