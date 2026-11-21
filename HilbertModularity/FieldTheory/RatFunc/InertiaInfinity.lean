/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.Reciprocal
public import HilbertModularity.FieldTheory.RatFunc.InertiaConstants
public import HilbertModularity.FieldTheory.Galois.FieldEquiv

/-! # Inertia at infinity through the reciprocal coordinate

A chosen extension of `X ↦ X⁻¹` to the algebraic closure transports inertia
above zero to inertia at infinity. This is a subgroup of the same actual
absolute Galois group and fixes every algebraic constant.
-/

@[expose] public noncomputable section
namespace RatFunc
variable (K : Type*) [Field K]

/-- Inertia at infinity, obtained from the prime at zero in the reciprocal coordinate. -/
def infinityInertia :
    Subgroup (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) :=
  (affineInertia K 0).map
    (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
      (reciprocalAlgEquiv K).toRingEquiv).toMonoidHom

/-- Inertia at infinity acts trivially on all algebraic constants. -/
theorem infinityInertia_fixes_algebraic_constants
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
    (hg : g ∈ infinityInertia K) (z : AlgebraicClosure (RatFunc K))
    (hz : IsIntegral K z) : g z = z := by
  let jRing := IsAlgClosure.equivOfEquiv (AlgebraicClosure (RatFunc K))
    (AlgebraicClosure (RatFunc K)) (reciprocalAlgEquiv K).toRingEquiv
  let j : AlgebraicClosure (RatFunc K) ≃ₐ[K] AlgebraicClosure (RatFunc K) :=
    AlgEquiv.ofRingEquiv (f := jRing) (by
      intro a
      simp only [jRing, IsScalarTower.algebraMap_apply K (RatFunc K)
        (AlgebraicClosure (RatFunc K)), IsAlgClosure.equivOfEquiv_algebraMap,
        AlgEquiv.coe_ringEquiv, AlgEquiv.commutes])
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
  change j (h (j.symm z)) = z
  rw [affineInertia_fixes_algebraic_constants K 0 h hh (j.symm z) (hz.map j.symm)]
  exact j.apply_symm_apply z

end RatFunc
