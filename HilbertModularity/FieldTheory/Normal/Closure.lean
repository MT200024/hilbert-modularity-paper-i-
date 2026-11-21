/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.Normal.Closure

/-! # Splitting over fields containing a normal closure -/

@[expose] public noncomputable section

namespace IntermediateField
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [Normal k Ω]
  (F E : IntermediateField k Ω)

/-- Containing the normal closure supplies all roots of the minimal polynomials of the smaller field. -/
theorem splits_minpoly_of_normalClosure_le (h : normalClosure k F Ω ≤ E) (x : F) :
    ((minpoly k x).map (algebraMap k E)).Splits := by
  have : Nonempty (F →ₐ[k] Ω) := ⟨F.val⟩
  have hs := IsNormalClosure.splits (F := k) (K := F) (L := normalClosure k F Ω) x
  have hi : (IntermediateField.inclusion h).toRingHom.comp
      (algebraMap k (normalClosure k F Ω)) = algebraMap k E :=
    (IntermediateField.inclusion h).comp_algebraMap
  simpa only [Polynomial.map_map, hi] using hs.map (IntermediateField.inclusion h).toRingHom

end IntermediateField

