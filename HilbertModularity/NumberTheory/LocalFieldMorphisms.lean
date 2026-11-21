/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Continuous morphisms of native local-field integer rings

Compactness of the integer ring forces a continuous field homomorphism to
preserve integrality: the powers of an integral element have bounded image.
This supplies the integral coefficient conjugations used in
[TripathiGoswami, ramified coefficient labels].
-/

@[expose] public noncomputable section
open scoped ValuativeRel
namespace IsNonarchimedeanLocalField
variable {K L : Type*} [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
  [UniformSpace K] [UniformSpace L] [IsUniformAddGroup K] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]

omit [IsUniformAddGroup K] in
/-- A continuous homomorphism of local fields preserves the native valuation rings. -/
theorem map_mem_integer_of_continuous (f : K →+* L) (hf : Continuous f)
    {x : K} (hx : x ∈ 𝒪[K]) : f x ∈ 𝒪[L] := by
  let : (Valued.v (R := L) (Γ₀ := ValuativeRel.ValueGroupWithZero L)).RankOne :=
    Valuation.RankOne.ofRankLeOneStruct ValuativeRel.IsRankLeOne.nonempty.some
  let : NormedField L := Valued.toNormedField L (ValuativeRel.ValueGroupWithZero L)
  have hc : IsCompact (Set.range (fun a : 𝒪[K] => f (a : K))) :=
    isCompact_range (hf.comp continuous_subtype_val)
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  change ValuativeRel.valuation L (f x) ≤ 1
  apply Valued.toNormedField.norm_le_one_iff.mp
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (lt_of_not_ge h)
  have hb := hB (f x ^ n) ⟨(⟨x, hx⟩ : 𝒪[K]) ^ n, by simp⟩
  rw [norm_pow] at hb
  exact hn.not_ge hb

/-- Restriction of a continuous field homomorphism to the actual integer rings. -/
def integerMap (f : K →+* L) (hf : Continuous f) : 𝒪[K] →+* 𝒪[L] :=
  (f.comp (𝒪[K]).subtype).codRestrict _ fun a => map_mem_integer_of_continuous f hf a.property

omit [IsUniformAddGroup K] in
/-- The induced integer map retains the original underlying field map. -/
@[simp] theorem coe_integerMap (f : K →+* L) (hf : Continuous f) (a : 𝒪[K]) :
    (integerMap f hf a : L) = f (a : K) := rfl

omit [IsUniformAddGroup K] in
/-- The induced integer-ring map is continuous for the native subspace topologies. -/
theorem continuous_integerMap (f : K →+* L) (hf : Continuous f) : Continuous (integerMap f hf) :=
  (hf.comp continuous_subtype_val).subtype_mk _

/-- A bicontinuous field isomorphism restricts to the native integer rings. -/
def integerEquiv (e : K ≃+* L) (he : Continuous e) (hei : Continuous e.symm) : 𝒪[K] ≃+* 𝒪[L] :=
  { integerMap e.toRingHom he with
    invFun := integerMap e.symm.toRingHom hei
    left_inv := fun a => Subtype.ext (e.symm_apply_apply a)
    right_inv := fun a => Subtype.ext (e.apply_symm_apply a) }

/-- The native integer-ring equivalence acts by the original field isomorphism. -/
@[simp] theorem coe_integerEquiv (e : K ≃+* L) (he : Continuous e) (hei : Continuous e.symm)
    (a : 𝒪[K]) : (integerEquiv e he hei a : L) = e (a : K) := rfl

end IsNonarchimedeanLocalField
