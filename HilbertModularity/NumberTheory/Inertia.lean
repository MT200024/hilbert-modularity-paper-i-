/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-! # Inertia in unramified finite extensions

The inertia group has order equal to the ramification index. Hence an
unramified prime has trivial inertia in a finite Galois extension.
-/

@[expose] public section

namespace Ideal

variable {R S G : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [Module.Flat R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (p : Ideal R) (P : Ideal S) [p.IsPrime] [P.IsPrime] [P.LiesOver p]
  [Algebra.HasSeparableResidueFieldsAt R S p]

include p

/-- An unramified prime has trivial inertia in a finite Galois ring extension. -/
theorem inertia_eq_bot_of_isUnramifiedAt [Algebra.IsUnramifiedAt R P] :
    inertia G P = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [card_inertia_eq_ramificationIdxIn p P,
    ramificationIdxIn_eq_ramificationIdx p P G]
  exact ramificationIdx_eq_one_of_isUnramifiedAt

end Ideal

namespace Ideal

open scoped NumberField

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]

/-- Restriction to a normal subfield sends inertia to inertia at the contracted integer prime. -/
theorem restrictNormal_mem_inertia (P : Ideal (𝓞 M)) (σ : M ≃ₐ[K] M)
    (hσ : σ ∈ inertia (M ≃ₐ[K] M) P) :
    σ.restrictNormal L ∈ inertia (L ≃ₐ[K] L) (P.under (𝓞 L)) := by
  rw [mem_inertia] at hσ ⊢
  intro x
  change algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • x - x) ∈ P
  have he : algebraMap (𝓞 L) (𝓞 M) ((σ.restrictNormal L) • x) =
      σ • algebraMap (𝓞 L) (𝓞 M) x := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ L (x : L)
  rw [map_sub, he]
  exact hσ (algebraMap (𝓞 L) (𝓞 M) x)

end Ideal

namespace Ideal

open scoped NumberField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- Inertia over an intermediate field maps to the intersection with its actual fixing subgroup. -/
theorem map_inertia_restrictScalars (F : IntermediateField K M) (P : Ideal (𝓞 M)) :
    (inertia (M ≃ₐ[F] M) P).map (AlgEquiv.restrictScalarsHom K) =
      inertia (M ≃ₐ[K] M) P ⊓ F.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (mem_inertia.mpr (mem_inertia.mp hτ))
    · apply (IntermediateField.mem_fixingSubgroup_iff F _).mpr
      intro x hx
      exact τ.commutes ⟨x, hx⟩
  · rintro ⟨hσ, hfix⟩
    refine ⟨F.fixingSubgroupEquiv ⟨σ, hfix⟩, ?_, ?_⟩
    · exact (mem_inertia.mpr (mem_inertia.mp hσ))
    · ext x
      rfl

end Ideal
