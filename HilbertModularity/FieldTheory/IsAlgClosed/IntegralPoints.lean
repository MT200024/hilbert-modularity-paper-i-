/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Integral algebra points under extension of an algebraically closed field

An integral algebra over an algebraically closed field acquires no new points
in a larger field. The factorization uses its actual image algebra.
-/

@[expose] public noncomputable section
namespace AlgHom

variable (K A Ω : Type*) [Field K] [IsAlgClosed K] [CommRing A]
  [Algebra K A] [Algebra.IsIntegral K A] [Field Ω] [Algebra K Ω]

/-- Extending the codomain of points of an integral algebra over an algebraically
closed field is bijective. -/
theorem bijective_comp_algebraMap_of_isAlgClosed :
    Function.Bijective (fun f : A →ₐ[K] K => (Algebra.ofId K Ω).comp f) := by
  constructor
  · intro f g h
    ext a
    apply (algebraMap K Ω).injective
    exact congrArg (fun φ : A →ₐ[K] Ω => φ a) h
  · intro φ
    let : Algebra.IsIntegral K φ.range :=
      Algebra.IsIntegral.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    let e : K ≃ₐ[K] φ.range := AlgEquiv.ofBijective (Algebra.ofId K φ.range)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨e.symm.toAlgHom.comp φ.rangeRestrict, ?_⟩
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (φ.rangeRestrict a))

/-- Points of an integral algebra are unchanged by an extension of an algebraically
closed coefficient field. -/
def codomainExtensionEquivOfIsAlgClosed : (A →ₐ[K] K) ≃ (A →ₐ[K] Ω) :=
  Equiv.ofBijective (fun f => (Algebra.ofId K Ω).comp f)
    (bijective_comp_algebraMap_of_isAlgClosed K A Ω)

end AlgHom

namespace IsAlgClosed

variable {K Ω : Type*} [Field K] [IsAlgClosed K] [Field Ω] [Algebra K Ω]

/-- An integral element of an extension of an algebraically closed field already
belongs to that field. -/
theorem exists_algebraMap_eq_of_isIntegral {x : Ω} (hx : IsIntegral K x) :
    ∃ c : K, algebraMap K Ω c = x := by
  let F := IntermediateField.adjoin K ({x} : Set Ω)
  let : FiniteDimensional K F := IntermediateField.adjoin.finiteDimensional hx
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := F)).surjective
    (IntermediateField.AdjoinSimple.gen K x)
  exact ⟨c, congrArg (fun z : F => (z : Ω)) hc⟩

end IsAlgClosed

namespace AlgHom
variable (k A Ω Ω' : Type*) [Field k] [CommRing A] [Algebra k A]
  [Algebra.IsIntegral k A] [Field Ω] [IsAlgClosed Ω] [Field Ω']
  [Algebra k Ω] [Algebra k Ω'] [Algebra Ω Ω'] [IsScalarTower k Ω Ω']

/-- Enlarging an algebraically closed geometric field does not change the points
of an integral algebra over its original ground field. -/
theorem bijective_comp_of_isAlgClosed :
    Function.Bijective (fun f : A →ₐ[k] Ω => (IsScalarTower.toAlgHom k Ω Ω').comp f) := by
  let j : Ω →ₐ[k] Ω' := IsScalarTower.toAlgHom k Ω Ω'
  constructor
  · intro f g h
    ext a
    apply j.injective
    exact congrArg (fun φ : A →ₐ[k] Ω' => φ a) h
  · intro φ
    have hφ (a : A) : φ a ∈ j.range := by
      have hi : IsIntegral Ω (φ a) :=
        ((Algebra.IsIntegral.isIntegral a : IsIntegral k a).map φ).tower_top
      exact IsAlgClosed.exists_algebraMap_eq_of_isIntegral hi
    let e : Ω ≃ₐ[k] j.range := AlgEquiv.ofInjectiveField j
    refine ⟨e.symm.toAlgHom.comp (φ.codRestrict j.range hφ), ?_⟩
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict j.range hφ a))

end AlgHom
