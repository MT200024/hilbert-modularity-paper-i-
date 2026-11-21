/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.Basic

/-! # Relabelling integral real multiplication

An injective self-map of the integers of a number field is an automorphism.
Consequently, when the full endomorphism ring is identified with these integers,
any injective integral action differs from that identification by a relabelling.
This is the algebraic step in applying [DarmonMestre, Proposition 2.1] to a
specified real-multiplication action on the generic Jacobian.
-/

public section

namespace NumberField.RingOfIntegers

/-- An injective endomorphism of the integers of a number field is bijective:
extend it to the fraction field and restrict the inverse field automorphism. -/
theorem bijective_of_injective {K : Type*} [Field K] [NumberField K]
    (f : 𝓞 K →+* 𝓞 K) (hf : Function.Injective f) : Function.Bijective f := by
  let g : 𝓞 K →+* K := (algebraMap (𝓞 K) K).comp f
  have hg : Function.Injective g :=
    (IsFractionRing.injective (𝓞 K) K).comp hf
  let e : K →+* K := IsFractionRing.lift hg
  let a : K ≃+* K := RingEquiv.ofBijective e e.toRatAlgHom.bijective
  have ha (x : 𝓞 K) : mapRingEquiv a x = f x := by
    apply ext
    exact IsFractionRing.lift_algebraMap hg x
  exact ⟨hf, fun y => by
    obtain ⟨x, hx⟩ := (mapRingEquiv a).surjective y
    exact ⟨x, (ha x).symm.trans hx⟩⟩

/-- A specified faithful integral action on a ring already identified with the
full ring of integers differs from that identification by an automorphism. -/
theorem exists_equiv_of_injective {K A : Type*} [Field K] [NumberField K] [Ring A]
    (e : 𝓞 K ≃+* A) (f : 𝓞 K →+* A) (hf : Function.Injective f) :
    ∃ σ : 𝓞 K ≃+* 𝓞 K, ∀ x, f x = e (σ x) := by
  let g : 𝓞 K →+* 𝓞 K := e.symm.toRingHom.comp f
  let σ := RingEquiv.ofBijective g (bijective_of_injective g (e.symm.injective.comp hf))
  exact ⟨σ, fun x => (e.apply_symm_apply (f x)).symm⟩

end NumberField.RingOfIntegers
