/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationProper
public import HilbertModularity.NumberTheory.Cyclotomic
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # A common algebraic closure for the proper Euler realization

The geometric proper fibre was constructed over `AlgebraicClosure F_N`, whereas
the arithmetic specialization and Frobenius APIs use the fixed `Qbar`.  A
chosen equivalence over the actual cyclotomic field transports the restricted
proper cohomology action to the same absolute Galois group.  This changes only
the model of the algebraic closure; it supplies no descent to the real field.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N]

/-- A chosen identification of the two algebraic closures over the actual
cyclotomic field. -/
def cyclotomicEulerClosureEquiv :
    AlgebraicClosure (cyclotomicField N) ≃+* Qbar := by
  letI : IsAlgClosure (cyclotomicField N) Qbar :=
    ⟨inferInstance, inferInstance⟩
  exact IsAlgClosure.equivOfEquiv (AlgebraicClosure (cyclotomicField N)) Qbar
    (RingEquiv.refl (cyclotomicField N))

/-- Conjugation transports automorphisms of the fixed `Qbar` to the closure
used by the geometric proper fibre. -/
def cyclotomicEulerClosureGaloisHom :
    (Qbar ≃ₐ[cyclotomicField N] Qbar) →*
      (AlgebraicClosure (cyclotomicField N) ≃ₐ[cyclotomicField N]
        AlgebraicClosure (cyclotomicField N)) where
  toFun g :=
    AlgEquiv.ofRingEquiv
      (f := ((cyclotomicEulerClosureEquiv N).trans g.toRingEquiv).trans
        (cyclotomicEulerClosureEquiv N).symm) (by
        intro a
        simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
        apply (cyclotomicEulerClosureEquiv N).injective
        simp only [RingEquiv.apply_symm_apply, cyclotomicEulerClosureEquiv,
          IsAlgClosure.equivOfEquiv_algebraMap, RingEquiv.refl_apply]
        exact g.commutes a)
  map_one' := by
    apply AlgEquiv.ext
    intro a
    simp [cyclotomicEulerClosureEquiv]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro a
    change (cyclotomicEulerClosureEquiv N).symm
        (g (h (cyclotomicEulerClosureEquiv N a))) =
      (cyclotomicEulerClosureEquiv N).symm
        (g (cyclotomicEulerClosureEquiv N
          ((cyclotomicEulerClosureEquiv N).symm
            (h (cyclotomicEulerClosureEquiv N a)))))
    rw [RingEquiv.apply_symm_apply]

/-- The transported action is literal conjugation on the two algebraic
closures. -/
theorem cyclotomicEulerClosureGaloisHom_apply
    (g : Qbar ≃ₐ[cyclotomicField N] Qbar)
    (a : AlgebraicClosure (cyclotomicField N)) :
    cyclotomicEulerClosureGaloisHom N g a =
      (cyclotomicEulerClosureEquiv N).symm
        (g (cyclotomicEulerClosureEquiv N a)) :=
  (rfl)

/-- The fixed-character proper Euler cohomology, with its Galois action
transported to the common algebraic closure `Qbar`. This remains a
representation of `G_{F_N}`; descent to `G_{K_N}` is a separate input. -/
def properPrimitiveQbarGaloisRepresentation (m : ℕ)
    (𝒞 : SmoothProperEulerFamily N m)
    (t : cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L) :
    Representation L (Qbar ≃ₐ[cyclotomicField N] Qbar)
      (properPrimitiveGaloisSubrepresentation N m 𝒞 t ht h1t ℓ L ι).toSubmodule :=
  (properPrimitiveGaloisRepresentation N m 𝒞 t ht h1t ℓ L ι).comp
    (cyclotomicEulerClosureGaloisHom N)

/-- Restricting a `Qbar` automorphism acts on the literal proper Euler
projector image through the chosen closure identification. -/
theorem properPrimitiveQbarGaloisRepresentation_apply (m : ℕ)
    (𝒞 : SmoothProperEulerFamily N m)
    (t : cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (g : Qbar ≃ₐ[cyclotomicField N] Qbar)
    (v : (properPrimitiveGaloisSubrepresentation N m 𝒞 t ht h1t ℓ L ι).toSubmodule) :
    properPrimitiveQbarGaloisRepresentation N m 𝒞 t ht h1t ℓ L ι g v =
      properPrimitiveGaloisRepresentation N m 𝒞 t ht h1t ℓ L ι
        (cyclotomicEulerClosureGaloisHom N g) v :=
  (rfl)

end HilbertModularity.Hypergeometric
