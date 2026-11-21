/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComparisonCharacterComplex

/-! # Transporting the chosen finite comparison into the complex label

The chosen p-adic character and its complex realization are images of one
finite algebraic character. When the fixed RM trace is represented in the
same algebraic coefficient field, the p-adic Euler comparison pulls back to
that field and hence holds under the exact oriented complex embedding.
-/

public noncomputable section

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic

local instance algebraicTransportFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Injectivity of the common algebraic coefficient field transports the
same-character p-adic comparison to the oriented complex label. The input
`t` is the algebraic realization of the *fixed* RM trace, rather than a
chosen numerical root. -/
theorem primeFive_complexComparison_of_algebraicRMTrace
    (L : Type*) [Field L] [Algebra (cyclotomicField 5) L]
    (E' : IntermediateField (cyclotomicField 5) L) [NumberField E']
    (ι : cyclotomicField 5 →+* L)
    (hι : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = ι)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ)
    (hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5))
    (a : cyclotomicField 5) (t : E') (u : L)
    (ht : E'.subtype t = u)
    (heq : ι a = (ν g : L) * u) :
    primeFiveComplexEmbedding a =
      (primeFiveComplexComparisonCharacter E' χ c g : ℂ) * c t := by
  have hχg : (ν g : L) = E'.subtype (χ.toMonoidHom g : E') := by
    have h := congrArg
      (fun f : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ =>
        (f g : L)) hχ
    exact h.symm
  have ha : ι a = E'.subtype (algebraMap (cyclotomicField 5) E' a) := by
    have h := congrArg (fun f : cyclotomicField 5 →+* L => f a) hι
    exact h.symm
  have hpull : algebraMap (cyclotomicField 5) E' a =
      (χ.toMonoidHom g : E') * t := by
    apply E'.subtype.injective
    calc
      E'.subtype (algebraMap (cyclotomicField 5) E' a) = ι a := ha.symm
      _ = (ν g : L) * u := heq
      _ = E'.subtype (χ.toMonoidHom g : E') * E'.subtype t := by rw [hχg, ht]
      _ = E'.subtype ((χ.toMonoidHom g : E') * t) := (map_mul E'.subtype _ _).symm
  have hcval : primeFiveComplexEmbedding a = c (algebraMap (cyclotomicField 5) E' a) :=
    (congrArg (fun f : cyclotomicField 5 →+* ℂ => f a) hc).symm
  calc
    primeFiveComplexEmbedding a = c (algebraMap (cyclotomicField 5) E' a) := hcval
    _ = c ((χ.toMonoidHom g : E') * t) := congrArg c hpull
    _ = (primeFiveComplexComparisonCharacter E' χ c g : ℂ) * c t := by
      rw [map_mul, primeFiveComplexComparisonCharacter_apply]

end HilbertModularity.Examples
