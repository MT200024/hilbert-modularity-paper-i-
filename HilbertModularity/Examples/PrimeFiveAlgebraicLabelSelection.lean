/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveComparisonAlgebraicTransport
public import HilbertModularity.Examples.PrimeFiveEulerLabelSelection
public import HilbertModularity.Examples.PrimeFiveAlgebraicRoots
public import HilbertModularity.Examples.PrimeFiveOrientedComparison

/-! # The worked finite-character selector in one algebraic coefficient field

The character value, fixed RM trace and Euler scalar are compared in one
number field before applying its oriented complex embedding. The numeric
factorization and algebraic realization of the RM trace remain explicit
inputs until supplied by the selected special Jacobian.
-/

public noncomputable section

open IsDedekindDomain Polynomial
open scoped NumberField

namespace HilbertModularity.Examples

open _root_.HilbertModularity.Cyclotomic Hypergeometric

attribute [local instance] Ideal.Quotient.field
local instance algebraicSelectorFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance algebraicSelectorElevenFact : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance algebraicSelectorFortyOneFact : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The exact algebraic comparison, factorized selected polynomial and
oriented direct sum force the fixed eleven-prime trace and finite character
value. No numerical trace or character value is assumed. -/
theorem primeFive_algebraicSelector_11
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
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    (t : E') (u : L) (ht : E'.subtype t = u) (b : ℂ)
    (hpoly : (1 - C (c t) * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : ℂ[X]))
    (hpadic : ι (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) =
      (ν g : L) * u) :
    c t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c g = 1 := by
  let νc := primeFiveComplexComparisonCharacter E' χ c
  have hfin := primeFiveComplexComparisonCharacter_finite E' χ c
  have hcomplex := primeFive_complexComparison_of_algebraicRMTrace
    L E' ι hι c hc χ ν hχ g
    (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) t u ht hpadic
  exact primeFive_orientedEulerSelectsLabel_11 P hP e he θ hθ
    νc hfin g (c t) b hpoly hcomplex

/-- The same algebraic selector at forty-one yields the negative square-root
fixed trace and trivial finite comparison value. -/
theorem primeFive_algebraicSelector_41
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
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    (t : E') (u : L) (ht : E'.subtype t = u) (b : ℂ)
    (hpoly : (1 - C (c t) * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : ℂ[X]))
    (hpadic : ι (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) =
      (ν g : L) * u) :
    c t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c g = 1 := by
  let νc := primeFiveComplexComparisonCharacter E' χ c
  have hfin := primeFiveComplexComparisonCharacter_finite E' χ c
  have hcomplex := primeFive_complexComparison_of_algebraicRMTrace
    L E' ι hι c hc χ ν hχ g
    (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) t u ht hpadic
  exact primeFive_orientedEulerSelectsLabel_41 P hP e he θ hθ
    νc hfin g (c t) b hpoly hcomplex

/-- An actual factorization over the chosen p-adic coefficient field
constructs its algebraic fixed trace. The oriented Euler comparison then
selects the first label and forces the same algebraic finite character to
evaluate to one at eleven. -/
theorem primeFive_algebraicSelector_of_padicFactorization_11
    (L : Type*) [Field L] [CharZero L] [Algebra (cyclotomicField 5) L]
    (E' : IntermediateField (cyclotomicField 5) L) [NumberField E']
    (ι : cyclotomicField 5 →+* L)
    (hι : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = ι)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ)
    (hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5))
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 11)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 4)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    (a b : L)
    (hpoly : (1 - C a * X + 11 * X ^ 2) *
      (1 - C b * X + 11 * X ^ 2) =
        (1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 : L[X]))
    (hpadic : ι (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) =
      (ν g : L) * a) :
    ∃ t : E', E'.subtype t = a ∧
      c t = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c g = 1 := by
  obtain ⟨t, ht, hpair⟩ :=
    exists_primeFive_algebraicTrace_11_of_factorization L E' ι hι c hc a b hpoly
  have hcomplex := primeFive_complexComparison_of_algebraicRMTrace
    L E' ι hι c hc χ ν hχ g
    (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) t a ht hpadic
  let νc := primeFiveComplexComparisonCharacter E' χ c
  have hfin := primeFiveComplexComparisonCharacter_finite E' χ c
  have hsum :=
    (primeFive_orientedMcCarthy_eq_normalizedEuler_11 P hP e he θ hθ).trans hcomplex
  obtain ⟨htrace, hvalue⟩ :=
    primeFive_orientedComparison_11 P hP e he θ hθ νc hfin g (c t)
      hpair hsum
  exact ⟨t, ht, htrace, hvalue⟩

/-- The same p-adic factorization route selects the negative-root fixed
trace and finite character value one at forty-one. -/
theorem primeFive_algebraicSelector_of_padicFactorization_41
    (L : Type*) [Field L] [CharZero L] [Algebra (cyclotomicField 5) L]
    (E' : IntermediateField (cyclotomicField 5) L) [NumberField E']
    (ι : cyclotomicField 5 →+* L)
    (hι : E'.subtype.comp (algebraMap (cyclotomicField 5) E') = ι)
    (c : E' →+* ℂ)
    (hc : c.comp (algebraMap (cyclotomicField 5) E') = primeFiveComplexEmbedding)
    (χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField 5) E')
    (ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5) →* Lˣ)
    (hχ : (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField 5))
    (P : Ideal (𝓞 (cyclotomicField 5))) [P.IsMaximal]
    (hP : (5 : 𝓞 (cyclotomicField 5)) ∉ P)
    (e : (𝓞 (cyclotomicField 5) ⧸ P) ≃+* ZMod 41)
    (he : e (Ideal.Quotient.mk P (rootInteger 5)) = 10)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    (a b : L)
    (hpoly : (1 - C a * X + 41 * X ^ 2) *
      (1 - C b * X + 41 * X ^ 2) =
        (1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 : L[X]))
    (hpadic : ι (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) =
      (ν g : L) * a) :
    ∃ t : E', E'.subtype t = a ∧
      c t = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧
      primeFiveComplexComparisonCharacter E' χ c g = 1 := by
  obtain ⟨t, ht, hpair⟩ :=
    exists_primeFive_algebraicTrace_41_of_factorization L E' ι hι c hc a b hpoly
  have hcomplex := primeFive_complexComparison_of_algebraicRMTrace
    L E' ι hι c hc χ ν hχ g
    (normalizedCyclotomicEulerTrace 5 P hP 1 (e.symm 125)) t a ht hpadic
  let νc := primeFiveComplexComparisonCharacter E' χ c
  have hfin := primeFiveComplexComparisonCharacter_finite E' χ c
  have hsum :=
    (primeFive_orientedMcCarthy_eq_normalizedEuler_41 P hP e he θ hθ).trans hcomplex
  obtain ⟨htrace, hvalue⟩ :=
    primeFive_orientedComparison_41 P hP e he θ hθ νc hfin g (c t)
      hpair hsum
  exact ⟨t, ht, htrace, hvalue⟩

end HilbertModularity.Examples
