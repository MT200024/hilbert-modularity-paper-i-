/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GoodPrimeEigenform
public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter

/-! # Finite character reciprocity and normalized eigenform twists

Global reciprocity is used once, with arithmetic Frobenius. Inverting the
resulting idele character gives the geometric-Frobenius convention of the
cohomological comparison in [TripathiGoswami, §3]. The actual cusp form is
then twisted using the existing finite-twist construction.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- An idele realization with arithmetic Artin normalization. The coefficient
embedding is fixed, and the prime formula holds for every normalized prime
coset and every choice of a prime of the algebraic closure above it. -/
structure ArithmeticIdeleRealization
    (χ : FiniteAlgebraicGaloisCharacter F E) (ι : E →+* ℂ)
    extends FiniteIdeleClassCharacter F where
  trivial_positive_infinity : ∀ g : AdelicGL2 F,
    (∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) →
    (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
    toFiniteIdeleClassCharacter.onGL2 g = 1
  arithmetic_frobenius : ∀ {level : FiniteLevel F}
    (q : HeightOneSpectrum (𝓞 F)), q ∉ χ.bad →
    ∀ (d : PrimeHeckeDatum level q)
    (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
    (toFiniteIdeleClassCharacter.onGL2 d.element : ℂ) =
      ι (χ.toMonoidHom
        (NumberField.arithmeticFrobenius F (AlgebraicClosure F) P Q) : E)

/-- Finite-character global class field theory, in arithmetic normalization.

The character has finite image, continuous realizations at the coefficient
completions, and trivial inertia outside `χ.bad`. Thus its open kernel cuts
out a finite abelian extension. Compose its character with the global Artin
map and the specified complex embedding. [MilneCFT, V Proposition 5.2 and
Theorem 5.3, pp.178–179] supply continuity, local compatibility and principal
idele triviality. [MilneCFT, I Theorem 1.1(a), p.20] gives the displayed
uniformizer/arithmetic-Frobenius formula. [MilneCFT, V Remark 5.7(a), p.179]
gives triviality on positive real and complex infinite components. The prime
datum has determinant a uniformizer at `q` and one at all other places.
No de Rham algebraization or modularity assertion is included. -/
theorem nonempty_arithmeticIdeleRealization
    (χ : FiniteAlgebraicGaloisCharacter F E) (ι : E →+* ℂ) :
    Nonempty (ArithmeticIdeleRealization χ ι) := by
  sorry

namespace ArithmeticIdeleRealization

variable {χ : FiniteAlgebraicGaloisCharacter F E} {ι : E →+* ℂ}

/-- Inverse Artin normalization for geometric-Frobenius traces. -/
def geometricCharacter (r : ArithmeticIdeleRealization χ ι) :
    FiniteIdeleClassCharacter F where
  toHom := r.toHom⁻¹
  continuous := r.continuous.inv
  finite_range := by
    apply (r.finite_range.image Inv.inv).subset
    rintro _ ⟨a, rfl⟩
    exact ⟨r.toHom a, ⟨a, rfl⟩, rfl⟩
  trivial_diagonal γ := by
    change (r.toHom (adelicDeterminant F (rationalDiagonal F γ)))⁻¹ = 1
    rw [r.trivial_diagonal, inv_one]

@[simp]
theorem geometricCharacter_onGL2
    (r : ArithmeticIdeleRealization χ ι) (g : AdelicGL2 F) :
    r.geometricCharacter.onGL2 g =
      (r.toFiniteIdeleClassCharacter.onGL2 g)⁻¹ := by
  simp only [FiniteIdeleClassCharacter.onGL2_apply, geometricCharacter,
    MonoidHom.inv_apply]

/-- The inverse character still kills the connected infinite component,
so the finite twist preserves parallel weight two. -/
theorem geometricCharacter_trivial_positive_infinity
    (r : ArithmeticIdeleRealization χ ι) (g : AdelicGL2 F)
    (hf : ∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
    (hpos : ∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) :
    r.geometricCharacter.onGL2 g = 1 := by
  rw [geometricCharacter_onGL2]
  rw [r.trivial_positive_infinity g hf hpos, inv_one]

/-- Inversion converts the arithmetic Artin formula to exactly the chosen
geometric-Frobenius lift, with no coefficient relabelling. -/
theorem geometricCharacter_frobenius
    (r : ArithmeticIdeleRealization χ ι) {level : FiniteLevel F}
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ χ.bad)
    (d : PrimeHeckeDatum level q)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (r.geometricCharacter.onGL2 d.element : ℂ) =
      ι (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) := by
  rw [geometricCharacter_onGL2]
  rw [Units.val_inv_eq_inv_val, r.arithmetic_frobenius q hq d P hP Q]
  simp [NumberField.geometricFrobenius]

/-- The actual weight-two cusp eigenform twisted by the geometric character.
The supplied level must kill the character; choosing or shrinking that level
is a separate automorphic application. -/
abbrev twist (r : ArithmeticIdeleRealization χ ι) {level : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform level μ)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1) :
    GoodPrimeEigenform level μ :=
  φ.twist r.geometricCharacter hK r.geometricCharacter_trivial_positive_infinity

@[simp]
theorem twist_bad (r : ArithmeticIdeleRealization χ ι) {level : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform level μ)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1) :
    (r.twist φ hK).bad = φ.bad := by
  simp only [twist, GoodPrimeEigenform.twist_bad]

/-- The normalized finite twist has the original Hecke eigenvalue multiplied
by the algebraic Galois character at geometric Frobenius. This is a deduction
from reciprocity and the cusp-form twist construction, not an admitted
automorphic or Galois comparison. -/
theorem twist_hecke_value
    (r : ArithmeticIdeleRealization χ ι) {level : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform level μ)
    (hK : ∀ k ∈ level.subgroup, r.geometricCharacter.onGL2 k = 1)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.bad) (hχ : q ∉ χ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (r.twist φ hK).hecke_value q (by simpa only [twist_bad] using hq) =
      ι (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) *
          φ.hecke_value q hq := by
  rw [GoodPrimeEigenform.twist_hecke_value]
  rw [r.geometricCharacter_frobenius q hχ (φ.hecke_data q hq) P hP Q]

end ArithmeticIdeleRealization

end HilbertModularity.HilbertModularForms
