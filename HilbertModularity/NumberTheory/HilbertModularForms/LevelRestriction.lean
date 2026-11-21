/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteLevel

/-! # Restricting the finite level of a Hilbert cusp form

A form invariant under a compact-open level remains a form at any smaller
compact-open level. Its adelic function, cusp integral, holomorphic models,
and central character are unchanged. This is the level restriction used
before finite-character twisting in [SkinnerWiles, §3, Lemma 3.17].
-/

public noncomputable section

open NumberField

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- Restrict the right-invariance group of a cuspidal adelic function. -/
def AdelicCuspForm.restrictLevel {K K' : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : AdelicCuspForm F K μ)
    (h : K' ≤ K) : AdelicCuspForm F K' μ where
  toFun := φ.toFun
  left_invariant := φ.left_invariant
  right_invariant k hk g := φ.right_invariant k (h hk) g
  cuspidal_integrable := φ.cuspidal_integrable
  cuspidal := φ.cuspidal
  nonzero := φ.nonzero

@[simp]
theorem AdelicCuspForm.restrictLevel_apply {K K' : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : AdelicCuspForm F K μ)
    (h : K' ≤ K) (g : AdelicGL2 F) :
    (φ.restrictLevel h).toFun g = φ.toFun g :=
  (rfl)

/-- Restrict the level while preserving all archimedean weight-two models. -/
def ParallelWeightTwoCuspForm.restrictLevel {K K' : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : ParallelWeightTwoCuspForm F K μ)
    (h : K' ≤ K) : ParallelWeightTwoCuspForm F K' μ where
  toAdelicCuspForm := φ.toAdelicCuspForm.restrictLevel h
  holomorphic_model := φ.holomorphic_model

@[simp]
theorem ParallelWeightTwoCuspForm.restrictLevel_apply
    {K K' : Subgroup (AdelicGL2 F)} {μ : AdditiveQuotientMeasure F}
    (φ : ParallelWeightTwoCuspForm F K μ) (h : K' ≤ K)
    (g : AdelicGL2 F) :
    (φ.restrictLevel h).toFun g = φ.toFun g :=
  (rfl)

/-- Restrict the level without altering the central character. -/
def ParallelWeightTwoCentralForm.restrictLevel
    {K K' : Subgroup (AdelicGL2 F)} {μ : AdditiveQuotientMeasure F}
    (φ : ParallelWeightTwoCentralForm K μ) (h : K' ≤ K) :
    ParallelWeightTwoCentralForm K' μ where
  toParallelWeightTwoCuspForm :=
    φ.toParallelWeightTwoCuspForm.restrictLevel h
  central_character := φ.central_character
  central_law z g := φ.central_law z g

@[simp]
theorem ParallelWeightTwoCentralForm.restrictLevel_apply
    {K K' : Subgroup (AdelicGL2 F)} {μ : AdditiveQuotientMeasure F}
    (φ : ParallelWeightTwoCentralForm K μ) (h : K' ≤ K)
    (g : AdelicGL2 F) :
    (φ.restrictLevel h).toFun g = φ.toFun g :=
  (rfl)

@[simp]
theorem ParallelWeightTwoCentralForm.restrictLevel_central_character
    {K K' : Subgroup (AdelicGL2 F)} {μ : AdditiveQuotientMeasure F}
    (φ : ParallelWeightTwoCentralForm K μ) (h : K' ≤ K) :
    (φ.restrictLevel h).central_character = φ.central_character :=
  (rfl)

/-- Twist a central cusp form at a smaller level on which the character is
trivial. The form still has its original holomorphic weight. -/
def ParallelWeightTwoCentralForm.twistAtSublevel
    {K K' : Subgroup (AdelicGL2 F)} {μ : AdditiveQuotientMeasure F}
    (φ : ParallelWeightTwoCentralForm K μ) (h : K' ≤ K)
    (χ : FiniteIdeleClassCharacter F)
    (hK' : ∀ k ∈ K', χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) : ParallelWeightTwoCentralForm K' μ :=
  (φ.restrictLevel h).twist χ hK' harch

@[simp]
theorem ParallelWeightTwoCentralForm.twistAtSublevel_apply
    {K K' : Subgroup (AdelicGL2 F)} {μ : AdditiveQuotientMeasure F}
    (φ : ParallelWeightTwoCentralForm K μ) (h : K' ≤ K)
    (χ : FiniteIdeleClassCharacter F)
    (hK' : ∀ k ∈ K', χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1)
    (g : AdelicGL2 F) :
    (φ.twistAtSublevel h χ hK' harch).toFun g =
      (χ.onGL2 g : ℂ) * φ.toFun g := by
  simp only [twistAtSublevel, ParallelWeightTwoCentralForm.twist_apply,
    ParallelWeightTwoCentralForm.restrictLevel_apply]

end HilbertModularity.HilbertModularForms
