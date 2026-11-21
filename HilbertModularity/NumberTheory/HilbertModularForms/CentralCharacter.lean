/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.Eigenforms

/-! # Central characters of parallel weight two cusp forms

The center acts through scalar adelic matrices. Recording its character on the
actual adelic function supplies the central-character normalization needed
when the determinant of a cohomological Galois realization is compared with
Hecke data. See [SkinnerWiles, §4.5, Theorem A].
-/

public noncomputable section

open NumberField

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- A weight-two Hilbert cusp form with an actual adelic central character. -/
structure ParallelWeightTwoCentralForm (K : Subgroup (AdelicGL2 F))
    (μ : AdditiveQuotientMeasure F) extends ParallelWeightTwoCuspForm F K μ where
  central_character : (AdeleRing F)ˣ →* ℂˣ
  central_law : ∀ z g, toFun (centralScalar F z * g) =
    (central_character z : ℂ) * toFun g

/-- A finite determinant twist squares its character on central scalars. -/
def ParallelWeightTwoCentralForm.twist {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : ParallelWeightTwoCentralForm K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) : ParallelWeightTwoCentralForm K μ where
  toParallelWeightTwoCuspForm := φ.toParallelWeightTwoCuspForm.twist F χ hK harch
  central_character := φ.central_character * χ.toHom * χ.toHom
  central_law z g := by
    simp only [ParallelWeightTwoCuspForm.twist_apply, map_mul,
      χ.onGL2_centralScalar, φ.central_law]
    simp only [MonoidHom.mul_apply, Units.val_mul]
    ring

/-- Determinant twisting multiplies the central character by its square. -/
theorem ParallelWeightTwoCentralForm.twist_central_character {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : ParallelWeightTwoCentralForm K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) :
    (φ.twist χ hK harch).central_character =
      φ.central_character * χ.toHom * χ.toHom := by
  rfl

@[simp]
theorem ParallelWeightTwoCentralForm.twist_apply {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : ParallelWeightTwoCentralForm K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) (g : AdelicGL2 F) :
    (φ.twist χ hK harch).toFun g = (χ.onGL2 g : ℂ) * φ.toFun g := by
  simp only [ParallelWeightTwoCentralForm.twist,
    ParallelWeightTwoCuspForm.twist_apply]

end HilbertModularity.HilbertModularForms
