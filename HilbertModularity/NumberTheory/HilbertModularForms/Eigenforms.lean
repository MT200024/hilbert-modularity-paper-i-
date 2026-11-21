/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.ArchimedeanWeight

/-! # Hecke eigenforms of parallel weight two

The Hecke operators are the finite adelic double-coset operators of
`HeckeOperators`. The archimedean holomorphy and cuspidality conditions come
from `ArchimedeanWeight`.
-/

public noncomputable section

open NumberField

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- A parallel-weight-two cusp form that is an eigenvector for a specified
finite adelic double-coset operator. -/
structure ParallelWeightTwoHeckeEigenform (K : Subgroup (AdelicGL2 F))
    (μ : AdditiveQuotientMeasure F) (a : AdelicGL2 F)
    (d : DoubleCosetRepresentatives K a) extends ParallelWeightTwoCuspForm F K μ where
  eigenvalue : ℂ
  hecke_eigen : ∀ g, heckeAction d toFun g = eigenvalue * toFun g

/-- Finite-character twisting preserves the actual weight-two Hecke
eigencondition and multiplies its eigenvalue by the determinant character. -/
def ParallelWeightTwoHeckeEigenform.twist {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} {a : AdelicGL2 F}
    {d : DoubleCosetRepresentatives K a}
    (φ : ParallelWeightTwoHeckeEigenform K μ a d)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) : ParallelWeightTwoHeckeEigenform K μ a d where
  toParallelWeightTwoCuspForm := φ.toParallelWeightTwoCuspForm.twist F χ hK harch
  eigenvalue := (χ.onGL2 a : ℂ) * φ.eigenvalue
  hecke_eigen g := by
    have ht : (φ.toParallelWeightTwoCuspForm.twist F χ hK harch).toFun =
        twistByCharacter χ.onGL2 φ.toFun := by
      funext x
      simp
    rw [ht, heckeAction_twist d χ.onGL2 hK φ.toFun g, φ.hecke_eigen g]
    simp only [twistByCharacter_apply]
    ring

end HilbertModularity.HilbertModularForms
