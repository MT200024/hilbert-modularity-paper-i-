/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteTwist
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-! # Parallel weight two at the real places

An adelic cusp function is holomorphic of parallel weight two when its
archimedean restriction is obtained from a separately holomorphic function on
the product of upper half planes by the weight-two automorphy factor. The
formula here uses the actual real-place components of an adelic matrix, so the
analytic function is tied to the adelic cusp function. This is the holomorphic
Hilbert-form convention underlying [SkinnerWiles, §4.5, Theorem A].
-/

public noncomputable section

open NumberField
open scoped Classical

namespace HilbertModularity.HilbertModularForms

variable (F : Type*) [Field F] [NumberField F]

/-- A real infinite place of the number field. -/
abbrev RealPlace := {v : NumberField.InfinitePlace F // v.IsReal}

/-- Evaluation of an adele at a real place, through its real completion. -/
def realPlaceMap (v : RealPlace F) : AdeleRing F →+* ℝ :=
  (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal v.2).toRingHom.comp
    ((Pi.evalRingHom (fun w : NumberField.InfinitePlace F => w.Completion) v.1).comp
      (RingHom.fst (NumberField.InfiniteAdeleRing F)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))

/-- The real matrix obtained from an adelic invertible matrix at a real place. -/
def realPlaceGL2 (v : RealPlace F) : AdelicGL2 F →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (realPlaceMap F v)

/-- The holomorphic weight-two factor at the standard point of the upper half
plane, multiplied across all real places. -/
def parallelWeightTwoFactor (g : AdelicGL2 F) : ℂ :=
  ∏ v : RealPlace F,
    ((|(realPlaceGL2 F v g).det.val| : ℝ) : ℂ) *
      UpperHalfPlane.denom (realPlaceGL2 F v g) UpperHalfPlane.I ^ (-2 : ℤ)

/-- A cuspidal adelic function of holomorphic parallel weight two.
For every finite adelic component (represented by `g`), its archimedean orbit
has a separately holomorphic model. The automorphy factor uses actual real
matrix components. Requiring this for every `g` enforces the condition at
all finite components, rather than only at the identity component. -/
structure ParallelWeightTwoCuspForm (K : Subgroup (AdelicGL2 F))
    (μ : AdditiveQuotientMeasure F) extends AdelicCuspForm F K μ where
  holomorphic_model : ∀ g : AdelicGL2 F,
    ∃ h : (RealPlace F → UpperHalfPlane) → ℂ,
      (∀ v : RealPlace F, ∀ z : RealPlace F → UpperHalfPlane,
        DifferentiableAt ℂ
          (fun τ : ℂ => h (Function.update z v (UpperHalfPlane.ofComplex τ)))
          (z v : ℂ)) ∧
      (∀ a : AdelicGL2 F,
        (∀ i j : Fin 2,
          ((a : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
            (1 : Matrix (Fin 2) (Fin 2)
              (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
        (∀ v : RealPlace F, 0 < (realPlaceGL2 F v a).det.val) →
        toFun (g * a) = parallelWeightTwoFactor F a *
          h (fun v => realPlaceGL2 F v a • UpperHalfPlane.I))

/-- The archimedean holomorphic model is unchanged by a finite idele-class
character trivial on the positive real component. That last condition is
spelled out here; its automatic validity for finite-order characters is a
separate connectedness statement. -/
def ParallelWeightTwoCuspForm.twist {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : ParallelWeightTwoCuspForm F K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) : ParallelWeightTwoCuspForm F K μ where
  toAdelicCuspForm := φ.toAdelicCuspForm.twist χ hK
  holomorphic_model g := by
    obtain ⟨h, hh, hmodel⟩ := φ.holomorphic_model g
    refine ⟨fun z => (χ.onGL2 g : ℂ) * h z, ?_, ?_⟩
    · intro v z
      exact (hh v z).const_mul _
    · intro a hfinite hpositive
      simp only [AdelicCuspForm.twist_apply, map_mul,
        harch a hfinite hpositive, mul_one,
        hmodel a hfinite hpositive]
      ring

@[simp]
theorem ParallelWeightTwoCuspForm.twist_apply {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : ParallelWeightTwoCuspForm F K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) (g : AdelicGL2 F) :
    (φ.twist F χ hK harch).toFun g = (χ.onGL2 g : ℂ) * φ.toFun g := by
  simp only [ParallelWeightTwoCuspForm.twist, AdelicCuspForm.twist_apply]

end HilbertModularity.HilbertModularForms
