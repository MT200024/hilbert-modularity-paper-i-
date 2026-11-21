/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.HeckeOperators

/-! # Adelic cusp forms over a number field

The underlying functions live on the actual adelic general linear group. Their
constant term integrates over the additive quotient of the adeles by the
diagonal number field. We keep the choice of normalized Haar measure explicit
because it is not supplied by the present number-field adele API. These data
are the finite-level cuspidal part of the Hilbert forms in [SkinnerWiles, §4.5].
-/

public noncomputable section

open NumberField MeasureTheory

namespace HilbertModularity.HilbertModularForms

variable (F : Type*) [Field F] [NumberField F]

/-- The Borel measurable structure on the additive adelic quotient. -/
instance additiveAdeleQuotientMeasurableSpace :
    MeasurableSpace (AdditiveAdeleQuotient F) :=
  borel _

/-- A normalized additive Haar measure on the adelic quotient `F \ A_F`.
Its existence and uniqueness are standard adelic measure facts; the measure
is explicit data until those facts are available in the library. -/
structure AdditiveQuotientMeasure where
  measure : Measure (AdditiveAdeleQuotient F)
  translation_invariant : ∀ a : AdditiveAdeleQuotient F,
    Measure.map (fun x => a + x) measure = measure
  normalized : measure Set.univ = 1

/-- A genuine finite-level cuspidal automorphic function on `GL₂(A_F)`.
The constant term is required to vanish for every section of the additive
quotient map, so its definition is independent of representatives. -/
structure AdelicCuspForm (K : Subgroup (AdelicGL2 F))
    (μ : AdditiveQuotientMeasure F) where
  toFun : AdelicGL2 F → ℂ
  left_invariant : ∀ γ : GL (Fin 2) F, ∀ g,
    toFun (rationalDiagonal F γ * g) = toFun g
  right_invariant : ∀ k ∈ K, ∀ g, toFun (g * k) = toFun g
  cuspidal_integrable : ∀ s : AdditiveAdeleQuotient F → AdeleRing F,
    (∀ x, QuotientAddGroup.mk (s x) = x) →
    ∀ g, Integrable (fun x : AdditiveAdeleQuotient F =>
      toFun (upperUnipotent F (s x) * g)) μ.measure
  cuspidal : ∀ s : AdditiveAdeleQuotient F → AdeleRing F,
    (∀ x, QuotientAddGroup.mk (s x) = x) →
    ∀ g, (∫ x : AdditiveAdeleQuotient F,
      toFun (upperUnipotent F (s x) * g) ∂μ.measure) = 0
  nonzero : ∃ g, toFun g ≠ 0

/-- A finite right-double-coset eigencondition on an actual cusp form. -/
structure AdelicHeckeEigenform {K : Subgroup (AdelicGL2 F)}
    (μ : AdditiveQuotientMeasure F) (a : AdelicGL2 F)
    (d : DoubleCosetRepresentatives K a) extends AdelicCuspForm F K μ where
  eigenvalue : ℂ
  hecke_eigen : ∀ g, heckeAction d toFun g = eigenvalue * toFun g

end HilbertModularity.HilbertModularForms
