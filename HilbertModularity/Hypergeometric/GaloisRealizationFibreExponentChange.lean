/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.ExponentCohomology
public import HilbertModularity.Hypergeometric.GaloisRealizationFibreDeckRelation

/-! # Exponent change on the selected proper Euler fibre chart

The exponent change of the affine Euler cover is compared with the deck
automorphism of the actual specialized proper fibre.  The base parameter
`ζ` becomes `ζ^m` before the fixed `χ₀` projector is applied.  This is the
geometric deck-label convention of [GPRV, equation (76)].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

/-- The base-cover deck map, transported by the coprime exponent change,
acts on the selected proper `m`-fibre by its actual `ζ^m` deck
automorphism.  Both sides are maps from the same base affine chart into
the selected proper fibre. -/
theorem exponentSchemeIso_selectedProperFibre_deck
    (N m mprime k : ℕ) [NeZero N]
    (𝒞 : SmoothProperEulerFamily N m)
    (t : cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (hm : m < N) (hbezout : m * mprime = 1 + k * N)
    (ζ : rootsOfUnity N (cyclotomicField N)) :
    ((EulerCover.deckTransformation N 1 t ζ).hom ≫
      (EulerCover.exponentSchemeIso N m mprime k t hm hbezout).hom) ≫
        smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t =
      ((EulerCover.exponentSchemeIso N m mprime k t hm hbezout).hom ≫
        smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t) ≫
          (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t (ζ ^ m)).unop.hom := by
  calc
    _ = ((EulerCover.exponentSchemeIso N m mprime k t hm hbezout).hom ≫
          (EulerCover.deckTransformation N m t (ζ ^ m)).hom) ≫
            smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t := by
              rw [EulerCover.exponentSchemeIso_deck N m mprime k t hm hbezout ζ]
    _ = (EulerCover.exponentSchemeIso N m mprime k t hm hbezout).hom ≫
          ((EulerCover.deckTransformation N m t (ζ ^ m)).hom ≫
            smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t) := by
              rw [Category.assoc]
    _ = _ := by
      rw [smoothProperEulerFibreChartInclusion_deck N m 𝒞 t ht h1t (ζ ^ m),
        Category.assoc]

end HilbertModularity.Hypergeometric
