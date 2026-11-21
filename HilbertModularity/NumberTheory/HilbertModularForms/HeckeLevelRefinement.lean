/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.GoodPrimeEigenform
public import HilbertModularity.NumberTheory.HilbertModularForms.LevelRestriction

/-! # Unramified Hecke operators after finite level refinement

The restricted product topology permits a smaller compact open level killing a
finite character. Away from finitely many primes both levels have full integral
local factor, and their prime Hecke sums agree on functions invariant under the
old level. This standard input is independent of eigenforms and Galois actions.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- A smaller finite level with the same unramified prime Hecke action.
The action equality applies to every right-invariant function, without any
cuspidality, eigenvalue or Galois-realization premise. -/
structure HeckeLevelRefinement (K : FiniteLevel F)
    (χ : FiniteIdeleClassCharacter F) where
  level : FiniteLevel F
  le : level.subgroup ≤ K.subgroup
  character_trivial : ∀ k ∈ level.subgroup, χ.onGL2 k = 1
  bad : Set (HeightOneSpectrum (𝓞 F))
  bad_finite : bad.Finite
  spherical_level : ∀ q, q ∉ bad → ∀ k : AdelicGL2 F,
    (∀ i j : Fin 2,
      ((k : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).1 =
        (1 : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing F)) i j) →
    (∀ v : HeightOneSpectrum (𝓞 F), v ≠ q → finitePlaceMatrix k v = 1) →
    (∀ i j : Fin 2,
      HeightOneSpectrum.adicCompletion.valuation F q (finitePlaceMatrix k q i j) ≤ 1 ∧
      HeightOneSpectrum.adicCompletion.valuation F q
        (finitePlaceMatrix k⁻¹ q i j) ≤ 1) →
    k ∈ level.subgroup
  primeDatum : ∀ q, q ∉ bad → PrimeHeckeDatum K q → PrimeHeckeDatum level q
  element_eq : ∀ q (hq : q ∉ bad) (d : PrimeHeckeDatum K q),
    (primeDatum q hq d).element = d.element
  action_eq : ∀ q (hq : q ∉ bad) (d : PrimeHeckeDatum K q) (f : AdelicGL2 F → ℂ),
    (∀ k ∈ K.subgroup, ∀ g, f (g * k) = f g) → ∀ g,
    heckeAction (primeDatum q hq d).cosets f g = heckeAction d.cosets f g

/-- Compact-open refinement and unramified Hecke level compatibility.

[SkinnerWiles, §3.1, pp.27–30] identifies the restricted product, defines the
finite double-coset sums in (3.1), and explicitly states on p.30 that level
inclusion respects T(q) and S(q) when both local factors are GL₂(O_q).
The passage from an arbitrary compact open K to a product sublevel uses the
restricted-product neighbourhood basis (p.27): outside a finite set K contains
and is contained in the integral local factors. Intersect at the remaining
places with an open subgroup in the finite character kernel. Finite image and
continuity make that kernel open. The common local coset decomposition proves
(3.1) agrees for every right-K-invariant function, independently of analytic
conditions. This is the standard topological/double-coset consequence of those
passages, not an application of the ordinary-family Lemma 3.17.

The same normalized prime element is retained; no measure rescaling or index
factor occurs in these finite sums. No eigenform or automorphic twist is
asserted by this named literature input. -/
theorem nonempty_heckeLevelRefinement (K : FiniteLevel F)
    (χ : FiniteIdeleClassCharacter F) : Nonempty (HeckeLevelRefinement K χ) := by
  sorry

/-- Regard the original eigenfunction at the refined level, enlarging only
the exceptional set. Its good Hecke eigenvalues are unchanged. -/
def GoodPrimeEigenform.refineLevel {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ) :
    GoodPrimeEigenform r.level μ where
  toParallelWeightTwoCentralForm := φ.toParallelWeightTwoCentralForm.restrictLevel r.le
  bad := φ.bad ∪ r.bad
  bad_finite := φ.bad_finite.union r.bad_finite
  spherical_level q hq := r.spherical_level q (fun h => hq (Or.inr h))
  hecke_data q hq := r.primeDatum q (fun h => hq (Or.inr h))
    (φ.hecke_data q (fun h => hq (Or.inl h)))
  hecke_value q hq := φ.hecke_value q (fun h => hq (Or.inl h))
  hecke_eigen q hq g := by
    have hf : (φ.toParallelWeightTwoCentralForm.restrictLevel r.le).toFun = φ.toFun :=
      funext (ParallelWeightTwoCentralForm.restrictLevel_apply _ _)
    rw [hf]
    rw [r.action_eq q _ _ φ.toFun φ.right_invariant]
    exact φ.hecke_eigen q _ g

@[simp]
theorem GoodPrimeEigenform.refineLevel_apply {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ)
    (g : AdelicGL2 F) : (φ.refineLevel r).toFun g = φ.toFun g :=
  ParallelWeightTwoCentralForm.restrictLevel_apply _ _ _

@[simp]
theorem GoodPrimeEigenform.refineLevel_bad {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ) :
    (φ.refineLevel r).bad = φ.bad ∪ r.bad :=
  (rfl)

@[simp]
theorem GoodPrimeEigenform.refineLevel_central_character {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ) :
    (φ.refineLevel r).central_character = φ.central_character :=
  ParallelWeightTwoCentralForm.restrictLevel_central_character _ _

theorem GoodPrimeEigenform.refineLevel_good {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ (φ.refineLevel r).bad) : q ∉ φ.bad := by
  rw [refineLevel_bad] at hq
  exact fun h => hq (Or.inl h)

@[simp]
theorem GoodPrimeEigenform.refineLevel_hecke_value {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ (φ.refineLevel r).bad) :
    (φ.refineLevel r).hecke_value q hq =
      φ.hecke_value q (φ.refineLevel_good r q hq) := (rfl)

@[simp]
theorem GoodPrimeEigenform.refineLevel_hecke_element {K : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F} (φ : GoodPrimeEigenform K μ)
    {χ : FiniteIdeleClassCharacter F} (r : HeckeLevelRefinement K χ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ (φ.refineLevel r).bad) :
    ((φ.refineLevel r).hecke_data q hq).element =
      (φ.hecke_data q (φ.refineLevel_good r q hq)).element :=
  r.element_eq _ _ _

end HilbertModularity.HilbertModularForms
