/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.FiniteLevel

/-! # Standard prime Hecke operators for Hilbert cusp forms

A prime Hecke element is the identity at the infinite places and at every
finite place away from the prime, and has diagonal entries `(π, 1)` at the
prime for a local uniformizer `π`. Thus its double coset is the actual
standard `T_𝔮` coset for the stated compact-open level. Eigenconditions are
required simultaneously outside a finite set. See [SkinnerWiles, §4.5].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- The matrix of an adelic element at a finite place. -/
def finitePlaceMatrix (a : AdelicGL2 F)
    (v : HeightOneSpectrum (𝓞 F)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  fun i j => (((a : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2) v

/-- The standard prime Hecke coset, with its certified finite right-coset
sum. The local matrix normalization fixes the choice of geometric Hecke
parameter used in the later Galois comparison. -/
structure PrimeHeckeDatum (level : FiniteLevel F)
    (q : HeightOneSpectrum (𝓞 F)) where
  uniformizer : q.adicCompletion F
  uniformizer_valuation :
    HeightOneSpectrum.adicCompletion.valuation F q uniformizer =
      (some (Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ))
  element : AdelicGL2 F
  infinite_trivial : ∀ i j : Fin 2,
    ((element : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing F)) i j
  at_prime : finitePlaceMatrix element q = Matrix.diagonal ![uniformizer, 1]
  away_from_prime : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ q →
    finitePlaceMatrix element v = 1
  cosets : DoubleCosetRepresentatives level.subgroup element

/-- A genuine parallel-weight-two central cusp form that is an eigenform for
the standard prime double coset at every prime outside a finite bad set. -/
structure GoodPrimeEigenform (level : FiniteLevel F)
    (μ : AdditiveQuotientMeasure F) extends
    ParallelWeightTwoCentralForm level.subgroup μ where
  bad : Set (HeightOneSpectrum (𝓞 F))
  bad_finite : bad.Finite
  /-- At a good prime the level contains the full local integral `GL₂` factor:
  both a matrix and its inverse have integral entries at that prime. -/
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
  hecke_data : ∀ q, q ∉ bad → PrimeHeckeDatum level q
  hecke_value : ∀ q, q ∉ bad → ℂ
  hecke_eigen : ∀ q (hq : q ∉ bad) g,
    heckeAction (hecke_data q hq).cosets toFun g =
      hecke_value q hq * toFun g

/-- Finite determinant twisting preserves all good-prime eigenconditions.
The new value is `χ(det a_𝔮)` times the old value, with the coset itself
unchanged. -/
def GoodPrimeEigenform.twist {level : FiniteLevel F}
    {μ : AdditiveQuotientMeasure F}
    (φ : GoodPrimeEigenform level μ) (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ level.subgroup, χ.onGL2 k = 1)
    (harch : ∀ g : AdelicGL2 F,
      (∀ i j : Fin 2,
        ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
          (1 : Matrix (Fin 2) (Fin 2)
            (FiniteAdeleRing (𝓞 F) F)) i j) →
      (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
      χ.onGL2 g = 1) : GoodPrimeEigenform level μ where
  toParallelWeightTwoCentralForm :=
    φ.toParallelWeightTwoCentralForm.twist χ hK harch
  bad := φ.bad
  bad_finite := φ.bad_finite
  spherical_level := φ.spherical_level
  hecke_data := φ.hecke_data
  hecke_value q hq :=
    (χ.onGL2 (φ.hecke_data q hq).element : ℂ) * φ.hecke_value q hq
  hecke_eigen q hq g := by
    have hfun : (φ.toParallelWeightTwoCentralForm.twist χ hK harch).toFun =
        twistByCharacter χ.onGL2 φ.toFun := by
      funext x
      simpa only [twistByCharacter_apply] using
        ParallelWeightTwoCentralForm.twist_apply
          φ.toParallelWeightTwoCentralForm χ hK harch x
    rw [hfun, heckeAction_twist (φ.hecke_data q hq).cosets
      χ.onGL2 hK φ.toFun g, φ.hecke_eigen q hq g]
    simp only [twistByCharacter_apply]
    ring

section TwistProperties

variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}
  (φ : GoodPrimeEigenform level μ) (χ : FiniteIdeleClassCharacter F)
  (hK : ∀ k ∈ level.subgroup, χ.onGL2 k = 1)
  (harch : ∀ g : AdelicGL2 F,
    (∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing F)) i j).2 =
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) →
    (∀ v : RealPlace F, 0 < (realPlaceGL2 F v g).det.val) →
    χ.onGL2 g = 1)

@[simp]
theorem GoodPrimeEigenform.twist_apply (g : AdelicGL2 F) :
    (φ.twist χ hK harch).toFun g = (χ.onGL2 g : ℂ) * φ.toFun g :=
  ParallelWeightTwoCentralForm.twist_apply _ _ _ _ _

@[simp]
theorem GoodPrimeEigenform.twist_bad :
    (φ.twist χ hK harch).bad = φ.bad := by
  rfl

theorem GoodPrimeEigenform.twist_hecke_value
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.bad) :
    (φ.twist χ hK harch).hecke_value q (by simpa only [twist_bad] using hq) =
      (χ.onGL2 (φ.hecke_data q hq).element : ℂ) * φ.hecke_value q hq := by
  rfl

/-- Central-character normalization of the actual twisted eigenform. -/
theorem GoodPrimeEigenform.twist_central_character :
    (φ.twist χ hK harch).central_character =
      φ.central_character * χ.toHom * χ.toHom := by
  exact ParallelWeightTwoCentralForm.twist_central_character
    φ.toParallelWeightTwoCentralForm χ hK harch

/-- Twisting preserves the chosen normalized prime coset. -/
theorem GoodPrimeEigenform.twist_hecke_data
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.bad) :
    (φ.twist χ hK harch).hecke_data q (by simpa only [twist_bad] using hq) =
      φ.hecke_data q hq := by
  rfl

end TwistProperties

end HilbertModularity.HilbertModularForms
