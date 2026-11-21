/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CuspForms

/-! # Finite idele characters and twists of adelic cusp forms

The character acts through the determinant of `GL₂(A_F)`. The proofs below
keep the actual cusp integral and double-coset Hecke sum, giving the local
algebraic part of finite-character twisting. Global class-field reciprocity
and its Galois normalization are separate literature inputs; see
[SkinnerWiles, §4.5] and the manuscript's automorphic dictionary.
-/

public noncomputable section

open NumberField MeasureTheory

namespace HilbertModularity.HilbertModularForms

variable {F : Type*} [Field F] [NumberField F]

/-- A continuous finite-order idele-class character, expressed on `A_Fˣ`.
Triviality on determinants of diagonal `GL₂(F)` is the principal-ideles
condition, since determinant maps `GL₂(F)` onto `Fˣ`. -/
structure FiniteIdeleClassCharacter (F : Type*) [Field F] [NumberField F] where
  toHom : (AdeleRing F)ˣ →* ℂˣ
  continuous : Continuous toHom
  finite_range : Set.Finite (Set.range toHom)
  trivial_diagonal : ∀ γ : GL (Fin 2) F,
    toHom (adelicDeterminant F (rationalDiagonal F γ)) = 1

/-- The determinant character of the adelic general linear group. -/
def FiniteIdeleClassCharacter.onGL2 (χ : FiniteIdeleClassCharacter F) :
    AdelicGL2 F →* ℂˣ :=
  χ.toHom.comp (adelicDeterminant F)

theorem FiniteIdeleClassCharacter.onGL2_apply
    (χ : FiniteIdeleClassCharacter F) (g : AdelicGL2 F) :
    χ.onGL2 g = χ.toHom (adelicDeterminant F g) := by
  rfl

@[simp]
theorem FiniteIdeleClassCharacter.onGL2_unipotent
    (χ : FiniteIdeleClassCharacter F) (x : AdeleRing F) :
    χ.onGL2 (upperUnipotent F x) = 1 := by
  simp [FiniteIdeleClassCharacter.onGL2]

@[simp]
theorem FiniteIdeleClassCharacter.onGL2_rational
    (χ : FiniteIdeleClassCharacter F) (γ : GL (Fin 2) F) :
    χ.onGL2 (rationalDiagonal F γ) = 1 := by
  exact χ.trivial_diagonal γ

@[simp]
theorem FiniteIdeleClassCharacter.onGL2_centralScalar
    (χ : FiniteIdeleClassCharacter F) (z : (AdeleRing F)ˣ) :
    χ.onGL2 (centralScalar F z) = χ.toHom z * χ.toHom z := by
  change χ.toHom (adelicDeterminant F (centralScalar F z)) = _
  rw [adelicDeterminant_centralScalar, map_pow, pow_two]

/-- Twisting a genuine adelic cusp form by a finite idele-class character
preserves its left invariance, cuspidal constant term and nonvanishing. -/
def AdelicCuspForm.twist {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : AdelicCuspForm F K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1) :
    AdelicCuspForm F K μ where
  toFun := twistByCharacter χ.onGL2 φ.toFun
  left_invariant γ g := by
    simp only [twistByCharacter_apply, map_mul, χ.onGL2_rational,
      one_mul, φ.left_invariant γ g]
  right_invariant k hk g := by
    simp only [twistByCharacter_apply, map_mul, hK k hk,
      mul_one, φ.right_invariant k hk g]
  cuspidal_integrable s hs g := by
    simp only [twistByCharacter_apply, map_mul, χ.onGL2_unipotent, one_mul]
    exact (φ.cuspidal_integrable s hs g).const_mul _
  cuspidal s hs g := by
    simp only [twistByCharacter_apply, map_mul, χ.onGL2_unipotent,
      one_mul]
    rw [integral_const_mul]
    simp [φ.cuspidal s hs g]
  nonzero := by
    obtain ⟨g, hg⟩ := φ.nonzero
    exact ⟨g, by simpa only [twistByCharacter_apply] using
      mul_ne_zero (Units.ne_zero (χ.onGL2 g)) hg⟩

@[simp]
theorem AdelicCuspForm.twist_apply {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} (φ : AdelicCuspForm F K μ)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1) (g : AdelicGL2 F) :
    (φ.twist χ hK).toFun g = (χ.onGL2 g : ℂ) * φ.toFun g := by
  simp only [AdelicCuspForm.twist, twistByCharacter_apply]

/-- A finite idele character multiplies the eigenvalue of the actual
double-coset operator by its value on the determinant of the coset. -/
def AdelicHeckeEigenform.twist {K : Subgroup (AdelicGL2 F)}
    {μ : AdditiveQuotientMeasure F} {a : AdelicGL2 F}
    {d : DoubleCosetRepresentatives K a}
    (φ : AdelicHeckeEigenform F μ a d)
    (χ : FiniteIdeleClassCharacter F)
    (hK : ∀ k ∈ K, χ.onGL2 k = 1) :
    AdelicHeckeEigenform F μ a d where
  toAdelicCuspForm := φ.toAdelicCuspForm.twist χ hK
  eigenvalue := (χ.onGL2 a : ℂ) * φ.eigenvalue
  hecke_eigen g := by
    have hfun : (φ.toAdelicCuspForm.twist χ hK).toFun =
        twistByCharacter χ.onGL2 φ.toFun := by
      funext x
      simp
    change heckeAction d (φ.toAdelicCuspForm.twist χ hK).toFun g =
      (χ.onGL2 a : ℂ) * φ.eigenvalue *
        (φ.toAdelicCuspForm.twist χ hK).toFun g
    rw [hfun, heckeAction_twist d χ.onGL2 hK φ.toFun g, φ.hecke_eigen g]
    simp only [twistByCharacter_apply]
    ring

end HilbertModularity.HilbertModularForms
