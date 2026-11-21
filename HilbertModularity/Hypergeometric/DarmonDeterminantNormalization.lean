/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeCohomologicalDeterminant
public import HilbertModularity.Hypergeometric.RMComparison

/-! # The determinant character used to normalize the Darmon comparison

The character is defined from the covariant Tate family. Its restriction along
an arithmetic fibre path is proved to be the actual cyclotomic character at
prime conductors at least five. Duality then supplies the cohomological
normalization in [TripathiGoswamiRevised, Theorem RMgeneral].
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField
namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [NormedAlgebra ℚ_[ℓ] L] [IsScalarTower ℚ_[ℓ] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
  (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))

/-- Determinant of the covariant Tate monodromy with its fixed coefficient label. -/
def darmonTateDeterminantCharacter :
    Scheme.etaleFundamentalGroup (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) →* Lˣ :=
  (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
    (darmonLabelledTateFamily (realCyclotomicField N) N hN ℓ m hm E hE w L)
    ).determinantCharacter

/-- The determinant of the cohomological dual cancels the covariant determinant. -/
theorem darmonCohomologicalFamily_det_mul_tateDeterminant
    (g : Scheme.etaleFundamentalGroup (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)) :
    (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
      (darmonCohomologicalFamily (realCyclotomicField N) N hN ℓ m hm E hE w L)
      ).determinantCharacter g *
      darmonTateDeterminantCharacter N hN ℓ m hm E hE w L ξ₀ g = 1 := by
  have he := Scheme.fiberMonodromy_cohDual (realCyclotomicField N)
    (ProjectiveLine.punctured (realCyclotomicField N))
    (darmonLabelledTateFamily (realCyclotomicField N) N hN ℓ m hm E hE w L
      ).algebraicFunctor (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)
  change (Scheme.fiberMonodromy (realCyclotomicField N)
    (ProjectiveLine.punctured (realCyclotomicField N))
    (ModuleCat.cohDual L (darmonLabelledTateFamily (realCyclotomicField N)
      N hN ℓ m hm E hE w L).algebraicFunctor)
    (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)).determinantCharacter g * _ = 1
  let F := darmonLabelledTateFamily (realCyclotomicField N) N hN ℓ m hm E hE w L
  let : Module.Finite L (F.algebraicFunctor.obj
      (Scheme.etaleFiberPoint (realCyclotomicField N)
        (ProjectiveLine.punctured (realCyclotomicField N))
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀))) := F.finite _
  rw [he]
  erw [Representation.determinantCharacter_dual]
  exact inv_mul_cancel _

variable [Fact N.Prime] (hp : 5 ≤ N) [IsScalarTower ℚ ℚ_[ℓ] L]

include hp

omit [CompleteSpace L] in
/-- At the base arithmetic section the actual Tate determinant is cyclotomic. -/
theorem darmonTateDeterminantCharacter_arithmetic
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    darmonTateDeterminantCharacter N hN ℓ m hm E hE w L ξ₀
      (Scheme.galoisToEtaleFundamentalGroup (realCyclotomicField N)
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) g) =
      Field.cyclotomicCharacterWithCoefficients (realCyclotomicField N) ℓ L g := by
  apply Units.ext
  exact darmonPrimeLabelledTateFamily_det N hN hp ℓ (realCyclotomicField N)
    (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) m hm E hE w L g

omit [CompleteSpace L] in
/-- At every nonsingular arithmetic fibre, the transported Tate determinant is
exactly cyclotomic. Thus the normalization character has its asserted arithmetic
meaning, including the coefficient label and the Frobenius convention. -/
theorem darmonTateDeterminantCharacter_along_arithmeticPath
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (e : Scheme.finiteArithmeticFiberFunctor (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor (realCyclotomicField N)
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    darmonTateDeterminantCharacter N hN ℓ m hm E hE w L ξ₀
        (puncturedArithmeticLoopsAlongPath (realCyclotomicField N) ξ₀ ξ e g) =
      Field.cyclotomicCharacterWithCoefficients (realCyclotomicField N) ℓ L g := by
  apply Units.ext
  have he := (puncturedArithmeticFiberPathEquiv (realCyclotomicField N) ξ₀ ξ e
    (darmonLabelledTateFamily (realCyclotomicField N) N hN ℓ m hm E hE w L)
    ).determinant_eq g
  exact he.trans (darmonPrimeLabelledTateFamily_det N hN hp ℓ (realCyclotomicField N)
    (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ) m hm E hE w L g)

end HilbertModularity.Hypergeometric
