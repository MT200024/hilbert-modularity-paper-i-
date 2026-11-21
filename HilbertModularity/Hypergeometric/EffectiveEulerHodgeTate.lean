/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EffectiveEulerRealization
public import HilbertModularity.Hypergeometric.GaloisRealizationHodgeTate
public import HilbertModularity.RepresentationTheory.FiniteCharacterLabelledHodgeTate

/-! # Hodge–Tate weights of the effective Euler action

The same selected raw quotient has complementary labelled weights
`{0,1}` [GPRV, §10.1, Case (1), p. 44]. The one selected κ character
has finite order on the real-field Galois group [GPRV, Lemma 9.4,
p. 40], so its tensor twist preserves these actual labelled
multiplicities. No Tate twist is inserted.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open NumberField.LocalGalois
open scoped NumberField

namespace HilbertModularity.Hypergeometric

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

/-- Coordinates of the actual κ-twisted arithmetic fibre. The quotient,
coefficient projector and κ character are selected before the fibre. -/
def chosenEffectiveEulerCoordinateAction
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 p L ι
    Representation L (HilbertModularForms.AbsoluteGalois (realCyclotomicField N))
      (Fin (Module.finrank L (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _
          (ProjectiveLine.puncturedPoint _ ξ)))) → L) :=
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  (puncturedFiberCoordinateRepresentation (realCyclotomicField N) L ξ
    D.localSystem).characterTwist (gprvKappaLocal N h3 m L)

/-- The restriction of the effective coordinate action to one actual
decomposition group, written directly as a finite scalar twist. -/
def chosenEffectiveEulerLocalCoordinateAction
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 p L ι
    Representation L (Gal(PadicAlgCl p/q.adicCompletion (realCyclotomicField N)))
      (Fin (Module.finrank L (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _
          (ProjectiveLine.puncturedPoint _ ξ)))) → L) :=
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  let s := localGaloisRestriction p (realCyclotomicField N) q
  Representation.characterTwist
    ((puncturedFiberCoordinateRepresentation (realCyclotomicField N)
      L ξ D.localSystem).comp s)
    ((gprvKappaLocal N h3 m L).comp s)

/-- The explicitly constructed local twist is exactly the restriction of
the one global effective coordinate action. No local character is
chosen independently. -/
theorem chosenEffectiveEulerLocalCoordinateAction_eq_restrict
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    chosenEffectiveEulerLocalCoordinateAction
      N m p h3 hm hmN hcop L ι ξ q =
      (chosenEffectiveEulerCoordinateAction
        N m p h3 hm hmN hcop L ι ξ).comp
        (localGaloisRestriction p (realCyclotomicField N) q) := by
  ext g v
  rfl

/-- The effective action has bijective Hodge–Tate comparison and exactly
one weight zero and one weight one at every local coefficient label,
for every coprime conductor. This applies the generic finite-character
period theorem to the raw GPRV quotient, retaining the fixed label and
actual same-fibre action. -/
theorem chosenEffectiveEulerCoordinateAction_labelledHodgeTate
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 p L ι
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.restrictScalars ℚ_[p]
          (Representation.characterTwist
            ((puncturedFiberCoordinateRepresentation (realCyclotomicField N)
              L ξ D.localSystem).comp
              (localGaloisRestriction p (realCyclotomicField N) q))
            ((gprvKappaLocal N h3 m L).comp
              (localGaloisRestriction p (realCyclotomicField N) q)))))) ∧
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]]
          AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.characterTwist
            ((puncturedFiberCoordinateRepresentation (realCyclotomicField N)
              L ξ D.localSystem).comp
              (localGaloisRestriction p (realCyclotomicField N) q))
            ((gprvKappaLocal N h3 m L).comp
              (localGaloisRestriction p (realCyclotomicField N) q))) n τ) =
        (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) := by
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  have hraw := commonRealEulerQuotientRealization_labelledHodgeTate_of_coprime
    N m p h3 hm hmN hcop 𝒞 R L ι ξ
  constructor
  · intro q hq
    let s := localGaloisRestriction p (realCyclotomicField N) q
    let ρ := (puncturedFiberCoordinateRepresentation
      (realCyclotomicField N) L ξ D.localSystem).comp s
    let χ := (gprvKappaLocal N h3 m L).comp s
    have hc : Continuous χ :=
      (continuous_gprvKappaLocal N h3 m L).comp
        (continuous_localGaloisRestriction p (realCyclotomicField N) q)
    have ho : IsOfFinOrder χ := by
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨2, by decide, ?_⟩
      apply MonoidHom.ext
      intro g
      exact gprvKappaLocal_apply_sq N h3 m L (s g)
    have h := (HodgeTate.finiteCharacterTwist_comparison_bijective_iff
      p ρ χ hc ho).mp (hraw.1 q)
    dsimp only [ρ, χ, s, D, R, 𝒞] at h
    exact h
  · intro q hq τ n
    let s := localGaloisRestriction p (realCyclotomicField N) q
    let ρ := (puncturedFiberCoordinateRepresentation
      (realCyclotomicField N) L ξ D.localSystem).comp s
    let χ := (gprvKappaLocal N h3 m L).comp s
    have hc : Continuous χ :=
      (continuous_gprvKappaLocal N h3 m L).comp
        (continuous_localGaloisRestriction p (realCyclotomicField N) q)
    have ho : IsOfFinOrder χ := by
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨2, by decide, ?_⟩
      apply MonoidHom.ext
      intro g
      exact gprvKappaLocal_apply_sq N h3 m L (s g)
    have h := HodgeTate.finiteCharacterTwist_labelledWeightSpace_finrank
      p ρ χ hc ho n τ
    dsimp only [ρ, χ, s, D, R, 𝒞] at h
    exact h.trans (hraw.2 q τ n)

end HilbertModularity.Hypergeometric
