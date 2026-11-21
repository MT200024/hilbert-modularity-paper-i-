/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationCompatibility
public import HilbertModularity.Hypergeometric.GoodReductionInertia
public import HilbertModularity.NumberTheory.AbsoluteFrobenius
public import HilbertModularity.RepresentationTheory.Unramified

/-! # Residue-degree Frobenius for the chosen Euler descent

The normalized Euler trace is evaluated at a prime of the cyclotomic field.
For the same chosen real-field descent, unramified restriction carries this
Frobenius to the residue-degree power at the prime of the real subfield.
This is the final field-extension step in [TripathiGoswamiRevised,
finitefield-hecke-master]; it does not assume an automorphic comparison.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open scoped NumberField Pointwise
attribute [local instance] Ideal.Quotient.field

namespace HilbertModularity.Hypergeometric

universe u

variable (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)

local instance : Algebra (realCyclotomicField N) (cyclotomicField N) :=
  (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra

local instance : IsScalarTower (realCyclotomicField N) (cyclotomicField N) Qbar :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The chosen cyclotomic geometric Frobenius has the canonical residue
action in the stabilizer-hom formulation. -/
theorem absoluteGeometricFrobenius_stabilizerHom
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    Ideal.Quotient.stabilizerHom Q P.asIdeal (Qbar ≃ₐ[cyclotomicField N] Qbar)
      ((absoluteGeometricFrobenius N P Q)⁻¹) =
      Ideal.Quotient.arithmeticFrobenius P.asIdeal Q := by
  rw [absoluteGeometricFrobenius, inv_inv]
  apply AlgEquiv.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ b =>
    rw [show (⟦b⟧ : 𝓞 Qbar ⧸ Q) = Ideal.Quotient.mk Q b from rfl,
      Ideal.Quotient.stabilizerHom_apply,
      Ideal.Quotient.arithmeticFrobenius_apply]
    exact absoluteArithmeticFrobenius_spec N P Q b

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- At a good prime of the real field, the actual representation of the
chosen Euler descent sends cyclotomic geometric Frobenius to the
residue-degree power of real geometric Frobenius. The real lift may be any
element with the stated residue action, since inertia acts trivially. -/
theorem ProperEulerRealDescent.geometricFrobenius_restrictScalars
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    (g𝔮 : MulAction.stabilizer (Qbar ≃ₐ[realCyclotomicField N] Qbar) Q)
    (hg𝔮 : Ideal.Quotient.stabilizerHom Q 𝔮
        (Qbar ≃ₐ[realCyclotomicField N] Qbar) (g𝔮⁻¹) =
      Ideal.Quotient.arithmeticFrobenius 𝔮 Q) :
    D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q)) =
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        (realEulerClosureGaloisHom N (g𝔮 : Qbar ≃ₐ[realCyclotomicField N] Qbar))) ^
        P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) := by
  let : P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans P.asIdeal 𝔮 _
  let ρ := (D.localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)).comp (realEulerClosureGaloisHom N)
  have hρ : ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      ρ g = 1 := D.inertia_eq_one_of_goodUnit N m ℓ L ι hN h5 hm hmN
        𝒞 q hq hqN P hP hℓ Q ξ hξ
  have h := Representation.geometricFrobenius_restrictScalars ρ
    𝔮 P.asIdeal Q hρ g𝔮 (absoluteGeometricFrobenius N P Q)
    hg𝔮 (absoluteGeometricFrobenius_stabilizerHom N P Q)
  have hrestrict :
      AlgEquiv.restrictScalarsHom (realCyclotomicField N)
          (absoluteGeometricFrobenius N P Q : Qbar ≃ₐ[cyclotomicField N] Qbar) =
        restrictCyclotomicGalois N (absoluteGeometricFrobenius N P Q) := by
    ext x
    rfl
  rw [hrestrict] at h
  simpa only [ρ, MonoidHom.comp_apply] using h

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- The residue-degree formula using the canonical geometric lift at the
real-field prime. Both sides act on the same chosen generic descent. -/
theorem ProperEulerRealDescent.geometricFrobenius_at_realPrime
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q)) =
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        (realEulerClosureGaloisHom N
          (NumberField.geometricFrobenius (realCyclotomicField N) Qbar 𝔮 Q :
            Qbar ≃ₐ[realCyclotomicField N] Qbar))) ^
        P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) := by
  exact D.geometricFrobenius_restrictScalars N m ℓ L ι hN h5 hm hmN 𝒞
    q hq hqN 𝔮 P hP hℓ Q ξ hξ
    (NumberField.geometricFrobenius (realCyclotomicField N) Qbar 𝔮 Q)
    (NumberField.geometricFrobenius_inv_residue
      (realCyclotomicField N) Qbar 𝔮 Q)

/-- The trace of the residue-degree power at the real prime is the same
normalized Euler value already proved at the cyclotomic prime. In particular,
the residue characteristic may be two when it is prime to the odd level. -/
theorem ProperEulerRealDescent.realGeometricFrobeniusPower_trace_eq_normalizedEulerTrace
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L
        (D.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      ((D.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          (realEulerClosureGaloisHom N
            (NumberField.geometricFrobenius (realCyclotomicField N) Qbar 𝔮 Q :
              Qbar ≃ₐ[realCyclotomicField N] Qbar))) ^
          P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N))) =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  let : Module.Finite L
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    D.localSystem.finite _
  have hpow := D.geometricFrobenius_at_realPrime N m ℓ L ι
    hN h5 hm hmN 𝒞 q hq hqN 𝔮 P hP hℓ Q ξ hξ
  have htrace := D.geometricFrobenius_trace_eq_normalizedEulerTrace
    N m ℓ L ι hN h5 hm hmN 𝒞 P hP hℓ Q ξ hξ
  exact (congrArg (LinearMap.trace L _) hpow).symm.trans htrace

end HilbertModularity.Hypergeometric
