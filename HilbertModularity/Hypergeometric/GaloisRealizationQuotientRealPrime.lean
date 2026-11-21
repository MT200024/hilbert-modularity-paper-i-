/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientTrace
public import HilbertModularity.Hypergeometric.GaloisRealizationResidueDegree

/-! # Real-prime Frobenius on the common Euler quotient

The labelled component of the actual quotient fibre is compared with the
chosen descended Euler family by [GPRV, Theorem 9.2 and Proposition 9.5].
Conjugacy of endomorphisms and the residue-degree calculation then give its
trace at real-field geometric Frobenius powers. The geometric input is the
common quotient comparison; no Frobenius value is included in that input.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

universe u

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)

local instance : Algebra (realCyclotomicField N) (cyclotomicField N) :=
  (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra

omit [CompleteSpace L] [ContinuousSMul ℚ_[ℓ] L] [FiniteDimensional ℚ_[ℓ] L] in
/-- Trace conjugacy for any real-field Galois element.  The cited quotient
comparison intertwines the actual H¹ component with the chosen generic
descent; trace invariance is linear algebra. -/
theorem RealEulerQuotientPlace.componentRealGalois_trace_eq_descent
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    letI : Module.Finite L ((R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
      Module.Finite.equiv (R.componentComparison ξ).symm
    LinearMap.trace L _
      ((R.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι g) =
    LinearMap.trace L _
      (R.descent.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ) g) := by
  let : Module.Finite L
      (R.descent.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    R.descent.localSystem.finite _
  let : Module.Finite L ((R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
    Module.Finite.equiv (R.componentComparison ξ).symm
  let f := (R.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι g
  let h := R.descent.localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ) g
  have hconj : (R.componentComparison ξ).conj f = h := by
    apply LinearMap.ext
    intro w
    have hi := R.componentComparison_galois ξ g
      ((R.componentComparison ξ).symm w)
    rw [← RealCyclotomicQuotientAction.componentGaloisEndomorphism_apply] at hi
    change (R.componentComparison ξ)
        (f ((R.componentComparison ξ).symm w)) =
      h ((R.componentComparison ξ) ((R.componentComparison ξ).symm w)) at hi
    rw [LinearEquiv.apply_symm_apply] at hi
    exact hi
  let b := Module.Free.chooseBasis L
    (R.descent.localSystem.toFunctor.obj
      (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ)))
  have ht : LinearMap.trace L _ ((R.componentComparison ξ).conj f) =
      LinearMap.trace L _ f := by
    rw [LinearMap.trace_eq_matrix_trace L b,
      LinearMap.trace_eq_matrix_trace L (b.map (R.componentComparison ξ).symm)]
    congr 1
  rw [hconj] at ht
  exact ht.symm

/-- At a good real prime, the residue-degree power of geometric Frobenius
on the actual labelled quotient cohomology has the normalized Euler trace
at the cyclotomic prime above it. The hypotheses permit residue
characteristic two. -/
theorem RealEulerQuotientPlace.realGeometricFrobeniusPower_trace_eq_normalizedEulerTrace
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L ((R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
      Module.Finite.equiv (R.componentComparison ξ).symm
    LinearMap.trace L _
      ((R.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι
        ((realEulerClosureGaloisHom N
          (NumberField.geometricFrobenius (realCyclotomicField N) Qbar 𝔮 Q :
            Qbar ≃ₐ[realCyclotomicField N] Qbar)) ^
          P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)))) =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  let : Module.Finite L ((R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
    Module.Finite.equiv (R.componentComparison ξ).symm
  calc
    _ = LinearMap.trace L _
        (R.descent.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          ((realEulerClosureGaloisHom N
            (NumberField.geometricFrobenius
              (realCyclotomicField N) Qbar 𝔮 Q :
                Qbar ≃ₐ[realCyclotomicField N] Qbar)) ^
            P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)))) :=
      R.componentRealGalois_trace_eq_descent N m 𝒞 𝒬 ξ ℓ L ι _
    _ = LinearMap.trace L _
        ((R.descent.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          (realEulerClosureGaloisHom N
            (NumberField.geometricFrobenius
              (realCyclotomicField N) Qbar 𝔮 Q :
                Qbar ≃ₐ[realCyclotomicField N] Qbar))) ^
          P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N))) := by
      rw [map_pow]
    _ = _ := R.descent.realGeometricFrobeniusPower_trace_eq_normalizedEulerTrace
      N m ℓ L ι hN h5 hm hmN 𝒞 q hq hqN 𝔮 P hP hℓ Q ξ hξ

/-- The real-prime Frobenius-power trace on a labelled component of the
single geometric quotient chosen before any coefficient place. -/
def CommonRealEulerQuotientRealization.componentRealFrobeniusPowerTrace
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮] : L := by
  let D := R.atPlace ℓ L ι
  letI : Module.Finite L
      ((D.action ξ).component N m 𝒞 R.quotient ξ ℓ L ι) :=
    Module.Finite.equiv (D.componentComparison ξ).symm
  exact LinearMap.trace L _
    ((D.action ξ).componentGaloisEndomorphism N m 𝒞 R.quotient ξ ℓ L ι
      ((realEulerClosureGaloisHom N
        (NumberField.geometricFrobenius (realCyclotomicField N) Qbar 𝔮 Q :
          Qbar ≃ₐ[realCyclotomicField N] Qbar)) ^
        P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N))))

/-- The same algebraic normalized Euler trace controls the labelled quotient
cohomology at every coefficient place. In particular, this applies at good
primes of residue characteristic two when `N` is odd and prime to two. -/
theorem CommonRealEulerQuotientRealization.componentRealFrobeniusPowerTrace_eq
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    R.componentRealFrobeniusPowerTrace N m 𝒞 ξ ℓ L ι 𝔮 P Q =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  exact (R.atPlace ℓ L ι).realGeometricFrobeniusPower_trace_eq_normalizedEulerTrace
    N m 𝒞 R.quotient ξ ℓ L ι hN h5 hm hmN q hq hqN
    𝔮 P hP hℓ Q hξ

/-- The real-prime Frobenius-power trace on the actual quotient is obtained
from the finite hypergeometric value through one algebraic scalar. The
finite-sum equality is the direct normalization calculation of
[TripathiGoswamiRevised, equation (2.4)]. -/
theorem CommonRealEulerQuotientRealization.componentRealFrobeniusPowerTrace_mccarthyValue
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (𝔮 : Ideal (𝓞 (realCyclotomicField N))) [𝔮.IsMaximal]
    [𝔮.LiesOver (Ideal.span {(q : ℤ)})]
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver 𝔮]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal] [Q.LiesOver 𝔮]
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1) :
    ∃ a : cyclotomicField N,
      R.componentRealFrobeniusPowerTrace N m 𝒞 ξ ℓ L ι 𝔮 P Q = ι a ∧
      (cyclotomicField N).val a =
        mccarthyValue N P hP m θ (realEulerParameter N ξ) hξ := by
  refine ⟨normalizedCyclotomicEulerTrace N P.asIdeal hP m
      (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le), ?_, ?_⟩
  · exact R.componentRealFrobeniusPowerTrace_eq N m 𝒞 ξ ℓ L ι
      hN h5 hm hmN q hq hqN 𝔮 P hP hℓ Q hξ
  · exact normalizedCyclotomicEulerTrace_val_mccarthyValue N P hP m hm hmN
      θ hθ (realEulerParameter N ξ) hξ

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- Good reduction of the chosen descent gives trivial inertia on the
labelled component of the actual quotient fibre. The comparison is for the
full real-field Galois action, so this applies to all real-field inertia
elements, including those outside the cyclotomic subgroup. -/
theorem RealEulerQuotientPlace.component_inertia_eq_one
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver (Ideal.span {(q : ℤ)})]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      (R.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι
        (realEulerClosureGaloisHom N g) = 1 := by
  have hdesc := R.descent.inertia_eq_one_of_goodUnit N m ℓ L ι
    hN h5 hm hmN 𝒞 q hq hqN P hP hℓ Q ξ hξ
  intro g hg
  apply LinearMap.ext
  intro v
  apply (R.componentComparison ξ).injective
  have hi := R.componentComparison_galois ξ (realEulerClosureGaloisHom N g) v
  rw [hdesc g hg] at hi
  simpa only [RealCyclotomicQuotientAction.componentGaloisEndomorphism_apply,
    Module.End.one_apply, LinearEquiv.apply_symm_apply] using hi

/-- The common quotient chosen before the coefficient place has an
unramified labelled component at every eligible good prime. This includes
residue characteristic two. -/
theorem CommonRealEulerQuotientRealization.component_inertia_eq_one
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (q : ℕ) (hq : q.Prime) (hqN : q ≠ N)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver (Ideal.span {(q : ℤ)})]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    ∀ g ∈ Q.inertia (Qbar ≃ₐ[realCyclotomicField N] Qbar),
      ((R.atPlace ℓ L ι).action ξ).componentGaloisEndomorphism
        N m 𝒞 R.quotient ξ ℓ L ι (realEulerClosureGaloisHom N g) = 1 := by
  exact (R.atPlace ℓ L ι).component_inertia_eq_one
    N m 𝒞 R.quotient ξ ℓ L ι hN h5 hm hmN q hq hqN P hP hℓ Q hξ

end HilbertModularity.Hypergeometric
