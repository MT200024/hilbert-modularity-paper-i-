/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientDescent
public import HilbertModularity.Hypergeometric.ProperFrobeniusComparison

/-! # Traces on a labelled quotient cohomology component

The comparison supplied by [GPRV, Theorem 9.2] intertwines the Galois action
on the labelled component of the actual quotient fibre with the chosen
descended local system. The resulting trace equality is linear algebra; it
does not assert a Frobenius value or introduce another geometric input.
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

/-- The actual Galois endomorphism on the real-labelled component of the
quotient fibre's degree-one cohomology. -/
def RealCyclotomicQuotientAction.componentGaloisEndomorphism
    (A : RealCyclotomicQuotientAction N m 𝒞 𝒬 ξ ℓ L)
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N)) :
    Module.End L (A.component N m 𝒞 𝒬 ξ ℓ L ι) where
  toFun v := ⟨geometricRealEulerQuotientGaloisRepresentation
      N m 𝒞 𝒬 ξ ℓ L g v.1,
    A.component_stable N m 𝒞 𝒬 ξ ℓ L ι g v⟩
  map_add' x y := by
    ext
    exact map_add _ _ _
  map_smul' c x := by
    ext
    exact map_smul _ _ _

omit [CompleteSpace L] [ContinuousSMul ℚ_[ℓ] L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The labelled component action is the restriction of the Galois action
on the actual quotient fibre. -/
theorem RealCyclotomicQuotientAction.componentGaloisEndomorphism_apply
    (A : RealCyclotomicQuotientAction N m 𝒞 𝒬 ξ ℓ L)
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (v : A.component N m 𝒞 𝒬 ξ ℓ L ι) :
    A.componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι g v =
      ⟨geometricRealEulerQuotientGaloisRepresentation N m 𝒞 𝒬 ξ ℓ L g v.1,
        A.component_stable N m 𝒞 𝒬 ξ ℓ L ι g v⟩ := by
  rfl

omit [CompleteSpace L] [ContinuousSMul ℚ_[ℓ] L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The trace on the labelled cohomology of the common quotient equals the
trace of its chosen descended local system at cyclotomic-field Galois elements. This uses
the cited comparison as an intertwiner, then invariance of matrix trace under
change of basis; the trace value itself is not an assumption. -/
theorem RealEulerQuotientPlace.componentGalois_trace_eq_descent
    (P : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (g : Qbar ≃ₐ[cyclotomicField N] Qbar) :
    letI : Module.Finite L ((P.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
      Module.Finite.equiv (P.componentComparison ξ).symm
    LinearMap.trace L _
        ((P.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι
          (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g))) =
      LinearMap.trace L _
        (P.descent.localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ)
          (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g))) := by
  let : Module.Finite L
      (P.descent.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    P.descent.localSystem.finite _
  let : Module.Finite L ((P.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
    Module.Finite.equiv (P.componentComparison ξ).symm
  let f := (P.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι
    (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g))
  let h := P.descent.localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)
    (realEulerClosureGaloisHom N (restrictCyclotomicGalois N g))
  have hconj : (P.componentComparison ξ).conj f = h := by
    apply LinearMap.ext
    intro w
    have hi := P.componentComparison_intertwines_restricted N m 𝒞 𝒬 ℓ L ι ξ g
      ((P.componentComparison ξ).symm w)
    change (P.componentComparison ξ)
        (f ((P.componentComparison ξ).symm w)) =
      h ((P.componentComparison ξ) ((P.componentComparison ξ).symm w)) at hi
    rw [LinearEquiv.apply_symm_apply] at hi
    exact hi
  let b := Module.Free.chooseBasis L
    (P.descent.localSystem.toFunctor.obj
      (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ)))
  have ht : LinearMap.trace L _ ((P.componentComparison ξ).conj f) =
      LinearMap.trace L _ f := by
    rw [LinearMap.trace_eq_matrix_trace L b,
      LinearMap.trace_eq_matrix_trace L (b.map (P.componentComparison ξ).symm)]
    congr 1
  rw [hconj] at ht
  exact ht.symm

/-- The labelled cohomology of the common real quotient has the normalized
Euler trace at every good geometric Frobenius.  The first equality is the
proved quotient/descent conjugacy; the second is the independently normalized
proper Euler cohomology calculation. -/
theorem RealEulerQuotientPlace.geometricFrobenius_trace_eq_normalizedEulerTrace
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (R : RealEulerQuotientPlace N m 𝒞 𝒬 ℓ L ι)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L ((R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
      Module.Finite.equiv (R.componentComparison ξ).symm
    LinearMap.trace L _
      ((R.action ξ).componentGaloisEndomorphism N m 𝒞 𝒬 ξ ℓ L ι
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q))) =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  let : Module.Finite L ((R.action ξ).component N m 𝒞 𝒬 ξ ℓ L ι) :=
    Module.Finite.equiv (R.componentComparison ξ).symm
  exact (R.componentGalois_trace_eq_descent N m 𝒞 𝒬 ξ ℓ L ι
    (absoluteGeometricFrobenius N P Q)).trans
    (R.descent.geometricFrobenius_trace_eq_normalizedEulerTrace
      N m ℓ L ι hN h5 hm hmN 𝒞 P hP hℓ Q ξ hξ)

end HilbertModularity.Hypergeometric
