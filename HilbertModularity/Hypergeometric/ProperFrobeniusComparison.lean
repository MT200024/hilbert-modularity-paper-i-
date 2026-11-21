/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisDescent
public import HilbertModularity.Hypergeometric.FrobeniusComparison
public import HilbertModularity.Hypergeometric.SpecializationInvolution
public import Mathlib.LinearAlgebra.Trace

/-! # Frobenius on the proper Euler realization

The fixed `χ₀` summand of the exponent-`m` proper Euler curve is the object in
[GPRV, Theorem 7.4]. Its raw trace is an admitted literature input below.
Conjugating by the comparison of the chosen generic real-field descent then
gives the trace of its arithmetic specialization. No finite-sum normalization
or Jacobi-sign identity is admitted in that comparison.
-/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic
open IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Cyclotomic

attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]
/-- The `κ_N^m` normalization factor is one at every prime away from an odd
level.  This is the same order argument as the arithmetic reflection sign. -/
theorem cyclotomicPowerResidueMulChar_neg_one_pow_of_odd
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hodd : Odd N) (m : ℕ) :
    (cyclotomicPowerResidueMulChar N P.asIdeal hP ^ m) (-1) = 1 := by
  have hq : (powerResidueMulChar N P.asIdeal hP ^ m) (-1) = 1 := by
    simpa only [coe_reflectionSign, Units.val_one] using
      congrArg Units.val (reflectionSign_eq_one_of_odd N P hP hodd m)
  have hc := (cyclotomicPowerResidueMulChar N P.asIdeal hP).pow_apply_coe m
    (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ)
  have hp := (powerResidueMulChar N P.asIdeal hP).pow_apply_coe m
    (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ)
  have hc' : (cyclotomicPowerResidueMulChar N P.asIdeal hP ^ m) (-1) =
      cyclotomicPowerResidueMulChar N P.asIdeal hP (-1) ^ m := by
    simpa only [Units.val_neg, Units.val_one] using hc
  have hp' : (powerResidueMulChar N P.asIdeal hP ^ m) (-1) =
      powerResidueMulChar N P.asIdeal hP (-1) ^ m := by
    simpa only [Units.val_neg, Units.val_one] using hp
  apply (cyclotomicField N).val.injective
  calc
    (cyclotomicField N).val
        ((cyclotomicPowerResidueMulChar N P.asIdeal hP ^ m) (-1)) =
      (cyclotomicField N).val
        (cyclotomicPowerResidueMulChar N P.asIdeal hP (-1) ^ m) :=
      congrArg _ hc'
    _ = powerResidueMulChar N P.asIdeal hP (-1) ^ m := by
      rw [map_pow, cyclotomicPowerResidueMulChar_val]
    _ = 1 := by rw [← hp', hq]
    _ = (cyclotomicField N).val 1 := (map_one _).symm

/-- For odd `N`, the normalized algebraic trace is the negative of the raw
fixed-character Euler count, without a quadratic correction. -/
theorem normalizedCyclotomicEulerTrace_eq_odd
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hodd : Odd N) (m : ℕ)
    (t : 𝓞 (cyclotomicField N) ⧸ P.asIdeal) :
    normalizedCyclotomicEulerTrace N P.asIdeal hP m t =
      -cyclotomicEulerCurveSum N P.asIdeal hP m t := by
  simp only [normalizedCyclotomicEulerTrace_eq_mul,
    cyclotomicPowerResidueMulChar_neg_one_pow_of_odd N P hP hodd m, neg_one_mul]

end HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

universe u

/-- [GPRV, Theorem 7.4 and Assumption 1], applied to the actual proper
Euler curve for any coprime exponents `m,N-m,m,N-m`. The geometric prime is away from
`N` and the coefficient characteristic, and `GoodUnit` keeps the four branch
sections distinct. Since the polynomial has degree `N+m`, the infinity term
of [GPRV, Definition 7.2] is zero. The deck projector is the fixed `χ₀`
projector on this exponent-`m` curve. Frobenius is geometric. -/
theorem properEuler_fixedPrimitive_geometricFrobenius_trace_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    [Module.Finite L
      (properPrimitiveGaloisSubrepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι).toSubmodule] :
    LinearMap.trace L _
      (properPrimitiveQbarGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
        (absoluteGeometricFrobenius N P Q)) =
      -ι (cyclotomicEulerCurveSum N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  sorry

/-- The prime raw Frobenius trace interface follows from the same
coprime-exponent GPRV source statement. -/
theorem properEuler_fixedPrimitive_geometricFrobenius_trace
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    [Module.Finite L
      (properPrimitiveGaloisSubrepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι).toSubmodule] :
    LinearMap.trace L _
      (properPrimitiveQbarGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι
        (absoluteGeometricFrobenius N P Q)) =
      -ι (cyclotomicEulerCurveSum N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact properEuler_fixedPrimitive_geometricFrobenius_trace_of_coprime
    N m ℓ L ι (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop
    𝒞 P hP hℓ Q ξ hξ

/-- The raw geometric Frobenius trace transports from the actual proper
fixed-character cohomology to the specialization of the one chosen generic
real-field descent. This is linear-equivalence invariance of trace. -/
theorem ProperEulerRealDescent.geometricFrobenius_trace_eq_eulerCurveSum_of_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L
        (D.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q))) =
      -ι (cyclotomicEulerCurveSum N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  let : Module.Finite L
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    D.localSystem.finite _
  let : Module.Finite L
      (properPrimitiveGaloisSubrepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι).toSubmodule :=
    Module.Finite.equiv (D.properComparison ξ)
  let g : Qbar ≃ₐ[cyclotomicField N] Qbar := absoluteGeometricFrobenius N P Q
  let f := D.localSystem.arithmeticRepresentation
    (ProjectiveLine.puncturedPoint _ ξ)
    ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N) g)
  have hconj : (D.properComparison ξ).conj f =
      properPrimitiveQbarGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι g := by
    apply LinearMap.ext
    intro w
    have h := D.properComparison_intertwines ξ g ((D.properComparison ξ).symm w)
    change (D.properComparison ξ) (f ((D.properComparison ξ).symm w)) =
      properPrimitiveQbarGaloisRepresentation N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ) ℓ L ι g w
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hraw := properEuler_fixedPrimitive_geometricFrobenius_trace_of_coprime N m ℓ L ι
    h3 hm hmN hcop 𝒞 P hP hℓ Q ξ hξ
  let b := Module.Free.chooseBasis L
    (D.localSystem.toFunctor.obj
      (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ)))
  have ht : LinearMap.trace L _ ((D.properComparison ξ).conj f) =
      LinearMap.trace L _ f := by
    rw [LinearMap.trace_eq_matrix_trace L (b.map (D.properComparison ξ)),
      LinearMap.trace_eq_matrix_trace L b]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, LinearEquiv.conj_apply]
  rw [hconj] at ht
  exact ht.symm.trans hraw


/-- The prime raw-trace transport is the same chosen descent applied
to the coprime-exponent proper-cohomology Frobenius formula. -/
theorem ProperEulerRealDescent.geometricFrobenius_trace_eq_eulerCurveSum
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L
        (D.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q))) =
      -ι (cyclotomicEulerCurveSum N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact D.geometricFrobenius_trace_eq_eulerCurveSum_of_coprime N m ℓ L ι
    (le_trans (by decide : 3 ≤ 5) h5) hm hmN hcop
    𝒞 P hP hℓ Q ξ hξ

/-- At odd coprime level, the specialization of the chosen generic descent has
the normalized cyclotomic Euler trace.  The normalization factor is proved to
be one; the only admitted input is the raw proper-cohomology Frobenius formula
above. -/
theorem ProperEulerRealDescent.geometricFrobenius_trace_eq_normalizedEulerTrace_of_odd_coprime
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (h3 : 3 ≤ N) (hodd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L
        (D.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q))) =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  simpa only [normalizedCyclotomicEulerTrace_eq_odd N P hP hodd m,
      map_neg] using
    D.geometricFrobenius_trace_eq_eulerCurveSum_of_coprime N m ℓ L ι
      h3 hm hmN hcop 𝒞 P hP hℓ Q ξ hξ


/-- The prime normalized Euler trace is the specialization of the
odd-coprime trace deduction, with the same chosen descent. -/
theorem ProperEulerRealDescent.geometricFrobenius_trace_eq_normalizedEulerTrace
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (L : Type u) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (D : ProperEulerRealDescent N m ℓ L ι 𝒞)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    letI : Module.Finite L
        (D.localSystem.toFunctor.obj
          (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
      D.localSystem.finite _
    LinearMap.trace L _
      (D.localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)
        ((realEulerClosureGaloisHom N).comp (restrictCyclotomicGalois N)
          (absoluteGeometricFrobenius N P Q))) =
      ι (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)) := by
  have hodd : Odd N := hN.odd_of_ne_two (by omega)
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact D.geometricFrobenius_trace_eq_normalizedEulerTrace_of_odd_coprime
    N m ℓ L ι (le_trans (by decide : 3 ≤ 5) h5) hodd hm hmN hcop
    𝒞 P hP hℓ Q ξ hξ

end HilbertModularity.Hypergeometric
