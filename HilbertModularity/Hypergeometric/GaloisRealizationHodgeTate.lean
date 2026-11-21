/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFiniteRamification
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientDescent
public import HilbertModularity.Hypergeometric.DarmonWeightComparison

/-! # Hodge–Tate weights of the selected Euler quotient realization

The original odd-coprime fibre, with its fixed coefficient embedding and the unshifted
cohomological convention, has weights `{0,1}` at every local label. This is
the external Hodge calculation in [GPRV, §10.1] combined with smooth proper
Hodge–Tate comparison [src_brinon_conrad, Theorem 2.2.3 and Example 2.4.13].
The finite-character deduction from these weights is proved separately.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open NumberField.LocalGalois
open scoped NumberField

namespace HilbertModularity.Hypergeometric

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

/-- [GPRV, §10.1, complementary branch fractions] computes one holomorphic
and one antiholomorphic dimension in every `χ₀` coefficient label of the
exponent-`m` Euler cover. [src_brinon_conrad, Theorem 2.2.3 and Example
2.4.13] identifies these with the labelled Hodge–Tate weights of smooth
proper degree-one étale cohomology. The quotient descent here is the chosen
same-map `R.placeDescent` of [GPRV, Proposition 9.5/Theorem 9.2/(76)],
whose fixed-projector comparison retains `χ₀(ζ)=ι(ζ)`. The statement refers
to the *original* two-dimensional arithmetic fibre, with no Tate twist.

For coprime N, [GPRV, §10.1, Case (1), p. 44] gives the Hodge
polynomial x+y because the denominator pair consists of integers, for every
coefficient embedding. The raw quotient has these weights for even N as
well: its effective normalization differs by finite κ [GPRV, Definition
8.8, Corollary 8.10 and Lemma 9.4], which has weight zero. N=3 is
included. This named
literature premise supplies only local comparison and weight
multiplicities. It supplies no determinant finite order, Darmon comparison,
automorphy or Frobenius trace. -/
theorem commonRealEulerQuotientRealization_labelledHodgeTate_of_coprime
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := R.placeDescent N m 𝒞 p L ι
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.restrictScalars ℚ_[p]
          ((puncturedFiberCoordinateRepresentation
            (realCyclotomicField N) L ξ D.localSystem).comp
            (localGaloisRestriction p (realCyclotomicField N) q))))) ∧
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]]
          AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        ((puncturedFiberCoordinateRepresentation
          (realCyclotomicField N) L ξ D.localSystem).comp
          (localGaloisRestriction p (realCyclotomicField N) q)) n τ) =
        (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) := by
  sorry


/-- The checked odd Hodge statement is the specialization of the raw
coprime quotient input; finite κ twists preserve the same weights. -/
theorem commonRealEulerQuotientRealization_labelledHodgeTate_of_odd_coprime
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (_hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := R.placeDescent N m 𝒞 p L ι
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.restrictScalars ℚ_[p]
          ((puncturedFiberCoordinateRepresentation
            (realCyclotomicField N) L ξ D.localSystem).comp
            (localGaloisRestriction p (realCyclotomicField N) q))))) ∧
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]]
          AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        ((puncturedFiberCoordinateRepresentation
          (realCyclotomicField N) L ξ D.localSystem).comp
          (localGaloisRestriction p (realCyclotomicField N) q)) n τ) =
        (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) := by
  exact commonRealEulerQuotientRealization_labelledHodgeTate_of_coprime
    N m p h3 hm hmN hcop 𝒞 R L ι ξ

/-- The prime Hodge–Tate statement is the specialization of the odd
coprime GPRV source interface for the same chosen quotient. -/
theorem commonRealEulerQuotientRealization_labelledHodgeTate
    (N m p : ℕ) [NeZero N] [Fact N.Prime] [Fact p.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := R.placeDescent N m 𝒞 p L ι
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.restrictScalars ℚ_[p]
          ((puncturedFiberCoordinateRepresentation
            (realCyclotomicField N) L ξ D.localSystem).comp
            (localGaloisRestriction p (realCyclotomicField N) q))))) ∧
    (∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]]
          AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p
          (K := q.adicCompletion (realCyclotomicField N)))
        ((puncturedFiberCoordinateRepresentation
          (realCyclotomicField N) L ξ D.localSystem).comp
          (localGaloisRestriction p (realCyclotomicField N) q)) n τ) =
        (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) := by
  have hOdd : Odd N := hN.odd_of_ne_two (by omega)
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact commonRealEulerQuotientRealization_labelledHodgeTate_of_odd_coprime
    N m p (le_trans (by decide : 3 ≤ 5) h5) hOdd hm hmN hcop
    𝒞 R L ι ξ

end HilbertModularity.Hypergeometric
