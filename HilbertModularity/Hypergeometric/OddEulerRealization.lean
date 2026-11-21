/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFamily
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientDescent
public import HilbertModularity.Hypergeometric.CoprimeEulerRealization
public import HilbertModularity.Hypergeometric.Parameters
public import HilbertModularity.Hypergeometric.GaloisRealizationHodgeTate
public import HilbertModularity.Hypergeometric.GaloisRealizationFiniteRamification
public import HilbertModularity.Hypergeometric.ProperFrobeniusComparison

/-! # The selected odd coprime Euler realization

For odd conductor the auxiliary GPRV character is trivial. The symmetric
Euler parameters satisfy GPRV's irreducibility test by their primitive
scaled exponents. One smooth proper Euler family and its involution quotient
are chosen before any coefficient prime or nonsingular fibre.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open NumberField.LocalGalois
open scoped NumberField
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

/-- The scaled differences in [GPRV, Lemma 8.5, p. 30] have gcd one.
The numerator fraction has exact denominator `N`, recorded as additive
order `N` modulo integers. Thus the Euler curve satisfies the source
condition `(Irr)` for every coprime exponent, including conductor three. -/
theorem oddEuler_irr_certificate
    (N m : ℕ) [NeZero N] (hcop : m.Coprime N) :
    addOrderOf (((m : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) = N ∧
    ∃ u v w : ℤ,
      (N : ℚ) * (1 - (1 - (m : ℚ) / N)) = u ∧
      (N : ℚ) * ((1 - (m : ℚ) / N) - 1) = v ∧
      (N : ℚ) * ((m : ℚ) / N - 1) = w ∧
      Nat.gcd (Int.gcd u v) (Int.gcd w N) = 1 :=
  ⟨numeratorParameter_addOrderOf hcop,
    symmetricParameters_irreducible (NeZero.ne N) hcop⟩

/-- The full cyclotomic field contains the normal closure of its real
subfield for any nonzero conductor, including composite conductors. -/
theorem realCyclotomicNormalClosure_le_full_of_neZero
    (N : ℕ) [NeZero N] :
    IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤
      cyclotomicField N :=
  IntermediateField.normalClosure_le_iff_of_normal.mpr (realCyclotomicField_le N)

/-- The canonical completion map from the full cyclotomic coefficient
field at a specified place. -/
def oddEulerCoefficientMap
    (N : ℕ) [NeZero N]
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [Field L] [Algebra (w.adicCompletion (cyclotomicField N)) L] :
    cyclotomicField N →+* L :=
  (algebraMap (w.adicCompletion (cyclotomicField N)) L).comp
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))

/-- The chosen local RM label is the exponent-`m` image under the
same canonical cyclotomic coefficient map, with no second power of `m`. -/
theorem oddEulerCoefficientMap_tau_one
    (N m : ℕ) [NeZero N] (hcop : m.Coprime N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (L : Type) [Field L] [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L] :
    coefficientEmbeddingAbovePrime N m hcop
      (cyclotomicField N)
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans
        (realCyclotomicNormalClosure_le_full_of_neZero N)) w L (tau N 1) =
      oddEulerCoefficientMap N w L ((root N) ^ m + (root N)⁻¹ ^ m) := by
  rw [coefficientEmbeddingAbovePrime_tau_one]
  have hv : IntermediateField.inclusion
      ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans
        (realCyclotomicNormalClosure_le_full_of_neZero N)) (tau N m) =
      (root N) ^ m + (root N)⁻¹ ^ m := by
    apply Subtype.ext
    rfl
  rw [hv]
  rfl

/-- The actual exponent-`m` smooth proper Euler family, selected once
from the tame cyclic-cover construction [EsnaultViehweg, §3]. -/
def chosenOddEulerFamily
    (N m : ℕ) [NeZero N] (h3 : 3 ≤ N) (_hOdd : Odd N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N) :
    SmoothProperEulerFamily N m :=
  chosenCoprimeEulerFamily N m h3 hm hmN hcop

/-- One quotient, fixed before its coefficient-place realizations, for
[GPRV, Theorem 9.2 and Proposition 9.5, pp. 40–41]. -/
def chosenOddEulerRealization
    (N m : ℕ) [NeZero N] (h3 : 3 ≤ N) (hOdd : Odd N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N) :
    CommonRealEulerQuotientRealization N m
      (chosenOddEulerFamily N m h3 hOdd hm hmN hcop) :=
  chosenCoprimeRawEulerRealization N m h3 hm hmN hcop

/-- The selected odd Euler action has rank two at every coefficient place
and every nonsingular fibre, with the same chosen quotient throughout. -/
theorem chosenOddEulerRealization_rank_two
    (N m : ℕ) [NeZero N] (h3 : 3 ≤ N) (hOdd : Odd N)
    (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenOddEulerFamily N m h3 hOdd hm hmN hcop
    let R := chosenOddEulerRealization N m h3 hOdd hm hmN hcop
    Module.finrank L
      ((R.placeDescent N m 𝒞 ℓ L ι).localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) = 2 := by
  dsimp only
  rw [CommonRealEulerQuotientRealization.placeDescent_eq_atPlace]
  exact ((chosenOddEulerRealization N m h3 hOdd hm hmN hcop).atPlace
    ℓ L ι).descent.rank_two ξ


/-- The actual selected odd coprime Euler realization has one Hodge–Tate
weight zero and one weight one at every local label. The same chosen quotient
is used at the specified coefficient place [GPRV, §10.1, Case (1), p. 44]. -/
theorem chosenOddEulerRealization_labelledHodgeTate
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenOddEulerFamily N m h3 hOdd hm hmN hcop
    let R := chosenOddEulerRealization N m h3 hOdd hm hmN hcop
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
  exact commonRealEulerQuotientRealization_labelledHodgeTate_of_odd_coprime
    N m p h3 hOdd hm hmN hcop
    (chosenOddEulerFamily N m h3 hOdd hm hmN hcop)
    (chosenOddEulerRealization N m h3 hOdd hm hmN hcop) L ι ξ

/-- The actual chosen odd Euler fibre has finitely ramified normalized
determinant outside its parameter, conductor and coefficient bad primes.
The same chosen quotient and exponent label are retained throughout. -/
theorem chosenOddEulerRealization_normalizedDeterminant_unramified
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (g : AlgebraicClosure (realCyclotomicField N) ≃ₐ[realCyclotomicField N]
      AlgebraicClosure (realCyclotomicField N))
    (hg : g ∈ Q.inertia _)
    (hq : q ∉ properEulerBadPrimesOfConductor N ℓ ξ) :
    let 𝒞 := chosenOddEulerFamily N m h3 hOdd hm hmN hcop
    let R := chosenOddEulerRealization N m h3 hOdd hm hmN hcop
    let D := R.placeDescent N m 𝒞 ℓ L ι
    puncturedFiberNormalizedDeterminant (realCyclotomicField N) ℓ L ξ
      D.localSystem g = 1 := by
  let 𝒞 := chosenOddEulerFamily N m h3 hOdd hm hmN hcop
  let R := chosenOddEulerRealization N m h3 hOdd hm hmN hcop
  let D := R.placeDescent N m 𝒞 ℓ L ι
  exact D.normalizedDeterminant_inertia_eq_one_of_coprime
    N m ℓ L ι h3 hm hmN hcop 𝒞 ξ q Q g hg hq

/-- Geometric Frobenius on the one chosen odd Euler descent has exactly the
normalized cyclotomic Euler trace at every good prime away from the
coefficient characteristic. The odd reflection factor is one, including
when the good prime has residue characteristic two. -/
theorem chosenOddEulerRealization_geometricFrobenius_trace
    (N m ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (h3 : 3 ≤ N) (hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra ℚ_[ℓ] L] [ContinuousSMul ℚ_[ℓ] L]
    [FiniteDimensional ℚ_[ℓ] L]
    (ι : cyclotomicField N →+* L)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hℓ : (ℓ : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (hξ : P.GoodUnit (realEulerParameter N ξ)) :
    let 𝒞 := chosenOddEulerFamily N m h3 hOdd hm hmN hcop
    let R := chosenOddEulerRealization N m h3 hOdd hm hmN hcop
    let D := R.placeDescent N m 𝒞 ℓ L ι
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
  let 𝒞 := chosenOddEulerFamily N m h3 hOdd hm hmN hcop
  let R := chosenOddEulerRealization N m h3 hOdd hm hmN hcop
  let D := R.placeDescent N m 𝒞 ℓ L ι
  exact D.geometricFrobenius_trace_eq_normalizedEulerTrace_of_odd_coprime
    N m ℓ L ι h3 hOdd hm hmN hcop 𝒞 P hP hℓ Q ξ hξ

end HilbertModularity.Hypergeometric
