/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientRealPrime
public import HilbertModularity.Hypergeometric.GaloisRealizationGenericMonodromy
public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem
public import HilbertModularity.RepresentationTheory.SemisimpleTransport
public import HilbertModularity.Hypergeometric.GaloisRealizationGoodPrimeSet

/-! # Compatible realizations of the chosen real Euler quotient

The quotient and exponent-`m` projector are chosen before the coefficient
place. We use the cyclotomic coefficient number field, so every completion
receives the same fixed embedding through its canonical algebra map.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open HilbertModularity.LocalSpecialization
open scoped NumberField

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N]
  (𝒞 : SmoothProperEulerFamily N m)
  (R : CommonRealEulerQuotientRealization N m 𝒞)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))

local instance (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (w.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (w.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- The exact selected descent at a coefficient place of the one fixed
cyclotomic number field. The embedding is the canonical map to that
completion, so no independent label is chosen. -/
def commonEulerCompletionDescent
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    ProperEulerRealDescent N m (NumberField.primeBelow (cyclotomicField N) w)
      (w.adicCompletion (cyclotomicField N))
      (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) 𝒞 := by
  letI : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  exact R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
    (w.adicCompletion (cyclotomicField N))
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))

/-- The completion descent is the place descent for the canonical embedding
of the same cyclotomic coefficient field. -/
@[simp] theorem commonEulerCompletionDescent_eq_placeDescent
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    commonEulerCompletionDescent N m 𝒞 R w =
      R.placeDescent N m 𝒞 (NumberField.primeBelow (cyclotomicField N) w)
        (w.adicCompletion (cyclotomicField N))
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) := (rfl)

/-- The rank-two arithmetic action of the same quotient at an actual
coefficient completion, in continuous coordinates. -/
def commonEulerCompletionAction
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    Representation (w.adicCompletion (cyclotomicField N))
      (HilbertModularForms.AbsoluteGalois (realCyclotomicField N))
      (Fin 2 → w.adicCompletion (cyclotomicField N)) := by
  letI : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  exact D.localSystem.arithmeticRepresentationOfFinrankEq
    (ProjectiveLine.puncturedPoint _ ξ) 2 (D.rank_two ξ)

/-- The coordinate action is equivariantly the original selected arithmetic
fibre, retaining the same fixed `χ₀` projector. -/
def commonEulerCompletionActionEquiv
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (commonEulerCompletionAction N m 𝒞 R ξ w).Equiv
      ((commonEulerCompletionDescent N m 𝒞 R w).localSystem.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint _ ξ)) := by
  letI : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  exact (D.localSystem.arithmeticEquivOfFinrankEq
    (ProjectiveLine.puncturedPoint _ ξ) 2 (D.rank_two ξ)).symm

/-- Continuity of each coordinate entry follows from the one descended
local system's topology. -/
theorem continuous_commonEulerCompletionAction_entry
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (i j : Fin 2) :
    Continuous (fun g : HilbertModularForms.AbsoluteGalois
      (realCyclotomicField N) =>
      commonEulerCompletionAction N m 𝒞 R ξ w g (Pi.single j 1) i) := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  exact D.localSystem.continuous_arithmeticRepresentationOfFinrankEq_entry
    (ProjectiveLine.puncturedPoint _ ξ) 2 (D.rank_two ξ) i j

/-- The geometric exceptional set depends on the chosen parameter and level,
not on the coefficient place. -/
def commonEulerBadPrimes
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    Set (HeightOneSpectrum (𝓞 (realCyclotomicField N))) :=
  badPrimesBelow (K := realCyclotomicField N)
    (realEulerParameter N ξ) N

/-- The canonical geometric exceptional set is the actual bad-prime set of
this Euler parameter and conductor. -/
theorem commonEulerBadPrimes_eq :
    commonEulerBadPrimes N ξ =
      badPrimesBelow (K := realCyclotomicField N) (realEulerParameter N ξ) N := (rfl)

/-- The actual parameter and conductor have only finitely many bad primes. -/
theorem commonEulerBadPrimes_finite (hN : N.Prime) :
    (commonEulerBadPrimes N ξ).Finite := by
  have hx0 : realEulerParameter N ξ ≠ 0 :=
    (realEulerParameter_isUnit N ξ).ne_zero
  have hx1 : realEulerParameter N ξ ≠ 1 := by
    intro hx
    exact (one_sub_realEulerParameter_isUnit N ξ).ne_zero
      (by rw [hx, sub_self])
  exact badPrimesBelow_finite (K := realCyclotomicField N)
    (realEulerParameter N ξ) hx0 hx1 N hN.ne_zero

/-- Removing the coefficient characteristic separately turns the canonical
bad set for `N` into the good set for `N * ℓ`, without enlarging the
geometric exceptional set. -/
theorem commonEulerBadPrimes_away_product
    (ℓ : ℕ) (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ)
    (hℓ : (ℓ : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal) :
    q ∉ badPrimesBelow (K := realCyclotomicField N)
      (realEulerParameter N ξ) (N * ℓ) :=
  not_mem_badPrimesBelow_mul_of_away (K := realCyclotomicField N)
    (realEulerParameter N ξ) N ℓ q hq hℓ

/-- At every completion away from its own residue characteristic, the actual
rank-two Euler action is unramified outside the canonical geometric set. -/
theorem commonEulerCompletionAction_unramified
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (hℓ : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N))
    (hg : g ∈ Q.inertia
      (HilbertModularForms.AbsoluteGalois (realCyclotomicField N))) :
    commonEulerCompletionAction N m 𝒞 R ξ w g = 1 := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  have hraw := D.inertia_eq_one_outside_badPrimes_realClosure N m
    (NumberField.primeBelow (cyclotomicField N) w)
    (w.adicCompletion (cyclotomicField N))
    (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N)))
    hN h5 hm hmN 𝒞 ξ q
    (commonEulerBadPrimes_away_product N ξ
      (NumberField.primeBelow (cyclotomicField N) w) q hq hℓ)
    Q g hg
  exact (commonEulerCompletionActionEquiv N m 𝒞 R ξ w).apply_eq_one_of g hraw

/-- [MilneAV, Chapter IV, Appendix, Theorem 3, p. 159] records Faltings'
semisimplicity for an abelian variety over a number field. Applied to the
Jacobian of the actual smooth proper Euler quotient, with the standard
curve-`H¹`/Jacobian Tate comparison and characteristic-zero coefficient
extension, it gives semisimplicity of this fixed labelled component.

This source input concerns only the selected cohomological action at one
completion. It does not assume compatible polynomials or automorphy. -/
theorem commonEulerCompletionAction_isSemisimple
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (commonEulerCompletionAction N m 𝒞 R ξ w).IsSemisimpleRepresentation := by
  sorry

/-- [GPRV, Definition 8.2 and Theorem 9.2] give the single quotient motive
and its number-field coefficient action. At a good prime the smooth proper
special fibre and its fixed projector yield one algebraic Frobenius polynomial
before choosing `ℓ`. The standard Jacobian endomorphism polynomial is
independent of the auxiliary prime by [MilneAV, Chapter I, Theorem 10.9,
pp. 46–47; Remark 10.11, p. 47; Proposition 10.20, pp. 50–52];
[src_milne_lec, Theorem 20.4, pp. 127–128] compares the smooth proper
cohomology at each auxiliary prime. The polynomial is attached to the
actual chosen quotient action, with the same `χ₀` coefficient label at
every completion. The residue characteristic is excluded at each completion;
the geometric bad set is the canonical `badPrimesBelow x N`.
At prime conductor this is the full labelled quotient `H¹`; at composite
conductor the source uses the new part. The theorem assumes an already chosen
`R` and does not assert its existence outside the prime case.

The cited passages do not state this project's fixed-component
`NumberFieldCompatibleSystem` interface verbatim; that projector and
coefficient-label passage is included in this explicitly admitted standard
comparison and needs source review at integration. It asserts neither the
normalized McCarthy trace nor modularity. -/
theorem exists_commonEulerCompletion_frobeniusPolynomial
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ) :
    ∃ T : Polynomial (cyclotomicField N),
      ∀ (w : HeightOneSpectrum (𝓞 (cyclotomicField N))),
        (NumberField.primeBelow (cyclotomicField N) w :
          𝓞 (realCyclotomicField N)) ∉ q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
          [Q.IsMaximal] [Q.LiesOver q.asIdeal],
          (commonEulerCompletionAction N m 𝒞 R ξ w
            (NumberField.geometricFrobenius (realCyclotomicField N)
              (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q)).charpoly =
            T.map (algebraMap (cyclotomicField N)
              (w.adicCompletion (cyclotomicField N))) := by
  sorry

/-- The one algebraic Frobenius polynomial at a canonical good prime,
extended by zero at exceptional primes. -/
def commonEulerFrobeniusPolynomial
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N))) :
    Polynomial (cyclotomicField N) := by
  classical
  exact if hq : q ∉ commonEulerBadPrimes N ξ then
    (exists_commonEulerCompletion_frobeniusPolynomial N m 𝒞 R ξ q hq).choose
  else 0

/-- The selected common polynomial has the prescribed image at every
permitted completion, with the same quotient, label and Frobenius prime. -/
theorem commonEulerFrobeniusPolynomial_spec
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ commonEulerBadPrimes N ξ)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hp : (NumberField.primeBelow (cyclotomicField N) w :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    (commonEulerCompletionAction N m 𝒞 R ξ w
      (NumberField.geometricFrobenius (realCyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q)).charpoly =
      (commonEulerFrobeniusPolynomial N m 𝒞 R ξ q).map
        (algebraMap (cyclotomicField N) (w.adicCompletion (cyclotomicField N))) := by
  dsimp only [commonEulerFrobeniusPolynomial]
  rw [dite_eq_left hq]
  exact (exists_commonEulerCompletion_frobeniusPolynomial
    N m 𝒞 R ξ q hq).choose_spec w hp Q

/-- The compatible system of the single selected real Euler quotient. Its
coefficient field is the cyclotomic field, which contains every fixed real
label; the action at a place uses the canonical map into that completion.
The two named literature interfaces above supply only semisimplicity and
the standard algebraic compatible Frobenius polynomial. Rank, topology,
common bad set and unramifiedness are derived from the chosen descent. -/
def commonEulerCompatibleSystem
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    NumberFieldCompatibleSystem (realCyclotomicField N) (cyclotomicField N) where
  residueCharacteristic := NumberField.primeBelow (cyclotomicField N)
  residueCharacteristic_prime := fun w =>
    (NumberField.primeBelow_prime (cyclotomicField N) w).out
  coefficientPrime := fun w => NumberField.liesOver_primeBelow (cyclotomicField N) w
  action := commonEulerCompletionAction N m 𝒞 R ξ
  continuous := continuous_commonEulerCompletionAction_entry N m 𝒞 R ξ
  semisimple := commonEulerCompletionAction_isSemisimple N m 𝒞 R ξ
  bad := commonEulerBadPrimes N ξ
  bad_finite := commonEulerBadPrimes_finite N ξ hN
  polynomial := commonEulerFrobeniusPolynomial N m 𝒞 R ξ
  unramified := by
    intro w q hq P _ hP hp Q _ _ g hg
    subst P
    exact commonEulerCompletionAction_unramified N m 𝒞 R ξ
      hN h5 hm hmN w q hq Q hp g hg
  frobenius_charpoly := by
    intro w q hq P _ hP hp Q _ _
    subst P
    dsimp only [commonEulerFrobeniusPolynomial]
    rw [dite_eq_left hq]
    exact (exists_commonEulerCompletion_frobeniusPolynomial
      N m 𝒞 R ξ q hq).choose_spec w hp Q

/-- The assembled system has exactly the canonical geometric bad set,
independent of the coefficient place. -/
theorem commonEulerCompatibleSystem_bad
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).bad =
      badPrimesBelow (K := realCyclotomicField N)
        (realEulerParameter N ξ) N := (rfl)

/-- The system's bad set is the previously defined canonical Euler set. -/
theorem commonEulerCompatibleSystem_bad_eq_common
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).bad =
      commonEulerBadPrimes N ξ := (rfl)

/-- Its completion action is the coordinate action of the very same chosen
descent at that place. -/
theorem commonEulerCompatibleSystem_action
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).action w =
      commonEulerCompletionAction N m 𝒞 R ξ w := (rfl)

/-- Its residue characteristic is the rational prime below that actual
coefficient place. -/
theorem commonEulerCompatibleSystem_residueCharacteristic
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).residueCharacteristic w =
      NumberField.primeBelow (cyclotomicField N) w := (rfl)

/-- The actual Euler parameter is the canonical scalar extension of the
real parameter, using the fixed inclusion into the cyclotomic field. -/
theorem realEulerParameter_eq_algebraMap :
    realEulerParameter N ξ =
      algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val := by
  rw [realEulerParameter_eq_inclusion, realEulerCoefficientInclusion_eq]
  rfl

/-- The system's geometric bad set is contained in the canonical set used by
the all-good-unit-prime eigenform endpoint, with no separate coefficient or
selected-model exclusion. -/
theorem commonEulerCompatibleSystem_bad_subset_canonical
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).bad ⊆
      badPrimesBelow (K := realCyclotomicField N)
        (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) N := by
  rw [commonEulerCompatibleSystem_bad, realEulerParameter_eq_algebraMap]

/-- Coordinates preserve the trace of every arithmetic Galois operator on
the chosen selected quotient descent. This is the bridge used for the
geometric-Frobenius normalization, with no extra trace hypothesis. -/
theorem commonEulerCompletionAction_trace
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N)) :
    LinearMap.trace (w.adicCompletion (cyclotomicField N))
        (Fin 2 → w.adicCompletion (cyclotomicField N))
        (commonEulerCompletionAction N m 𝒞 R ξ w g) =
      LinearMap.trace (w.adicCompletion (cyclotomicField N)) _
        ((commonEulerCompletionDescent N m 𝒞 R w).localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ) g) := by
  let : Fact (NumberField.primeBelow (cyclotomicField N) w).Prime :=
    NumberField.primeBelow_prime (cyclotomicField N) w
  let D := commonEulerCompletionDescent N m 𝒞 R w
  let : Module.Finite (w.adicCompletion (cyclotomicField N))
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
    D.localSystem.finite _
  let e := commonEulerCompletionActionEquiv N m 𝒞 R ξ w
  calc
    _ = LinearMap.trace (w.adicCompletion (cyclotomicField N)) _
        (e.toLinearEquiv.conj (commonEulerCompletionAction N m 𝒞 R ξ w g)) :=
      (LinearMap.trace_conj' _ e.toLinearEquiv).symm
    _ = _ := by rw [e.conj_apply_self]

/-- Choose the exponent-`m` Euler family and its real quotient once, before
any coefficient completion. This is the effective compatible system used in
the manuscript comparison; the coefficient number field is the full
cyclotomic field and may later be enlarged canonically. -/
def chosenCommonEulerCompatibleSystem
    (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    NumberFieldCompatibleSystem (realCyclotomicField N) (cyclotomicField N) :=
  let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
  let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
  commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN

/-- The chosen system is exactly the compatible system of the single chosen
Euler family and its single chosen real quotient. -/
theorem chosenCommonEulerCompatibleSystem_eq_common
    (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ =
      commonEulerCompatibleSystem N m
        (chosenSmoothProperEulerFamily N m hN h5 hm hmN)
        (chosenCommonRealEulerQuotientRealization N m
          (chosenSmoothProperEulerFamily N m hN h5 hm hmN)
          hN h5 hm hmN)
        ξ hN h5 hm hmN := (rfl)

/-- The chosen effective system has no bad geometric primes beyond the
canonical parameter/conductor set required by the main endpoint. -/
theorem chosenCommonEulerCompatibleSystem_bad_subset
    (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    (chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).bad ⊆
      badPrimesBelow (K := realCyclotomicField N)
        (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) N :=
  commonEulerCompatibleSystem_bad_subset_canonical N m
    (chosenSmoothProperEulerFamily N m hN h5 hm hmN)
    (chosenCommonRealEulerQuotientRealization N m
      (chosenSmoothProperEulerFamily N m hN h5 hm hmN) hN h5 hm hmN)
    ξ hN h5 hm hmN

end HilbertModularity.Hypergeometric
