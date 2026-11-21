/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFrobeniusTransport
public import HilbertModularity.RepresentationTheory.CompatibleSystemCoefficientExtension

/-! # Coefficient extension of the chosen Euler compatible system

The cyclotomic number field supplies the original fixed deck label. Enlarging
the number field uses the canonical completion map at each contracted place;
the quotient family and finite comparison character are not chosen anew.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open HilbertModularity.LocalSpecialization
open scoped NumberField

namespace Representation

variable {R S G n : Type*} [Field R] [Field S]
  [Fintype n] [DecidableEq n] [Group G]

/-- Entrywise coefficient extension sends the trace of a coordinate action
through the same ring homomorphism. -/
theorem trace_mapCoefficients (f : R →+* S)
    (ρ : Representation R G (n → R)) (g : G) :
    LinearMap.trace S (n → S) (ρ.mapCoefficients f g) =
      f (LinearMap.trace R (n → R) (ρ g)) := by
  rw [LinearMap.trace_eq_matrix_trace S (Pi.basisFun S n),
    LinearMap.trace_eq_matrix_trace R (Pi.basisFun R n)]
  change Matrix.trace (LinearMap.toMatrixAlgEquiv' (ρ.mapCoefficients f g)) =
    f (Matrix.trace (LinearMap.toMatrixAlgEquiv' (ρ g)))
  rw [toMatrix_mapCoefficients]
  exact (AddMonoidHom.map_trace f _).symm

end Representation

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N]
  (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
  (A : Type*) [Field A] [NumberField A]
  [Algebra (cyclotomicField N) A]

local instance (v : HeightOneSpectrum (𝓞 (cyclotomicField N))) :
    NontriviallyNormedField (v.adicCompletion (cyclotomicField N)) :=
  Valued.toNontriviallyNormedField (v.adicCompletion (cyclotomicField N))
    (WithZero (Multiplicative ℤ))

/-- Enlarge the coefficient field of the *same* chosen Euler system.
At every upper coefficient place, the action is the scalar extension of the
action at its contracted cyclotomic place. -/
def chosenCommonEulerCompatibleSystemExtended :
    NumberFieldCompatibleSystem (realCyclotomicField N) A :=
  (chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).extendCoefficients

/-- The enlarged chosen system is the coefficient extension of the same
cyclotomic Euler system. -/
@[simp] theorem chosenCommonEulerCompatibleSystemExtended_eq_extendCoefficients :
    chosenCommonEulerCompatibleSystemExtended N m hN h5 hm hmN ξ A =
      (chosenCommonEulerCompatibleSystem N m hN h5 hm hmN ξ).extendCoefficients := (rfl)

/-- Coefficient enlargement does not alter the canonical geometric bad set.
This is exactly the bad-set containment needed by the good-unit endpoint. -/
theorem chosenCommonEulerCompatibleSystemExtended_bad_subset :
    (chosenCommonEulerCompatibleSystemExtended N m hN h5 hm hmN ξ A).bad ⊆
      badPrimesBelow (K := realCyclotomicField N)
        (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val) N := by
  rw [chosenCommonEulerCompatibleSystemExtended,
    NumberFieldCompatibleSystem.extendCoefficients_bad]
  exact chosenCommonEulerCompatibleSystem_bad_subset N m hN h5 hm hmN ξ

/-- After one number-field coefficient enlargement, the normalized Euler
trace is still the image of the *same* algebraic scalar from the cyclotomic
coefficient field. The proof applies the lower selected quotient trace once
and transports matrix trace along the canonical map of completions. -/
theorem commonEulerCompatibleSystemExtended_geometricFrobenius_trace
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (w : HeightOneSpectrum (𝓞 A))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ ((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
      (L := A)).bad)
    (hℓq : (((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
      (L := A)).residueCharacteristic w : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [P.asIdeal.LiesOver q.asIdeal]
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hξ : P.GoodUnit (realEulerParameter N ξ))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver P.asIdeal] :
    let t := normalizedCyclotomicEulerTrace N P.asIdeal hP m
      (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)
    let g := AlgEquiv.restrictScalarsHom (realCyclotomicField N)
      (NumberField.geometricFrobenius (cyclotomicField N)
        (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
          AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
            AlgebraicClosure (realCyclotomicField N))
    LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
      (((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
        (L := A)).action w g) =
      algebraMap A (w.adicCompletion A)
        (algebraMap (cyclotomicField N) A t) := by
  let S := commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN
  let v := w.under (𝓞 (cyclotomicField N))
  let : w.asIdeal.LiesOver v.asIdeal := Ideal.over_under w.asIdeal
  let c := HeightOneSpectrum.completionMap
    (K := cyclotomicField N) (L := A) v w
  have hqv : q ∉ S.bad := by
    simpa only [NumberFieldCompatibleSystem.extendCoefficients_bad] using hq
  have hℓv : (NumberField.primeBelow (cyclotomicField N) v :
      𝓞 (realCyclotomicField N)) ∉ q.asIdeal := by
    simpa only [NumberFieldCompatibleSystem.extendCoefficients_residueCharacteristic,
      commonEulerCompatibleSystem_residueCharacteristic] using hℓq
  have hlow := commonEulerCompatibleSystem_geometricFrobenius_trace
    N m 𝒞 R ξ hN h5 hm hmN v q hqv hℓv P hP hξ Q
  let g := AlgEquiv.restrictScalarsHom (realCyclotomicField N)
    (NumberField.geometricFrobenius (cyclotomicField N)
      (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
        AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
          AlgebraicClosure (realCyclotomicField N))
  let t := normalizedCyclotomicEulerTrace N P.asIdeal hP m
    (P.specialization (realEulerParameter N ξ) hξ.valuation_eq_one.le)
  calc
    _ = LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        ((S.action v).mapCoefficients c g) := by
      rw [NumberFieldCompatibleSystem.extendCoefficients_action,
        NumberFieldCompatibleSystem.extendedAction_eq_mapCoefficients]
    _ = c (LinearMap.trace (v.adicCompletion (cyclotomicField N))
        (Fin 2 → v.adicCompletion (cyclotomicField N)) (S.action v g)) :=
      Representation.trace_mapCoefficients c (S.action v) g
    _ = c (algebraMap (cyclotomicField N)
        (v.adicCompletion (cyclotomicField N)) t) := congrArg c hlow
    _ = algebraMap A (w.adicCompletion A)
        (algebraMap (cyclotomicField N) A t) :=
      HeightOneSpectrum.completionMap_algebraMap
        (K := cyclotomicField N) (L := A) v w t

/-- Exact normalized trace in the signature of
`exists_mccarthyEigenform_at_goodUnit_primes` after a single number-field
coefficient enlargement. The fixed embedding `i₀` restricts to the original
cyclotomic coefficient inclusion; its completion extension `ι` therefore
reads the same algebraic Euler scalar at every place. -/
theorem commonEulerCompatibleSystemExtended_endpoint_trace
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (i₀ : A →+* Qbar)
    (hi₀ : i₀.comp (algebraMap (cyclotomicField N) A) =
      (cyclotomicField N).val.toRingHom)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hξ : P.GoodUnit
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ ((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
      (L := A)).bad)
    [P.asIdeal.LiesOver q.asIdeal]
    (w : HeightOneSpectrum (𝓞 A))
    (hℓq : (((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
      (L := A)).residueCharacteristic w : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (ι : Qbar →+* AlgebraicClosure (w.adicCompletion A))
    (hι : ι.comp i₀ =
      (algebraMap (w.adicCompletion A)
        (AlgebraicClosure (w.adicCompletion A))).comp
        (algebraMap A (w.adicCompletion A)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal] :
    ι ((cyclotomicField N).val
      (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization
          (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val)
          hξ.valuation_eq_one.le))) =
    algebraMap (w.adicCompletion A)
      (AlgebraicClosure (w.adicCompletion A))
      (LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        (((commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
          (L := A)).action w
          (AlgEquiv.restrictScalarsHom (realCyclotomicField N)
            (NumberField.geometricFrobenius (cyclotomicField N)
              (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
                AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
                  AlgebraicClosure (realCyclotomicField N))))) := by
  let t := normalizedCyclotomicEulerTrace N P.asIdeal hP m
    (P.specialization
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val)
      hξ.valuation_eq_one.le)
  have hreal : realEulerParameter N ξ =
      algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val :=
    realEulerParameter_eq_algebraMap N ξ
  have hξ' : P.GoodUnit (realEulerParameter N ξ) := by
    rwa [hreal]
  have ht := commonEulerCompatibleSystemExtended_geometricFrobenius_trace
    N m hN h5 hm hmN ξ A 𝒞 R w q hq hℓq P hP hξ' Q
  simp only [realEulerParameter_eq_algebraMap] at ht
  have hsource := congrArg
    (fun f : cyclotomicField N →+* Qbar => f t) hi₀
  change i₀ (algebraMap (cyclotomicField N) A t) =
    (cyclotomicField N).val t at hsource
  have hcoeff := congrArg
    (fun f : A →+* AlgebraicClosure (w.adicCompletion A) =>
      f (algebraMap (cyclotomicField N) A t)) hι
  change ι (i₀ (algebraMap (cyclotomicField N) A t)) =
    algebraMap (w.adicCompletion A) (AlgebraicClosure (w.adicCompletion A))
      (algebraMap A (w.adicCompletion A)
        (algebraMap (cyclotomicField N) A t)) at hcoeff
  rw [hsource] at hcoeff
  exact hcoeff.trans (congrArg _ ht.symm)

/-- The same endpoint trace for the project's one chosen Euler family and
one chosen quotient, after extending its fixed coefficient field once. -/
theorem chosenCommonEulerCompatibleSystemExtended_endpoint_trace
    (i₀ : A →+* Qbar)
    (hi₀ : i₀.comp (algebraMap (cyclotomicField N) A) =
      (cyclotomicField N).val.toRingHom)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hξ : P.GoodUnit
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val))
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    (hq : q ∉ (chosenCommonEulerCompatibleSystemExtended
      N m hN h5 hm hmN ξ A).bad)
    [P.asIdeal.LiesOver q.asIdeal]
    (w : HeightOneSpectrum (𝓞 A))
    (hℓq : ((chosenCommonEulerCompatibleSystemExtended
      N m hN h5 hm hmN ξ A).residueCharacteristic w :
        𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (ι : Qbar →+* AlgebraicClosure (w.adicCompletion A))
    (hι : ι.comp i₀ =
      (algebraMap (w.adicCompletion A)
        (AlgebraicClosure (w.adicCompletion A))).comp
        (algebraMap A (w.adicCompletion A)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] [Q.LiesOver P.asIdeal] :
    ι ((cyclotomicField N).val
      (normalizedCyclotomicEulerTrace N P.asIdeal hP m
        (P.specialization
          (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ.val)
          hξ.valuation_eq_one.le))) =
    algebraMap (w.adicCompletion A)
      (AlgebraicClosure (w.adicCompletion A))
      (LinearMap.trace (w.adicCompletion A) (Fin 2 → w.adicCompletion A)
        ((chosenCommonEulerCompatibleSystemExtended
          N m hN h5 hm hmN ξ A).action w
          (AlgEquiv.restrictScalarsHom (realCyclotomicField N)
            (NumberField.geometricFrobenius (cyclotomicField N)
              (AlgebraicClosure (realCyclotomicField N)) P.asIdeal Q :
                AlgebraicClosure (realCyclotomicField N) ≃ₐ[cyclotomicField N]
                  AlgebraicClosure (realCyclotomicField N))))) := by
  let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hm hmN
  let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hm hmN
  have hS : chosenCommonEulerCompatibleSystemExtended N m hN h5 hm hmN ξ A =
      (commonEulerCompatibleSystem N m 𝒞 R ξ hN h5 hm hmN).extendCoefficients
        (L := A) := by
    rw [chosenCommonEulerCompatibleSystemExtended,
      chosenCommonEulerCompatibleSystem_eq_common]
  rw [hS] at hq hℓq ⊢
  exact commonEulerCompatibleSystemExtended_endpoint_trace
    N m hN h5 hm hmN ξ A 𝒞 R i₀ hi₀ P hP hξ q hq w hℓq ι hι Q

end HilbertModularity.Hypergeometric
