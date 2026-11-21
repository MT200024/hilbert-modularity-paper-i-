/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.AdicCompletionResidue
public import HilbertModularity.Algebra.AdicCompletion.IdealPower
public import HilbertModularity.Algebra.AdicCompletion.IdealCongruence
public import HilbertModularity.Algebra.AdicCompletion.Padic
public import HilbertModularity.NumberTheory.RealCyclotomicPrime

/-! # Adic completion and native completion integers

The inverse limit of the global integer ring modulo powers of a height-one
prime is the valuation ring of the corresponding number-field completion.
The comparison uses localization modulo prime powers before applying the DVR
completion theorem [MilneANT, Theorem 7.23 and Remark 7.24, p. 115; Lemma
7.25, p. 116; Aside 7.30, p. 119].
-/

public noncomputable section

open IsDedekindDomain
open scoped NumberField ValuativeRel

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]
  (P : HeightOneSpectrum (𝓞 K))

/-- The canonical inverse-limit completion of global integers is the native
valuation-integer ring of the completed field. This is the global-integer form
of [MilneANT, Lemma 7.25 and Aside 7.30, pp. 116, 119]: localization at `P`
does not change `𝓞 K / Pⁿ`, and the local DVR's inverse-limit completion is
the valuation ring in `P.adicCompletion K`. The map on global integers is the
existing `adicCompletionIntegerMap`; no Tate action or determinant is included.
-/
theorem exists_adicCompletionIntegersEquiv :
    ∃ e : AdicCompletion P.asIdeal (𝓞 K) ≃+* 𝒪[P.adicCompletion K],
      ∀ a : 𝓞 K,
        e (algebraMap (𝓞 K) (AdicCompletion P.asIdeal (𝓞 K)) a) =
          adicCompletionIntegerMap K P a := by
  sorry

/-- Select the cited comparison with its specified action on global integers. -/
def adicCompletionIntegersEquiv :
    AdicCompletion P.asIdeal (𝓞 K) ≃+* 𝒪[P.adicCompletion K] :=
  Classical.choose (exists_adicCompletionIntegersEquiv K P)

@[simp] theorem adicCompletionIntegersEquiv_algebraMap (a : 𝓞 K) :
    adicCompletionIntegersEquiv K P
        (algebraMap (𝓞 K) (AdicCompletion P.asIdeal (𝓞 K)) a) =
      adicCompletionIntegerMap K P a :=
  Classical.choose_spec (exists_adicCompletionIntegersEquiv K P) a

/-- The comparison gives the original global-integer embedding into the
completed field after forgetting integrality. -/
@[simp] theorem coe_adicCompletionIntegersEquiv_algebraMap (a : 𝓞 K) :
    (adicCompletionIntegersEquiv K P
      (algebraMap (𝓞 K) (AdicCompletion P.asIdeal (𝓞 K)) a) :
        P.adicCompletion K) =
      algebraMap (𝓞 K) (P.adicCompletion K) a := by
  rw [adicCompletionIntegersEquiv_algebraMap, coe_adicCompletionIntegerMap]

end NumberField

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)

/-- Global integers of the selected real cyclotomic field. -/
abbrev RealIntegerRing := 𝓞 (realCyclotomicField p)

/-- Native integer comparison at the unique prime above the conductor. -/
def realPrimeAdicCompletionIntegersEquiv :
    AdicCompletion (realPrimeAboveConductor p).asIdeal (RealIntegerRing p) ≃+*
      𝒪[RealCompletion p] :=
  NumberField.adicCompletionIntegersEquiv (realCyclotomicField p)
    (realPrimeAboveConductor p)

@[simp] theorem realPrimeAdicCompletionIntegersEquiv_algebraMap
    (a : RealIntegerRing p) :
    realPrimeAdicCompletionIntegersEquiv p
        (algebraMap (RealIntegerRing p)
          (AdicCompletion (realPrimeAboveConductor p).asIdeal
            (RealIntegerRing p)) a) =
      NumberField.adicCompletionIntegerMap (realCyclotomicField p)
        (realPrimeAboveConductor p) a :=
  NumberField.adicCompletionIntegersEquiv_algebraMap
    (realCyclotomicField p) (realPrimeAboveConductor p) a

/-- The canonical coefficient map from `ℤₚ` to the completion at the unique
real prime. The proved total-ramification identity identifies the rational
`p`-adic filtration with a positive power of this prime's filtration. -/
@[expose] def padicIntToRealPrimeAdicCompletion :
    ℤ_[p] →+* AdicCompletion (realPrimeAboveConductor p).asIdeal
      (RealIntegerRing p) := by
  let I : Ideal (RealIntegerRing p) := Ideal.span {realPrimeGenerator p}
  have hI : I = (realPrimeAboveConductor p).asIdeal :=
    span_realPrimeGenerator p (by omega)
  have hpow : I ^ ((p - 1) / 2) =
      Ideal.span {(p : RealIntegerRing p)} :=
    span_realPrimeGenerator_pow p (by omega)
  have hd : 0 < (p - 1) / 2 := by omega
  let e : AdicCompletion (Ideal.span {(p : RealIntegerRing p)})
      (RealIntegerRing p) ≃+*
      AdicCompletion (realPrimeAboveConductor p).asIdeal
        (RealIntegerRing p) :=
    (hpow ▸ AdicCompletion.powAlgEquiv I ((p - 1) / 2) hd).toRingEquiv.trans
      (AdicCompletion.idealEqRingEquiv hI)
  exact e.toRingHom.comp (PadicInt.toAdicCompletion p (RealIntegerRing p))

/-- The canonical comparison preserves the selected `ℤₚ` coefficient map.
Here the right side is the already defined embedding of `ℚₚ` into the actual
real cyclotomic completion, restricted to `ℤₚ`. This is the scalar part of
[MilneANT, Theorem 7.23, Lemma 7.25 and Aside 7.30, pp. 115–119], together
with the cofinal ramification identity proved in `RealCyclotomicPrime`.
It does not assert an equivalence of Tate actions or a determinant identity.
-/
theorem coe_adicCompletionIntegersEquiv_padicInt (z : ℤ_[p]) :
    (realPrimeAdicCompletionIntegersEquiv p
      (padicIntToRealPrimeAdicCompletion p hp z) :
        (realPrimeAboveConductor p).adicCompletion (realCyclotomicField p)) =
      NumberField.padicCompletionMap p (realCyclotomicField p)
        (realPrimeAboveConductor p) (z : ℚ_[p]) := by
  sorry

/-- The resulting `ℤₚ` map into the actual native integer ring. -/
def padicIntToRealCompletionIntegers : ℤ_[p] →+* 𝒪[RealCompletion p] :=
  (realPrimeAdicCompletionIntegersEquiv p).toRingHom.comp
    (padicIntToRealPrimeAdicCompletion p hp)

@[simp] theorem coe_padicIntToRealCompletionIntegers (z : ℤ_[p]) :
    (padicIntToRealCompletionIntegers p hp z : RealCompletion p) =
      NumberField.padicCompletionMap p (realCyclotomicField p)
        (realPrimeAboveConductor p) (z : ℚ_[p]) :=
  coe_adicCompletionIntegersEquiv_padicInt p hp z

end HilbertModularity.Cyclotomic
