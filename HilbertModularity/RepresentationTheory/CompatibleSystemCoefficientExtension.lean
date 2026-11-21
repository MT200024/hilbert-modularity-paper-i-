/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem
public import HilbertModularity.RepresentationTheory.SemisimpleCoefficientMap
public import HilbertModularity.NumberTheory.AdicCompletion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Enlarging the coefficient field of a compatible system

At an upper coefficient prime, contract the prime and extend the original
matrices along the canonical continuous map of completions. The common
Frobenius polynomial is the image of the original algebraic polynomial.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.NumberFieldCompatibleSystem

variable {F E L : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra E L]

local instance (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal :=
  Ideal.over_under w.asIdeal

/-- The actual action at an upper coefficient place, obtained from the contracted
place of the original system. -/
def extendedAction (S : NumberFieldCompatibleSystem F E)
    (w : HeightOneSpectrum (𝓞 L)) :
    Representation (w.adicCompletion L) (HilbertModularForms.AbsoluteGalois F)
      (Fin 2 → w.adicCompletion L) :=
  (S.action (w.under (𝓞 E))).mapCoefficients
    (HeightOneSpectrum.completionMap (w.under (𝓞 E)) w)

/-- The upper action is literally the lower action mapped along the
canonical completion homomorphism. -/
theorem extendedAction_eq_mapCoefficients
    (S : NumberFieldCompatibleSystem F E)
    (w : HeightOneSpectrum (𝓞 L)) :
    S.extendedAction w =
      (S.action (w.under (𝓞 E))).mapCoefficients
        (HeightOneSpectrum.completionMap (w.under (𝓞 E)) w) := (rfl)

/-- Extend coefficients without changing the geometric exceptional set.
Semisimplicity uses the named perfect-field separability input. -/
def extendCoefficients (S : NumberFieldCompatibleSystem F E) :
    NumberFieldCompatibleSystem F L where
  residueCharacteristic w := S.residueCharacteristic (w.under (𝓞 E))
  residueCharacteristic_prime w := S.residueCharacteristic_prime (w.under (𝓞 E))
  coefficientPrime w := by
    let v := w.under (𝓞 E)
    let := S.coefficientPrime v
    exact Ideal.LiesOver.trans w.asIdeal v.asIdeal _
  action := S.extendedAction
  continuous w := Representation.continuous_mapCoefficients _
    (HeightOneSpectrum.continuous_completionMap (w.under (𝓞 E)) w)
    _ (S.continuous (w.under (𝓞 E)))
  semisimple w := by
    let v := w.under (𝓞 E)
    let : CharZero (v.adicCompletion E) := charZero_of_injective_algebraMap
      (algebraMap E (v.adicCompletion E)).injective
    exact Representation.isSemisimple_mapCoefficients _ _ (S.semisimple v)
  bad := S.bad
  bad_finite := S.bad_finite
  polynomial q := (S.polynomial q).map (algebraMap E L)
  unramified w q hq P _ hP hp Q _ _ g hg :=
    Representation.mapCoefficients_eq_one _ _ _
      (S.unramified (w.under (𝓞 E)) q hq P hP hp Q g hg)
  frobenius_charpoly w q hq P _ hP hp Q _ _ := by
    rw [extendedAction, Representation.charpoly_mapCoefficients,
      S.frobenius_charpoly (w.under (𝓞 E)) q hq P hP hp Q,
      Polynomial.map_map, Polynomial.map_map]
    congr 1
    apply RingHom.ext
    intro x
    exact HeightOneSpectrum.completionMap_algebraMap (K := E) (L := L) (w.under (𝓞 E)) w x

/-- The coefficient-place residue characteristic is inherited from the
contracted prime; it is never chosen independently after enlargement. -/
@[simp] theorem extendCoefficients_residueCharacteristic
    (S : NumberFieldCompatibleSystem F E)
    (w : HeightOneSpectrum (𝓞 L)) :
    (S.extendCoefficients (L := L)).residueCharacteristic w =
      S.residueCharacteristic (w.under (𝓞 E)) := (rfl)

/-- Coefficient enlargement retains the original geometric exceptional set. -/
@[simp] theorem extendCoefficients_bad (S : NumberFieldCompatibleSystem F E) :
    (S.extendCoefficients (L := L)).bad = S.bad := (rfl)

/-- The common polynomial keeps its prescribed algebraic coefficient map. -/
@[simp] theorem extendCoefficients_polynomial (S : NumberFieldCompatibleSystem F E)
    (q : HeightOneSpectrum (𝓞 F)) :
    (S.extendCoefficients (L := L)).polynomial q =
      (S.polynomial q).map (algebraMap E L) := (rfl)

/-- The enlarged system uses the constructed action at the contracted place. -/
@[simp] theorem extendCoefficients_action (S : NumberFieldCompatibleSystem F E)
    (w : HeightOneSpectrum (𝓞 L)) :
    (S.extendCoefficients (L := L)).action w = S.extendedAction w := (rfl)

end HilbertModularity.NumberFieldCompatibleSystem
