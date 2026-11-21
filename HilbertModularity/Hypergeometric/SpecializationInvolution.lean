/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FiniteFieldInvolution
public import HilbertModularity.Hypergeometric.Specialization

/-! # Complementary arithmetic hypergeometric values

The actual positive power-residue character and canonical good-unit reduction
satisfy the reflection identity for odd levels in [TripathiGoswami].
Both McCarthy and GPRV finite-sum normalizations are treated; identification
with an arithmetic Galois trace is a separate theorem.
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The complement of a good unit is again a good unit. -/
theorem GoodUnit.complement {P : HeightOneSpectrum R} {x : K} (h : P.GoodUnit x) :
    P.GoodUnit (1 - x) :=
  ⟨h.complement_valuation_eq_one, by simpa only [sub_sub_cancel] using h.valuation_eq_one⟩

/-- Canonical reduction commutes with taking the complement of a good unit. -/
theorem GoodUnit.specialization_complement {P : HeightOneSpectrum R} {x : K}
    (h : P.GoodUnit x) :
    P.specialization (1 - x) h.complement.valuation_eq_one.le =
      1 - P.specialization x h.valuation_eq_one.le := by
  have hsub : P.localElement (1 - x) h.complement.valuation_eq_one.le =
      1 - P.localElement x h.valuation_eq_one.le := Subtype.ext rfl
  dsimp [specialization]
  rw [hsub, map_sub, map_one]

end IsDedekindDomain.HeightOneSpectrum

namespace HilbertModularity.Cyclotomic

open scoped NumberField
open IsDedekindDomain Hypergeometric
attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N] (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)

/-- The actual prime residue field, with its finite enumeration. -/
local instance instFintypeComplementResidue : Fintype (𝓞 (cyclotomicField N) ⧸ P.asIdeal) :=
  Fintype.ofFinite _

/-- The parameter-independent reflection sign at the specified cyclotomic
prime and character label. -/
def reflectionSign (m : ℕ) : Qbarˣ :=
  (powerResidueMulChar N P.asIdeal hP ^ m).toUnitHom (-1)

@[simp]
theorem coe_reflectionSign (m : ℕ) :
    (reflectionSign N P hP m : Qbar) = (powerResidueMulChar N P.asIdeal hP ^ m) (-1) := by
  simp only [reflectionSign, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one]

/-- The explicit reflection factor is a genuine unit of order dividing two. -/
theorem reflectionSign_sq (m : ℕ) : reflectionSign N P hP m ^ 2 = 1 := by
  dsimp [reflectionSign]
  rw [← map_pow]
  have h : (-1 : (𝓞 (cyclotomicField N) ⧸ P.asIdeal)ˣ) ^ 2 = 1 := by
    apply Units.ext
    simp
  rw [h, map_one]

/-- At odd levels the explicit quadratic reflection sign is trivial. -/
theorem reflectionSign_eq_one_of_odd (hN : Odd N) (m : ℕ) :
    reflectionSign N P hP m = 1 := by
  apply Units.ext
  rw [coe_reflectionSign, Units.val_one]
  apply character_neg_one_of_odd_power _ N hN
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hpow : powerResidueMulChar N P.asIdeal hP ^ N = 1 := by
    simpa only [powerResidueMulChar_orderOf] using
      pow_orderOf_eq_one (powerResidueMulChar N P.asIdeal hP)
  rw [hpow, one_pow]

/-- The arithmetic McCarthy reflection formula at every level, with its
explicit quadratic scalar retained. -/
theorem mccarthyValue_complement_eq (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ (1 - ξ) hξ.complement =
      (reflectionSign N P hP m : Qbar) * mccarthyValue N P hP m θ ξ hξ := by
  classical
  dsimp [mccarthyValue]
  rw [hξ.specialization_complement, coe_reflectionSign]
  apply symmetricMcCarthySum_complement_eq (powerResidueMulChar N P.asIdeal hP)
    m hm (by simpa only [powerResidueMulChar_orderOf] using hmN) θ hθ
  · exact hξ.specialization_ne_zero_one.1
  · exact hξ.specialization_ne_zero_one.2

/-- The identical quadratic scalar occurs in the precise GPRV normalization. -/
theorem gprvValue_complement_eq (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    gprvValue N P hP m θ (1 - ξ) hξ.complement =
      (reflectionSign N P hP m : Qbar) * gprvValue N P hP m θ ξ hξ := by
  rw [← mccarthyValue_eq_gprvValue N P hP m hmN.le θ hθ,
    ← mccarthyValue_eq_gprvValue N P hP m hmN.le θ hθ]
  exact mccarthyValue_complement_eq N P hP m hm hmN θ hθ ξ hξ

/-- The exact arithmetic McCarthy value is unchanged at complementary good
parameters for every nontrivial label at an odd level. -/
theorem mccarthyValue_complement (hN : Odd N) (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ (1 - ξ) hξ.complement = mccarthyValue N P hP m θ ξ hξ := by
  classical
  dsimp [mccarthyValue]
  rw [hξ.specialization_complement]
  apply symmetricMcCarthySum_complement (powerResidueMulChar N P.asIdeal hP)
    (by simpa only [powerResidueMulChar_orderOf] using hN) m hm
    (by simpa only [powerResidueMulChar_orderOf] using hmN) θ hθ
  · exact hξ.specialization_ne_zero_one.1
  · exact hξ.specialization_ne_zero_one.2

/-- The same reflection identity holds in the precise GPRV finite-sum
normalization, with its existing inverse power-residue convention. -/
theorem gprvValue_complement (hN : Odd N) (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    gprvValue N P hP m θ (1 - ξ) hξ.complement = gprvValue N P hP m θ ξ hξ := by
  rw [← mccarthyValue_eq_gprvValue N P hP m hmN.le θ hθ,
    ← mccarthyValue_eq_gprvValue N P hP m hmN.le θ hθ]
  exact mccarthyValue_complement N P hP hN m hm hmN θ hθ ξ hξ

end HilbertModularity.Cyclotomic
