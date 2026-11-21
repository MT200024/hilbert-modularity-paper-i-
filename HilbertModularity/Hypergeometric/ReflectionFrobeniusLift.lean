/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ReflectionFrobenius
public import HilbertModularity.NumberTheory.GaloisPrimes

/-! # Actual absolute Frobenius lifts for reflection

The profinite decomposition group surjects onto the automorphisms of the
algebraic residue extension. Lifting its arithmetic Frobenius and taking the
inverse supplies the geometric convention in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace HilbertModularity.Cyclotomic

open scoped NumberField Pointwise
open IsDedekindDomain
attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N] (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  (Q : Ideal (𝓞 Qbar)) [Q.IsMaximal] [Q.LiesOver P.asIdeal]

/-- Arithmetic Frobenius lifts to the actual absolute decomposition group. -/
theorem exists_absoluteArithmeticFrobenius :
    ∃ g : MulAction.stabilizer (Qbar ≃ₐ[cyclotomicField N] Qbar) Q,
      ∀ b : 𝓞 Qbar, Ideal.Quotient.mk Q (g • b) =
        (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) := by
  let : TopologicalSpace (𝓞 Qbar) := ⊥
  let : DiscreteTopology (𝓞 Qbar) := ⟨rfl⟩
  have : Algebra.IsIntegral (cyclotomicField N) Qbar := Algebra.IsIntegral.tower_top ℚ
  have : Algebra.IsIntegral (𝓞 (cyclotomicField N)) (𝓞 Qbar) :=
    Algebra.IsIntegral.tower_top ℤ
  have : Algebra.IsIntegral (𝓞 (cyclotomicField N) ⧸ P.asIdeal) (𝓞 Qbar ⧸ Q) :=
    Algebra.IsIntegral.tower_top (𝓞 (cyclotomicField N))
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Qbar ≃ₐ[cyclotomicField N] Qbar) P.asIdeal Q
    (Ideal.Quotient.arithmeticFrobenius P.asIdeal Q)
  refine ⟨g, fun b => ?_⟩
  have hv := congrArg
    (fun f : (𝓞 Qbar ⧸ Q) ≃ₐ[𝓞 (cyclotomicField N) ⧸ P.asIdeal] (𝓞 Qbar ⧸ Q) =>
      f (Ideal.Quotient.mk Q b)) hg
  simpa only [Ideal.Quotient.stabilizerHom_apply, Ideal.Quotient.arithmeticFrobenius_apply,
    Subgroup.smul_def] using hv

/-- A constructed arithmetic Frobenius in the actual absolute decomposition group. -/
def absoluteArithmeticFrobenius :
    MulAction.stabilizer (Qbar ≃ₐ[cyclotomicField N] Qbar) Q :=
  (exists_absoluteArithmeticFrobenius N P Q).choose

/-- The chosen absolute arithmetic Frobenius has its actual residue power action. -/
theorem absoluteArithmeticFrobenius_spec (b : 𝓞 Qbar) :
    Ideal.Quotient.mk Q (absoluteArithmeticFrobenius N P Q • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) :=
  (exists_absoluteArithmeticFrobenius N P Q).choose_spec b

/-- The actual absolute geometric Frobenius is the inverse arithmetic lift. -/
def absoluteGeometricFrobenius :
    MulAction.stabilizer (Qbar ≃ₐ[cyclotomicField N] Qbar) Q :=
  (absoluteArithmeticFrobenius N P Q)⁻¹

/-- The inverse of the constructed geometric lift has arithmetic residue action. -/
theorem absoluteGeometricFrobenius_spec (b : 𝓞 Qbar) :
    Ideal.Quotient.mk Q ((absoluteGeometricFrobenius N P Q)⁻¹ • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) := by
  simpa only [absoluteGeometricFrobenius, inv_inv] using absoluteArithmeticFrobenius_spec N P Q b

/-- Restriction from the cyclotomic base field to its actual real subfield. -/
def restrictCyclotomicGalois :
    (Qbar ≃ₐ[cyclotomicField N] Qbar) →* (Qbar ≃ₐ[realCyclotomicField N] Qbar) where
  toFun g :=
    { g.toRingEquiv with
      commutes' a := g.commutes ⟨(a : Qbar), realCyclotomicField_le N a.property⟩ }
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

@[simp]
theorem restrictCyclotomicGalois_apply (g : Qbar ≃ₐ[cyclotomicField N] Qbar) (x : Qbar) :
    restrictCyclotomicGalois N g x = g x := rfl

/-- The constructed geometric Frobenius, regarded over the real cyclotomic field. -/
def reflectionGeometricFrobenius : Qbar ≃ₐ[realCyclotomicField N] Qbar :=
  restrictCyclotomicGalois N (absoluteGeometricFrobenius N P Q)

/-- Restricting the base field preserves the actual geometric residue action. -/
theorem reflectionGeometricFrobenius_spec (b : 𝓞 Qbar) :
    Ideal.Quotient.mk Q ((reflectionGeometricFrobenius N P Q)⁻¹ • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal) := by
  change Ideal.Quotient.mk Q ((absoluteGeometricFrobenius N P Q)⁻¹ • b) = _
  exact absoluteGeometricFrobenius_spec N P Q b

/-- The global quadratic character at the constructed geometric Frobenius
is exactly the canonical labelled power-residue reflection sign. -/
theorem reflectionCharacter_at_geometricFrobenius
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (hN : 3 ≤ N)
    (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal))) (m : ℕ) :
    reflectionCharacter N hN (reflectionGeometricFrobenius N P Q) ^ m =
      reflectionSign N P hP m :=
  reflectionCharacter_pow_eq_reflectionSign_of_geometric_residue N P hP hN
    (reflectionGeometricFrobenius N P Q) Q hQ hodd (reflectionGeometricFrobenius_spec N P Q) m

/-- The exact McCarthy values reflect by the actual global character evaluated
at the constructed geometric Frobenius, uniformly in the good parameter. -/
theorem mccarthyValue_complement_at_geometricFrobenius
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (hN : 3 ≤ N)
    (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN (reflectionGeometricFrobenius N P Q) ^ m : Qbarˣ) : Qbar) *
        mccarthyValue N P hP m θ ξ hξ := by
  rw [mccarthyValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_at_geometricFrobenius N P Q hP hN hQ hodd m]

/-- The GPRV normalization has the identical reflection formula at the
constructed geometric Frobenius. -/
theorem gprvValue_complement_at_geometricFrobenius
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (hN : 3 ≤ N)
    (hQ : (2 * N : 𝓞 Qbar) ∉ Q)
    (hodd : Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)))
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    gprvValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN (reflectionGeometricFrobenius N P Q) ^ m : Qbarˣ) : Qbar) *
        gprvValue N P hP m θ ξ hξ := by
  rw [gprvValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_at_geometricFrobenius N P Q hP hN hQ hodd m]

/-- Every cyclotomic prime has an actual maximal prime above it in the
algebraic integer ring of the fixed algebraic closure. -/
theorem exists_absolutePrime :
    ∃ Q : Ideal (𝓞 Qbar), Q.IsMaximal ∧ Q.LiesOver P.asIdeal := by
  have : Algebra.IsIntegral (𝓞 (cyclotomicField N)) (𝓞 Qbar) :=
    Algebra.IsIntegral.tower_top ℤ
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 Qbar) P.asIdeal

/-- A chosen actual algebraic prime above the specified cyclotomic prime. -/
def absolutePrime : Ideal (𝓞 Qbar) := (exists_absolutePrime N P).choose

/-- The chosen algebraic prime is maximal. -/
instance absolutePrime_isMaximal : (absolutePrime N P).IsMaximal :=
  (exists_absolutePrime N P).choose_spec.1

/-- The chosen algebraic prime contracts to the original prime. -/
instance absolutePrime_liesOver : (absolutePrime N P).LiesOver P.asIdeal :=
  (exists_absolutePrime N P).choose_spec.2

/-- A constructed geometric Frobenius with the algebraic prime chosen as well. -/
def specializationGeometricFrobenius : Qbar ≃ₐ[realCyclotomicField N] Qbar :=
  reflectionGeometricFrobenius N P (absolutePrime N P)

/-- Avoiding `2N` is preserved at the chosen algebraic prime. -/
theorem absolutePrime_two_mul_not_mem
    (h : (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) :
    (2 * N : 𝓞 Qbar) ∉ absolutePrime N P := by
  intro hm
  apply h
  apply (Ideal.mem_of_liesOver (absolutePrime N P) P.asIdeal (2 * N)).mpr
  simpa only [map_mul, map_ofNat, map_natCast] using hm

/-- The actual finite residue field is enumerated for the cardinality argument. -/
local instance instFintypeLiftResidue : Fintype (𝓞 (cyclotomicField N) ⧸ P.asIdeal) :=
  Fintype.ofFinite _

/-- A cyclotomic prime away from two has odd residue cardinality. -/
theorem residueCard_odd_of_two_not_mem (h : (2 : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) :
    Odd (Nat.card (𝓞 (cyclotomicField N) ⧸ P.asIdeal)) := by
  have hchar : ringChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) ≠ 2 := by
    intro hc
    apply h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz := CharP.cast_eq_zero (𝓞 (cyclotomicField N) ⧸ P.asIdeal)
      (ringChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal))
    simpa only [hc, Nat.cast_ofNat, map_ofNat] using hz
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hchar)

/-- The canonical global-character value at a fully constructed geometric
Frobenius agrees with the residue sign, with no lift or power-action input. -/
theorem reflectionCharacter_at_specializationGeometricFrobenius
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (hN : 3 ≤ N)
    (h2N : (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (m : ℕ) :
    reflectionCharacter N hN (specializationGeometricFrobenius N P) ^ m =
      reflectionSign N P hP m := by
  have htwo : (2 : 𝓞 (cyclotomicField N)) ∉ P.asIdeal := by
    intro h
    exact h2N (Ideal.mul_mem_right (N : 𝓞 (cyclotomicField N)) P.asIdeal h)
  exact reflectionCharacter_at_geometricFrobenius N P (absolutePrime N P) hP hN
    (absolutePrime_two_mul_not_mem N P h2N) (residueCard_odd_of_two_not_mem N P htwo) m

/-- Fully constructed geometric Frobenius and global character give the exact
McCarthy reflection formula at every prime away from `2N`. -/
theorem mccarthyValue_complement_at_specializationGeometricFrobenius
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (hN : 3 ≤ N)
    (h2N : (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    mccarthyValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN (specializationGeometricFrobenius N P) ^ m : Qbarˣ) : Qbar) *
        mccarthyValue N P hP m θ ξ hξ := by
  rw [mccarthyValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_at_specializationGeometricFrobenius N P hP hN h2N m]

/-- The fully constructed Frobenius formula in the GPRV normalization. -/
theorem gprvValue_complement_at_specializationGeometricFrobenius
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal) (hN : 3 ≤ N)
    (h2N : (2 * N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : m ≠ 0) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ) :
    gprvValue N P hP m θ (1 - ξ) hξ.complement =
      ((reflectionCharacter N hN (specializationGeometricFrobenius N P) ^ m : Qbarˣ) : Qbar) *
        gprvValue N P hP m θ ξ hξ := by
  rw [gprvValue_complement_eq N P hP m hm hmN θ hθ ξ hξ,
    reflectionCharacter_at_specializationGeometricFrobenius N P hP hN h2N m]

end HilbertModularity.Cyclotomic
