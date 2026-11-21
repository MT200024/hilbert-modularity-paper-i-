/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.AdjoinRoot.KummerEquivalence
public import HilbertModularity.Hypergeometric.EulerCover.DeckTransformations
public import HilbertModularity.NumberTheory.CyclotomicEmbeddings
import Mathlib.Tactic.Group

/-! # Coprime exponent changes for the Euler cover

On the branch complement, the coordinate `z_m = y/(1-x)` satisfies
`z_m^N = h^m` for `h = x(1-t*x)/(1-x)`. The corresponding Kummer
algebra equivalence is the affine algebraic part of revised Definition 2.3
[TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

open Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {R : Type*} [CommRing R] (t : R)

/-- The original branch coordinate in the localized base ring. -/
def xCoordinate : BaseRing t := algebraMap R[X] (BaseRing t) X

/-- The invertible factor `1-x` on the branch complement. -/
def oneMinusX : BaseRing t := algebraMap R[X] (BaseRing t) (1 - X)

/-- The invertible factor `1-t*x` on the branch complement. -/
def oneMinusTX : BaseRing t := algebraMap R[X] (BaseRing t) (1 - C t * X)

theorem isUnit_xCoordinate : IsUnit (xCoordinate t) := by
  have h : IsUnit (algebraMap R[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  exact h.1.1

theorem isUnit_oneMinusX : IsUnit (oneMinusX t) := by
  have h : IsUnit (algebraMap R[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  exact h.1.2

theorem isUnit_oneMinusTX : IsUnit (oneMinusTX t) := by
  have h : IsUnit (algebraMap R[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  exact h.2

/-- Unit representing `x` in the localized base ring. -/
def xUnit : (BaseRing t)ˣ := (isUnit_xCoordinate t).unit

/-- Unit representing `1-x` in the localized base ring. -/
def oneMinusXUnit : (BaseRing t)ˣ := (isUnit_oneMinusX t).unit

/-- Unit representing `1-t*x` in the localized base ring. -/
def oneMinusTXUnit : (BaseRing t)ˣ := (isUnit_oneMinusTX t).unit

@[simp] theorem xUnit_val : (xUnit t : BaseRing t) = xCoordinate t := IsUnit.unit_spec _
@[simp] theorem oneMinusXUnit_val : (oneMinusXUnit t : BaseRing t) = oneMinusX t :=
  IsUnit.unit_spec _
@[simp] theorem oneMinusTXUnit_val : (oneMinusTXUnit t : BaseRing t) = oneMinusTX t :=
  IsUnit.unit_spec _

/-- The rational Kummer radicand `h=x(1-t*x)/(1-x)` as a unit. -/
def hUnit : (BaseRing t)ˣ := xUnit t * oneMinusTXUnit t * (oneMinusXUnit t)⁻¹

theorem hUnit_val : (hUnit t : BaseRing t) =
    xCoordinate t * oneMinusTX t * ((oneMinusXUnit t)⁻¹ : (BaseRing t)ˣ) := by
  simp [hUnit]

/-- The Euler radicand is the `N`th-power coordinate factor times `h^m`. -/
theorem radicand_eq_kummer (N m : ℕ) (hm : m ≤ N) :
    radicand N m t = (oneMinusXUnit t : BaseRing t) ^ N * (hUnit t : BaseRing t) ^ m := by
  have heq : oneMinusXUnit t ^ N * hUnit t ^ m =
      xUnit t ^ m * oneMinusXUnit t ^ (N - m) * oneMinusTXUnit t ^ m := by
    calc
      oneMinusXUnit t ^ N * hUnit t ^ m =
          oneMinusXUnit t ^ (m + (N - m)) *
            (xUnit t * oneMinusTXUnit t * (oneMinusXUnit t)⁻¹) ^ m := by
              rw [Nat.add_sub_of_le hm]
              rfl
      _ = (oneMinusXUnit t ^ m * ((oneMinusXUnit t)⁻¹) ^ m) *
            (xUnit t ^ m * oneMinusXUnit t ^ (N - m) * oneMinusTXUnit t ^ m) := by
              simp only [pow_add, mul_pow]
              simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by rw [← mul_pow, mul_inv_cancel, one_pow, one_mul]
  have hv := congrArg (fun u : (BaseRing t)ˣ => (u : BaseRing t)) heq
  simpa [radicand, branchPolynomial, xUnit_val, oneMinusXUnit_val,
    oneMinusTXUnit_val, xCoordinate, oneMinusX, oneMinusTX] using hv.symm

/-- The actual coordinate `z_m=y/(1-x)` in the Euler cover algebra. -/
def normalizedRoot (N m : ℕ) : CoverRing N m t :=
  algebraMap (BaseRing t) (CoverRing N m t) (↑((oneMinusXUnit t)⁻¹) : BaseRing t) *
    coverRoot N m t

/-- Recover the original Euler coordinate from `z_m`. -/
theorem oneMinusX_mul_normalizedRoot (N m : ℕ) :
    algebraMap (BaseRing t) (CoverRing N m t) (oneMinusXUnit t : BaseRing t) *
      normalizedRoot t N m = coverRoot N m t := by
  rw [normalizedRoot, ← mul_assoc, ← map_mul]
  change algebraMap (BaseRing t) (CoverRing N m t)
    (((oneMinusXUnit t * (oneMinusXUnit t)⁻¹ : (BaseRing t)ˣ) : BaseRing t)) *
      coverRoot N m t = coverRoot N m t
  rw [mul_inv_cancel, Units.val_one, map_one, one_mul]

/-- The original deck action scales the normalized Kummer coordinate by the
same root of unity. -/
theorem deckAlgebraAction_normalizedRoot (N m : ℕ) [NeZero N]
    (ζ : rootsOfUnity N R) :
    deckAlgebraAction N m t ζ (normalizedRoot t N m) =
      (algebraMap R[X] (BaseRing t) (C ((ζ : Rˣ) : R))) • normalizedRoot t N m := by
  rw [normalizedRoot, map_mul, (deckAlgebraAction N m t ζ).commutes,
    deckAlgebraAction_root]
  simp only [Algebra.smul_def]
  ring

/-- The coefficient of a powered deck parameter is the corresponding power
of its coefficient in the branch-complement ring. -/
theorem deckScalar_pow (N : ℕ) (ζ : rootsOfUnity N R) (j : ℕ) :
    (algebraMap R[X] (BaseRing t) (C ((ζ : Rˣ) : R))) ^ j =
      algebraMap R[X] (BaseRing t) (C (((ζ ^ j : rootsOfUnity N R) : Rˣ) : R)) := by
  simp

/-- The deck action on a power of the Kummer coordinate uses the powered
deck parameter. -/
theorem deckAlgebraAction_normalizedRoot_pow (N m : ℕ) [NeZero N]
    (ζ : rootsOfUnity N R) (j : ℕ) :
    deckAlgebraAction N m t ζ (normalizedRoot t N m ^ j) =
      (algebraMap R[X] (BaseRing t)
        (C (((ζ ^ j : rootsOfUnity N R) : Rˣ) : R))) •
          normalizedRoot t N m ^ j := by
  rw [Algebra.smul_def]
  calc
    deckAlgebraAction N m t ζ (normalizedRoot t N m ^ j) =
        (deckAlgebraAction N m t ζ (normalizedRoot t N m)) ^ j := map_pow _ _ _
    _ = (algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap R[X] (BaseRing t) (C ((ζ : Rˣ) : R))) *
            normalizedRoot t N m) ^ j := by
          rw [deckAlgebraAction_normalizedRoot, Algebra.smul_def]
    _ = algebraMap (BaseRing t) (CoverRing N m t)
          ((algebraMap R[X] (BaseRing t) (C ((ζ : Rˣ) : R))) ^ j) *
            normalizedRoot t N m ^ j := by rw [mul_pow, map_pow]
    _ = _ := by rw [deckScalar_pow]

/-- The normalized coordinate obeys the precise Kummer equation. -/
theorem normalizedRoot_pow (N m : ℕ) (hm : m ≤ N) :
    normalizedRoot t N m ^ N =
      algebraMap (BaseRing t) (CoverRing N m t) ((hUnit t : BaseRing t) ^ m) := by
  rw [normalizedRoot, mul_pow, coverRoot_pow, radicand_eq_kummer t N m hm]
  simp only [map_mul, map_pow]
  rw [← mul_assoc, ← mul_pow, ← map_mul]
  change (algebraMap (BaseRing t) (CoverRing N m t)
    (((oneMinusXUnit t)⁻¹ * oneMinusXUnit t : (BaseRing t)ˣ) : BaseRing t)) ^ N *
      (algebraMap (BaseRing t) (CoverRing N m t) (hUnit t : BaseRing t)) ^ m = _
  rw [inv_mul_cancel, Units.val_one, map_one, one_pow, one_mul]

/-- The original Euler algebra is the Kummer algebra of `h^m` after the
coordinate change `z_m=y/(1-x)`. -/
def eulerKummerEquiv (N m : ℕ) (hm : m ≤ N) :
    CoverRing N m t ≃ₐ[BaseRing t] AdjoinRoot.KummerRing N m (hUnit t) := by
  have hp : coverPolynomial N m t =
      X ^ N - C ((oneMinusXUnit t : BaseRing t) ^ N * (hUnit t : BaseRing t) ^ m) := by
    rw [coverPolynomial, radicand_eq_kummer t N m hm]
  exact (AdjoinRoot.rootEquivOfEq hp).trans (AdjoinRoot.kummerScaleEquiv N (oneMinusXUnit t)
    ((hUnit t : BaseRing t) ^ m))

/-- The cover coordinate maps to `(1-x)z_m` under the Euler–Kummer equivalence. -/
theorem eulerKummerEquiv_coverRoot (N m : ℕ) (hm : m ≤ N) :
    eulerKummerEquiv t N m hm (coverRoot N m t) =
      algebraMap (BaseRing t) (AdjoinRoot.KummerRing N m (hUnit t))
        (oneMinusXUnit t : BaseRing t) *
      AdjoinRoot.root (X ^ N - C ((hUnit t : BaseRing t) ^ m)) := by
  simp [eulerKummerEquiv, AdjoinRoot.kummerScaleEquiv, coverRoot]

/-- The rescaled cover coordinate is precisely the Kummer root. -/
@[simp] theorem eulerKummerEquiv_normalizedRoot (N m : ℕ) (hm : m ≤ N) :
    eulerKummerEquiv t N m hm (normalizedRoot t N m) =
      AdjoinRoot.root (X ^ N - C ((hUnit t : BaseRing t) ^ m)) := by
  rw [normalizedRoot, map_mul, (eulerKummerEquiv t N m hm).commutes,
    eulerKummerEquiv_coverRoot t N m hm, ← mul_assoc, ← map_mul]
  change algebraMap (BaseRing t) (AdjoinRoot.KummerRing N m (hUnit t))
    (((oneMinusXUnit t)⁻¹ * oneMinusXUnit t : (BaseRing t)ˣ) : BaseRing t) * _ = _
  rw [inv_mul_cancel, Units.val_one, map_one, one_mul]

/-- Coprime exponent change between the two actual affine Euler algebras. -/
def exponentChangeEquiv (N m mprime k : ℕ) (hm : m < N)
    (hbezout : m * mprime = 1 + k * N) :
    CoverRing N m t ≃ₐ[BaseRing t] CoverRing N 1 t := by
  have hN : N ≠ 0 := by omega
  have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  exact (eulerKummerEquiv t N m (Nat.le_of_lt hm)).trans
    ((AdjoinRoot.kummerExponentEquiv N m mprime k (hUnit t) hN hbezout).trans
      (eulerKummerEquiv t N 1 h1).symm)

/-- A pointwise form of the three algebra equivalences used in exponent change. -/
theorem exponentChangeEquiv_apply (N m mprime k : ℕ) (hm : m < N)
    (hbezout : m * mprime = 1 + k * N) (z : CoverRing N m t) :
    exponentChangeEquiv t N m mprime k hm hbezout z =
      (eulerKummerEquiv t N 1 (Nat.one_le_iff_ne_zero.mpr (by omega))).symm
        ((AdjoinRoot.kummerExponentEquiv N m mprime k (hUnit t) (by omega) hbezout)
          ((eulerKummerEquiv t N m (Nat.le_of_lt hm)) z)) := by
  rfl

/-- The inverse equivalence applies the base Euler, Kummer and exponent maps
in the reverse order. -/
theorem exponentChangeEquiv_symm_apply (N m mprime k : ℕ) (hm : m < N)
    (hbezout : m * mprime = 1 + k * N) (z : CoverRing N 1 t) :
    (exponentChangeEquiv t N m mprime k hm hbezout).symm z =
      (eulerKummerEquiv t N m (Nat.le_of_lt hm)).symm
        ((AdjoinRoot.kummerExponentEquiv N m mprime k (hUnit t) (by omega) hbezout).symm
          ((eulerKummerEquiv t N 1 (Nat.one_le_iff_ne_zero.mpr (by omega))) z)) := by
  rfl

/-- The actual exponent change sends `z_m` to `z_1^m`. -/
theorem exponentChangeEquiv_normalizedRoot (N m mprime k : ℕ) (hm : m < N)
    (hbezout : m * mprime = 1 + k * N) :
    exponentChangeEquiv t N m mprime k hm hbezout (normalizedRoot t N m) =
      normalizedRoot t N 1 ^ m := by
  have hN : N ≠ 0 := by omega
  have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  apply (eulerKummerEquiv t N 1 h1).injective
  calc
    eulerKummerEquiv t N 1 h1
        (exponentChangeEquiv t N m mprime k hm hbezout (normalizedRoot t N m)) =
      (AdjoinRoot.kummerExponentEquiv N m mprime k (hUnit t) hN hbezout)
        ((eulerKummerEquiv t N m (Nat.le_of_lt hm)) (normalizedRoot t N m)) := by
          rw [exponentChangeEquiv_apply]
          exact (eulerKummerEquiv t N 1 h1).apply_symm_apply _
    _ = AdjoinRoot.root (X ^ N - C ((hUnit t : BaseRing t) ^ 1)) ^ m := by
      rw [eulerKummerEquiv_normalizedRoot,
        AdjoinRoot.kummerExponentEquiv_root]
    _ = eulerKummerEquiv t N 1 h1 (normalizedRoot t N 1 ^ m) := by
      simpa only [eulerKummerEquiv_normalizedRoot] using
        (map_pow (eulerKummerEquiv t N 1 h1) (normalizedRoot t N 1) m).symm

/-- The actual Euler coordinate maps to `(1-x)z_1^m`. -/
theorem exponentChangeEquiv_coverRoot (N m mprime k : ℕ) (hm : m < N)
    (hbezout : m * mprime = 1 + k * N) :
    exponentChangeEquiv t N m mprime k hm hbezout (coverRoot N m t) =
      algebraMap (BaseRing t) (CoverRing N 1 t) (oneMinusXUnit t : BaseRing t) *
        normalizedRoot t N 1 ^ m := by
  let e := exponentChangeEquiv t N m mprime k hm hbezout
  calc
    e (coverRoot N m t) =
        e (algebraMap (BaseRing t) (CoverRing N m t)
          (oneMinusXUnit t : BaseRing t) * normalizedRoot t N m) := by
            rw [oneMinusX_mul_normalizedRoot]
    _ = algebraMap (BaseRing t) (CoverRing N 1 t)
          (oneMinusXUnit t : BaseRing t) * e (normalizedRoot t N m) := by
            rw [map_mul, e.commutes]
    _ = _ := by rw [exponentChangeEquiv_normalizedRoot]

/-- The inverse coordinate in the actual Euler cover is
`z_1 = z_m^mprime / h^k`. -/
theorem exponentChangeEquiv_symm_normalizedRoot (N m mprime k : ℕ) (hm : m < N)
    (hbezout : m * mprime = 1 + k * N) :
    (exponentChangeEquiv t N m mprime k hm hbezout).symm (normalizedRoot t N 1) =
      normalizedRoot t N m ^ mprime *
        algebraMap (BaseRing t) (CoverRing N m t)
          ((((hUnit t)⁻¹) ^ k : (BaseRing t)ˣ) : BaseRing t) := by
  have hN : N ≠ 0 := by omega
  have h1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  apply (eulerKummerEquiv t N m (Nat.le_of_lt hm)).injective
  calc
    eulerKummerEquiv t N m (Nat.le_of_lt hm)
        ((exponentChangeEquiv t N m mprime k hm hbezout).symm
          (normalizedRoot t N 1)) =
      (AdjoinRoot.kummerExponentEquiv N m mprime k (hUnit t) hN hbezout).symm
        ((eulerKummerEquiv t N 1 h1) (normalizedRoot t N 1)) := by
          rw [exponentChangeEquiv_symm_apply]
          exact (eulerKummerEquiv t N m (Nat.le_of_lt hm)).apply_symm_apply _
    _ = (AdjoinRoot.kummerInverseCoordinate N m mprime k (hUnit t) hN :
        AdjoinRoot.KummerRing N m (hUnit t)) := by
          rw [eulerKummerEquiv_normalizedRoot,
            AdjoinRoot.kummerExponentEquiv_symm_root]
    _ = eulerKummerEquiv t N m (Nat.le_of_lt hm)
        (normalizedRoot t N m ^ mprime *
          algebraMap (BaseRing t) (CoverRing N m t)
            ((((hUnit t)⁻¹) ^ k : (BaseRing t)ˣ) : BaseRing t)) := by
          simp only [AdjoinRoot.kummerInverseCoordinate_val, map_mul, map_pow,
            eulerKummerEquiv_normalizedRoot,
            (eulerKummerEquiv t N m (Nat.le_of_lt hm)).commutes]

/-- On the normalized coordinate, exponent change conjugates the `m`-cover
deck factor `ζ` to the base-cover factor `ζ^mprime`. -/
theorem exponentChangeEquiv_deck_normalizedRoot (N m mprime k : ℕ) [NeZero N]
    (hm : m < N) (hbezout : m * mprime = 1 + k * N)
    (ζ : rootsOfUnity N R) :
    exponentChangeEquiv t N m mprime k hm hbezout
      (deckAlgebraAction N m t ζ (normalizedRoot t N m)) =
    deckAlgebraAction N 1 t (ζ ^ mprime)
      (exponentChangeEquiv t N m mprime k hm hbezout (normalizedRoot t N m)) := by
  let e := exponentChangeEquiv t N m mprime k hm hbezout
  let c := algebraMap R[X] (BaseRing t) (C ((ζ : Rˣ) : R))
  have hc : e (c • normalizedRoot t N m) = c • e (normalizedRoot t N m) := by
    simp only [Algebra.smul_def, map_mul, e.commutes]
  calc
    e (deckAlgebraAction N m t ζ (normalizedRoot t N m)) =
        e (c • normalizedRoot t N m) := by rw [deckAlgebraAction_normalizedRoot]
    _ = c • e (normalizedRoot t N m) := hc
    _ = c • normalizedRoot t N 1 ^ m := by
      rw [exponentChangeEquiv_normalizedRoot]
    _ = (algebraMap R[X] (BaseRing t)
          (C (((((ζ ^ mprime) ^ m : rootsOfUnity N R) : Rˣ) : R)))) •
            normalizedRoot t N 1 ^ m := by
      rw [AdjoinRoot.rootsOfUnity_pow_bezout N m mprime k hbezout]
    _ = deckAlgebraAction N 1 t (ζ ^ mprime) (normalizedRoot t N 1 ^ m) := by
      rw [deckAlgebraAction_normalizedRoot_pow]
    _ = deckAlgebraAction N 1 t (ζ ^ mprime) (e (normalizedRoot t N m)) := by
      rw [exponentChangeEquiv_normalizedRoot]

/-- Exact intertwining of the actual Euler-cover algebra maps. The factor
`ζ` on the `m`-cover becomes `ζ^mprime` on the base cover. -/
theorem exponentChangeEquiv_deck (N m mprime k : ℕ) [NeZero N]
    (hm : m < N) (hbezout : m * mprime = 1 + k * N)
    (ζ : rootsOfUnity N R) :
    (exponentChangeEquiv t N m mprime k hm hbezout).toAlgHom.comp
        (deckAlgebraAction N m t ζ).toAlgHom =
      (deckAlgebraAction N 1 t (ζ ^ mprime)).toAlgHom.comp
        (exponentChangeEquiv t N m mprime k hm hbezout).toAlgHom := by
  let e := exponentChangeEquiv t N m mprime k hm hbezout
  let dm := deckAlgebraAction N m t ζ
  let d1 := deckAlgebraAction N 1 t (ζ ^ mprime)
  let u := (oneMinusXUnit t : BaseRing t)
  have hnorm : e (dm (normalizedRoot t N m)) = d1 (e (normalizedRoot t N m)) :=
    exponentChangeEquiv_deck_normalizedRoot t N m mprime k hm hbezout ζ
  apply AdjoinRoot.algHom_ext
  change e (dm (coverRoot N m t)) = d1 (e (coverRoot N m t))
  calc
    e (dm (coverRoot N m t)) =
        e (dm (algebraMap (BaseRing t) (CoverRing N m t) u *
          normalizedRoot t N m)) := by rw [oneMinusX_mul_normalizedRoot]
    _ = algebraMap (BaseRing t) (CoverRing N 1 t) u *
          e (dm (normalizedRoot t N m)) := by
      simp only [map_mul, AlgEquiv.commutes]
    _ = algebraMap (BaseRing t) (CoverRing N 1 t) u *
          d1 (e (normalizedRoot t N m)) := by rw [hnorm]
    _ = d1 (e (algebraMap (BaseRing t) (CoverRing N m t) u *
          normalizedRoot t N m)) := by
      simp only [map_mul, AlgEquiv.commutes]
    _ = d1 (e (coverRoot N m t)) := by rw [oneMinusX_mul_normalizedRoot]

/-- Equivalently, the base-cover deck factor `ζ` corresponds to `ζ^m` on
the `m`-cover. This is the direction used to read the fixed character on the
`m`-cover as the `m`th coefficient label of the base cover. -/
theorem exponentChangeEquiv_deck_baseParameter (N m mprime k : ℕ) [NeZero N]
    (hm : m < N) (hbezout : m * mprime = 1 + k * N)
    (ζ : rootsOfUnity N R) :
    (exponentChangeEquiv t N m mprime k hm hbezout).toAlgHom.comp
        (deckAlgebraAction N m t (ζ ^ m)).toAlgHom =
      (deckAlgebraAction N 1 t ζ).toAlgHom.comp
        (exponentChangeEquiv t N m mprime k hm hbezout).toAlgHom := by
  simpa only [AdjoinRoot.rootsOfUnity_pow_bezout' N m mprime k hbezout] using
    exponentChangeEquiv_deck t N m mprime k hm hbezout (ζ ^ m)

/-- Coprimality supplies the Bézout coordinate and hence an equivalence of the
actual Euler covers whose base deck parameter acts by its `m`th power on the
`m`-cover. -/
theorem exists_exponentChangeEquiv_of_coprime (N m : ℕ) [NeZero N]
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    ∃ e : CoverRing N m t ≃ₐ[BaseRing t] CoverRing N 1 t,
      e (normalizedRoot t N m) = normalizedRoot t N 1 ^ m ∧
      ∀ ζ : rootsOfUnity N R,
        e.toAlgHom.comp (deckAlgebraAction N m t (ζ ^ m)).toAlgHom =
          (deckAlgebraAction N 1 t ζ).toAlgHom.comp e.toAlgHom := by
  obtain ⟨mprime, k, _, hbezout⟩ :=
    AdjoinRoot.exists_bezout_exponents N m (by omega) hcop
  exact ⟨exponentChangeEquiv t N m mprime k hm hbezout,
    exponentChangeEquiv_normalizedRoot t N m mprime k hm hbezout,
    exponentChangeEquiv_deck_baseParameter t N m mprime k hm hbezout⟩

/-- The real label of the base cover under the actual `m`th deck-parameter
change, followed by the chosen full-cyclotomic coefficient embedding. The
algebraic source of the exponent is `exponentChangeEquiv_deck_baseParameter`;
the field-label calculation is `Cyclotomic.coefficientEmbedding_tau_one`. -/
theorem exponentChange_realCoefficientLabel (N m : ℕ) [NeZero N]
    (hm : m.Coprime N) (L : Type*) [Field L] [Algebra ℚ L]
    (ι : Cyclotomic.cyclotomicField N →ₐ[ℚ] L) :
    ι (Cyclotomic.coefficientEmbedding N m hm (Cyclotomic.cyclotomicField N)
      (Cyclotomic.realCyclotomicField_le N) (Cyclotomic.tau N 1)) =
    ι (IntermediateField.inclusion (Cyclotomic.realCyclotomicField_le N)
      (Cyclotomic.tau N m)) := by
  rw [Cyclotomic.coefficientEmbedding_tau_one]

end HilbertModularity.Hypergeometric.EulerCover
