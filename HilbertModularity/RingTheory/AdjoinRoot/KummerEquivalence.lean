/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.AdjoinRoot.RootsOfUnity
import Mathlib.Tactic.Group

/-! # Coprime exponents in Kummer root algebras

Changing a Kummer exponent prime to the covering degree gives an equivalence
of the actual root algebras over a ring where the radicand is a unit. This is
the algebraic coordinate change used in [TripathiGoswamiRevised].
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

/-- A coprime exponent has a representative inverse modulo `N`, with the
integer quotient made explicit for the Kummer coordinate formula. -/
theorem exists_bezout_exponents (N m : ℕ) (hN : 1 < N) (hm : m.Coprime N) :
    ∃ mprime k : ℕ, mprime < N ∧ m * mprime = 1 + k * N := by
  have : NeZero N := ⟨by omega⟩
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime m hm
  let mprime := (u⁻¹ : ZMod N).val
  have hu : (u : ZMod N) = (m : ZMod N) := rfl
  have hc : ((m * mprime : ℕ) : ZMod N) = 1 := by
    calc
      ((m * mprime : ℕ) : ZMod N) = (u : ZMod N) * (u⁻¹ : ZMod N) := by
        rw [Nat.cast_mul, ← hu, ZMod.natCast_zmod_val]
      _ = 1 := Units.mul_inv u
  have hc' : ((m * mprime : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
    simpa using hc
  rw [ZMod.natCast_eq_natCast_iff] at hc'
  have hmod : m * mprime % N = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hN] using hc'
  refine ⟨mprime, (m * mprime) / N, ZMod.val_lt _, ?_⟩
  calc
    m * mprime = m * mprime % N + N * (m * mprime / N) :=
      (Nat.mod_add_div (m * mprime) N).symm
    _ = 1 + (m * mprime / N) * N := by rw [hmod, mul_comm]

/-- Bézout inversion gives the inverse power map on the actual root-of-unity
group. -/
theorem rootsOfUnity_pow_bezout (N m mprime k : ℕ)
    (hbezout : m * mprime = 1 + k * N) (ζ : rootsOfUnity N R) :
    (ζ ^ mprime) ^ m = ζ := by
  have hζ : ζ ^ N = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact (mem_rootsOfUnity' N (ζ : Rˣ)).mp ζ.property
  rw [← pow_mul, mul_comm mprime m, hbezout, pow_add, pow_one,
    mul_comm k N, pow_mul, hζ, one_pow, mul_one]

/-- The converse root-of-unity parameter change uses the `m`th power. -/
theorem rootsOfUnity_pow_bezout' (N m mprime k : ℕ)
    (hbezout : m * mprime = 1 + k * N) (ζ : rootsOfUnity N R) :
    (ζ ^ m) ^ mprime = ζ := by
  calc
    (ζ ^ m) ^ mprime = ζ ^ (m * mprime) := by rw [pow_mul]
    _ = ζ ^ (mprime * m) := by rw [mul_comm mprime m]
    _ = (ζ ^ mprime) ^ m := by rw [pow_mul]
    _ = ζ := rootsOfUnity_pow_bezout N m mprime k hbezout ζ

/-- The deck parameters of two Bézout-related Kummer covers are identified
by the inverse power map. -/
def rootsOfUnityPowEquiv (N m mprime k : ℕ)
    (hbezout : m * mprime = 1 + k * N) :
    rootsOfUnity N R ≃* rootsOfUnity N R where
  toFun ζ := ζ ^ mprime
  invFun ζ := ζ ^ m
  left_inv ζ := rootsOfUnity_pow_bezout N m mprime k hbezout ζ
  right_inv ζ := rootsOfUnity_pow_bezout' N m mprime k hbezout ζ
  map_mul' ζ η := mul_pow ζ η mprime

@[simp] theorem rootsOfUnityPowEquiv_apply (N m mprime k : ℕ)
    (hbezout : m * mprime = 1 + k * N) (ζ : rootsOfUnity N R) :
    rootsOfUnityPowEquiv N m mprime k hbezout ζ = ζ ^ mprime := rfl

@[simp] theorem rootsOfUnityPowEquiv_symm_apply (N m mprime k : ℕ)
    (hbezout : m * mprime = 1 + k * N) (ζ : rootsOfUnity N R) :
    (rootsOfUnityPowEquiv N m mprime k hbezout).symm ζ = ζ ^ m := rfl

/-- Equal defining polynomials present the same root algebra, preserving its root. -/
def rootEquivOfEq {f g : R[X]} (h : f = g) : AdjoinRoot f ≃ₐ[R] AdjoinRoot g :=
  AlgEquiv.ofAlgHom
    (liftAlgHom f (Algebra.ofId R _) (root g) (by
      change aeval (root g) f = 0
      rw [h, aeval_eq, mk_self]))
    (liftAlgHom g (Algebra.ofId R _) (root f) (by
      change aeval (root f) g = 0
      rw [← h, aeval_eq, mk_self]))
    (by apply algHom_ext; simp only [AlgHom.comp_apply, liftAlgHom_root]; rfl)
    (by apply algHom_ext; simp only [AlgHom.comp_apply, liftAlgHom_root]; rfl)

@[simp] theorem rootEquivOfEq_root {f g : R[X]} (h : f = g) :
    rootEquivOfEq h (root f) = root g := by simp [rootEquivOfEq]

/-- The Kummer algebra for the `m`th power of a unit. -/
abbrev KummerRing (N m : ℕ) (a : Rˣ) := AdjoinRoot (X ^ N - C ((a : R) ^ m))

/-- The tautological Kummer coordinate is a unit when the covering degree is positive. -/
def kummerRootUnit (N m : ℕ) (a : Rˣ) (hN : N ≠ 0) : (KummerRing N m a)ˣ :=
  ((isUnit_pow_iff (a := root (X ^ N - C ((a : R) ^ m))) hN).mp (by
    rw [root_X_pow_sub_C_pow]
    exact ((a.isUnit.pow m).map (algebraMap R (KummerRing N m a))))).unit

@[simp] theorem kummerRootUnit_val (N m : ℕ) (a : Rˣ) (hN : N ≠ 0) :
    ((kummerRootUnit N m a hN : (KummerRing N m a)ˣ) : KummerRing N m a) =
      root (X ^ N - C ((a : R) ^ m)) :=
  by simp [kummerRootUnit]

/-- The defining equation as an equality in the unit group. -/
theorem kummerRootUnit_pow (N m : ℕ) (a : Rˣ) (hN : N ≠ 0) :
    kummerRootUnit N m a hN ^ N =
      (Units.map (algebraMap R (KummerRing N m a)).toMonoidHom a) ^ m := by
  apply Units.ext
  simpa using root_X_pow_sub_C_pow N ((a : R) ^ m)

/-- A Bézout inverse coordinate in the `m`th-power root algebra. -/
def kummerInverseCoordinate (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0) :
    (KummerRing N m a)ˣ :=
  kummerRootUnit N m a hN ^ mprime *
    (Units.map (algebraMap R (KummerRing N m a)).toMonoidHom a)⁻¹ ^ k

/-- The Bézout coordinate as an ordinary element of the root algebra. -/
theorem kummerInverseCoordinate_val (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0) :
    (kummerInverseCoordinate N m mprime k a hN : KummerRing N m a) =
      root (X ^ N - C ((a : R) ^ m)) ^ mprime *
        algebraMap R (KummerRing N m a) (((a⁻¹) ^ k : Rˣ) : R) := by
  simp [kummerInverseCoordinate, kummerRootUnit_val, Units.map]

/-- The inverse coordinate is an actual root of the base Kummer equation. -/
theorem kummerInverseCoordinate_pow (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    kummerInverseCoordinate N m mprime k a hN ^ N =
      Units.map (algebraMap R (KummerRing N m a)).toMonoidHom a := by
  let u := Units.map (algebraMap R (KummerRing N m a)).toMonoidHom a
  let z := kummerRootUnit N m a hN
  have hz : z ^ N = u ^ m := kummerRootUnit_pow N m a hN
  dsimp [kummerInverseCoordinate]
  calc
    (z ^ mprime * u⁻¹ ^ k) ^ N = (z ^ N) ^ mprime * (u⁻¹ ^ N) ^ k := by
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm mprime N, mul_comm k N]
    _ = u ^ (m * mprime) * (u ^ (k * N))⁻¹ := by rw [hz]; group
    _ = u := by rw [hbezout]; group

/-- Raising the inverse coordinate back to `m` recovers the original root. -/
theorem kummerInverseCoordinate_pow_m (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    kummerInverseCoordinate N m mprime k a hN ^ m =
      kummerRootUnit N m a hN := by
  let u := Units.map (algebraMap R (KummerRing N m a)).toMonoidHom a
  let z := kummerRootUnit N m a hN
  have hz : z ^ N = u ^ m := kummerRootUnit_pow N m a hN
  dsimp [kummerInverseCoordinate]
  calc
    (z ^ mprime * u⁻¹ ^ k) ^ m = z ^ (m * mprime) * (u ^ m)⁻¹ ^ k := by
      simp only [mul_pow, inv_pow, ← pow_mul]
      rw [mul_comm mprime m, mul_comm k m]
    _ = z ^ (1 + k * N) * (z ^ N)⁻¹ ^ k := by rw [hbezout, hz]
    _ = z := by group

/-- The root `z ↦ z^m` map from the `m`th-power algebra to the base algebra. -/
def kummerToBase (N m : ℕ) (a : Rˣ) :
    KummerRing N m a →ₐ[R] KummerRing N 1 a :=
  liftAlgHom (X ^ N - C ((a : R) ^ m)) (Algebra.ofId R _)
    (root (X ^ N - C ((a : R) ^ 1)) ^ m) (by
      change aeval (root (X ^ N - C ((a : R) ^ 1)) ^ m) (X ^ N - C ((a : R) ^ m)) = 0
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [← pow_mul, mul_comm m N, pow_mul, root_X_pow_sub_C_pow]
      simp)

@[simp] theorem kummerToBase_root (N m : ℕ) (a : Rˣ) :
    kummerToBase N m a (root (X ^ N - C ((a : R) ^ m))) =
      root (X ^ N - C ((a : R) ^ 1)) ^ m :=
  liftAlgHom_root _ _ _ _

/-- The Bézout coordinate gives the inverse map to the base root algebra. -/
def kummerFromBase (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    KummerRing N 1 a →ₐ[R] KummerRing N m a :=
  liftAlgHom (X ^ N - C ((a : R) ^ 1)) (Algebra.ofId R _)
    (kummerInverseCoordinate N m mprime k a hN : KummerRing N m a) (by
      change aeval (kummerInverseCoordinate N m mprime k a hN : KummerRing N m a)
        (X ^ N - C ((a : R) ^ 1)) = 0
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [sub_eq_zero]
      simpa [Units.map, pow_one] using
        congrArg Units.val (kummerInverseCoordinate_pow N m mprime k a hN hbezout))

@[simp] theorem kummerFromBase_root (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    kummerFromBase N m mprime k a hN hbezout
      (root (X ^ N - C ((a : R) ^ 1))) =
      (kummerInverseCoordinate N m mprime k a hN : KummerRing N m a) :=
  liftAlgHom_root _ _ _ _

/-- The Bézout coordinate maps back to the base Kummer root. -/
theorem kummerToBase_inverseCoordinate (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    kummerToBase N m a
      (kummerInverseCoordinate N m mprime k a hN : KummerRing N m a) =
      root (X ^ N - C ((a : R) ^ 1)) := by
  let f := kummerToBase N m a
  let zb := kummerRootUnit N 1 a hN
  let ub := Units.map (algebraMap R (KummerRing N 1 a)).toMonoidHom a
  have hzb : zb ^ N = ub := by
    simpa [zb, ub, algebraMap_eq] using kummerRootUnit_pow N 1 a hN
  have hr : Units.map f.toRingHom.toMonoidHom (kummerRootUnit N m a hN) = zb ^ m := by
    apply Units.ext
    simp [f, zb]
  have hu : Units.map f.toRingHom.toMonoidHom
      (Units.map (algebraMap R (KummerRing N m a)).toMonoidHom a) = ub := by
    apply Units.ext
    simpa [f, ub, Units.map] using f.commutes (a : R)
  have hc : Units.map f.toRingHom.toMonoidHom
      (kummerInverseCoordinate N m mprime k a hN) = zb := by
    simp only [kummerInverseCoordinate, map_mul, map_pow, map_inv, hr, hu]
    calc
      (zb ^ m) ^ mprime * ub⁻¹ ^ k = zb ^ (m * mprime) * ub⁻¹ ^ k := by rw [pow_mul]
      _ = zb ^ (1 + k * N) * (zb ^ N)⁻¹ ^ k := by rw [hbezout, hzb]
      _ = zb := by group
  exact congrArg Units.val hc

/-- The actual Kummer root algebras for Bézout-related exponents are equivalent. -/
def kummerExponentEquiv (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    KummerRing N m a ≃ₐ[R] KummerRing N 1 a :=
  AlgEquiv.ofAlgHom (kummerToBase N m a)
    (kummerFromBase N m mprime k a hN hbezout)
    (by
      apply algHom_ext
      simp only [AlgHom.comp_apply, kummerFromBase_root]
      exact kummerToBase_inverseCoordinate N m mprime k a hN hbezout)
    (by
      apply algHom_ext
      simp only [AlgHom.comp_apply, kummerToBase_root, map_pow, kummerFromBase_root]
      exact congrArg Units.val (kummerInverseCoordinate_pow_m N m mprime k a hN hbezout))

@[simp] theorem kummerExponentEquiv_root (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    kummerExponentEquiv N m mprime k a hN hbezout
      (root (X ^ N - C ((a : R) ^ m))) =
      root (X ^ N - C ((a : R) ^ 1)) ^ m :=
  kummerToBase_root N m a

@[simp] theorem kummerExponentEquiv_symm_root (N m mprime k : ℕ) (a : Rˣ) (hN : N ≠ 0)
    (hbezout : m * mprime = 1 + k * N) :
    (kummerExponentEquiv N m mprime k a hN hbezout).symm
      (root (X ^ N - C ((a : R) ^ 1))) =
      (kummerInverseCoordinate N m mprime k a hN : KummerRing N m a) :=
  kummerFromBase_root N m mprime k a hN hbezout

/-- Removing an `N`th-power unit from a root equation, in the direction of
division of the original root by that unit. -/
def kummerScaleTo (N : ℕ) (u : Rˣ) (a : R) :
    AdjoinRoot (X ^ N - C ((u : R) ^ N * a)) →ₐ[R] AdjoinRoot (X ^ N - C a) :=
  liftAlgHom (X ^ N - C ((u : R) ^ N * a)) (Algebra.ofId R _)
    ((algebraMap R (AdjoinRoot (X ^ N - C a)) (u : R)) * root (X ^ N - C a)) (by
      change aeval ((algebraMap R (AdjoinRoot (X ^ N - C a)) (u : R)) *
        root (X ^ N - C a)) (X ^ N - C ((u : R) ^ N * a)) = 0
      simp only [map_sub, map_pow, aeval_X, aeval_C, mul_pow, root_X_pow_sub_C_pow,
        map_mul, map_pow]
      simp only [algebraMap_eq]
      ring)

@[simp] theorem kummerScaleTo_root (N : ℕ) (u : Rˣ) (a : R) :
    kummerScaleTo N u a (root (X ^ N - C ((u : R) ^ N * a))) =
      (algebraMap R (AdjoinRoot (X ^ N - C a)) (u : R)) * root (X ^ N - C a) :=
  liftAlgHom_root _ _ _ _

/-- Adjoining a root after multiplying the radicand by an `N`th-power unit. -/
def kummerScaleFrom (N : ℕ) (u : Rˣ) (a : R) :
    AdjoinRoot (X ^ N - C a) →ₐ[R] AdjoinRoot (X ^ N - C ((u : R) ^ N * a)) :=
  liftAlgHom (X ^ N - C a) (Algebra.ofId R _)
    ((algebraMap R (AdjoinRoot (X ^ N - C ((u : R) ^ N * a))) ((u⁻¹ : Rˣ) : R)) *
      root (X ^ N - C ((u : R) ^ N * a))) (by
      change aeval ((algebraMap R (AdjoinRoot (X ^ N - C ((u : R) ^ N * a)))
        ((u⁻¹ : Rˣ) : R)) * root (X ^ N - C ((u : R) ^ N * a))) (X ^ N - C a) = 0
      simp only [map_sub, map_pow, aeval_X, aeval_C, mul_pow, root_X_pow_sub_C_pow,
        map_mul, map_pow]
      simp only [algebraMap_eq]
      rw [← mul_assoc, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow, one_mul]
      simp)

@[simp] theorem kummerScaleFrom_root (N : ℕ) (u : Rˣ) (a : R) :
    kummerScaleFrom N u a (root (X ^ N - C a)) =
      (algebraMap R (AdjoinRoot (X ^ N - C ((u : R) ^ N * a))) ((u⁻¹ : Rˣ) : R)) *
        root (X ^ N - C ((u : R) ^ N * a)) :=
  liftAlgHom_root _ _ _ _

/-- An `N`th-power unit factor does not change the actual root algebra. -/
def kummerScaleEquiv (N : ℕ) (u : Rˣ) (a : R) :
    AdjoinRoot (X ^ N - C ((u : R) ^ N * a)) ≃ₐ[R] AdjoinRoot (X ^ N - C a) :=
  AlgEquiv.ofAlgHom (kummerScaleTo N u a) (kummerScaleFrom N u a)
    (by
      apply algHom_ext
      simp only [AlgHom.comp_apply, kummerScaleFrom_root, map_mul,
        AlgHom.commutes, kummerScaleTo_root]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rfl)
    (by
      apply algHom_ext
      simp only [AlgHom.comp_apply, kummerScaleTo_root, map_mul,
        AlgHom.commutes, kummerScaleFrom_root]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
      rfl)

end AdjoinRoot
