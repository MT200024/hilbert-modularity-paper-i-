/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.Smoothness
public import HilbertModularity.RingTheory.AdjoinRoot.KummerEquivalence
public import HilbertModularity.RingTheory.Smooth.KummerHypersurface
public import HilbertModularity.NumberTheory.PowerResidue
import Mathlib.Tactic.Group

/-! # The zero branch of the Euler cover

The zero-branch chart retains the `x` coordinate and replaces the singular
covering coordinate by a Bézout coordinate. Its equation is
`z ^ N = x * U ^ a`, where `U = (1-x) ^ (N-m) * (1-t*x) ^ m` is a unit on this
chart. This is one affine chart of the smooth proper family described in
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [CommRing K]

/-- The two branch factors that stay invertible on the zero chart. -/
def zeroBranchProduct (t : K) : K[X] := (1 - X) * (1 - C t * X)

/-- The base of the zero-branch chart. -/
abbrev ZeroBaseRing (t : K) := Localization.Away (zeroBranchProduct t)

/-- The original `x` coordinate on the zero chart. -/
def zeroBaseX (t : K) : ZeroBaseRing t :=
  algebraMap K[X] (ZeroBaseRing t) X

/-- The invertible part of the Euler radicand near `x=0`. -/
def zeroBranchFactor (N m : ℕ) (t : K) : ZeroBaseRing t :=
  algebraMap K[X] (ZeroBaseRing t)
    ((1 - X) ^ (N - m) * (1 - C t * X) ^ m)

theorem isUnit_zeroBranchFactor (N m : ℕ) (t : K) :
    IsUnit (zeroBranchFactor N m t) := by
  have h : IsUnit (algebraMap K[X] (ZeroBaseRing t) (zeroBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (zeroBranchProduct t)
  simp only [zeroBranchProduct, map_mul, IsUnit.mul_iff] at h
  simpa only [zeroBranchFactor, map_mul, map_pow] using
    (h.1.pow (N - m)).mul (h.2.pow m)

/-- The unit `U` in the zero-branch equation. -/
def zeroBranchUnit (N m : ℕ) (t : K) : (ZeroBaseRing t)ˣ :=
  (isUnit_zeroBranchFactor N m t).unit

@[simp] theorem zeroBranchUnit_val (N m : ℕ) (t : K) :
    (zeroBranchUnit N m t : ZeroBaseRing t) = zeroBranchFactor N m t := by
  simp [zeroBranchUnit]

/-- The normalized zero-branch equation `z^N = x U^a`. -/
def zeroBranchPolynomial (N m a : ℕ) (t : K) : (ZeroBaseRing t)[X] :=
  X ^ N - C (zeroBaseX t * (zeroBranchUnit N m t : ZeroBaseRing t) ^ a)

/-- The actual root algebra of the zero-branch equation. -/
abbrev ZeroBranchRing (N m a : ℕ) (t : K) :=
  AdjoinRoot (zeroBranchPolynomial N m a t)

/-- The coordinate `z` of the normalized zero chart. -/
def zeroBranchRoot (N m a : ℕ) (t : K) : ZeroBranchRing N m a t :=
  AdjoinRoot.root (zeroBranchPolynomial N m a t)

theorem zeroBranchRoot_pow (N m a : ℕ) (t : K) :
    zeroBranchRoot N m a t ^ N =
      algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t)
        (zeroBaseX t * (zeroBranchUnit N m t : ZeroBaseRing t) ^ a) :=
  AdjoinRoot.root_X_pow_sub_C_pow N _

/-- The original Euler equation before the normalization at `x=0`. -/
def zeroSingularPolynomial (N m : ℕ) (t : K) : (ZeroBaseRing t)[X] :=
  X ^ N - C (zeroBaseX t ^ m * (zeroBranchUnit N m t : ZeroBaseRing t))

/-- The actual singular Euler root algebra on the zero-chart base. -/
abbrev ZeroSingularRing (N m : ℕ) (t : K) :=
  AdjoinRoot (zeroSingularPolynomial N m t)

/-- The original covering coordinate `y` on this base. -/
def zeroSingularRoot (N m : ℕ) (t : K) : ZeroSingularRing N m t :=
  AdjoinRoot.root (zeroSingularPolynomial N m t)

theorem zeroSingularRoot_pow (N m : ℕ) (t : K) :
    zeroSingularRoot N m t ^ N =
      algebraMap (ZeroBaseRing t) (ZeroSingularRing N m t)
        (zeroBaseX t ^ m * (zeroBranchUnit N m t : ZeroBaseRing t)) :=
  AdjoinRoot.root_X_pow_sub_C_pow N _

/-- The unit exponent identity behind the Bézout coordinate at a branch point. -/
theorem eulerUnit_pow_bezout {S : Type*} [CommRing S] (u : Sˣ)
    (N m a b : ℕ) (hbezout : m * a = 1 + b * N) :
    (u ^ a) ^ m * (u⁻¹ ^ b) ^ N = u := by
  rw [← pow_mul, ← pow_mul, mul_comm a m, hbezout]
  group

/-- The Bézout coordinate satisfies the original Euler equation. -/
theorem eulerRoot_pow_bezout {S : Type*} [CommRing S] (u : Sˣ) (x z : S)
    (N m a b : ℕ) (hbezout : m * a = 1 + b * N)
    (hz : z ^ N = x * (u : S) ^ a) :
    (z ^ m * ((u⁻¹ ^ b : Sˣ) : S)) ^ N = x ^ m * (u : S) := by
  have hu : ((u : S) ^ a) ^ m * (((u⁻¹ ^ b : Sˣ) : S) ^ N) = (u : S) := by
    exact congrArg Units.val (eulerUnit_pow_bezout u N m a b hbezout)
  calc
    (z ^ m * ((u⁻¹ ^ b : Sˣ) : S)) ^ N =
        (z ^ N) ^ m * (((u⁻¹ ^ b : Sˣ) : S) ^ N) := by
          rw [mul_pow, ← pow_mul, mul_comm m N, pow_mul]
    _ = x ^ m * (((u : S) ^ a) ^ m * (((u⁻¹ ^ b : Sˣ) : S) ^ N)) := by
      rw [hz, mul_pow]
      ring
    _ = x ^ m * (u : S) := by rw [hu]

/-- After `x` is inverted, the Bézout coordinate recovers `z`. -/
theorem eulerUnit_recover_branch {S : Type*} [CommRing S] (x u z : Sˣ)
    (N m a b : ℕ) (hbezout : m * a = 1 + b * N)
    (hz : z ^ N = x * u ^ a) :
    (z ^ m * u⁻¹ ^ b) ^ a * x⁻¹ ^ b = z := by
  simp only [mul_pow, ← pow_mul, hbezout, pow_add, pow_one]
  rw [Nat.mul_comm b N, pow_mul, hz]
  rw [mul_pow]
  simp [← pow_mul, inv_pow, mul_comm, mul_assoc]

/-- The inverse Bézout coordinate recovers the original Euler root. -/
theorem eulerUnit_recover_original {S : Type*} [CommRing S] (x u y : Sˣ)
    (N m a b : ℕ) (hbezout : m * a = 1 + b * N)
    (hy : y ^ N = x ^ m * u) :
    (y ^ a * x⁻¹ ^ b) ^ m * u⁻¹ ^ b = y := by
  simp only [mul_pow, ← pow_mul, mul_comm a m, hbezout, pow_add, pow_one]
  rw [Nat.mul_comm b N, pow_mul, hy]
  rw [mul_pow]
  simp [← pow_mul, inv_pow, mul_comm, mul_assoc]

/-- The inverse Bézout coordinate satisfies the normalized branch equation
when the original Euler coordinate and `x` are units. -/
theorem eulerUnit_inverse_root {S : Type*} [CommRing S] (x u y : Sˣ)
    (N m a b : ℕ) (hbezout : m * a = 1 + b * N)
    (hy : y ^ N = x ^ m * u) :
    (y ^ a * x⁻¹ ^ b) ^ N = x * u ^ a := by
  calc
    (y ^ a * x⁻¹ ^ b) ^ N = (y ^ N) ^ a * (x⁻¹ ^ N) ^ b := by
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm a N, Nat.mul_comm b N]
    _ = (x ^ m * u) ^ a * (x⁻¹ ^ N) ^ b := by rw [hy]
    _ = x * u ^ a := by
      rw [mul_pow, ← pow_mul, hbezout, pow_add, pow_one]
      simp [← pow_mul, inv_pow, mul_comm, mul_assoc]

/-- The original singular Euler chart maps into the normalized zero chart by
`y ↦ z^m U^(-b)`, with the base `x` coordinate fixed. -/
def zeroSingularToBranch (N m a b : ℕ) (t : K)
    (hbezout : m * a = 1 + b * N) :
    ZeroSingularRing N m t →ₐ[ZeroBaseRing t] ZeroBranchRing N m a t := by
  let u : (ZeroBranchRing N m a t)ˣ :=
    Units.map (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t)).toMonoidHom
      (zeroBranchUnit N m t)
  let y : ZeroBranchRing N m a t := zeroBranchRoot N m a t ^ m * (u⁻¹ ^ b : _)
  have hu : (u : ZeroBranchRing N m a t) =
      algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t)
        (zeroBranchUnit N m t : ZeroBaseRing t) := rfl
  have hz : zeroBranchRoot N m a t ^ N =
      algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t) (zeroBaseX t) *
        (u : ZeroBranchRing N m a t) ^ a := by
    rw [hu, ← map_pow, ← map_mul]
    exact zeroBranchRoot_pow N m a t
  apply AdjoinRoot.liftAlgHom (zeroSingularPolynomial N m t)
    (Algebra.ofId (ZeroBaseRing t) _) y
  change aeval y (zeroSingularPolynomial N m t) = 0
  simp only [zeroSingularPolynomial, map_sub, map_pow, aeval_X, aeval_C]
  rw [sub_eq_zero]
  dsimp only [y]
  rw [map_mul, map_pow, ← hu]
  exact eulerRoot_pow_bezout u
      (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t) (zeroBaseX t))
      (zeroBranchRoot N m a t) N m a b hbezout hz

@[simp] theorem zeroSingularToBranch_root (N m a b : ℕ) (t : K)
    (hbezout : m * a = 1 + b * N) :
    zeroSingularToBranch N m a b t hbezout (zeroSingularRoot N m t) =
      zeroBranchRoot N m a t ^ m *
        algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t)
          (((zeroBranchUnit N m t)⁻¹ ^ b : (ZeroBaseRing t)ˣ) : ZeroBaseRing t) := by
  unfold zeroSingularToBranch zeroSingularRoot
  rw [AdjoinRoot.liftAlgHom_root]
  simp [map_pow]

/-- Localizing the zero-chart base at `x` gives the actual branch-complement base. -/
theorem zeroBaseOpen_isLocalization (t : K) :
    IsLocalization.Away (branchProduct t)
      (Localization.Away (zeroBaseX t)) := by
  have : IsLocalization.Away
      (algebraMap K[X] (ZeroBaseRing t) X)
      (Localization.Away (zeroBaseX t)) := by
    change IsLocalization.Away (zeroBaseX t) (Localization.Away (zeroBaseX t))
    infer_instance
  have h := IsLocalization.Away.mul' (ZeroBaseRing t)
    (Localization.Away (zeroBaseX t)) (zeroBranchProduct t) (X : K[X])
  have heq : zeroBranchProduct t * X = branchProduct t := by
    simp only [zeroBranchProduct, branchProduct]
    ring
  simpa only [heq] using h

/-- The actual branch-complement coordinate ring is the `x`-localization of
the zero-chart coordinate ring. -/
def zeroBaseOpenEquiv (t : K) :
    Localization.Away (zeroBaseX t) ≃ₐ[K[X]] BaseRing t := by
  haveI : IsLocalization.Away (branchProduct t)
      (Localization.Away (zeroBaseX t)) := zeroBaseOpen_isLocalization t
  exact IsLocalization.algEquiv (Submonoid.powers (branchProduct t)) _ _

/-- Restriction of functions from the zero chart to the branch complement. -/
def zeroBaseToCoverBase (t : K) : ZeroBaseRing t →+* BaseRing t :=
  (zeroBaseOpenEquiv t).toRingHom.comp
    (algebraMap (ZeroBaseRing t) (Localization.Away (zeroBaseX t)))

@[simp] theorem zeroBaseToCoverBase_polynomial (t : K) (p : K[X]) :
    zeroBaseToCoverBase t (algebraMap K[X] (ZeroBaseRing t) p) =
      algebraMap K[X] (BaseRing t) p := by
  change zeroBaseOpenEquiv t
    (algebraMap K[X] (Localization.Away (zeroBaseX t)) p) = _
  exact (zeroBaseOpenEquiv t).commutes p

@[simp] theorem zeroBaseToCoverBase_x (t : K) :
    zeroBaseToCoverBase t (zeroBaseX t) =
      algebraMap K[X] (BaseRing t) X :=
  zeroBaseToCoverBase_polynomial t X

@[simp] theorem zeroBaseToCoverBase_factor (N m : ℕ) (t : K) :
    zeroBaseToCoverBase t (zeroBranchFactor N m t) =
      algebraMap K[X] (BaseRing t)
        ((1 - X) ^ (N - m) * (1 - C t * X) ^ m) :=
  zeroBaseToCoverBase_polynomial t _

/-- The branch-complement base also inverts the original `x` coordinate. -/
theorem isUnit_coverBaseX (t : K) :
    IsUnit (algebraMap K[X] (BaseRing t) X) := by
  have h : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  exact h.1.1

/-- The invertible `x` coordinate on the branch-complement base. -/
def coverBaseXUnit (t : K) : (BaseRing t)ˣ := (isUnit_coverBaseX t).unit

@[simp] theorem coverBaseXUnit_val (t : K) :
    (coverBaseXUnit t : BaseRing t) = algebraMap K[X] (BaseRing t) X := by
  simp [coverBaseXUnit]

/-- The original radicand factors as `x^m U` after restriction to the overlap. -/
theorem radicand_eq_zeroFactor (N m : ℕ) (t : K) :
    radicand N m t =
      (algebraMap K[X] (BaseRing t) X) ^ m *
        zeroBaseToCoverBase t (zeroBranchUnit N m t : ZeroBaseRing t) := by
  simp only [zeroBranchUnit_val, zeroBaseToCoverBase_factor, radicand,
    branchPolynomial, map_mul, map_pow]
  ring

/-- The original covering coordinate is invertible on the branch complement. -/
theorem isUnit_coverRoot (N m : ℕ) (t : K) (hN : N ≠ 0) :
    IsUnit (coverRoot N m t) := by
  apply (isUnit_pow_iff hN).mp
  rw [coverRoot_pow]
  exact (isUnit_radicand N m t).map
    (algebraMap (BaseRing t) (CoverRing N m t))

/-- The original covering coordinate as a unit. -/
def coverRootUnit (N m : ℕ) (t : K) (hN : N ≠ 0) :
    (CoverRing N m t)ˣ := (isUnit_coverRoot N m t hN).unit

@[simp] theorem coverRootUnit_val (N m : ℕ) (t : K) (hN : N ≠ 0) :
    (coverRootUnit N m t hN : CoverRing N m t) = coverRoot N m t := by
  simp [coverRootUnit]

/-- Restriction of zero-chart base functions to the existing Euler cover. -/
def zeroBaseToCover (N m : ℕ) (t : K) :
    ZeroBaseRing t →+* CoverRing N m t :=
  (algebraMap (BaseRing t) (CoverRing N m t)).comp (zeroBaseToCoverBase t)

@[simp] theorem zeroBaseToCover_x (N m : ℕ) (t : K) :
    zeroBaseToCover N m t (zeroBaseX t) =
      algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) X) := by
  simp [zeroBaseToCover]

/-- The invertible `x` coordinate in the Euler cover. -/
def coverXUnit (N m : ℕ) (t : K) : (CoverRing N m t)ˣ :=
  Units.map (algebraMap (BaseRing t) (CoverRing N m t)).toMonoidHom
    (coverBaseXUnit t)

/-- The invertible factor `U` in the Euler cover. -/
def coverUUnit (N m : ℕ) (t : K) : (CoverRing N m t)ˣ :=
  Units.map (zeroBaseToCover N m t).toMonoidHom (zeroBranchUnit N m t)

@[simp] theorem coverXUnit_val (N m : ℕ) (t : K) :
    (coverXUnit N m t : CoverRing N m t) =
      algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) X) := by
  simp [coverXUnit]

@[simp] theorem coverUUnit_val (N m : ℕ) (t : K) :
    (coverUUnit N m t : CoverRing N m t) =
      zeroBaseToCover N m t (zeroBranchUnit N m t) := by
  rfl

/-- The Euler equation as an identity in units on the overlap. -/
theorem coverRootUnit_pow (N m : ℕ) (t : K) (hN : N ≠ 0) :
    coverRootUnit N m t hN ^ N =
      coverXUnit N m t ^ m * coverUUnit N m t := by
  apply Units.ext
  change (coverRootUnit N m t hN : CoverRing N m t) ^ N =
    (coverXUnit N m t : CoverRing N m t) ^ m *
      (coverUUnit N m t : CoverRing N m t)
  rw [coverRootUnit_val, coverRoot_pow, radicand_eq_zeroFactor, map_mul, map_pow]
  simp only [coverXUnit_val, coverUUnit_val]
  rfl

/-- The inverse Bézout coordinate `z=y^a/x^b` in the actual Euler algebra. -/
def inverseBranchCoordinate (N m a b : ℕ) (t : K) (hN : N ≠ 0) :
    CoverRing N m t :=
  ((coverRootUnit N m t hN ^ a * (coverXUnit N m t)⁻¹ ^ b :
      (CoverRing N m t)ˣ) : CoverRing N m t)

theorem inverseBranchCoordinate_pow (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    inverseBranchCoordinate N m a b t hN ^ N =
      zeroBaseToCover N m t
        (zeroBaseX t * (zeroBranchUnit N m t : ZeroBaseRing t) ^ a) := by
  have h := eulerUnit_inverse_root (coverXUnit N m t) (coverUUnit N m t)
    (coverRootUnit N m t hN) N m a b hbezout
    (coverRootUnit_pow N m t hN)
  have h' := congrArg (fun v : (CoverRing N m t)ˣ => (v : CoverRing N m t)) h
  change inverseBranchCoordinate N m a b t hN ^ N =
    (coverXUnit N m t : CoverRing N m t) *
      (coverUUnit N m t : CoverRing N m t) ^ a at h'
  rw [h', map_mul, map_pow]
  simp only [coverXUnit_val, coverUUnit_val, zeroBaseToCover_x]

/-- The normalized zero chart restricts to the existing branch-open Euler
cover by `z ↦ y^a/x^b`. -/
def zeroBranchToCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    ZeroBranchRing N m a t →+* CoverRing N m t :=
  AdjoinRoot.lift (zeroBaseToCover N m t)
    (inverseBranchCoordinate N m a b t hN) (by
      simp only [zeroBranchPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [sub_eq_zero]
      exact inverseBranchCoordinate_pow N m a b t hN hbezout)

@[simp] theorem zeroBranchToCover_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    zeroBranchToCover N m a b t hN hbezout (zeroBranchRoot N m a t) =
      inverseBranchCoordinate N m a b t hN := by
  simp [zeroBranchToCover, zeroBranchRoot]

/-- The zero-chart `x` coordinate inside its root algebra. -/
def zeroBranchX (N m a : ℕ) (t : K) : ZeroBranchRing N m a t :=
  algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t) (zeroBaseX t)

/-- The actual restriction of the normalized zero chart to `x ≠ 0`. -/
abbrev ZeroBranchOpen (N m a : ℕ) (t : K) :=
  Localization.Away (zeroBranchX N m a t)

/-- The invertible `x` coordinate in the normalized overlap. -/
def zeroBranchOpenXUnit (N m a : ℕ) (t : K) :
    (ZeroBranchOpen N m a t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (zeroBranchX N m a t)).unit

@[simp] theorem zeroBranchOpenXUnit_val (N m a : ℕ) (t : K) :
    (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t) =
      algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
        (zeroBranchX N m a t) := by
  simp [zeroBranchOpenXUnit]

/-- The factor `U` remains a unit in the normalized overlap. -/
def zeroBranchOpenUUnit (N m a : ℕ) (t : K) :
    (ZeroBranchOpen N m a t)ˣ :=
  Units.map
    ((algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)).comp
      (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t))).toMonoidHom
    (zeroBranchUnit N m t)

/-- The normalized coordinate is a unit on `x ≠ 0`. -/
theorem isUnit_zeroBranchOpenRoot (N m a : ℕ) (t : K) (hN : N ≠ 0) :
    IsUnit (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
      (zeroBranchRoot N m a t)) := by
  apply (isUnit_pow_iff hN).mp
  rw [← map_pow, zeroBranchRoot_pow]
  simp only [map_mul, map_pow]
  change IsUnit ((zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t) *
    (zeroBranchOpenUUnit N m a t : ZeroBranchOpen N m a t) ^ a)
  exact (zeroBranchOpenXUnit N m a t).isUnit.mul
    ((zeroBranchOpenUUnit N m a t).isUnit.pow a)

/-- The normalized coordinate as an actual unit on the overlap. -/
def zeroBranchOpenRootUnit (N m a : ℕ) (t : K) (hN : N ≠ 0) :
    (ZeroBranchOpen N m a t)ˣ :=
  (isUnit_zeroBranchOpenRoot N m a t hN).unit

@[simp] theorem zeroBranchOpenRootUnit_val (N m a : ℕ) (t : K) (hN : N ≠ 0) :
    (zeroBranchOpenRootUnit N m a t hN : ZeroBranchOpen N m a t) =
      algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
        (zeroBranchRoot N m a t) := by
  simp [zeroBranchOpenRootUnit]

/-- The normalized zero chart maps to the existing Euler cover, preserving `x`. -/
@[simp] theorem zeroBranchToCover_x (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    zeroBranchToCover N m a b t hN hbezout (zeroBranchX N m a t) =
      (coverXUnit N m t : CoverRing N m t) := by
  simp [zeroBranchToCover, zeroBranchX, zeroBaseToCover_x, coverXUnit_val,
    AdjoinRoot.lift_of]

/-- The actual restriction map from the localized normalized chart to the
existing branch-open Euler algebra. -/
def zeroBranchOpenToCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    ZeroBranchOpen N m a t →+* CoverRing N m t :=
  Localization.awayLift (zeroBranchToCover N m a b t hN hbezout)
    (zeroBranchX N m a t) (by
      rw [zeroBranchToCover_x]
      exact (coverXUnit N m t).isUnit)

/-- The polynomial base of the zero chart mapped into its overlap. -/
def polynomialToZeroBranchOpen (N m a : ℕ) (t : K) :
    K[X] →+* ZeroBranchOpen N m a t :=
  ((algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)).comp
    (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t))).comp
      (algebraMap K[X] (ZeroBaseRing t))

/-- The full branch product is invertible on the overlap. -/
theorem isUnit_branchProduct_zeroBranchOpen (N m a : ℕ) (t : K) :
    IsUnit (polynomialToZeroBranchOpen N m a t (branchProduct t)) := by
  have hU : IsUnit (algebraMap K[X] (ZeroBaseRing t) (zeroBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (zeroBranchProduct t)
  have hU' := (hU.map (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t))).map
    (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t))
  have hpoly : branchProduct t = X * zeroBranchProduct t := by
    simp only [branchProduct, zeroBranchProduct]
    ring
  rw [hpoly, map_mul]
  exact (zeroBranchOpenXUnit N m a t).isUnit.mul hU'

/-- The existing branch-complement base maps into the normalized overlap. -/
def coverBaseToZeroBranchOpen (N m a : ℕ) (t : K) :
    BaseRing t →+* ZeroBranchOpen N m a t :=
  Localization.awayLift (polynomialToZeroBranchOpen N m a t)
    (branchProduct t) (isUnit_branchProduct_zeroBranchOpen N m a t)

@[simp] theorem coverBaseToZeroBranchOpen_polynomial (N m a : ℕ) (t : K)
    (p : K[X]) :
    coverBaseToZeroBranchOpen N m a t (algebraMap K[X] (BaseRing t) p) =
      polynomialToZeroBranchOpen N m a t p :=
  by simp [coverBaseToZeroBranchOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The zero-chart base maps into the localized normalized chart. -/
def zeroBaseToBranchOpen (N m a : ℕ) (t : K) :
    ZeroBaseRing t →+* ZeroBranchOpen N m a t :=
  (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)).comp
    (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t))

@[simp] theorem coverBaseToZeroBranchOpen_zeroBase (N m a : ℕ) (t : K)
    (v : ZeroBaseRing t) :
    coverBaseToZeroBranchOpen N m a t (zeroBaseToCoverBase t v) =
      zeroBaseToBranchOpen N m a t v := by
  have h : (coverBaseToZeroBranchOpen N m a t).comp
      (zeroBaseToCoverBase t) = zeroBaseToBranchOpen N m a t := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (zeroBranchProduct t))
    apply RingHom.ext
    intro p
    change coverBaseToZeroBranchOpen N m a t
      (zeroBaseToCoverBase t (algebraMap K[X] (ZeroBaseRing t) p)) = _
    rw [zeroBaseToCoverBase_polynomial,
      coverBaseToZeroBranchOpen_polynomial]
    rfl
  exact congrArg (fun f : ZeroBaseRing t →+* ZeroBranchOpen N m a t => f v) h

@[simp] theorem coverBaseToZeroBranchOpen_radicand (N m a : ℕ) (t : K) :
    coverBaseToZeroBranchOpen N m a t (radicand N m t) =
      (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t) ^ m *
        (zeroBranchOpenUUnit N m a t : ZeroBranchOpen N m a t) := by
  rw [radicand_eq_zeroFactor, map_mul, map_pow,
    coverBaseToZeroBranchOpen_zeroBase]
  have hx : coverBaseToZeroBranchOpen N m a t
      (algebraMap K[X] (BaseRing t) X) =
        (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t) := by
    rw [← zeroBaseToCoverBase_x, coverBaseToZeroBranchOpen_zeroBase]
    rfl
  rw [hx]
  rfl

/-- The normalized equation, viewed in the unit group of the overlap. -/
theorem zeroBranchOpenRootUnit_pow (N m a : ℕ) (t : K) (hN : N ≠ 0) :
    zeroBranchOpenRootUnit N m a t hN ^ N =
      zeroBranchOpenXUnit N m a t * zeroBranchOpenUUnit N m a t ^ a := by
  apply Units.ext
  change (zeroBranchOpenRootUnit N m a t hN : ZeroBranchOpen N m a t) ^ N =
    (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t) *
      (zeroBranchOpenUUnit N m a t : ZeroBranchOpen N m a t) ^ a
  rw [zeroBranchOpenRootUnit_val, ← map_pow, zeroBranchRoot_pow, map_mul, map_pow]
  simp [zeroBranchOpenXUnit_val, zeroBranchOpenUUnit, zeroBranchX]

/-- The original Euler coordinate, as a unit on the zero-chart overlap. -/
def zeroBranchOpenYUnit (N m a b : ℕ) (t : K) (hN : N ≠ 0) :
    (ZeroBranchOpen N m a t)ˣ :=
  zeroBranchOpenRootUnit N m a t hN ^ m *
    (zeroBranchOpenUUnit N m a t)⁻¹ ^ b

/-- The original Euler equation holds for the reconstructed overlap coordinate. -/
theorem zeroBranchOpenYUnit_pow (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (zeroBranchOpenYUnit N m a b t hN : ZeroBranchOpen N m a t) ^ N =
      coverBaseToZeroBranchOpen N m a t (radicand N m t) := by
  rw [coverBaseToZeroBranchOpen_radicand]
  exact eulerRoot_pow_bezout (zeroBranchOpenUUnit N m a t)
    (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t)
    (zeroBranchOpenRootUnit N m a t hN : ZeroBranchOpen N m a t)
    N m a b hbezout
    (congrArg Units.val (zeroBranchOpenRootUnit_pow N m a t hN))

/-- The actual Euler cover maps to the localized normalized zero chart by
the original coordinate formula `y ↦ z^m/U^b`. -/
def coverToZeroBranchOpen (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    CoverRing N m t →+* ZeroBranchOpen N m a t :=
  AdjoinRoot.lift (coverBaseToZeroBranchOpen N m a t)
    (zeroBranchOpenYUnit N m a b t hN : ZeroBranchOpen N m a t) (by
      simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [sub_eq_zero]
      exact zeroBranchOpenYUnit_pow N m a b t hN hbezout)

@[simp] theorem coverToZeroBranchOpen_root (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    coverToZeroBranchOpen N m a b t hN hbezout (coverRoot N m t) =
      (zeroBranchOpenYUnit N m a b t hN : ZeroBranchOpen N m a t) := by
  simp [coverToZeroBranchOpen, coverRoot]

@[simp] theorem zeroBranchOpenToCover_zeroBase (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N)
    (v : ZeroBaseRing t) :
    zeroBranchOpenToCover N m a b t hN hbezout
        (zeroBaseToBranchOpen N m a t v) = zeroBaseToCover N m t v := by
  simp [zeroBranchOpenToCover, zeroBaseToBranchOpen, zeroBranchToCover,
    IsLocalization.Away.lift_eq, AdjoinRoot.lift_of]

@[simp] theorem coverToZeroBranchOpen_zeroBase (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N)
    (v : ZeroBaseRing t) :
    coverToZeroBranchOpen N m a b t hN hbezout (zeroBaseToCover N m t v) =
      zeroBaseToBranchOpen N m a t v := by
  change coverToZeroBranchOpen N m a b t hN hbezout
    (algebraMap (BaseRing t) (CoverRing N m t) (zeroBaseToCoverBase t v)) = _
  rw [show coverToZeroBranchOpen N m a b t hN hbezout
      (algebraMap (BaseRing t) (CoverRing N m t) (zeroBaseToCoverBase t v)) =
        coverBaseToZeroBranchOpen N m a t (zeroBaseToCoverBase t v) from by
          simp [coverToZeroBranchOpen, AdjoinRoot.lift_of]]
  exact coverBaseToZeroBranchOpen_zeroBase N m a t v

@[simp] theorem zeroBranchOpenToCover_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    zeroBranchOpenToCover N m a b t hN hbezout
      (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
        (zeroBranchRoot N m a t)) = inverseBranchCoordinate N m a b t hN := by
  simp [zeroBranchOpenToCover, IsLocalization.Away.lift_eq]

theorem zeroBranchOpenToCover_xUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    Units.map (zeroBranchOpenToCover N m a b t hN hbezout).toMonoidHom
      (zeroBranchOpenXUnit N m a t) = coverXUnit N m t := by
  apply Units.ext
  change zeroBranchOpenToCover N m a b t hN hbezout
    (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t) =
      (coverXUnit N m t : CoverRing N m t)
  rw [zeroBranchOpenXUnit_val]
  change zeroBranchOpenToCover N m a b t hN hbezout
    (zeroBaseToBranchOpen N m a t (zeroBaseX t)) = _
  rw [zeroBranchOpenToCover_zeroBase, zeroBaseToCover_x]
  rfl

theorem zeroBranchOpenToCover_uUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    Units.map (zeroBranchOpenToCover N m a b t hN hbezout).toMonoidHom
      (zeroBranchOpenUUnit N m a t) = coverUUnit N m t := by
  apply Units.ext
  change zeroBranchOpenToCover N m a b t hN hbezout
    (zeroBaseToBranchOpen N m a t (zeroBranchUnit N m t : ZeroBaseRing t)) =
      (coverUUnit N m t : CoverRing N m t)
  rw [zeroBranchOpenToCover_zeroBase]
  rfl

theorem zeroBranchOpenToCover_rootUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    Units.map (zeroBranchOpenToCover N m a b t hN hbezout).toMonoidHom
      (zeroBranchOpenRootUnit N m a t hN) =
        coverRootUnit N m t hN ^ a * (coverXUnit N m t)⁻¹ ^ b := by
  apply Units.ext
  change zeroBranchOpenToCover N m a b t hN hbezout
    (zeroBranchOpenRootUnit N m a t hN : ZeroBranchOpen N m a t) =
      inverseBranchCoordinate N m a b t hN
  rw [zeroBranchOpenRootUnit_val, zeroBranchOpenToCover_root]

theorem coverToZeroBranchOpen_xUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    Units.map (coverToZeroBranchOpen N m a b t hN hbezout).toMonoidHom
      (coverXUnit N m t) = zeroBranchOpenXUnit N m a t := by
  apply Units.ext
  change coverToZeroBranchOpen N m a b t hN hbezout
    (coverXUnit N m t : CoverRing N m t) =
      (zeroBranchOpenXUnit N m a t : ZeroBranchOpen N m a t)
  rw [coverXUnit_val, ← zeroBaseToCover_x,
    coverToZeroBranchOpen_zeroBase]
  rfl

theorem coverToZeroBranchOpen_uUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    Units.map (coverToZeroBranchOpen N m a b t hN hbezout).toMonoidHom
      (coverUUnit N m t) = zeroBranchOpenUUnit N m a t := by
  apply Units.ext
  change coverToZeroBranchOpen N m a b t hN hbezout
    (zeroBaseToCover N m t (zeroBranchUnit N m t : ZeroBaseRing t)) =
      (zeroBranchOpenUUnit N m a t : ZeroBranchOpen N m a t)
  rw [coverToZeroBranchOpen_zeroBase]
  rfl

theorem coverToZeroBranchOpen_rootUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    Units.map (coverToZeroBranchOpen N m a b t hN hbezout).toMonoidHom
      (coverRootUnit N m t hN) = zeroBranchOpenYUnit N m a b t hN := by
  apply Units.ext
  change coverToZeroBranchOpen N m a b t hN hbezout
    (coverRootUnit N m t hN : CoverRing N m t) =
      (zeroBranchOpenYUnit N m a b t hN : ZeroBranchOpen N m a t)
  rw [coverRootUnit_val, coverToZeroBranchOpen_root]

@[simp] theorem zeroBranchOpenToCover_coverBase (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N)
    (v : BaseRing t) :
    zeroBranchOpenToCover N m a b t hN hbezout
        (coverBaseToZeroBranchOpen N m a t v) =
      algebraMap (BaseRing t) (CoverRing N m t) v := by
  have h : (zeroBranchOpenToCover N m a b t hN hbezout).comp
      (coverBaseToZeroBranchOpen N m a t) =
        algebraMap (BaseRing t) (CoverRing N m t) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
    apply RingHom.ext
    intro p
    change zeroBranchOpenToCover N m a b t hN hbezout
      (coverBaseToZeroBranchOpen N m a t (algebraMap K[X] (BaseRing t) p)) = _
    rw [coverBaseToZeroBranchOpen_polynomial]
    change zeroBranchOpenToCover N m a b t hN hbezout
      (zeroBaseToBranchOpen N m a t
        (algebraMap K[X] (ZeroBaseRing t) p)) = _
    rw [zeroBranchOpenToCover_zeroBase]
    simp [zeroBaseToCover, zeroBaseToCoverBase_polynomial]
  exact congrArg (fun f : BaseRing t →+* CoverRing N m t => f v) h

@[simp] theorem zeroBranchOpenToCover_coverRoot (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    zeroBranchOpenToCover N m a b t hN hbezout
        (coverToZeroBranchOpen N m a b t hN hbezout (coverRoot N m t)) =
      coverRoot N m t := by
  rw [coverToZeroBranchOpen_root]
  let f := zeroBranchOpenToCover N m a b t hN hbezout
  have h : Units.map f.toMonoidHom (zeroBranchOpenYUnit N m a b t hN) =
      coverRootUnit N m t hN := by
    simp only [zeroBranchOpenYUnit, map_mul, map_pow, map_inv]
    rw [zeroBranchOpenToCover_rootUnit, zeroBranchOpenToCover_uUnit]
    exact eulerUnit_recover_original (coverXUnit N m t) (coverUUnit N m t)
      (coverRootUnit N m t hN) N m a b hbezout (coverRootUnit_pow N m t hN)
  exact (congrArg Units.val h).trans (coverRootUnit_val N m t hN)

/-- The overlap maps compose to the identity on the original Euler algebra. -/
theorem zeroBranchOpenToCover_coverToZeroBranchOpen (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    (zeroBranchOpenToCover N m a b t hN hbezout).comp
      (coverToZeroBranchOpen N m a b t hN hbezout) =
        RingHom.id (CoverRing N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change zeroBranchOpenToCover N m a b t hN hbezout
      (coverToZeroBranchOpen N m a b t hN hbezout
        (algebraMap (BaseRing t) (CoverRing N m t) v)) = _
    simp [coverToZeroBranchOpen, AdjoinRoot.lift_of]
  · change zeroBranchOpenToCover N m a b t hN hbezout
      (coverToZeroBranchOpen N m a b t hN hbezout (coverRoot N m t)) = _
    exact zeroBranchOpenToCover_coverRoot N m a b t hN hbezout

@[simp] theorem coverToZeroBranchOpen_zeroBranchRoot (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    coverToZeroBranchOpen N m a b t hN hbezout
      (zeroBranchOpenToCover N m a b t hN hbezout
        (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
          (zeroBranchRoot N m a t))) =
      algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
        (zeroBranchRoot N m a t) := by
  rw [zeroBranchOpenToCover_root]
  let g := coverToZeroBranchOpen N m a b t hN hbezout
  have h : Units.map g.toMonoidHom
      (coverRootUnit N m t hN ^ a * (coverXUnit N m t)⁻¹ ^ b) =
        zeroBranchOpenRootUnit N m a t hN := by
    simp only [map_mul, map_pow, map_inv]
    rw [coverToZeroBranchOpen_rootUnit, coverToZeroBranchOpen_xUnit]
    exact eulerUnit_recover_branch (zeroBranchOpenXUnit N m a t)
      (zeroBranchOpenUUnit N m a t) (zeroBranchOpenRootUnit N m a t hN)
      N m a b hbezout (zeroBranchOpenRootUnit_pow N m a t hN)
  change g (((coverRootUnit N m t hN ^ a * (coverXUnit N m t)⁻¹ ^ b :
      (CoverRing N m t)ˣ) : CoverRing N m t)) =
        (zeroBranchOpenRootUnit N m a t hN : ZeroBranchOpen N m a t)
  exact congrArg Units.val h

/-- The overlap maps also compose to the identity on the localized zero chart. -/
theorem coverToZeroBranchOpen_zeroBranchOpenToCover (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : m * a = 1 + b * N) :
    (coverToZeroBranchOpen N m a b t hN hbezout).comp
      (zeroBranchOpenToCover N m a b t hN hbezout) =
        RingHom.id (ZeroBranchOpen N m a t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (zeroBranchX N m a t))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change coverToZeroBranchOpen N m a b t hN hbezout
      (zeroBranchOpenToCover N m a b t hN hbezout
        (zeroBaseToBranchOpen N m a t v)) = _
    rw [zeroBranchOpenToCover_zeroBase, coverToZeroBranchOpen_zeroBase]
    rfl
  · change coverToZeroBranchOpen N m a b t hN hbezout
      (zeroBranchOpenToCover N m a b t hN hbezout
        (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)
          (zeroBranchRoot N m a t))) = _
    exact coverToZeroBranchOpen_zeroBranchRoot N m a b t hN hbezout

/-- The normalized zero chart restricted to `x ≠ 0` is the existing Euler
cover, with both actual algebra maps as inverses. -/
def zeroBranchOpenEquivCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    ZeroBranchOpen N m a t ≃+* CoverRing N m t where
  toFun := zeroBranchOpenToCover N m a b t hN hbezout
  invFun := coverToZeroBranchOpen N m a b t hN hbezout
  left_inv v := by
    have h := congrArg (fun f : ZeroBranchOpen N m a t →+* ZeroBranchOpen N m a t => f v)
      (coverToZeroBranchOpen_zeroBranchOpenToCover N m a b t hN hbezout)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg (fun f : CoverRing N m t →+* CoverRing N m t => f v)
      (zeroBranchOpenToCover_coverToZeroBranchOpen N m a b t hN hbezout)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (zeroBranchOpenToCover N m a b t hN hbezout)
  map_add' := map_add (zeroBranchOpenToCover N m a b t hN hbezout)

/-- The overlap equivalence respects the coefficient ring as well as the
branch coordinates. -/
def zeroBranchOpenAlgEquivCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    ZeroBranchOpen N m a t ≃ₐ[K] CoverRing N m t :=
  AlgEquiv.ofRingEquiv (f := zeroBranchOpenEquivCover N m a b t hN hbezout) (by
    intro c
    change zeroBranchOpenToCover N m a b t hN hbezout
      (zeroBaseToBranchOpen N m a t (algebraMap K (ZeroBaseRing t) c)) = _
    rw [zeroBranchOpenToCover_zeroBase]
    change algebraMap (BaseRing t) (CoverRing N m t)
      (zeroBaseToCoverBase t (algebraMap K (ZeroBaseRing t) c)) = _
    have hc : zeroBaseToCoverBase t (algebraMap K (ZeroBaseRing t) c) =
        algebraMap K (BaseRing t) c := by
      convert zeroBaseToCoverBase_polynomial t (C c)
    rw [hc]
    exact (IsScalarTower.algebraMap_apply K (BaseRing t) (CoverRing N m t) c))

/-- The overlap `x ≠ 0` of the normalized zero chart is smooth over the
coefficient ring. -/
theorem zeroBranchOpen_smooth (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hn : IsUnit (N : K)) (hbezout : m * a = 1 + b * N) :
    Algebra.Smooth K (ZeroBranchOpen N m a t) := by
  have : Algebra.Smooth K (CoverRing N m t) := coverRing_smooth N m t hN hn
  exact Algebra.Smooth.of_equiv
    (zeroBranchOpenAlgEquivCover N m a b t hN hbezout).symm

/-- The base of the zero chart is smooth over the coefficient ring. -/
theorem zeroBaseRing_smooth (t : K) : Algebra.Smooth K (ZeroBaseRing t) := by
  have : Algebra.Smooth K K[X] := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth K[X] (ZeroBaseRing t) :=
    Algebra.Smooth.of_isLocalization_Away (zeroBranchProduct t)
  exact Algebra.Smooth.comp K K[X] (ZeroBaseRing t)

/-- The polynomial unit factor before localization at the nonzero branch sections. -/
def zeroBranchUnitPolynomial (N m : ℕ) (t : K) : K[X] :=
  (1 - X) ^ (N - m) * (1 - C t * X) ^ m

/-- The radicand viewed as a polynomial in the retained `x` coordinate. -/
def zeroBranchRadicandPolynomial (N m a : ℕ) (t : K) : K[X] :=
  X * zeroBranchUnitPolynomial N m t ^ a

/-- The polynomial radicand is the displayed zero-branch radicand after
localization. -/
theorem zeroBranchRadicandPolynomial_map (N m a : ℕ) (t : K) :
    algebraMap K[X] (ZeroBaseRing t) (zeroBranchRadicandPolynomial N m a t) =
      zeroBaseX t * (zeroBranchUnit N m t : ZeroBaseRing t) ^ a := by
  simp [zeroBranchRadicandPolynomial, zeroBranchUnitPolynomial,
    zeroBranchUnit_val, zeroBranchFactor, zeroBaseX, map_mul, map_pow]

/-- The root algebra equation is precisely the localized polynomial
`z^N-P(x)` required by the Kummer hypersurface criterion. -/
theorem zeroBranchPolynomial_eq_kummer (N m a : ℕ) (t : K) :
    zeroBranchPolynomial N m a t =
      X ^ N - C (algebraMap K[X] (ZeroBaseRing t)
        (zeroBranchRadicandPolynomial N m a t)) := by
  rw [zeroBranchRadicandPolynomial_map]
  rfl

/-- The derivative of the radicand with respect to `x` has unit constant part. -/
theorem zeroBranchRadicandPolynomial_derivative (N m a : ℕ) (t : K) :
    (zeroBranchRadicandPolynomial N m a t).derivative =
      zeroBranchUnitPolynomial N m t ^ a +
        X * (zeroBranchUnitPolynomial N m t ^ a).derivative := by
  simp [zeroBranchRadicandPolynomial, derivative_mul]

/-- The two partial derivatives of `z^N-xU^a` generate the unit ideal whenever
`U^a` and `N` are units. This is the algebraic Jacobian identity used at the
zero branch. -/
theorem euler_jacobian_bezout {S : Type*} [CommRing S] (u n : Sˣ)
    (x z v : S) (N : ℕ) (hN : 0 < N) (hz : z ^ N = x * (u : S)) :
    (u⁻¹ : Sˣ) * ((u : S) + x * v) -
      ((u⁻¹ : Sˣ) ^ 2 : S) * v * z * (n⁻¹ : Sˣ) *
        ((n : S) * z ^ (N - 1)) = 1 := by
  let α : S := (u⁻¹ : Sˣ)
  let β : S := (n⁻¹ : Sˣ)
  let U : S := u
  let M : S := n
  have hu : α * U = 1 := by simp [α, U]
  have hn : β * M = 1 := by simp [β, M]
  have hpow : z * z ^ (N - 1) = z ^ N := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right, pow_succ]
    ring
  change α * (U + x * v) - α ^ 2 * v * z * β * (M * z ^ (N - 1)) = 1
  calc
    α * (U + x * v) - α ^ 2 * v * z * β * (M * z ^ (N - 1)) =
        α * U + α * x * v - α ^ 2 * v * (z * z ^ (N - 1)) * (β * M) := by ring
    _ = α * U + α * x * v - α ^ 2 * v * z ^ N := by rw [hpow, hn]; ring
    _ = α * U + α * x * v * (1 - α * U) := by rw [hz]; ring
    _ = 1 := by rw [hu]; ring

/-- The actual derivative in the retained `x` coordinate of the normalized
zero-branch equation (up to its harmless sign). -/
def zeroBranchXDerivative (N m a : ℕ) (t : K) : ZeroBranchRing N m a t :=
  (algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t)).comp
    (algebraMap K[X] (ZeroBaseRing t))
      ((zeroBranchRadicandPolynomial N m a t).derivative)

/-- The retained-coordinate derivative is evaluation of the polynomial
derivative at the actual chart coordinate. -/
theorem zeroBranchXDerivative_eq_aeval (N m a : ℕ) (t : K) :
    zeroBranchXDerivative N m a t =
      aeval (zeroBranchX N m a t)
        (zeroBranchRadicandPolynomial N m a t).derivative := by
  let f : K[X] →ₐ[K] ZeroBaseRing t :=
    IsScalarTower.toAlgHom K K[X] (ZeroBaseRing t)
  let h : ZeroBaseRing t →ₐ[K] ZeroBranchRing N m a t :=
    IsScalarTower.toAlgHom K (ZeroBaseRing t) (ZeroBranchRing N m a t)
  have hf (p : K[X]) : aeval (zeroBaseX t) p = f p := by
    change aeval (f X) p = f p
    rw [Polynomial.aeval_def]
    exact Polynomial.eval₂_algebraMap_X p f
  calc
    zeroBranchXDerivative N m a t =
        h (aeval (zeroBaseX t)
          (zeroBranchRadicandPolynomial N m a t).derivative) := by
      change h (f (zeroBranchRadicandPolynomial N m a t).derivative) = _
      rw [hf]
    _ = aeval (h (zeroBaseX t))
          (zeroBranchRadicandPolynomial N m a t).derivative :=
        (Polynomial.aeval_algHom_apply h _ _).symm
    _ = aeval (zeroBranchX N m a t)
          (zeroBranchRadicandPolynomial N m a t).derivative := rfl

/-- The actual derivative in the root coordinate of the normalized equation. -/
def zeroBranchZDerivative (N m a : ℕ) (t : K) : ZeroBranchRing N m a t :=
  (N : ZeroBranchRing N m a t) * zeroBranchRoot N m a t ^ (N - 1)

/-- The two actual partial derivatives of the normalized zero-branch equation
generate the unit ideal. -/
theorem zeroBranch_jacobian_bezout (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    ∃ p q : ZeroBranchRing N m a t,
      p * zeroBranchXDerivative N m a t +
        q * zeroBranchZDerivative N m a t = 1 := by
  let S := ZeroBranchRing N m a t
  let x : S := zeroBranchX N m a t
  let z : S := zeroBranchRoot N m a t
  let u : Sˣ := (Units.map (algebraMap (ZeroBaseRing t) S).toMonoidHom
    (zeroBranchUnit N m t)) ^ a
  let n : Sˣ := Units.map (algebraMap K S).toMonoidHom hn.unit
  let v : S := (algebraMap (ZeroBaseRing t) S).comp
    (algebraMap K[X] (ZeroBaseRing t))
      ((zeroBranchUnitPolynomial N m t ^ a).derivative)
  have hu : (u : S) =
      algebraMap (ZeroBaseRing t) S ((zeroBranchUnit N m t : ZeroBaseRing t) ^ a) := by
    simp [u]
  have hn' : (n : S) = (N : S) := by
    calc
      (n : S) = (algebraMap K S) (hn.unit : K) := by simp [n]
      _ = (algebraMap K S) (N : K) := congrArg (algebraMap K S) hn.unit_spec
      _ = (N : S) := by simp
  have hmap (w : ZeroBaseRing t) :
      (algebraMap (ZeroBaseRing t) S) w =
        AdjoinRoot.of (zeroBranchPolynomial N m a t) w := by
    change (algebraMap (ZeroBaseRing t) (AdjoinRoot (zeroBranchPolynomial N m a t))) w = _
    rw [AdjoinRoot.algebraMap_eq]
  have hz : z ^ N = x * (u : S) := by
    rw [zeroBranchRoot_pow]
    simp [x, hu, zeroBranchX, map_mul, hmap]
  have hd : zeroBranchXDerivative N m a t = (u : S) + x * v := by
    simp [zeroBranchXDerivative, zeroBranchRadicandPolynomial_derivative,
      zeroBranchUnitPolynomial, zeroBranchFactor, zeroBranchUnit_val,
      x, v, hu, zeroBranchX, zeroBaseX, map_add, map_mul, map_pow,
      hmap]
  have h := euler_jacobian_bezout u n x z v N hN hz
  refine ⟨(u⁻¹ : Sˣ),
    -((u⁻¹ : Sˣ) ^ 2 : S) * v * z * (n⁻¹ : Sˣ), ?_⟩
  rw [← hd, hn'] at h
  simpa only [zeroBranchZDerivative, z, sub_eq_add_neg, neg_mul, mul_assoc] using h

/-- The normalized zero-branch chart is smooth over the coefficient ring.
The Jacobian identity uses both the retained `x` and root `z` coordinates, so
smoothness includes the ramification point `x = z = 0`. -/
theorem zeroBranchRing_smooth (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Algebra.Smooth K (ZeroBranchRing N m a t) := by
  let J : (ZeroBaseRing t)[X] → Prop := fun f =>
    ∃ p q : AdjoinRoot f,
      p * aeval (AdjoinRoot.of f (zeroBaseX t))
          (zeroBranchRadicandPolynomial N m a t).derivative +
        q * (N : AdjoinRoot f) * (AdjoinRoot.root f) ^ (N - 1) = 1
  have hzero : J (zeroBranchPolynomial N m a t) := by
    dsimp only [J]
    simpa only [zeroBranchXDerivative_eq_aeval, zeroBranchZDerivative,
      zeroBranchX, zeroBranchRoot, AdjoinRoot.algebraMap_eq, mul_assoc] using
      (zeroBranch_jacobian_bezout N m a t hN hn)
  have hkummer : J (RingTheory.Smooth.localizedKummerEquation
      (zeroBranchProduct t) (zeroBranchRadicandPolynomial N m a t) N) :=
    by simpa only [RingTheory.Smooth.localizedKummerEquation,
      zeroBranchPolynomial_eq_kummer] using hzero
  dsimp only [J] at hkummer
  obtain ⟨p, q, hjac⟩ := hkummer
  have h : Algebra.Smooth K
      (RingTheory.Smooth.localizedKummerAlgebra
        (zeroBranchProduct t) (zeroBranchRadicandPolynomial N m a t) N) := by
    exact RingTheory.Smooth.smooth_localizedKummer
      (zeroBranchProduct t) (zeroBranchRadicandPolynomial N m a t) N hN p q hjac
  change Algebra.Smooth K (AdjoinRoot (zeroBranchPolynomial N m a t))
  rw [zeroBranchPolynomial_eq_kummer]
  exact h

/-- The actual affine scheme of the normalized zero-branch root algebra. -/
@[expose] def zeroBranchScheme (N m a : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (ZeroBranchRing N m a t))

/-- The structural morphism of the normalized zero-branch chart. -/
def zeroBranchStructureMap (N m a : ℕ) (t : K) :
    zeroBranchScheme N m a t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ZeroBranchRing N m a t)))

/-- The actual structural map of the normalized zero-branch chart is smooth. -/
theorem zeroBranchStructureMap_smooth (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Smooth (zeroBranchStructureMap N m a t) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  exact RingHom.smooth_algebraMap.mpr (zeroBranchRing_smooth N m a t hN hn)

/-- The original singular equation on the same zero-chart base, as a scheme. -/
def zeroSingularScheme (N m : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (ZeroSingularRing N m t))

/-- The coefficient-ring structural morphism of the original singular chart. -/
def zeroSingularStructureMap (N m : ℕ) (t : K) :
    zeroSingularScheme N m t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ZeroSingularRing N m t)))

/-- The normalization coordinate gives an actual morphism from the zero branch
to the original singular affine chart. -/
def zeroBranchToSingularScheme (N m a b : ℕ) (t : K)
    (hbezout : m * a = 1 + b * N) :
    zeroBranchScheme N m a t ⟶ zeroSingularScheme N m t :=
  Spec.map (CommRingCat.ofHom
    (zeroSingularToBranch N m a b t hbezout).toRingHom)

/-- The singular-to-normalized algebra map preserves the coefficient ring. -/
theorem zeroBranchToSingularScheme_structureMap (N m a b : ℕ) (t : K)
    (hbezout : m * a = 1 + b * N) :
    zeroBranchToSingularScheme N m a b t hbezout ≫
      zeroSingularStructureMap N m t = zeroBranchStructureMap N m a t := by
  unfold zeroBranchToSingularScheme zeroSingularStructureMap zeroBranchStructureMap
  erw [← Spec.map_comp]
  congr 1
  ext c
  change zeroSingularToBranch N m a b t hbezout
      (algebraMap K (ZeroSingularRing N m t) c) =
    algebraMap K (ZeroBranchRing N m a t) c
  rw [IsScalarTower.algebraMap_apply K (ZeroBaseRing t)
        (ZeroSingularRing N m t) c,
      IsScalarTower.algebraMap_apply K (ZeroBaseRing t)
        (ZeroBranchRing N m a t) c]
  exact (zeroSingularToBranch N m a b t hbezout).commutes
    (algebraMap K (ZeroBaseRing t) c)

/-- The open overlap of the normalized zero branch, as an actual affine scheme. -/
@[expose] def zeroBranchOpenScheme (N m a : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (ZeroBranchOpen N m a t))

/-- The open overlap maps to the normalized chart through its localization. -/
def zeroBranchOpenInclusion (N m a : ℕ) (t : K) :
    zeroBranchOpenScheme N m a t ⟶ zeroBranchScheme N m a t :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ZeroBranchRing N m a t) (ZeroBranchOpen N m a t)))

/-- The overlap is the principal open `D(x)` in the normalized zero chart. -/
instance zeroBranchOpenInclusion_isOpenImmersion (N m a : ℕ) (t : K) :
    IsOpenImmersion (zeroBranchOpenInclusion N m a t) :=
  IsOpenImmersion.of_isLocalization (zeroBranchX N m a t)

/-- The image of the overlap is exactly the locus where `x` is invertible. -/
theorem zeroBranchOpenInclusion_opensRange (N m a : ℕ) (t : K) :
    (zeroBranchOpenInclusion N m a t).opensRange =
      PrimeSpectrum.basicOpen (zeroBranchX N m a t) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (ZeroBranchOpen N m a t)
    (zeroBranchX N m a t)

/-- The coefficient-ring structural morphism of the overlap. -/
def zeroBranchOpenStructureMap (N m a : ℕ) (t : K) :
    zeroBranchOpenScheme N m a t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ZeroBranchOpen N m a t)))

/-- Restricting the normalized chart to the overlap preserves its projection
to the coefficient ring. -/
theorem zeroBranchOpenInclusion_structureMap (N m a : ℕ) (t : K) :
    zeroBranchOpenInclusion N m a t ≫ zeroBranchStructureMap N m a t =
      zeroBranchOpenStructureMap N m a t := by
  unfold zeroBranchOpenInclusion zeroBranchStructureMap zeroBranchOpenStructureMap
  erw [← Spec.map_comp]
  congr 1

/-- The overlap equivalence induces the scheme isomorphism with the existing
branch-complement Euler cover. -/
def zeroBranchOpenIsoCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    zeroBranchOpenScheme N m a t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso
    (zeroBranchOpenEquivCover N m a b t hN hbezout).symm.toCommRingCatIso.op

/-- The forward overlap isomorphism is induced by `y ↦ z^m/U^b`. -/
theorem zeroBranchOpenIsoCover_hom (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (zeroBranchOpenIsoCover N m a b t hN hbezout).hom =
      Spec.map (CommRingCat.ofHom (coverToZeroBranchOpen N m a b t hN hbezout)) := (rfl)

/-- The inverse overlap isomorphism is induced by `z ↦ y^a/x^b`. -/
theorem zeroBranchOpenIsoCover_inv (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (zeroBranchOpenIsoCover N m a b t hN hbezout).inv =
      Spec.map (CommRingCat.ofHom (zeroBranchOpenToCover N m a b t hN hbezout)) := (rfl)

/-- The overlap isomorphism preserves the projection to the coefficient
ring. -/
theorem zeroBranchOpenIsoCover_structureMap (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (zeroBranchOpenIsoCover N m a b t hN hbezout).hom ≫ structureMap N m t =
      zeroBranchOpenStructureMap N m a t := by
  rw [zeroBranchOpenIsoCover_hom]
  change Spec.map (CommRingCat.ofHom
    (coverToZeroBranchOpen N m a b t hN hbezout)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (CoverRing N m t))) = _
  erw [← Spec.map_comp]
  congr 1
  ext c
  change coverToZeroBranchOpen N m a b t hN hbezout
    (algebraMap K (CoverRing N m t) c) =
      algebraMap K (ZeroBranchOpen N m a t) c
  exact (zeroBranchOpenAlgEquivCover N m a b t hN hbezout).symm.commutes c

/-- The actual overlap scheme is smooth over the coefficient ring. -/
theorem zeroBranchOpenScheme_smooth (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hn : IsUnit (N : K))
    (hbezout : m * a = 1 + b * N) :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap K (ZeroBranchOpen N m a t)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  exact RingHom.smooth_algebraMap.mpr
    (zeroBranchOpen_smooth N m a b t hN hn hbezout)

/-- Coefficient roots of unity scale the normalized zero-branch coordinate.
The exponent `m` appears when this action is expressed on the original
covering coordinate. -/
def zeroBranchDeckAlgebraAction (N m a : ℕ) [NeZero N] (t : K) :
    rootsOfUnity N K →* (ZeroBranchRing N m a t ≃ₐ[ZeroBaseRing t]
      ZeroBranchRing N m a t) :=
  (AdjoinRoot.rootScaling N
    (zeroBaseX t * (zeroBranchUnit N m t : ZeroBaseRing t) ^ a)).comp
      (rootsOfUnity.mapHom N
        ((algebraMap K[X] (ZeroBaseRing t)).comp Polynomial.C))

/-- The normalized deck action fixes the base and scales `z` once. -/
theorem zeroBranchDeckAlgebraAction_root (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    zeroBranchDeckAlgebraAction N m a t ζ (zeroBranchRoot N m a t) =
      (algebraMap K[X] (ZeroBaseRing t) (C ((ζ : Kˣ) : K))) •
        zeroBranchRoot N m a t := by
  exact AdjoinRoot.rootScaling_root N
    (zeroBaseX t * (zeroBranchUnit N m t : ZeroBaseRing t) ^ a)
    (rootsOfUnity.mapHom N
      ((algebraMap K[X] (ZeroBaseRing t)).comp Polynomial.C) ζ)

/-- The deck automorphism of the actual normalized zero-branch scheme. -/
def zeroBranchDeckTransformation (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    zeroBranchScheme N m a t ≅ zeroBranchScheme N m a t :=
  Scheme.Spec.mapIso
    (zeroBranchDeckAlgebraAction N m a t ζ).toRingEquiv.toCommRingCatIso.op

/-- The normalized deck transformation preserves the coefficient-ring map. -/
theorem zeroBranchDeckTransformation_structureMap (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    (zeroBranchDeckTransformation N m a t ζ).hom ≫
      zeroBranchStructureMap N m a t = zeroBranchStructureMap N m a t := by
  unfold zeroBranchDeckTransformation zeroBranchStructureMap
  erw [← Spec.map_comp]
  congr 1
  ext c
  change zeroBranchDeckAlgebraAction N m a t ζ
      (algebraMap K (ZeroBranchRing N m a t) c) =
    algebraMap K (ZeroBranchRing N m a t) c
  rw [IsScalarTower.algebraMap_apply K (ZeroBaseRing t)
        (ZeroBranchRing N m a t) c]
  exact (zeroBranchDeckAlgebraAction N m a t ζ).commutes
    (algebraMap K (ZeroBaseRing t) c)

/-- On the original Euler coordinate, the normalized deck action has weight
`m`, as required by the branch exponent in Definition 2.3 of
[TripathiGoswamiRevised]. -/
theorem zeroBranchDeckAlgebraAction_singularRoot (N m a b : ℕ) [NeZero N]
    (t : K) (hbezout : m * a = 1 + b * N) (ζ : rootsOfUnity N K) :
    zeroBranchDeckAlgebraAction N m a t ζ
        (zeroSingularToBranch N m a b t hbezout (zeroSingularRoot N m t)) =
      (((ζ : Kˣ) : K) ^ m) •
        zeroSingularToBranch N m a b t hbezout (zeroSingularRoot N m t) := by
  let d := zeroBranchDeckAlgebraAction N m a t ζ
  let u : ZeroBaseRing t := ((zeroBranchUnit N m t)⁻¹ ^ b : (ZeroBaseRing t)ˣ)
  let c : K := ((ζ : Kˣ) : K)
  have hc : algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t)
      (algebraMap K[X] (ZeroBaseRing t) (C c)) =
      algebraMap K (ZeroBranchRing N m a t) c := by
    rw [IsScalarTower.algebraMap_apply K (ZeroBaseRing t)
      (ZeroBranchRing N m a t) c]
    rfl
  rw [zeroSingularToBranch_root, map_mul, map_pow, d.commutes,
    zeroBranchDeckAlgebraAction_root]
  simp only [Algebra.smul_def]
  rw [hc, mul_pow]
  change (algebraMap K (ZeroBranchRing N m a t) c) ^ m *
      zeroBranchRoot N m a t ^ m *
        algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t) u =
    (algebraMap K (ZeroBranchRing N m a t) (c ^ m)) *
      (zeroBranchRoot N m a t ^ m *
        algebraMap (ZeroBaseRing t) (ZeroBranchRing N m a t) u)
  rw [map_pow]
  ring

end HilbertModularity.Hypergeometric.EulerCover
