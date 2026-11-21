/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.TameBranch
public import HilbertModularity.Hypergeometric.EulerCover.DeckTransformations
import Mathlib.Tactic.Group

/-! # The branch of the Euler cover at infinity

With `u = 1/x` and `v = y*u^2`, the equation of the Euler cover becomes
`v^N = u^(N-m) * (u-1)^(N-m) * (u-t)^m`.  The normalized chart uses a
Bézout coordinate `z` satisfying `z^N = u*P^a`.  The factor `u^2` retains
the original covering coordinate and its deck character from
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [CommRing K]

/-- The two finite branch factors in the inverse coordinate `u = 1/x`. -/
def infinityBranchProduct (t : K) : K[X] := (X - 1) * (X - C t)

/-- The base of the infinity chart, where `u-1` and `u-t` are invertible. -/
abbrev InfinityBaseRing (t : K) := Localization.Away (infinityBranchProduct t)

/-- The inverse projection coordinate on the infinity chart. -/
def infinityBaseU (t : K) : InfinityBaseRing t :=
  algebraMap K[X] (InfinityBaseRing t) X

/-- The unit factor in the infinity equation. -/
def infinityBranchFactor (N m : ℕ) (t : K) : InfinityBaseRing t :=
  algebraMap K[X] (InfinityBaseRing t)
    ((X - 1) ^ (N - m) * (X - C t) ^ m)

theorem isUnit_infinityBranchFactor (N m : ℕ) (t : K) :
    IsUnit (infinityBranchFactor N m t) := by
  have h : IsUnit
      (algebraMap K[X] (InfinityBaseRing t) (infinityBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (infinityBranchProduct t)
  simp only [infinityBranchProduct, map_mul, IsUnit.mul_iff] at h
  simpa only [infinityBranchFactor, map_mul, map_pow] using
    (h.1.pow (N - m)).mul (h.2.pow m)

/-- The actual unit `P = (u-1)^(N-m)(u-t)^m` on the infinity base. -/
def infinityBranchUnit (N m : ℕ) (t : K) : (InfinityBaseRing t)ˣ :=
  (isUnit_infinityBranchFactor N m t).unit

@[simp] theorem infinityBranchUnit_val (N m : ℕ) (t : K) :
    (infinityBranchUnit N m t : InfinityBaseRing t) =
      infinityBranchFactor N m t := by
  simp [infinityBranchUnit]

/-- The normalized infinity-branch equation `z^N = u P^a`. -/
def infinityBranchPolynomial (N m a : ℕ) (t : K) : (InfinityBaseRing t)[X] :=
  X ^ N - C (infinityBaseU t * (infinityBranchUnit N m t : InfinityBaseRing t) ^ a)

/-- The root algebra of the normalized infinity chart. -/
abbrev InfinityBranchRing (N m a : ℕ) (t : K) :=
  AdjoinRoot (infinityBranchPolynomial N m a t)

/-- The normalized infinity coordinate. -/
def infinityBranchRoot (N m a : ℕ) (t : K) : InfinityBranchRing N m a t :=
  AdjoinRoot.root (infinityBranchPolynomial N m a t)

theorem infinityBranchRoot_pow (N m a : ℕ) (t : K) :
    infinityBranchRoot N m a t ^ N =
      algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
        (infinityBaseU t * (infinityBranchUnit N m t : InfinityBaseRing t) ^ a) :=
  AdjoinRoot.root_X_pow_sub_C_pow N _

/-- The concrete infinity equation is the generic tame equation for its
inverse-coordinate branch factors. -/
theorem infinityBranchPolynomial_eq_tame (N m a : ℕ) (t : K) :
    infinityBranchPolynomial N m a t =
      RingTheory.Smooth.localizedKummerEquation
        (infinityBranchProduct t)
        (tameBranchRadicand ((X - 1) ^ (N - m) * (X - C t) ^ m) a) N := by
  simp only [infinityBranchPolynomial, RingTheory.Smooth.localizedKummerEquation,
    tameBranchRadicand, infinityBaseU, infinityBranchUnit_val, infinityBranchFactor,
    map_mul, map_pow]

/-- The substituted Euler equation in the singular coordinate `v = y*u^2`. -/
def infinitySingularPolynomial (N m : ℕ) (t : K) : (InfinityBaseRing t)[X] :=
  X ^ N - C (infinityBaseU t ^ (N - m) *
    (infinityBranchUnit N m t : InfinityBaseRing t))

/-- The root algebra of the substituted, generally singular equation. -/
abbrev InfinitySingularRing (N m : ℕ) (t : K) :=
  AdjoinRoot (infinitySingularPolynomial N m t)

/-- The substituted coordinate `v`, retaining the original deck weight. -/
def infinitySingularRoot (N m : ℕ) (t : K) : InfinitySingularRing N m t :=
  AdjoinRoot.root (infinitySingularPolynomial N m t)

theorem infinitySingularRoot_pow (N m : ℕ) (t : K) :
    infinitySingularRoot N m t ^ N =
      algebraMap (InfinityBaseRing t) (InfinitySingularRing N m t)
        (infinityBaseU t ^ (N - m) *
          (infinityBranchUnit N m t : InfinityBaseRing t)) :=
  AdjoinRoot.root_X_pow_sub_C_pow N _

/-- Coprimality supplies the Bézout coordinate for the infinity ramification
exponent `N-m`. [TripathiGoswamiRevised, Definition 2.3] -/
theorem exists_infinityBranchBezout (N m : ℕ) (hmPos : 1 ≤ m)
    (hm : m < N) (hcop : m.Coprime N) :
    ∃ a b : ℕ, (N - m) * a = 1 + b * N := by
  have hrcop : (N - m).Coprime N :=
    (Nat.coprime_self_sub_left (Nat.le_of_lt hm)).2 hcop
  obtain ⟨a, b, _, hab⟩ :=
    AdjoinRoot.exists_bezout_exponents N (N - m) (by omega) hrcop
  exact ⟨a, b, hab⟩

/-- The singular coordinate is `v = z^(N-m)/P^b` on the normalized chart. -/
def infinitySingularToBranch (N m a b : ℕ) (t : K)
    (hbezout : (N - m) * a = 1 + b * N) :
    InfinitySingularRing N m t →ₐ[InfinityBaseRing t]
      InfinityBranchRing N m a t := by
  let u : (InfinityBranchRing N m a t)ˣ :=
    Units.map (algebraMap (InfinityBaseRing t)
      (InfinityBranchRing N m a t)).toMonoidHom (infinityBranchUnit N m t)
  let v : InfinityBranchRing N m a t :=
    infinityBranchRoot N m a t ^ (N - m) * (u⁻¹ ^ b : _)
  have hu : (u : InfinityBranchRing N m a t) =
      algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
        (infinityBranchUnit N m t : InfinityBaseRing t) := rfl
  have hz : infinityBranchRoot N m a t ^ N =
      algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
        (infinityBaseU t) * (u : InfinityBranchRing N m a t) ^ a := by
    rw [hu, ← map_pow, ← map_mul]
    exact infinityBranchRoot_pow N m a t
  apply AdjoinRoot.liftAlgHom (infinitySingularPolynomial N m t)
    (Algebra.ofId (InfinityBaseRing t) _) v
  change aeval v (infinitySingularPolynomial N m t) = 0
  simp only [infinitySingularPolynomial, map_sub, map_pow, aeval_X, aeval_C]
  rw [sub_eq_zero]
  dsimp only [v]
  rw [map_mul, map_pow, ← hu]
  exact eulerRoot_pow_bezout u
    (algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t) (infinityBaseU t))
    (infinityBranchRoot N m a t) N (N - m) a b hbezout hz

@[simp] theorem infinitySingularToBranch_root (N m a b : ℕ) (t : K)
    (hbezout : (N - m) * a = 1 + b * N) :
    infinitySingularToBranch N m a b t hbezout (infinitySingularRoot N m t) =
      infinityBranchRoot N m a t ^ (N - m) *
        algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
          (((infinityBranchUnit N m t)⁻¹ ^ b : (InfinityBaseRing t)ˣ) :
            InfinityBaseRing t) := by
  unfold infinitySingularToBranch infinitySingularRoot
  rw [AdjoinRoot.liftAlgHom_root]
  simp [map_pow]

/-- The punctured infinity base, where `u` is also invertible. -/
abbrev InfinityBaseOpen (t : K) := Localization.Away (infinityBaseU t)

/-- The inverse projection coordinate is a unit on the punctured base. -/
def infinityBaseOpenUUnit (t : K) : (InfinityBaseOpen t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (infinityBaseU t)).unit

@[simp] theorem infinityBaseOpenUUnit_val (t : K) :
    (infinityBaseOpenUUnit t : InfinityBaseOpen t) =
      algebraMap (InfinityBaseRing t) (InfinityBaseOpen t) (infinityBaseU t) := by
  simp [infinityBaseOpenUUnit]

/-- Evaluate a polynomial in `u` at the inverse of the actual `x` coordinate. -/
def inversePolynomialToCoverBase (t : K) : K[X] →+* BaseRing t :=
  Polynomial.eval₂RingHom (algebraMap K (BaseRing t))
    (↑((coverBaseXUnit t)⁻¹) : BaseRing t)

@[simp] theorem inversePolynomialToCoverBase_X (t : K) :
    inversePolynomialToCoverBase t X =
      (↑((coverBaseXUnit t)⁻¹) : BaseRing t) := by
  simp [inversePolynomialToCoverBase]

@[simp] theorem inversePolynomialToCoverBase_C (t c : K) :
    inversePolynomialToCoverBase t (C c) = algebraMap K (BaseRing t) c := by
  simp [inversePolynomialToCoverBase]

/-- The two factors omitted from the affine Euler base remain units after
substitution `u = x⁻¹`. -/
theorem isUnit_inversePolynomial_branchProduct (t : K) :
    IsUnit (inversePolynomialToCoverBase t (infinityBranchProduct t)) := by
  have h : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  have hx : (coverBaseXUnit t : BaseRing t) =
      algebraMap K[X] (BaseRing t) X := coverBaseXUnit_val t
  have hOne : IsUnit (1 - (coverBaseXUnit t : BaseRing t)) := by
    simpa only [map_sub, map_one, hx] using h.1.2
  have hT : IsUnit (1 - algebraMap K (BaseRing t) t *
      (coverBaseXUnit t : BaseRing t)) := by
    have hT' : IsUnit (1 - algebraMap K[X] (BaseRing t) (C t) *
        algebraMap K[X] (BaseRing t) X) := by
      simpa only [map_sub, map_one, map_mul] using h.2
    have hc : algebraMap K[X] (BaseRing t) (C t) =
        algebraMap K (BaseRing t) t := by
      exact (IsScalarTower.algebraMap_apply K K[X] (BaseRing t) t).symm
    simpa only [hc, ← hx] using hT'
  have hLeft : IsUnit ((↑((coverBaseXUnit t)⁻¹) : BaseRing t) - 1) := by
    have heq : (↑((coverBaseXUnit t)⁻¹) : BaseRing t) - 1 =
        (↑((coverBaseXUnit t)⁻¹) : BaseRing t) *
          (1 - (coverBaseXUnit t : BaseRing t)) := by
      simp only [mul_sub, mul_one, Units.inv_mul]
    rw [heq]
    exact ((coverBaseXUnit t)⁻¹).isUnit.mul hOne
  have hRight : IsUnit ((↑((coverBaseXUnit t)⁻¹) : BaseRing t) -
      algebraMap K (BaseRing t) t) := by
    have heq : (↑((coverBaseXUnit t)⁻¹) : BaseRing t) -
        algebraMap K (BaseRing t) t =
        (↑((coverBaseXUnit t)⁻¹) : BaseRing t) *
          (1 - algebraMap K (BaseRing t) t *
            (coverBaseXUnit t : BaseRing t)) := by
      calc
        _ = (↑((coverBaseXUnit t)⁻¹) : BaseRing t) -
            algebraMap K (BaseRing t) t *
              ((↑((coverBaseXUnit t)⁻¹) : BaseRing t) *
                (coverBaseXUnit t : BaseRing t)) := by
          simp only [Units.inv_mul, mul_one]
        _ = _ := by ring
    rw [heq]
    exact ((coverBaseXUnit t)⁻¹).isUnit.mul hT
  simp only [infinityBranchProduct, map_mul, map_sub, map_one,
    inversePolynomialToCoverBase_X, inversePolynomialToCoverBase_C]
  exact hLeft.mul hRight

/-- Restriction of functions from the inverse-coordinate base to the actual
Euler base, with `u ↦ x⁻¹`. -/
def infinityBaseToCoverBase (t : K) : InfinityBaseRing t →+* BaseRing t :=
  Localization.awayLift (inversePolynomialToCoverBase t)
    (infinityBranchProduct t) (isUnit_inversePolynomial_branchProduct t)

@[simp] theorem infinityBaseToCoverBase_polynomial (t : K) (p : K[X]) :
    infinityBaseToCoverBase t (algebraMap K[X] (InfinityBaseRing t) p) =
      inversePolynomialToCoverBase t p := by
  simp [infinityBaseToCoverBase, Localization.awayLift,
    IsLocalization.Away.lift_eq]

@[simp] theorem infinityBaseToCoverBase_u (t : K) :
    infinityBaseToCoverBase t (infinityBaseU t) =
      (↑((coverBaseXUnit t)⁻¹) : BaseRing t) := by
  rw [infinityBaseU, infinityBaseToCoverBase_polynomial,
    inversePolynomialToCoverBase_X]

/-- The `u`-branch factor becomes the explicit Laurent expression in `x`. -/
theorem infinityBaseToCoverBase_factor (N m : ℕ) (t : K) :
    infinityBaseToCoverBase t (infinityBranchFactor N m t) =
      ((↑((coverBaseXUnit t)⁻¹) : BaseRing t) - 1) ^ (N - m) *
      ((↑((coverBaseXUnit t)⁻¹) : BaseRing t) -
        algebraMap K (BaseRing t) t) ^ m := by
  simp [infinityBranchFactor, infinityBaseToCoverBase,
    inversePolynomialToCoverBase]

/-- On the punctured infinity base, restriction sends `u` to `x⁻¹`. -/
def infinityBaseOpenToCoverBase (t : K) : InfinityBaseOpen t →+* BaseRing t :=
  Localization.awayLift (infinityBaseToCoverBase t) (infinityBaseU t) (by
    rw [infinityBaseToCoverBase_u]
    exact ((coverBaseXUnit t)⁻¹).isUnit)

@[simp] theorem infinityBaseOpenToCoverBase_base (t : K)
    (v : InfinityBaseRing t) :
    infinityBaseOpenToCoverBase t
      (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t) v) =
      infinityBaseToCoverBase t v := by
  simp [infinityBaseOpenToCoverBase, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- Evaluate the affine coordinate `x` at the inverse of `u` on the infinity
overlap. -/
def coverPolynomialToInfinityBaseOpen (t : K) : K[X] →+* InfinityBaseOpen t :=
  Polynomial.eval₂RingHom (algebraMap K (InfinityBaseOpen t))
    (↑((infinityBaseOpenUUnit t)⁻¹) : InfinityBaseOpen t)

@[simp] theorem coverPolynomialToInfinityBaseOpen_X (t : K) :
    coverPolynomialToInfinityBaseOpen t X =
      (↑((infinityBaseOpenUUnit t)⁻¹) : InfinityBaseOpen t) := by
  simp [coverPolynomialToInfinityBaseOpen]

@[simp] theorem coverPolynomialToInfinityBaseOpen_C (t c : K) :
    coverPolynomialToInfinityBaseOpen t (C c) =
      algebraMap K (InfinityBaseOpen t) c := by
  simp [coverPolynomialToInfinityBaseOpen]

/-- The original three branch factors are units after `x = u⁻¹` on the
punctured infinity chart. -/
theorem isUnit_coverPolynomial_infinityBaseOpen (t : K) :
    IsUnit (coverPolynomialToInfinityBaseOpen t (branchProduct t)) := by
  have h : IsUnit (algebraMap K[X] (InfinityBaseRing t)
      (infinityBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (infinityBranchProduct t)
  simp only [infinityBranchProduct, map_mul, IsUnit.mul_iff] at h
  have hOne : IsUnit ((infinityBaseOpenUUnit t : InfinityBaseOpen t) - 1) := by
    have h' := h.1.map (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t))
    simpa [infinityBaseOpenUUnit_val, infinityBaseU, map_sub,
      IsScalarTower.algebraMap_apply] using h'
  have hT : IsUnit ((infinityBaseOpenUUnit t : InfinityBaseOpen t) -
      algebraMap K (InfinityBaseOpen t) t) := by
    have h' := h.2.map (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t))
    have hc : algebraMap (InfinityBaseRing t) (InfinityBaseOpen t)
        (algebraMap K[X] (InfinityBaseRing t) (C t)) =
        algebraMap K (InfinityBaseOpen t) t := by
      rw [← IsScalarTower.algebraMap_apply K[X] (InfinityBaseRing t)
        (InfinityBaseOpen t) (C t)]
      exact (IsScalarTower.algebraMap_apply K K[X] (InfinityBaseOpen t) t).symm
    simpa only [map_sub, hc, infinityBaseOpenUUnit_val, infinityBaseU]
      using h'
  let u := infinityBaseOpenUUnit t
  have hOne' : 1 - (↑(u⁻¹) : InfinityBaseOpen t) =
      (↑(u⁻¹) : InfinityBaseOpen t) * ((u : InfinityBaseOpen t) - 1) := by
    have hc : (↑(u⁻¹) : InfinityBaseOpen t) * (u : InfinityBaseOpen t) = 1 := by
      simp
    calc
      1 - (↑(u⁻¹) : InfinityBaseOpen t) =
          (↑(u⁻¹) : InfinityBaseOpen t) * (u : InfinityBaseOpen t) -
            (↑(u⁻¹) : InfinityBaseOpen t) := by rw [hc]
      _ = _ := by ring
  have hT' : 1 - algebraMap K (InfinityBaseOpen t) t *
      (↑(u⁻¹) : InfinityBaseOpen t) =
        (↑(u⁻¹) : InfinityBaseOpen t) *
          ((u : InfinityBaseOpen t) - algebraMap K (InfinityBaseOpen t) t) := by
    have hc : (↑(u⁻¹) : InfinityBaseOpen t) * (u : InfinityBaseOpen t) = 1 := by
      simp
    calc
      1 - algebraMap K (InfinityBaseOpen t) t *
          (↑(u⁻¹) : InfinityBaseOpen t) =
          (↑(u⁻¹) : InfinityBaseOpen t) * (u : InfinityBaseOpen t) -
            algebraMap K (InfinityBaseOpen t) t *
              (↑(u⁻¹) : InfinityBaseOpen t) := by rw [hc]
      _ = _ := by ring
  simp only [branchProduct, map_mul, map_sub, map_one,
    coverPolynomialToInfinityBaseOpen_X,
    coverPolynomialToInfinityBaseOpen_C]
  rw [hOne', hT']
  exact u⁻¹ |>.isUnit.mul ((u⁻¹).isUnit.mul hOne) |>.mul
    ((u⁻¹).isUnit.mul hT)

/-- The original branch-complement base maps to the punctured infinity base
by `x ↦ u⁻¹`. -/
def coverBaseToInfinityBaseOpen (t : K) : BaseRing t →+* InfinityBaseOpen t :=
  Localization.awayLift (coverPolynomialToInfinityBaseOpen t)
    (branchProduct t) (isUnit_coverPolynomial_infinityBaseOpen t)

@[simp] theorem coverBaseToInfinityBaseOpen_polynomial (t : K) (p : K[X]) :
    coverBaseToInfinityBaseOpen t (algebraMap K[X] (BaseRing t) p) =
      coverPolynomialToInfinityBaseOpen t p := by
  simp [coverBaseToInfinityBaseOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

@[simp] theorem coverBaseToInfinityBaseOpen_x (t : K) :
    coverBaseToInfinityBaseOpen t (coverBaseXUnit t : BaseRing t) =
      (↑((infinityBaseOpenUUnit t)⁻¹) : InfinityBaseOpen t) := by
  rw [coverBaseXUnit_val, coverBaseToInfinityBaseOpen_polynomial,
    coverPolynomialToInfinityBaseOpen_X]

@[simp] theorem infinityBaseOpenToCoverBase_u (t : K) :
    infinityBaseOpenToCoverBase t
      (infinityBaseOpenUUnit t : InfinityBaseOpen t) =
      (↑((coverBaseXUnit t)⁻¹) : BaseRing t) := by
  rw [infinityBaseOpenUUnit_val, infinityBaseOpenToCoverBase_base,
    infinityBaseToCoverBase_u]

@[simp] theorem infinityBaseOpenToCoverBase_u_inv (t : K) :
    infinityBaseOpenToCoverBase t
      (↑((infinityBaseOpenUUnit t)⁻¹) : InfinityBaseOpen t) =
      (coverBaseXUnit t : BaseRing t) := by
  have hu : Units.map (infinityBaseOpenToCoverBase t).toMonoidHom
      (infinityBaseOpenUUnit t) = (coverBaseXUnit t)⁻¹ := by
    apply Units.ext
    exact infinityBaseOpenToCoverBase_u t
  calc
    _ = ((Units.map (infinityBaseOpenToCoverBase t).toMonoidHom
        ((infinityBaseOpenUUnit t)⁻¹) : (BaseRing t)ˣ) : BaseRing t) := rfl
    _ = (((Units.map (infinityBaseOpenToCoverBase t).toMonoidHom
        (infinityBaseOpenUUnit t))⁻¹ : (BaseRing t)ˣ) : BaseRing t) := by rw [map_inv]
    _ = (coverBaseXUnit t : BaseRing t) := by rw [hu]; simp

@[simp] theorem coverBaseToInfinityBaseOpen_x_inv (t : K) :
    coverBaseToInfinityBaseOpen t
      (↑((coverBaseXUnit t)⁻¹) : BaseRing t) =
      (infinityBaseOpenUUnit t : InfinityBaseOpen t) := by
  have hx : Units.map (coverBaseToInfinityBaseOpen t).toMonoidHom
      (coverBaseXUnit t) = (infinityBaseOpenUUnit t)⁻¹ := by
    apply Units.ext
    exact coverBaseToInfinityBaseOpen_x t
  calc
    _ = ((Units.map (coverBaseToInfinityBaseOpen t).toMonoidHom
        ((coverBaseXUnit t)⁻¹) : (InfinityBaseOpen t)ˣ) : InfinityBaseOpen t) := rfl
    _ = (((Units.map (coverBaseToInfinityBaseOpen t).toMonoidHom
        (coverBaseXUnit t))⁻¹ : (InfinityBaseOpen t)ˣ) : InfinityBaseOpen t) := by rw [map_inv]
    _ = (infinityBaseOpenUUnit t : InfinityBaseOpen t) := by rw [hx]; simp

/-- The inverse-coordinate maps compose to the identity on the original base. -/
theorem infinityBaseOpenToCoverBase_comp_coverBaseToInfinityBaseOpen (t : K) :
    (infinityBaseOpenToCoverBase t).comp
      (coverBaseToInfinityBaseOpen t) = RingHom.id (BaseRing t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
  apply Polynomial.ringHom_ext
  · intro c
    change infinityBaseOpenToCoverBase t
      (coverBaseToInfinityBaseOpen t (algebraMap K[X] (BaseRing t) (C c))) =
        algebraMap K[X] (BaseRing t) (C c)
    rw [coverBaseToInfinityBaseOpen_polynomial,
      coverPolynomialToInfinityBaseOpen_C]
    calc
      infinityBaseOpenToCoverBase t (algebraMap K (InfinityBaseOpen t) c) =
          infinityBaseToCoverBase t (algebraMap K (InfinityBaseRing t) c) := by
            rw [IsScalarTower.algebraMap_apply K (InfinityBaseRing t)
              (InfinityBaseOpen t) c, infinityBaseOpenToCoverBase_base]
      _ = inversePolynomialToCoverBase t (C c) := by
        convert infinityBaseToCoverBase_polynomial t (C c)
      _ = algebraMap K[X] (BaseRing t) (C c) := by
        rw [inversePolynomialToCoverBase_C]
        exact (IsScalarTower.algebraMap_apply K K[X] (BaseRing t) c).symm
  · simp [infinityBaseOpenToCoverBase_u_inv, coverBaseXUnit_val]

/-- The inverse-coordinate maps compose to the identity on the punctured
infinity base. -/
theorem coverBaseToInfinityBaseOpen_comp_infinityBaseOpenToCoverBase (t : K) :
    (coverBaseToInfinityBaseOpen t).comp
      (infinityBaseOpenToCoverBase t) = RingHom.id (InfinityBaseOpen t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (infinityBaseU t))
  apply IsLocalization.ringHom_ext (Submonoid.powers (infinityBranchProduct t))
  apply Polynomial.ringHom_ext
  · intro c
    change coverBaseToInfinityBaseOpen t
      (infinityBaseOpenToCoverBase t
        (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t)
          (algebraMap K[X] (InfinityBaseRing t) (C c)))) =
        algebraMap (InfinityBaseRing t) (InfinityBaseOpen t)
          (algebraMap K[X] (InfinityBaseRing t) (C c))
    rw [infinityBaseOpenToCoverBase_base,
      infinityBaseToCoverBase_polynomial,
      inversePolynomialToCoverBase_C,
      IsScalarTower.algebraMap_apply K K[X] (BaseRing t) c,
      coverBaseToInfinityBaseOpen_polynomial]
    change coverPolynomialToInfinityBaseOpen t (C c) = _
    rw [coverPolynomialToInfinityBaseOpen_C]
    calc
      algebraMap K (InfinityBaseOpen t) c =
          algebraMap (InfinityBaseRing t) (InfinityBaseOpen t)
            (algebraMap K (InfinityBaseRing t) c) :=
              IsScalarTower.algebraMap_apply K (InfinityBaseRing t)
                (InfinityBaseOpen t) c
      _ = algebraMap (InfinityBaseRing t) (InfinityBaseOpen t)
            (algebraMap K[X] (InfinityBaseRing t) (C c)) := by
              rw [IsScalarTower.algebraMap_apply K K[X]
                (InfinityBaseRing t) c, Polynomial.C_eq_algebraMap]
  · simp [infinityBaseOpenToCoverBase_base,
      coverBaseToInfinityBaseOpen_x_inv,
      infinityBaseOpenUUnit_val, infinityBaseU]

/-- The punctured infinity base is the original affine Euler base under
`u = x⁻¹` and `x = u⁻¹`. -/
def infinityBaseOpenEquivCoverBase (t : K) :
    InfinityBaseOpen t ≃+* BaseRing t where
  toFun := infinityBaseOpenToCoverBase t
  invFun := coverBaseToInfinityBaseOpen t
  left_inv v := by
    have h := congrArg (fun f : InfinityBaseOpen t →+* InfinityBaseOpen t => f v)
      (coverBaseToInfinityBaseOpen_comp_infinityBaseOpenToCoverBase t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg (fun f : BaseRing t →+* BaseRing t => f v)
      (infinityBaseOpenToCoverBase_comp_coverBaseToInfinityBaseOpen t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (infinityBaseOpenToCoverBase t)
  map_add' := map_add (infinityBaseOpenToCoverBase t)

/-- Clearing the pole at infinity requires `u²`, where `u=x⁻¹`.
This identity keeps the original Euler root coordinate and its deck weight.
[TripathiGoswamiRevised, Definition 2.3] -/
theorem inverseEulerEquation {S : Type*} [CommRing S] (x : Sˣ) (t : S)
    (N m : ℕ) (hm : m ≤ N) :
    (x : S) ^ m * (1 - (x : S)) ^ (N - m) *
        (1 - t * (x : S)) ^ m * ((x⁻¹ : Sˣ) : S) ^ (2 * N) =
      ((x⁻¹ : Sˣ) : S) ^ (N - m) *
        (((x⁻¹ : Sˣ) : S) - 1) ^ (N - m) *
        (((x⁻¹ : Sˣ) : S) - t) ^ m := by
  let u : Sˣ := x⁻¹
  have huOne : (u : S) - 1 = (u : S) * (1 - (x : S)) := by
    dsimp [u]
    simp [mul_sub]
  have huT : (u : S) - t = (u : S) * (1 - t * (x : S)) := by
    dsimp [u]
    calc
      _ = (x⁻¹ : Sˣ) - t * ((x⁻¹ : Sˣ) : S) * (x : S) := by simp
      _ = _ := by ring
  have hunit : x ^ m * u ^ (2 * N) =
      u ^ (N - m) * (u ^ (N - m) * u ^ m) := by
    dsimp [u]
    have hmul : 2 * N = m + (N - m) + (N - m) + m := by omega
    rw [hmul]
    group
  have hunit' := congrArg (fun w : Sˣ => (w : S)) hunit
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hunit'
  change (x : S) ^ m * (u : S) ^ (2 * N) =
    (u : S) ^ (N - m) * ((u : S) ^ (N - m) * (u : S) ^ m) at hunit'
  change (x : S) ^ m * (1 - (x : S)) ^ (N - m) *
      (1 - t * (x : S)) ^ m * (u : S) ^ (2 * N) =
    (u : S) ^ (N - m) * ((u : S) - 1) ^ (N - m) *
      ((u : S) - t) ^ m
  rw [huOne, huT, mul_pow, mul_pow]
  calc
    _ = ((x : S) ^ m * (u : S) ^ (2 * N)) *
        ((1 - (x : S)) ^ (N - m) * (1 - t * (x : S)) ^ m) := by ring
    _ = _ := by rw [hunit']; ring

/-- On the actual affine base, clearing the pole by `u^(2N)` gives the
substituted infinity equation. -/
theorem infinityBaseToCoverBase_radicand (N m : ℕ) (t : K) (hm : m ≤ N) :
    radicand N m t *
        (↑((coverBaseXUnit t)⁻¹) : BaseRing t) ^ (2 * N) =
      (↑((coverBaseXUnit t)⁻¹) : BaseRing t) ^ (N - m) *
        infinityBaseToCoverBase t (infinityBranchFactor N m t) := by
  have hrad : radicand N m t =
      (coverBaseXUnit t : BaseRing t) ^ m *
        (1 - (coverBaseXUnit t : BaseRing t)) ^ (N - m) *
        (1 - algebraMap K (BaseRing t) t *
          (coverBaseXUnit t : BaseRing t)) ^ m := by
    have ht : algebraMap K[X] (BaseRing t) (C t) =
        algebraMap K (BaseRing t) t := by
      exact (IsScalarTower.algebraMap_apply K K[X] (BaseRing t) t).symm
    simp only [radicand, branchPolynomial, map_mul, map_pow, map_sub, map_one,
      coverBaseXUnit_val, ht]
  rw [hrad, infinityBaseToCoverBase_factor]
  simpa only [mul_assoc] using inverseEulerEquation (coverBaseXUnit t)
    (algebraMap K (BaseRing t) t) N m hm

/-- The inverse-coordinate infinity base acts on the actual affine Euler
cover through `u = x⁻¹`. -/
def infinityBaseToCover (N m : ℕ) (t : K) :
    InfinityBaseRing t →+* CoverRing N m t :=
  (algebraMap (BaseRing t) (CoverRing N m t)).comp
    (infinityBaseToCoverBase t)

/-- The invertible inverse projection coordinate in the actual Euler algebra. -/
def infinityCoverUUnit (N m : ℕ) (t : K) : (CoverRing N m t)ˣ :=
  Units.map (algebraMap (BaseRing t) (CoverRing N m t)).toMonoidHom
    ((coverBaseXUnit t)⁻¹)

@[simp] theorem infinityCoverUUnit_val (N m : ℕ) (t : K) :
    (infinityCoverUUnit N m t : CoverRing N m t) =
      algebraMap (BaseRing t) (CoverRing N m t)
        (↑((coverBaseXUnit t)⁻¹) : BaseRing t) := (rfl)

@[simp] theorem infinityBaseToCover_u (N m : ℕ) (t : K) :
    infinityBaseToCover N m t (infinityBaseU t) =
      (infinityCoverUUnit N m t : CoverRing N m t) := by
  simp [infinityBaseToCover, infinityBaseToCoverBase_u]

/-- The original Euler root after the required `u²` rescaling. -/
def infinityCoverV (N m : ℕ) (t : K) : CoverRing N m t :=
  coverRoot N m t * (infinityCoverUUnit N m t : CoverRing N m t) ^ 2

/-- The rescaled actual Euler root satisfies the substituted infinity
equation, including the exponent `N-m` at `u=0`. -/
theorem infinityCoverV_pow (N m : ℕ) (t : K) (hm : m ≤ N) :
    infinityCoverV N m t ^ N =
      (infinityCoverUUnit N m t : CoverRing N m t) ^ (N - m) *
        infinityBaseToCover N m t (infinityBranchFactor N m t) := by
  have h := congrArg (algebraMap (BaseRing t) (CoverRing N m t))
    (infinityBaseToCoverBase_radicand N m t hm)
  simp only [map_mul, map_pow] at h
  change algebraMap (BaseRing t) (CoverRing N m t) (radicand N m t) *
      (infinityCoverUUnit N m t : CoverRing N m t) ^ (2 * N) =
    (infinityCoverUUnit N m t : CoverRing N m t) ^ (N - m) *
      infinityBaseToCover N m t (infinityBranchFactor N m t) at h
  rw [infinityCoverV, mul_pow, ← pow_mul, coverRoot_pow]
  exact h

/-- The substituted singular infinity equation maps to the actual Euler
cover, sending `v` to the original `y` times `u²`. -/
def infinitySingularToCover (N m : ℕ) (t : K) (hm : m ≤ N) :
    InfinitySingularRing N m t →+* CoverRing N m t :=
  AdjoinRoot.lift (infinityBaseToCover N m t) (infinityCoverV N m t) (by
    simp only [infinitySingularPolynomial, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X,
      eval₂_C, sub_eq_zero, map_mul, map_pow, infinityBaseToCover_u,
      infinityBranchUnit_val]
    rw [infinityCoverV_pow N m t hm])

@[simp] theorem infinitySingularToCover_root (N m : ℕ) (t : K)
    (hm : m ≤ N) :
    infinitySingularToCover N m t hm (infinitySingularRoot N m t) =
      infinityCoverV N m t := by
  simp [infinitySingularToCover, infinitySingularRoot]

/-- The unit factor `P` after restriction to the actual Euler cover. -/
def infinityCoverPUnit (N m : ℕ) (t : K) : (CoverRing N m t)ˣ :=
  Units.map (infinityBaseToCover N m t).toMonoidHom
    (infinityBranchUnit N m t)

/-- The rescaled original root, viewed as a unit on the branch complement. -/
def infinityCoverVUnit (N m : ℕ) (t : K) (hN : N ≠ 0) :
    (CoverRing N m t)ˣ :=
  coverRootUnit N m t hN * infinityCoverUUnit N m t ^ 2

@[simp] theorem infinityCoverVUnit_val (N m : ℕ) (t : K) (hN : N ≠ 0) :
    (infinityCoverVUnit N m t hN : CoverRing N m t) =
      infinityCoverV N m t := by
  simp [infinityCoverVUnit, infinityCoverV]

/-- In units, the substituted infinity equation is `v^N = u^(N-m) P`. -/
theorem infinityCoverVUnit_pow (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) :
    infinityCoverVUnit N m t hN ^ N =
      infinityCoverUUnit N m t ^ (N - m) * infinityCoverPUnit N m t := by
  apply Units.ext
  change (infinityCoverVUnit N m t hN : CoverRing N m t) ^ N =
    (infinityCoverUUnit N m t : CoverRing N m t) ^ (N - m) *
      (infinityCoverPUnit N m t : CoverRing N m t)
  rw [infinityCoverVUnit_val, infinityCoverV_pow N m t hm]
  rfl

/-- On the actual affine cover, the normalized infinity root is
`z = (y*u²)^a/u^b`. -/
def infinityInverseBranchCoordinate (N m a b : ℕ) (t : K) (hN : N ≠ 0) :
    CoverRing N m t :=
  ((infinityCoverVUnit N m t hN ^ a *
      (infinityCoverUUnit N m t)⁻¹ ^ b : (CoverRing N m t)ˣ) :
    CoverRing N m t)

/-- The inverse Bézout coordinate in the actual affine Euler ring satisfies
the normalized infinity equation. -/
theorem infinityInverseBranchCoordinate_pow (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    infinityInverseBranchCoordinate N m a b t hN ^ N =
      infinityBaseToCover N m t
        (infinityBaseU t * (infinityBranchUnit N m t : InfinityBaseRing t) ^ a) := by
  have h := eulerUnit_inverse_root (infinityCoverUUnit N m t)
    (infinityCoverPUnit N m t) (infinityCoverVUnit N m t hN)
    N (N - m) a b hbezout (infinityCoverVUnit_pow N m t hN hm)
  have h' := congrArg (fun v : (CoverRing N m t)ˣ => (v : CoverRing N m t)) h
  change infinityInverseBranchCoordinate N m a b t hN ^ N =
    (infinityCoverUUnit N m t : CoverRing N m t) *
      (infinityCoverPUnit N m t : CoverRing N m t) ^ a at h'
  rw [h', map_mul, map_pow, infinityBaseToCover_u]
  rfl

/-- Restrict the normalized infinity chart to the actual affine Euler
cover, with `z ↦ (y*u²)^a/u^b`. -/
def infinityBranchToCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    InfinityBranchRing N m a t →+* CoverRing N m t :=
  AdjoinRoot.lift (infinityBaseToCover N m t)
    (infinityInverseBranchCoordinate N m a b t hN) (by
      simp only [infinityBranchPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
        eval₂_C, sub_eq_zero]
      exact infinityInverseBranchCoordinate_pow N m a b t hN hm hbezout)

@[simp] theorem infinityBranchToCover_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    infinityBranchToCover N m a b t hN hm hbezout
      (infinityBranchRoot N m a t) =
        infinityInverseBranchCoordinate N m a b t hN := by
  simp [infinityBranchToCover, infinityBranchRoot]

/-- The inverse projection coordinate in the normalized infinity algebra. -/
def infinityBranchU (N m a : ℕ) (t : K) : InfinityBranchRing N m a t :=
  algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
    (infinityBaseU t)

/-- Restriction of the normalized infinity chart to `u ≠ 0`. -/
abbrev InfinityBranchOpen (N m a : ℕ) (t : K) :=
  Localization.Away (infinityBranchU N m a t)

/-- The unit `u` on the normalized infinity overlap. -/
def infinityBranchOpenUUnit (N m a : ℕ) (t : K) :
    (InfinityBranchOpen N m a t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (infinityBranchU N m a t)).unit

@[simp] theorem infinityBranchOpenUUnit_val (N m a : ℕ) (t : K) :
    (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) =
      algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t)
        (infinityBranchU N m a t) := by
  simp [infinityBranchOpenUUnit]

/-- The unit factor `P` on the normalized infinity overlap. -/
def infinityBranchOpenPUnit (N m a : ℕ) (t : K) :
    (InfinityBranchOpen N m a t)ˣ :=
  Units.map
    ((algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t)).comp
      (algebraMap (InfinityBaseRing t)
        (InfinityBranchRing N m a t))).toMonoidHom
    (infinityBranchUnit N m t)

/-- The normalized root becomes a unit on `D(u)`. -/
theorem isUnit_infinityBranchOpenRoot (N m a : ℕ) (t : K)
    (hN : N ≠ 0) :
    IsUnit (algebraMap (InfinityBranchRing N m a t)
      (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) := by
  apply (isUnit_pow_iff hN).mp
  rw [← map_pow, infinityBranchRoot_pow]
  simp only [map_mul, map_pow]
  change IsUnit ((infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) *
    (infinityBranchOpenPUnit N m a t : InfinityBranchOpen N m a t) ^ a)
  exact (infinityBranchOpenUUnit N m a t).isUnit.mul
    ((infinityBranchOpenPUnit N m a t).isUnit.pow a)

/-- The normalized infinity coordinate as a unit on its overlap. -/
def infinityBranchOpenRootUnit (N m a : ℕ) (t : K) (hN : N ≠ 0) :
    (InfinityBranchOpen N m a t)ˣ :=
  (isUnit_infinityBranchOpenRoot N m a t hN).unit

@[simp] theorem infinityBranchOpenRootUnit_val (N m a : ℕ) (t : K)
    (hN : N ≠ 0) :
    (infinityBranchOpenRootUnit N m a t hN : InfinityBranchOpen N m a t) =
      algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t) := by
  simp [infinityBranchOpenRootUnit]

theorem infinityBranchOpenRootUnit_pow (N m a : ℕ) (t : K) (hN : N ≠ 0) :
    infinityBranchOpenRootUnit N m a t hN ^ N =
      infinityBranchOpenUUnit N m a t *
        infinityBranchOpenPUnit N m a t ^ a := by
  apply Units.ext
  change (infinityBranchOpenRootUnit N m a t hN : InfinityBranchOpen N m a t) ^ N =
    (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) *
      (infinityBranchOpenPUnit N m a t : InfinityBranchOpen N m a t) ^ a
  rw [infinityBranchOpenRootUnit_val, ← map_pow, infinityBranchRoot_pow,
    map_mul, map_pow]
  simp [infinityBranchOpenUUnit_val, infinityBranchOpenPUnit, infinityBranchU]

/-- The normalized chart restricts to the actual Euler cover on `D(u)`. -/
def infinityBranchOpenToCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    InfinityBranchOpen N m a t →+* CoverRing N m t :=
  Localization.awayLift (infinityBranchToCover N m a b t hN hm hbezout)
    (infinityBranchU N m a t) (by
      change IsUnit (infinityBranchToCover N m a b t hN hm hbezout
        (algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
          (infinityBaseU t)))
      simpa [infinityBranchToCover, AdjoinRoot.lift_of,
        infinityBaseToCover_u, infinityCoverUUnit_val] using
        (infinityCoverUUnit N m t).isUnit)

/-- The infinity base maps into its normalized overlap. -/
def infinityBaseToBranchOpen (N m a : ℕ) (t : K) :
    InfinityBaseRing t →+* InfinityBranchOpen N m a t :=
  (algebraMap (InfinityBranchRing N m a t)
    (InfinityBranchOpen N m a t)).comp
      (algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t))

@[simp] theorem infinityBranchOpenToCover_base (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N)
    (v : InfinityBaseRing t) :
    infinityBranchOpenToCover N m a b t hN hm hbezout
      (infinityBaseToBranchOpen N m a t v) =
        infinityBaseToCover N m t v := by
  simp [infinityBranchOpenToCover, infinityBaseToBranchOpen,
    infinityBranchToCover, IsLocalization.Away.lift_eq, AdjoinRoot.lift_of]

@[simp] theorem infinityBranchOpenToCover_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    infinityBranchOpenToCover N m a b t hN hm hbezout
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) =
      infinityInverseBranchCoordinate N m a b t hN := by
  simp [infinityBranchOpenToCover, IsLocalization.Away.lift_eq]

/-- The inverse projection base maps into the normalized overlap. -/
def infinityBaseOpenToBranchOpen (N m a : ℕ) (t : K) :
    InfinityBaseOpen t →+* InfinityBranchOpen N m a t :=
  Localization.awayLift (infinityBaseToBranchOpen N m a t)
    (infinityBaseU t) (by
      change IsUnit (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t)
      exact (infinityBranchOpenUUnit N m a t).isUnit)

@[simp] theorem infinityBaseOpenToBranchOpen_base (N m a : ℕ) (t : K)
    (v : InfinityBaseRing t) :
    infinityBaseOpenToBranchOpen N m a t
      (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t) v) =
        infinityBaseToBranchOpen N m a t v := by
  simp [infinityBaseOpenToBranchOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The original affine base, with `x=u⁻¹`, maps to the infinity overlap. -/
def coverBaseToInfinityBranchOpen (N m a : ℕ) (t : K) :
    BaseRing t →+* InfinityBranchOpen N m a t :=
  (infinityBaseOpenToBranchOpen N m a t).comp
    (coverBaseToInfinityBaseOpen t)

@[simp] theorem coverBaseToInfinityBaseOpen_infinityBase (t : K)
    (w : InfinityBaseRing t) :
    coverBaseToInfinityBaseOpen t (infinityBaseToCoverBase t w) =
      algebraMap (InfinityBaseRing t) (InfinityBaseOpen t) w := by
  have h := congrArg (fun f : InfinityBaseOpen t →+* InfinityBaseOpen t =>
      f (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t) w))
    (coverBaseToInfinityBaseOpen_comp_infinityBaseOpenToCoverBase t)
  simpa only [RingHom.comp_apply, RingHom.id_apply,
    infinityBaseOpenToCoverBase_base] using h

/-- The original radicand after the inverse-coordinate substitution. -/
theorem coverBaseToInfinityBaseOpen_radicand (N m : ℕ) (t : K)
    (hm : m ≤ N) :
    coverBaseToInfinityBaseOpen t (radicand N m t) *
        (infinityBaseOpenUUnit t : InfinityBaseOpen t) ^ (2 * N) =
      (infinityBaseOpenUUnit t : InfinityBaseOpen t) ^ (N - m) *
        algebraMap (InfinityBaseRing t) (InfinityBaseOpen t)
          (infinityBranchFactor N m t) := by
  have h := congrArg (coverBaseToInfinityBaseOpen t)
    (infinityBaseToCoverBase_radicand N m t hm)
  simpa only [map_mul, map_pow, coverBaseToInfinityBaseOpen_x_inv,
    coverBaseToInfinityBaseOpen_infinityBase] using h

/-- The substituted coordinate is a unit on the overlap. -/
def infinityBranchOpenVUnit (N m a b : ℕ) (t : K) (hN : N ≠ 0) :
    (InfinityBranchOpen N m a t)ˣ :=
  infinityBranchOpenRootUnit N m a t hN ^ (N - m) *
    (infinityBranchOpenPUnit N m a t)⁻¹ ^ b

theorem infinityBranchOpenVUnit_pow (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    infinityBranchOpenVUnit N m a b t hN ^ N =
      infinityBranchOpenUUnit N m a t ^ (N - m) *
        infinityBranchOpenPUnit N m a t := by
  apply Units.ext
  change (infinityBranchOpenVUnit N m a b t hN :
      InfinityBranchOpen N m a t) ^ N =
    (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) ^
        (N - m) *
      (infinityBranchOpenPUnit N m a t : InfinityBranchOpen N m a t)
  exact eulerRoot_pow_bezout (infinityBranchOpenPUnit N m a t)
    (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t)
    (infinityBranchOpenRootUnit N m a t hN :
      InfinityBranchOpen N m a t) N (N - m) a b hbezout
    (congrArg Units.val (infinityBranchOpenRootUnit_pow N m a t hN))

/-- The original Euler coordinate on the infinity overlap is y=v/u². -/
def infinityBranchOpenYUnit (N m a b : ℕ) (t : K) (hN : N ≠ 0) :
    (InfinityBranchOpen N m a t)ˣ :=
  infinityBranchOpenVUnit N m a b t hN *
    (infinityBranchOpenUUnit N m a t)⁻¹ ^ 2

/-- The original Euler equation holds for the reconstructed coordinate. -/
theorem infinityBranchOpenYUnit_pow (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    (infinityBranchOpenYUnit N m a b t hN :
      InfinityBranchOpen N m a t) ^ N =
      coverBaseToInfinityBranchOpen N m a t (radicand N m t) := by
  have h := congrArg (infinityBaseOpenToBranchOpen N m a t)
    (coverBaseToInfinityBaseOpen_radicand N m t hm)
  simp only [map_mul, map_pow] at h
  simp only [infinityBaseOpenUUnit_val, infinityBaseOpenToBranchOpen_base] at h
  change coverBaseToInfinityBranchOpen N m a t (radicand N m t) *
      (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) ^
        (2 * N) =
    (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) ^
        (N - m) *
      (infinityBranchOpenPUnit N m a t : InfinityBranchOpen N m a t) at h
  let hu := infinityBranchOpenUUnit N m a t
  let hv := infinityBranchOpenVUnit N m a b t hN
  have hunit : hv ^ N =
      hu ^ (N - m) * infinityBranchOpenPUnit N m a t :=
    infinityBranchOpenVUnit_pow N m a b t hN hbezout
  have h' : (hv : InfinityBranchOpen N m a t) ^ N =
      coverBaseToInfinityBranchOpen N m a t (radicand N m t) *
        (hu : InfinityBranchOpen N m a t) ^ (2 * N) := by
    exact (congrArg Units.val hunit).trans h.symm
  change ((hv * hu⁻¹ ^ 2 : (InfinityBranchOpen N m a t)ˣ) :
      InfinityBranchOpen N m a t) ^ N = _
  have hpow : ((hv * hu⁻¹ ^ 2 : (InfinityBranchOpen N m a t)ˣ) :
      InfinityBranchOpen N m a t) ^ N *
        (hu : InfinityBranchOpen N m a t) ^ (2 * N) =
        (hv : InfinityBranchOpen N m a t) ^ N := by
    have hg : (hv * hu⁻¹ ^ 2) ^ N * hu ^ (2 * N) = hv ^ N := by
      calc
        _ = hv ^ N * ((hu⁻¹ ^ 2) ^ N * hu ^ (2 * N)) := by
          rw [mul_pow]
          simp only [Nat.mul_comm 2 N, mul_assoc] at *
        _ = hv ^ N * ((hu⁻¹) ^ (2 * N) * hu ^ (2 * N)) := by
          rw [← pow_mul]
        _ = hv ^ N := by
          rw [← mul_pow]
          simp
    exact congrArg Units.val hg
  have heq := congrArg
    (fun q : InfinityBranchOpen N m a t =>
      q * (hu⁻¹ : (InfinityBranchOpen N m a t)ˣ) ^ (2 * N))
    (hpow.trans h')
  simpa [mul_assoc, ← mul_pow] using heq

/-- The original affine Euler algebra maps into the normalized infinity
overlap with x=u⁻¹ and y=(z^(N-m)/P^b)/u². -/
def coverToInfinityBranchOpen (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    CoverRing N m t →+* InfinityBranchOpen N m a t :=
  AdjoinRoot.lift (coverBaseToInfinityBranchOpen N m a t)
    (infinityBranchOpenYUnit N m a b t hN :
      InfinityBranchOpen N m a t) (by
      simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [sub_eq_zero]
      exact infinityBranchOpenYUnit_pow N m a b t hN hm hbezout)

@[simp] theorem coverToInfinityBranchOpen_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    coverToInfinityBranchOpen N m a b t hN hm hbezout (coverRoot N m t) =
      (infinityBranchOpenYUnit N m a b t hN :
        InfinityBranchOpen N m a t) := by
  simp [coverToInfinityBranchOpen, coverRoot]

@[simp] theorem coverToInfinityBranchOpen_base (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) (w : BaseRing t) :
    coverToInfinityBranchOpen N m a b t hN hm hbezout
        (algebraMap (BaseRing t) (CoverRing N m t) w) =
      coverBaseToInfinityBranchOpen N m a t w := by
  simp [coverToInfinityBranchOpen, AdjoinRoot.lift_of]

@[simp] theorem coverToInfinityBranchOpen_infinityBase
    (N m a b : ℕ) (t : K) (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N)
    (w : InfinityBaseRing t) :
    coverToInfinityBranchOpen N m a b t hN hm hbezout
        (infinityBaseToCover N m t w) =
      infinityBaseToBranchOpen N m a t w := by
  change coverToInfinityBranchOpen N m a b t hN hm hbezout
    (algebraMap (BaseRing t) (CoverRing N m t)
      (infinityBaseToCoverBase t w)) = _
  rw [coverToInfinityBranchOpen_base, coverBaseToInfinityBranchOpen,
    RingHom.comp_apply, coverBaseToInfinityBaseOpen_infinityBase,
    infinityBaseOpenToBranchOpen_base]

@[simp] theorem infinityBranchOpenToCover_infinityBaseOpen
    (N m a b : ℕ) (t : K) (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N)
    (w : InfinityBaseOpen t) :
    infinityBranchOpenToCover N m a b t hN hm hbezout
        (infinityBaseOpenToBranchOpen N m a t w) =
      algebraMap (BaseRing t) (CoverRing N m t)
        (infinityBaseOpenToCoverBase t w) := by
  have h : (infinityBranchOpenToCover N m a b t hN hm hbezout).comp
      (infinityBaseOpenToBranchOpen N m a t) =
      (algebraMap (BaseRing t) (CoverRing N m t)).comp
        (infinityBaseOpenToCoverBase t) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (infinityBaseU t))
    apply RingHom.ext
    intro v
    change infinityBranchOpenToCover N m a b t hN hm hbezout
      (infinityBaseOpenToBranchOpen N m a t
        (algebraMap (InfinityBaseRing t) (InfinityBaseOpen t) v)) = _
    rw [infinityBaseOpenToBranchOpen_base, infinityBranchOpenToCover_base]
    simp only [RingHom.comp_apply, infinityBaseOpenToCoverBase_base]
    rfl
  exact congrArg (fun f : InfinityBaseOpen t →+* CoverRing N m t => f w) h

@[simp] theorem infinityBranchOpenToCover_coverBase
    (N m a b : ℕ) (t : K) (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N)
    (w : BaseRing t) :
    infinityBranchOpenToCover N m a b t hN hm hbezout
      (coverBaseToInfinityBranchOpen N m a t w) =
        algebraMap (BaseRing t) (CoverRing N m t) w := by
  rw [coverBaseToInfinityBranchOpen, RingHom.comp_apply,
    infinityBranchOpenToCover_infinityBaseOpen]
  have h := congrArg (fun f : BaseRing t →+* BaseRing t => f w)
    (infinityBaseOpenToCoverBase_comp_coverBaseToInfinityBaseOpen t)
  simpa only [RingHom.comp_apply, RingHom.id_apply] using
    congrArg (algebraMap (BaseRing t) (CoverRing N m t)) h

theorem infinityBranchOpenToCover_uUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    Units.map (infinityBranchOpenToCover N m a b t hN hm hbezout).toMonoidHom
      (infinityBranchOpenUUnit N m a t) =
        infinityCoverUUnit N m t := by
  apply Units.ext
  change infinityBranchOpenToCover N m a b t hN hm hbezout
    (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t) = _
  rw [infinityBranchOpenUUnit_val]
  change infinityBranchOpenToCover N m a b t hN hm hbezout
    (infinityBaseToBranchOpen N m a t (infinityBaseU t)) = _
  rw [infinityBranchOpenToCover_base, infinityBaseToCover_u]

theorem infinityBranchOpenToCover_pUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    Units.map (infinityBranchOpenToCover N m a b t hN hm hbezout).toMonoidHom
      (infinityBranchOpenPUnit N m a t) =
        infinityCoverPUnit N m t := by
  apply Units.ext
  change infinityBranchOpenToCover N m a b t hN hm hbezout
    (infinityBaseToBranchOpen N m a t
      (infinityBranchUnit N m t : InfinityBaseRing t)) = _
  rw [infinityBranchOpenToCover_base]
  rfl

theorem infinityBranchOpenToCover_rootUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    Units.map (infinityBranchOpenToCover N m a b t hN hm hbezout).toMonoidHom
      (infinityBranchOpenRootUnit N m a t hN) =
        infinityCoverVUnit N m t hN ^ a *
          (infinityCoverUUnit N m t)⁻¹ ^ b := by
  apply Units.ext
  change infinityBranchOpenToCover N m a b t hN hm hbezout
    (infinityBranchOpenRootUnit N m a t hN :
      InfinityBranchOpen N m a t) =
        infinityInverseBranchCoordinate N m a b t hN
  rw [infinityBranchOpenRootUnit_val, infinityBranchOpenToCover_root]

theorem coverToInfinityBranchOpen_uUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    Units.map (coverToInfinityBranchOpen N m a b t hN hm hbezout).toMonoidHom
      (infinityCoverUUnit N m t) =
        infinityBranchOpenUUnit N m a t := by
  apply Units.ext
  change coverToInfinityBranchOpen N m a b t hN hm hbezout
    (infinityCoverUUnit N m t : CoverRing N m t) =
      (infinityBranchOpenUUnit N m a t : InfinityBranchOpen N m a t)
  rw [← infinityBaseToCover_u, coverToInfinityBranchOpen_infinityBase]
  rfl

theorem coverToInfinityBranchOpen_pUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    Units.map (coverToInfinityBranchOpen N m a b t hN hm hbezout).toMonoidHom
      (infinityCoverPUnit N m t) =
        infinityBranchOpenPUnit N m a t := by
  apply Units.ext
  change coverToInfinityBranchOpen N m a b t hN hm hbezout
    (infinityBaseToCover N m t
      (infinityBranchUnit N m t : InfinityBaseRing t)) = _
  rw [coverToInfinityBranchOpen_infinityBase]
  rfl

theorem coverToInfinityBranchOpen_rootUnit (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    Units.map (coverToInfinityBranchOpen N m a b t hN hm hbezout).toMonoidHom
      (coverRootUnit N m t hN) =
        infinityBranchOpenYUnit N m a b t hN := by
  apply Units.ext
  change coverToInfinityBranchOpen N m a b t hN hm hbezout
    (coverRootUnit N m t hN : CoverRing N m t) =
      (infinityBranchOpenYUnit N m a b t hN :
        InfinityBranchOpen N m a t)
  rw [coverRootUnit_val, coverToInfinityBranchOpen_root]

@[simp] theorem infinityBranchOpenToCover_coverRoot (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    infinityBranchOpenToCover N m a b t hN hm hbezout
        (coverToInfinityBranchOpen N m a b t hN hm hbezout
          (coverRoot N m t)) = coverRoot N m t := by
  rw [coverToInfinityBranchOpen_root]
  let f := infinityBranchOpenToCover N m a b t hN hm hbezout
  have h : Units.map f.toMonoidHom
      (infinityBranchOpenYUnit N m a b t hN) =
        coverRootUnit N m t hN := by
    simp only [infinityBranchOpenYUnit, infinityBranchOpenVUnit,
      map_mul, map_pow, map_inv]
    rw [infinityBranchOpenToCover_rootUnit,
      infinityBranchOpenToCover_pUnit, infinityBranchOpenToCover_uUnit]
    calc
      ((infinityCoverVUnit N m t hN ^ a *
          (infinityCoverUUnit N m t)⁻¹ ^ b) ^ (N - m) *
            (infinityCoverPUnit N m t)⁻¹ ^ b) *
          (infinityCoverUUnit N m t)⁻¹ ^ 2 =
          infinityCoverVUnit N m t hN *
            (infinityCoverUUnit N m t)⁻¹ ^ 2 := by
              rw [eulerUnit_recover_original
                (infinityCoverUUnit N m t) (infinityCoverPUnit N m t)
                (infinityCoverVUnit N m t hN) N (N - m) a b hbezout
                (infinityCoverVUnit_pow N m t hN hm)]
      _ = coverRootUnit N m t hN := by
        simp [infinityCoverVUnit, mul_assoc]
  exact (congrArg Units.val h).trans (coverRootUnit_val N m t hN)

/-- The two overlap maps compose to the identity on the actual Euler cover. -/
theorem infinityBranchOpenToCover_coverToInfinityBranchOpen
    (N m a b : ℕ) (t : K) (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    (infinityBranchOpenToCover N m a b t hN hm hbezout).comp
      (coverToInfinityBranchOpen N m a b t hN hm hbezout) =
        RingHom.id (CoverRing N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro w
    change infinityBranchOpenToCover N m a b t hN hm hbezout
      (coverToInfinityBranchOpen N m a b t hN hm hbezout
        (algebraMap (BaseRing t) (CoverRing N m t) w)) = _
    rw [coverToInfinityBranchOpen_base,
      infinityBranchOpenToCover_coverBase]
    rfl
  · change infinityBranchOpenToCover N m a b t hN hm hbezout
      (coverToInfinityBranchOpen N m a b t hN hm hbezout
        (coverRoot N m t)) = _
    exact infinityBranchOpenToCover_coverRoot N m a b t hN hm hbezout

@[simp] theorem coverToInfinityBranchOpen_branchRoot (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    coverToInfinityBranchOpen N m a b t hN hm hbezout
      (infinityBranchOpenToCover N m a b t hN hm hbezout
        (algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t)
          (infinityBranchRoot N m a t))) =
      algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t)
        (infinityBranchRoot N m a t) := by
  rw [infinityBranchOpenToCover_root]
  let g := coverToInfinityBranchOpen N m a b t hN hm hbezout
  have h : Units.map g.toMonoidHom
      (infinityCoverVUnit N m t hN ^ a *
        (infinityCoverUUnit N m t)⁻¹ ^ b) =
        infinityBranchOpenRootUnit N m a t hN := by
    change Units.map g.toMonoidHom
      ((coverRootUnit N m t hN * infinityCoverUUnit N m t ^ 2) ^ a *
        (infinityCoverUUnit N m t)⁻¹ ^ b) = _
    simp only [map_mul, map_pow, map_inv]
    rw [coverToInfinityBranchOpen_rootUnit,
      coverToInfinityBranchOpen_uUnit]
    have hv : infinityBranchOpenYUnit N m a b t hN *
        infinityBranchOpenUUnit N m a t ^ 2 =
          infinityBranchOpenVUnit N m a b t hN := by
      unfold infinityBranchOpenYUnit
      group
    rw [hv]
    exact eulerUnit_recover_branch (infinityBranchOpenUUnit N m a t)
      (infinityBranchOpenPUnit N m a t)
      (infinityBranchOpenRootUnit N m a t hN)
      N (N - m) a b hbezout
      (infinityBranchOpenRootUnit_pow N m a t hN)
  change g (((infinityCoverVUnit N m t hN ^ a *
      (infinityCoverUUnit N m t)⁻¹ ^ b : (CoverRing N m t)ˣ) :
        CoverRing N m t)) =
      (infinityBranchOpenRootUnit N m a t hN : InfinityBranchOpen N m a t)
  exact congrArg Units.val h

/-- The overlap maps also compose to the identity on the localized infinity chart. -/
theorem coverToInfinityBranchOpen_infinityBranchOpenToCover
    (N m a b : ℕ) (t : K) (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    (coverToInfinityBranchOpen N m a b t hN hm hbezout).comp
      (infinityBranchOpenToCover N m a b t hN hm hbezout) =
        RingHom.id (InfinityBranchOpen N m a t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (infinityBranchU N m a t))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro w
    change coverToInfinityBranchOpen N m a b t hN hm hbezout
      (infinityBranchOpenToCover N m a b t hN hm hbezout
        (infinityBaseToBranchOpen N m a t w)) = _
    rw [infinityBranchOpenToCover_base,
      coverToInfinityBranchOpen_infinityBase]
    rfl
  · change coverToInfinityBranchOpen N m a b t hN hm hbezout
      (infinityBranchOpenToCover N m a b t hN hm hbezout
        (algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t)
          (infinityBranchRoot N m a t))) = _
    exact coverToInfinityBranchOpen_branchRoot N m a b t hN hm hbezout

/-- The punctured normalized infinity chart is the actual affine Euler cover. -/
def infinityBranchOpenEquivCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    InfinityBranchOpen N m a t ≃+* CoverRing N m t where
  toFun := infinityBranchOpenToCover N m a b t hN hm hbezout
  invFun := coverToInfinityBranchOpen N m a b t hN hm hbezout
  left_inv v := by
    have h := congrArg
      (fun f : InfinityBranchOpen N m a t →+* InfinityBranchOpen N m a t => f v)
      (coverToInfinityBranchOpen_infinityBranchOpenToCover N m a b t hN hm hbezout)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg (fun f : CoverRing N m t →+* CoverRing N m t => f v)
      (infinityBranchOpenToCover_coverToInfinityBranchOpen N m a b t hN hm hbezout)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (infinityBranchOpenToCover N m a b t hN hm hbezout)
  map_add' := map_add (infinityBranchOpenToCover N m a b t hN hm hbezout)

/-- The infinity overlap equivalence preserves the coefficient ring. -/
def infinityBranchOpenAlgEquivCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    InfinityBranchOpen N m a t ≃ₐ[K] CoverRing N m t :=
  AlgEquiv.ofRingEquiv
    (f := infinityBranchOpenEquivCover N m a b t hN hm hbezout) (by
    intro c
    change infinityBranchOpenToCover N m a b t hN hm hbezout
      (infinityBaseToBranchOpen N m a t
        (algebraMap K (InfinityBaseRing t) c)) = _
    rw [infinityBranchOpenToCover_base]
    change algebraMap (BaseRing t) (CoverRing N m t)
      (infinityBaseToCoverBase t (algebraMap K (InfinityBaseRing t) c)) = _
    have hc : infinityBaseToCoverBase t
        (algebraMap K (InfinityBaseRing t) c) =
          algebraMap K (BaseRing t) c := by
      convert infinityBaseToCoverBase_polynomial t (C c)
      simp
    rw [hc]
    exact (IsScalarTower.algebraMap_apply K (BaseRing t) (CoverRing N m t) c))

/-- The normalized infinity chart is smooth over the coefficient ring,
including its ramification point above `u = 0`.
[TripathiGoswamiRevised, Definition 2.3] -/
theorem infinityBranchRing_smooth (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Algebra.Smooth K (InfinityBranchRing N m a t) := by
  have h : Algebra.Smooth K
      (TameBranchRing (infinityBranchProduct t)
        ((X - 1) ^ (N - m) * (X - C t) ^ m) N a) :=
    tameBranchRing_smooth (infinityBranchProduct t)
      ((X - 1) ^ (N - m) * (X - C t) ^ m) N a
      (isUnit_infinityBranchFactor N m t) hN hn
  change Algebra.Smooth K (AdjoinRoot (infinityBranchPolynomial N m a t))
  rw [infinityBranchPolynomial_eq_tame]
  exact h

/-- The normalized infinity chart, before restricting to `u ≠ 0`. -/
@[expose] def infinityBranchScheme (N m a : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (InfinityBranchRing N m a t))

/-- Its structural morphism to the coefficient ring. -/
def infinityBranchStructureMap (N m a : ℕ) (t : K) :
    infinityBranchScheme N m a t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (InfinityBranchRing N m a t)))

/-- The structural morphism of the normalized infinity chart is smooth.
[TripathiGoswamiRevised, Definition 2.3] -/
theorem infinityBranchStructureMap_smooth (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Smooth (infinityBranchStructureMap N m a t) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  exact RingHom.smooth_algebraMap.mpr (infinityBranchRing_smooth N m a t hN hn)

/-- The punctured normalized infinity chart as a scheme. -/
@[expose] def infinityBranchOpenScheme (N m a : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (InfinityBranchOpen N m a t))

/-- Localization at `u` includes the punctured chart into the normalized chart. -/
def infinityBranchOpenInclusion (N m a : ℕ) (t : K) :
    infinityBranchOpenScheme N m a t ⟶ infinityBranchScheme N m a t :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t)))

/-- The overlap inclusion is an open immersion. -/
instance infinityBranchOpenInclusion_isOpenImmersion (N m a : ℕ) (t : K) :
    IsOpenImmersion (infinityBranchOpenInclusion N m a t) :=
  IsOpenImmersion.of_isLocalization (infinityBranchU N m a t)

/-- Its image is exactly the principal open `D(u)` on the normalized chart. -/
theorem infinityBranchOpenInclusion_opensRange (N m a : ℕ) (t : K) :
    (infinityBranchOpenInclusion N m a t).opensRange =
      PrimeSpectrum.basicOpen (infinityBranchU N m a t) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (InfinityBranchOpen N m a t)
    (infinityBranchU N m a t)

/-- The structural map of the punctured normalized chart. -/
def infinityBranchOpenStructureMap (N m a : ℕ) (t : K) :
    infinityBranchOpenScheme N m a t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (InfinityBranchOpen N m a t)))

/-- Restriction to the overlap commutes with the coefficient-ring projection. -/
theorem infinityBranchOpenInclusion_structureMap (N m a : ℕ) (t : K) :
    infinityBranchOpenInclusion N m a t ≫ infinityBranchStructureMap N m a t =
      infinityBranchOpenStructureMap N m a t := by
  unfold infinityBranchOpenInclusion infinityBranchStructureMap
    infinityBranchOpenStructureMap
  erw [← Spec.map_comp]
  congr 1

/-- The overlap equivalence gives the actual affine Euler cover scheme. -/
def infinityBranchOpenIsoCover (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    infinityBranchOpenScheme N m a t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso
    (infinityBranchOpenEquivCover N m a b t hN hm hbezout).symm.toCommRingCatIso.op

/-- On functions the forward overlap isomorphism sends `x` to `u⁻¹` and
`y` to `(z^(N-m)/P^b)/u²`. -/
theorem infinityBranchOpenIsoCover_hom (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    (infinityBranchOpenIsoCover N m a b t hN hm hbezout).hom =
      Spec.map (CommRingCat.ofHom
        (coverToInfinityBranchOpen N m a b t hN hm hbezout)) := (rfl)

/-- The inverse overlap map sends `z` to `(y*u²)^a/u^b`. -/
theorem infinityBranchOpenIsoCover_inv (N m a b : ℕ) (t : K) (hN : N ≠ 0)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N) :
    (infinityBranchOpenIsoCover N m a b t hN hm hbezout).inv =
      Spec.map (CommRingCat.ofHom
        (infinityBranchOpenToCover N m a b t hN hm hbezout)) := (rfl)

/-- The overlap isomorphism preserves the projection to the coefficient ring. -/
theorem infinityBranchOpenIsoCover_structureMap (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    (infinityBranchOpenIsoCover N m a b t hN hm hbezout).hom ≫
      structureMap N m t = infinityBranchOpenStructureMap N m a t := by
  rw [infinityBranchOpenIsoCover_hom]
  change Spec.map (CommRingCat.ofHom
    (coverToInfinityBranchOpen N m a b t hN hm hbezout)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (CoverRing N m t))) = _
  erw [← Spec.map_comp]
  congr 1
  ext c
  change coverToInfinityBranchOpen N m a b t hN hm hbezout
    (algebraMap K (CoverRing N m t) c) =
      algebraMap K (InfinityBranchOpen N m a t) c
  exact (infinityBranchOpenAlgEquivCover N m a b t hN hm hbezout).symm.commutes c

/-- The forward overlap map sends the original projection coordinate to
`u⁻¹`. -/
theorem coverToInfinityBranchOpen_x (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    coverToInfinityBranchOpen N m a b t hN hm hbezout
      (algebraMap (BaseRing t) (CoverRing N m t)
        (coverBaseXUnit t : BaseRing t)) =
      ((infinityBranchOpenUUnit N m a t)⁻¹ :
        (InfinityBranchOpen N m a t)ˣ) := by
  rw [coverToInfinityBranchOpen_base, coverBaseToInfinityBranchOpen,
    RingHom.comp_apply, coverBaseToInfinityBaseOpen_x]
  have hu : Units.map (infinityBaseOpenToBranchOpen N m a t).toMonoidHom
      (infinityBaseOpenUUnit t) = infinityBranchOpenUUnit N m a t := by
    apply Units.ext
    change infinityBaseOpenToBranchOpen N m a t
      (infinityBaseOpenUUnit t : InfinityBaseOpen t) = _
    rw [infinityBaseOpenUUnit_val, infinityBaseOpenToBranchOpen_base]
    rfl
  calc
    infinityBaseOpenToBranchOpen N m a t
        (↑((infinityBaseOpenUUnit t)⁻¹) : InfinityBaseOpen t) =
      (↑((Units.map (infinityBaseOpenToBranchOpen N m a t).toMonoidHom
        ((infinityBaseOpenUUnit t)⁻¹)) :
          (InfinityBranchOpen N m a t)ˣ) : InfinityBranchOpen N m a t) := rfl
    _ = _ := by rw [map_inv, hu]

/-- The forward overlap map sends the original covering coordinate to
`(z^(N-m)/P^b)/u²`. -/
theorem coverToInfinityBranchOpen_y (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    coverToInfinityBranchOpen N m a b t hN hm hbezout (coverRoot N m t) =
      ((infinityBranchOpenRootUnit N m a t hN ^ (N - m) *
        (infinityBranchOpenPUnit N m a t)⁻¹ ^ b *
        (infinityBranchOpenUUnit N m a t)⁻¹ ^ 2 :
          (InfinityBranchOpen N m a t)ˣ) : InfinityBranchOpen N m a t) := by
  rw [coverToInfinityBranchOpen_root]
  rfl

/-- The inverse overlap map sends `z` to `(y u²)^a/u^b`. -/
theorem infinityBranchOpenToCover_z (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hm : m ≤ N)
    (hbezout : (N - m) * a = 1 + b * N) :
    infinityBranchOpenToCover N m a b t hN hm hbezout
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) =
      (((coverRootUnit N m t hN * infinityCoverUUnit N m t ^ 2) ^ a *
        (infinityCoverUUnit N m t)⁻¹ ^ b : (CoverRing N m t)ˣ) :
          CoverRing N m t) := by
  rw [infinityBranchOpenToCover_root]
  rfl

/-- Coefficient roots of unity scale the normalized infinity coordinate.
The original `y` character corresponds to the parameter `ζ^a` on `z`. -/
def infinityBranchDeckAlgebraAction (N m a : ℕ) [NeZero N] (t : K) :
    rootsOfUnity N K →* (InfinityBranchRing N m a t ≃ₐ[InfinityBaseRing t]
      InfinityBranchRing N m a t) :=
  (AdjoinRoot.rootScaling N
    (infinityBaseU t * (infinityBranchUnit N m t : InfinityBaseRing t) ^ a)).comp
      (rootsOfUnity.mapHom N
        ((algebraMap K[X] (InfinityBaseRing t)).comp Polynomial.C))

/-- The normalized infinity deck action fixes `u` and scales `z`. -/
theorem infinityBranchDeckAlgebraAction_root (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    infinityBranchDeckAlgebraAction N m a t ζ (infinityBranchRoot N m a t) =
      (algebraMap K[X] (InfinityBaseRing t) (C ((ζ : Kˣ) : K))) •
        infinityBranchRoot N m a t := by
  exact AdjoinRoot.rootScaling_root N
    (infinityBaseU t * (infinityBranchUnit N m t : InfinityBaseRing t) ^ a)
    (rootsOfUnity.mapHom N
      ((algebraMap K[X] (InfinityBaseRing t)).comp Polynomial.C) ζ)

/-- With deck parameter `ζ^a` on `z`, the substituted original coordinate
`v=y u²` has the original `ζ` character. -/
theorem infinityBranchDeckAlgebraAction_singularRoot (N m a b : ℕ) [NeZero N]
    (t : K) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    infinityBranchDeckAlgebraAction N m a t (ζ ^ a)
        (infinitySingularToBranch N m a b t hbezout
          (infinitySingularRoot N m t)) =
      ((ζ : Kˣ) : K) •
        infinitySingularToBranch N m a b t hbezout
          (infinitySingularRoot N m t) := by
  let d := infinityBranchDeckAlgebraAction N m a t (ζ ^ a)
  let u : InfinityBaseRing t :=
    ((infinityBranchUnit N m t)⁻¹ ^ b : (InfinityBaseRing t)ˣ)
  let c : K := (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K)
  have hc : algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t)
      (algebraMap K[X] (InfinityBaseRing t) (C c)) =
      algebraMap K (InfinityBranchRing N m a t) c := by
    rw [IsScalarTower.algebraMap_apply K (InfinityBaseRing t)
      (InfinityBranchRing N m a t) c]
    rfl
  rw [infinitySingularToBranch_root, map_mul, map_pow, d.commutes,
    infinityBranchDeckAlgebraAction_root]
  simp only [Algebra.smul_def]
  rw [hc, mul_pow]
  have hζ : c ^ (N - m) = ((ζ : Kˣ) : K) := by
    exact congrArg (fun w : rootsOfUnity N K => ((w : Kˣ) : K))
      (AdjoinRoot.rootsOfUnity_pow_bezout N (N - m) a b hbezout ζ)
  change (algebraMap K (InfinityBranchRing N m a t) c) ^ (N - m) *
      infinityBranchRoot N m a t ^ (N - m) *
        algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t) u =
    algebraMap K (InfinityBranchRing N m a t) (((ζ : Kˣ) : K)) *
      (infinityBranchRoot N m a t ^ (N - m) *
        algebraMap (InfinityBaseRing t) (InfinityBranchRing N m a t) u)
  rw [← map_pow, hζ]
  ring

/-- The normalized deck action on the infinity chart as a scheme map. -/
def infinityBranchDeckTransformation (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    infinityBranchScheme N m a t ≅ infinityBranchScheme N m a t :=
  Scheme.Spec.mapIso
    (infinityBranchDeckAlgebraAction N m a t ζ).toRingEquiv.toCommRingCatIso.op

/-- The normalized deck transformation preserves the coefficient-ring map. -/
theorem infinityBranchDeckTransformation_structureMap (N m a : ℕ) [NeZero N]
    (t : K) (ζ : rootsOfUnity N K) :
    (infinityBranchDeckTransformation N m a t ζ).hom ≫
      infinityBranchStructureMap N m a t = infinityBranchStructureMap N m a t := by
  unfold infinityBranchDeckTransformation infinityBranchStructureMap
  erw [← Spec.map_comp]
  congr 1
  ext c
  change infinityBranchDeckAlgebraAction N m a t ζ
      (algebraMap K (InfinityBranchRing N m a t) c) =
    algebraMap K (InfinityBranchRing N m a t) c
  rw [IsScalarTower.algebraMap_apply K (InfinityBaseRing t)
        (InfinityBranchRing N m a t) c]
  exact (infinityBranchDeckAlgebraAction N m a t ζ).commutes
    (algebraMap K (InfinityBaseRing t) c)

/-- Transport the original Euler deck transformation to the punctured
infinity chart through its actual overlap equivalence. -/
def infinityBranchOpenOriginalDeck (N m a b : ℕ) [NeZero N] (t : K)
    (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    InfinityBranchOpen N m a t ≃+* InfinityBranchOpen N m a t :=
  ((infinityBranchOpenEquivCover N m a b t (NeZero.ne N) hm hbezout).trans
    (deckAlgebraAction N m t ζ).toRingEquiv).trans
      (infinityBranchOpenEquivCover N m a b t (NeZero.ne N) hm hbezout).symm

/-- Under the overlap, the original deck action scales `y` once. -/
theorem infinityBranchOpenOriginalDeck_y (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
      (coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout
        (coverRoot N m t)) =
      (algebraMap K (InfinityBranchOpen N m a t) ((ζ : Kˣ) : K)) *
        coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout
          (coverRoot N m t) := by
  let e := infinityBranchOpenAlgEquivCover N m a b t (NeZero.ne N) hm hbezout
  let f := infinityBranchOpenEquivCover N m a b t (NeZero.ne N) hm hbezout
  have hroot : (deckAlgebraAction N m t ζ) (coverRoot N m t) =
      algebraMap K (CoverRing N m t) ((ζ : Kˣ) : K) * coverRoot N m t := by
    rw [deckAlgebraAction_root]
    simp only [Algebra.smul_def]
    congr 1
  calc
    infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
        (coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout
          (coverRoot N m t)) =
      f.symm ((deckAlgebraAction N m t ζ) (coverRoot N m t)) := by
        simp only [infinityBranchOpenOriginalDeck, RingEquiv.trans_apply]
        have hinv : coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout
            (coverRoot N m t) = f.symm (coverRoot N m t) := rfl
        rw [hinv, f.apply_symm_apply]
        rfl
    _ = f.symm (algebraMap K (CoverRing N m t) ((ζ : Kˣ) : K) *
        coverRoot N m t) := by rw [hroot]
    _ = algebraMap K (InfinityBranchOpen N m a t) ((ζ : Kˣ) : K) *
        coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout
          (coverRoot N m t) := by
        change e.symm (algebraMap K (CoverRing N m t) ((ζ : Kˣ) : K) *
          coverRoot N m t) = _
        rw [map_mul, e.symm.commutes]
        rfl

/-- On the actual Euler cover the original deck action fixes the inverse
projection coordinate `u=x⁻¹`. -/
theorem deckAlgebraAction_infinityCoverUUnit (N m : ℕ) [NeZero N]
    (t : K) (ζ : rootsOfUnity N K) :
    Units.map (deckAlgebraAction N m t ζ).toRingHom.toMonoidHom
      (infinityCoverUUnit N m t) = infinityCoverUUnit N m t := by
  apply Units.ext
  change deckAlgebraAction N m t ζ
      (infinityCoverUUnit N m t : CoverRing N m t) = _
  rw [infinityCoverUUnit_val]
  exact (deckAlgebraAction N m t ζ).commutes
    (↑((coverBaseXUnit t)⁻¹) : BaseRing t)

/-- The rescaled coordinate `v=y*u²` retains the original deck character. -/
theorem deckAlgebraAction_infinityCoverVUnit (N m : ℕ) [NeZero N]
    (t : K) (ζ : rootsOfUnity N K) :
    Units.map (deckAlgebraAction N m t ζ).toRingHom.toMonoidHom
      (infinityCoverVUnit N m t (NeZero.ne N)) =
      Units.map (algebraMap K (CoverRing N m t)).toMonoidHom (ζ : Kˣ) *
        infinityCoverVUnit N m t (NeZero.ne N) := by
  apply Units.ext
  change deckAlgebraAction N m t ζ
      (infinityCoverVUnit N m t (NeZero.ne N) : CoverRing N m t) =
      algebraMap K (CoverRing N m t) ((ζ : Kˣ) : K) *
        (infinityCoverVUnit N m t (NeZero.ne N) : CoverRing N m t)
  rw [infinityCoverVUnit_val, infinityCoverV, map_mul, map_pow]
  have hroot : (deckAlgebraAction N m t ζ) (coverRoot N m t) =
      algebraMap K (CoverRing N m t) ((ζ : Kˣ) : K) * coverRoot N m t := by
    rw [deckAlgebraAction_root]
    simp only [Algebra.smul_def]
    congr 1
  rw [hroot]
  have hu := congrArg Units.val
    (deckAlgebraAction_infinityCoverUUnit N m t ζ)
  change deckAlgebraAction N m t ζ
      (infinityCoverUUnit N m t : CoverRing N m t) = _ at hu
  rw [hu]
  ring

/-- On the punctured infinity chart the original `y` deck action sends the
normalized coordinate `z=(y*u²)^a/u^b` to `ζ^a z`. -/
theorem infinityBranchOpenOriginalDeck_z (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) =
      algebraMap K (InfinityBranchOpen N m a t) (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) *
        algebraMap (InfinityBranchRing N m a t)
          (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t) := by
  let f := infinityBranchOpenAlgEquivCover N m a b t (NeZero.ne N) hm hbezout
  let d := (deckAlgebraAction N m t ζ).toRingHom
  let s : (CoverRing N m t)ˣ :=
    Units.map (algebraMap K (CoverRing N m t)).toMonoidHom (ζ : Kˣ)
  have hv : Units.map d.toMonoidHom
      (infinityCoverVUnit N m t (NeZero.ne N)) =
        s * infinityCoverVUnit N m t (NeZero.ne N) :=
    deckAlgebraAction_infinityCoverVUnit N m t ζ
  have hu : Units.map d.toMonoidHom (infinityCoverUUnit N m t) =
      infinityCoverUUnit N m t :=
    deckAlgebraAction_infinityCoverUUnit N m t ζ
  have hcoord : Units.map d.toMonoidHom
      (infinityCoverVUnit N m t (NeZero.ne N) ^ a *
        (infinityCoverUUnit N m t)⁻¹ ^ b) =
      s ^ a * (infinityCoverVUnit N m t (NeZero.ne N) ^ a *
        (infinityCoverUUnit N m t)⁻¹ ^ b) := by
    simp only [map_mul, map_pow, map_inv, hv, hu, mul_pow]
    group
  have hcoord' := congrArg Units.val hcoord
  simp only [Units.coe_map, Units.val_mul, Units.val_pow_eq_pow_val] at hcoord'
  have hc : (s : CoverRing N m t) ^ a =
      algebraMap K (CoverRing N m t)
        (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) := by
    change (algebraMap K (CoverRing N m t) ((ζ : Kˣ) : K)) ^ a = _
    rw [← map_pow]
    rfl
  rw [hc] at hcoord'
  have hd (w : CoverRing N m t) : d w =
      (deckAlgebraAction N m t ζ) w := rfl
  change d (infinityInverseBranchCoordinate N m a b t (NeZero.ne N)) =
    algebraMap K (CoverRing N m t)
      (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) *
      infinityInverseBranchCoordinate N m a b t (NeZero.ne N) at hcoord'
  have hcoordD : d
      (infinityInverseBranchCoordinate N m a b t (NeZero.ne N)) =
    algebraMap K (CoverRing N m t)
      (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) *
      infinityInverseBranchCoordinate N m a b t (NeZero.ne N) := hcoord'
  have hcoord'' : (deckAlgebraAction N m t ζ)
      (infinityInverseBranchCoordinate N m a b t (NeZero.ne N)) =
    algebraMap K (CoverRing N m t)
      (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) *
      infinityInverseBranchCoordinate N m a b t (NeZero.ne N) := by
    exact (hd _).symm.trans hcoordD
  have htransport : f
      (infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
        (algebraMap (InfinityBranchRing N m a t)
          (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t))) =
      f (algebraMap K (InfinityBranchOpen N m a t)
          (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) *
        algebraMap (InfinityBranchRing N m a t)
          (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) := by
    simp only [infinityBranchOpenOriginalDeck, RingEquiv.trans_apply,
      map_mul, f.commutes]
    change f (f.symm ((deckAlgebraAction N m t ζ)
      (f (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t))))) = _
    rw [f.apply_symm_apply]
    change (deckAlgebraAction N m t ζ)
        (infinityBranchOpenToCover N m a b t (NeZero.ne N) hm hbezout
          (algebraMap (InfinityBranchRing N m a t)
            (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t))) =
      algebraMap K (CoverRing N m t)
        (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) *
        infinityBranchOpenToCover N m a b t (NeZero.ne N) hm hbezout
          (algebraMap (InfinityBranchRing N m a t)
            (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t))
    rw [infinityBranchOpenToCover_root]
    exact hcoord''
  exact f.injective htransport

/-- The normalized deck action fixes the inverse projection coordinate. -/
theorem infinityBranchDeckAlgebraAction_u (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    infinityBranchDeckAlgebraAction N m a t ζ (infinityBranchU N m a t) =
      infinityBranchU N m a t := by
  exact (infinityBranchDeckAlgebraAction N m a t ζ).commutes (infinityBaseU t)

/-- Restriction of the normalized deck action to the punctured infinity chart. -/
def infinityBranchOpenDeckAction (N m a : ℕ) [NeZero N] (t : K)
    (ζ : rootsOfUnity N K) :
    InfinityBranchOpen N m a t →+* InfinityBranchOpen N m a t :=
  Localization.awayLift
    ((algebraMap (InfinityBranchRing N m a t)
      (InfinityBranchOpen N m a t)).comp
        (infinityBranchDeckAlgebraAction N m a t ζ).toRingHom)
    (infinityBranchU N m a t) (by
      change IsUnit (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t)
          (infinityBranchDeckAlgebraAction N m a t ζ
            (infinityBranchU N m a t)))
      rw [infinityBranchDeckAlgebraAction_u]
      exact (infinityBranchOpenUUnit N m a t).isUnit)

@[simp] theorem infinityBranchOpenDeckAction_of (N m a : ℕ) [NeZero N]
    (t : K) (ζ : rootsOfUnity N K) (w : InfinityBranchRing N m a t) :
    infinityBranchOpenDeckAction N m a t ζ
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) w) =
      algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t)
          (infinityBranchDeckAlgebraAction N m a t ζ w) := by
  simp [infinityBranchOpenDeckAction, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The localized normalized deck action scales the normalized root. -/
theorem infinityBranchOpenDeckAction_root (N m a : ℕ) [NeZero N]
    (t : K) (ζ : rootsOfUnity N K) :
    infinityBranchOpenDeckAction N m a t ζ
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) =
      algebraMap K (InfinityBranchOpen N m a t) ((ζ : Kˣ) : K) *
        algebraMap (InfinityBranchRing N m a t)
          (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t) := by
  rw [infinityBranchOpenDeckAction_of,
    infinityBranchDeckAlgebraAction_root]
  simp only [Algebra.smul_def, map_mul]
  congr 1

/-- The transported original deck action fixes the entire inverse-coordinate base. -/
theorem infinityBranchOpenOriginalDeck_base (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) (w : InfinityBaseRing t) :
    infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
      (infinityBaseToBranchOpen N m a t w) =
        infinityBaseToBranchOpen N m a t w := by
  let f := infinityBranchOpenEquivCover N m a b t (NeZero.ne N) hm hbezout
  apply f.injective
  change f (f.symm ((deckAlgebraAction N m t ζ)
    (f (infinityBaseToBranchOpen N m a t w)))) =
      f (infinityBaseToBranchOpen N m a t w)
  rw [f.apply_symm_apply]
  change (deckAlgebraAction N m t ζ)
      (infinityBranchOpenToCover N m a b t (NeZero.ne N) hm hbezout
        (infinityBaseToBranchOpen N m a t w)) =
      infinityBranchOpenToCover N m a b t (NeZero.ne N) hm hbezout
        (infinityBaseToBranchOpen N m a t w)
  rw [infinityBranchOpenToCover_base]
  exact (deckAlgebraAction N m t ζ).commutes
    (infinityBaseToCoverBase t w)

/-- Restricting `z ↦ ζ^a z` to `D(u)` gives the original action `y ↦ ζ y`
under the actual Euler-cover overlap. This identifies the whole ring action,
not just its values on the two coordinates. -/
theorem infinityBranchOpenDeckAction_original (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    infinityBranchOpenDeckAction N m a t (ζ ^ a) =
      (infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ).toRingHom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (infinityBranchU N m a t))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro w
    change infinityBranchOpenDeckAction N m a t (ζ ^ a)
      (infinityBaseToBranchOpen N m a t w) =
        infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
          (infinityBaseToBranchOpen N m a t w)
    rw [infinityBranchOpenOriginalDeck_base]
    change infinityBranchOpenDeckAction N m a t (ζ ^ a)
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t)
          (algebraMap (InfinityBaseRing t)
            (InfinityBranchRing N m a t) w)) = _
    rw [infinityBranchOpenDeckAction_of]
    exact congrArg (algebraMap (InfinityBranchRing N m a t)
      (InfinityBranchOpen N m a t))
        ((infinityBranchDeckAlgebraAction N m a t (ζ ^ a)).commutes w)
  · change infinityBranchOpenDeckAction N m a t (ζ ^ a)
      (algebraMap (InfinityBranchRing N m a t)
        (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t)) =
        infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ
          (algebraMap (InfinityBranchRing N m a t)
            (InfinityBranchOpen N m a t) (infinityBranchRoot N m a t))
    rw [infinityBranchOpenDeckAction_root,
      infinityBranchOpenOriginalDeck_z]

/-- The original deck transformation on the punctured infinity chart. -/
def infinityBranchOpenDeckTransformation (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    infinityBranchOpenScheme N m a t ≅ infinityBranchOpenScheme N m a t :=
  Scheme.Spec.mapIso
    (infinityBranchOpenOriginalDeck N m a b t hm hbezout ζ).toCommRingCatIso.op

/-- Its forward map is the localization of `z ↦ ζ^a z`. -/
theorem infinityBranchOpenDeckTransformation_hom (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    (infinityBranchOpenDeckTransformation N m a b t hm hbezout ζ).hom =
      Spec.map (CommRingCat.ofHom
        (infinityBranchOpenDeckAction N m a t (ζ ^ a))) := by
  rw [infinityBranchOpenDeckAction_original N m a b t hm hbezout ζ]
  rfl

/-- The chart deck transformation restricts to the punctured infinity chart. -/
theorem infinityBranchOpenDeckTransformation_inclusion (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    (infinityBranchOpenDeckTransformation N m a b t hm hbezout ζ).hom ≫
        infinityBranchOpenInclusion N m a t =
      infinityBranchOpenInclusion N m a t ≫
        (infinityBranchDeckTransformation N m a t (ζ ^ a)).hom := by
  rw [infinityBranchOpenDeckTransformation_hom]
  change Spec.map (CommRingCat.ofHom (infinityBranchOpenDeckAction N m a t (ζ ^ a))) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t))) =
    Spec.map (CommRingCat.ofHom
        (algebraMap (InfinityBranchRing N m a t) (InfinityBranchOpen N m a t))) ≫
      Spec.map (CommRingCat.ofHom
        (infinityBranchDeckAlgebraAction N m a t (ζ ^ a)).toRingHom)
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (by
    apply RingHom.ext
    intro w
    exact infinityBranchOpenDeckAction_of N m a t (ζ ^ a) w)

/-- On the actual Euler-cover overlap, the chart action is the original
`y ↦ ζ y` deck transformation. -/
theorem infinityBranchOpenDeckTransformation_cover (N m a b : ℕ) [NeZero N]
    (t : K) (hm : m ≤ N) (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    (infinityBranchOpenDeckTransformation N m a b t hm hbezout ζ).hom ≫
        (infinityBranchOpenIsoCover N m a b t (NeZero.ne N) hm hbezout).hom =
      (infinityBranchOpenIsoCover N m a b t (NeZero.ne N) hm hbezout).hom ≫
        (deckTransformation N m t ζ).hom := by
  rw [infinityBranchOpenDeckTransformation_hom,
    infinityBranchOpenIsoCover_hom, deckTransformation_hom]
  erw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (by
    apply RingHom.ext
    intro w
    change infinityBranchOpenDeckAction N m a t (ζ ^ a)
        (coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout w) =
      coverToInfinityBranchOpen N m a b t (NeZero.ne N) hm hbezout
        (deckAlgebraAction N m t ζ w)
    rw [infinityBranchOpenDeckAction_original]
    let f := infinityBranchOpenEquivCover N m a b t (NeZero.ne N) hm hbezout
    change f.symm ((deckAlgebraAction N m t ζ) (f (f.symm w))) =
      f.symm ((deckAlgebraAction N m t ζ) w)
    rw [f.apply_symm_apply])


end HilbertModularity.Hypergeometric.EulerCover
