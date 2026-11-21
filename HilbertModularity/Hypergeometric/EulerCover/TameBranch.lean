/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.ZeroBranch

/-! # A tame branch chart for a localized Kummer cover

Let `u` be the affine-line coordinate, and let `U` be a unit on a principal
open of the line. A branch of exponent `r` in `v^N = u^r U` has the smooth
coordinate `z^N = u U^a` when `r a = 1 + b N`. The original deck action on
`v` consequently acts on `z` through its `a`-th power. This is the local
construction used at the branch sections of
[TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [CommRing K]

/-- The principal-open base of a tame branch chart. -/
abbrev TameBaseRing (g : K[X]) := Localization.Away g

/-- The branch coordinate on the principal-open base. -/
def tameBaseX (g : K[X]) : TameBaseRing g :=
  algebraMap K[X] (TameBaseRing g) X

/-- The invertible polynomial factor on the branch base. -/
def tameBaseUnit (g P : K[X])
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (TameBaseRing g)ˣ := hP.unit

@[simp] theorem tameBaseUnit_val (g P : K[X])
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (tameBaseUnit g P hP : TameBaseRing g) =
      algebraMap K[X] (TameBaseRing g) P := by
  simp [tameBaseUnit]

/-- The normalized radicand before localization. -/
def tameBranchRadicand (P : K[X]) (a : ℕ) : K[X] := X * P ^ a

/-- The original radicand before normalization. -/
def tameSingularRadicand (P : K[X]) (r : ℕ) : K[X] := X ^ r * P

/-- The actual normalized root algebra `z^N = u U^a`. -/
abbrev TameBranchRing (g P : K[X]) (N a : ℕ) :=
  RingTheory.Smooth.localizedKummerAlgebra g (tameBranchRadicand P a) N

/-- The actual singular root algebra `v^N = u^r U`. -/
abbrev TameSingularRing (g P : K[X]) (N r : ℕ) :=
  RingTheory.Smooth.localizedKummerAlgebra g (tameSingularRadicand P r) N

/-- The retained branch coordinate in the normalized ring. -/
def tameBranchX (g P : K[X]) (N a : ℕ) : TameBranchRing g P N a :=
  RingTheory.Smooth.localizedKummerX g (tameBranchRadicand P a) N

/-- The normalized covering coordinate. -/
def tameBranchRoot (g P : K[X]) (N a : ℕ) : TameBranchRing g P N a :=
  RingTheory.Smooth.localizedKummerZ g (tameBranchRadicand P a) N

/-- The retained branch coordinate in the original singular ring. -/
def tameSingularX (g P : K[X]) (N r : ℕ) : TameSingularRing g P N r :=
  RingTheory.Smooth.localizedKummerX g (tameSingularRadicand P r) N

/-- The original covering coordinate. -/
def tameSingularRoot (g P : K[X]) (N r : ℕ) : TameSingularRing g P N r :=
  RingTheory.Smooth.localizedKummerZ g (tameSingularRadicand P r) N

private theorem tame_aeval_X {Q : K[X]} (g : K[X]) (N : ℕ) (H : K[X]) :
    aeval (RingTheory.Smooth.localizedKummerX g Q N) H =
      algebraMap K[X] (RingTheory.Smooth.localizedKummerAlgebra g Q N) H := by
  let f : K[X] →ₐ[K] TameBaseRing g :=
    IsScalarTower.toAlgHom K K[X] (TameBaseRing g)
  let h : TameBaseRing g →ₐ[K] RingTheory.Smooth.localizedKummerAlgebra g Q N :=
    IsScalarTower.toAlgHom K (TameBaseRing g)
      (RingTheory.Smooth.localizedKummerAlgebra g Q N)
  have hf (p : K[X]) : aeval (tameBaseX g) p = f p := by
    change aeval (f X) p = f p
    rw [Polynomial.aeval_def]
    exact Polynomial.eval₂_algebraMap_X p f
  calc
    aeval (RingTheory.Smooth.localizedKummerX g Q N) H =
        h (aeval (tameBaseX g) H) := by
      exact Polynomial.aeval_algHom_apply h _ H
    _ = h (f H) := by rw [hf]
    _ = algebraMap K[X] (RingTheory.Smooth.localizedKummerAlgebra g Q N) H := by
      exact (IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
        (RingTheory.Smooth.localizedKummerAlgebra g Q N) H).symm

/-- The normalized root equation in its actual coordinate algebra. -/
theorem tameBranchRoot_pow (g P : K[X]) (N a : ℕ) :
    tameBranchRoot g P N a ^ N =
      tameBranchX g P N a *
        (algebraMap K[X] (TameBranchRing g P N a) P) ^ a := by
  calc
    tameBranchRoot g P N a ^ N =
        algebraMap (TameBaseRing g) (TameBranchRing g P N a)
          (algebraMap K[X] (TameBaseRing g) (tameBranchRadicand P a)) :=
      AdjoinRoot.root_X_pow_sub_C_pow N _
    _ = algebraMap K[X] (TameBranchRing g P N a)
          (tameBranchRadicand P a) :=
      (IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
        (TameBranchRing g P N a) _).symm
    _ = _ := by
      simp only [tameBranchRadicand, map_mul, map_pow]
      rfl

/-- The original root equation in its actual coordinate algebra. -/
theorem tameSingularRoot_pow (g P : K[X]) (N r : ℕ) :
    tameSingularRoot g P N r ^ N =
      tameSingularX g P N r ^ r *
        algebraMap K[X] (TameSingularRing g P N r) P := by
  calc
    tameSingularRoot g P N r ^ N =
        algebraMap (TameBaseRing g) (TameSingularRing g P N r)
          (algebraMap K[X] (TameBaseRing g) (tameSingularRadicand P r)) :=
      AdjoinRoot.root_X_pow_sub_C_pow N _
    _ = algebraMap K[X] (TameSingularRing g P N r)
          (tameSingularRadicand P r) :=
      (IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
        (TameSingularRing g P N r) _).symm
    _ = _ := by
      simp only [tameSingularRadicand, map_mul, map_pow]
      rfl

/-- The two partial derivatives of the normalized equation generate one.
This identity includes the ramification point `u=z=0`. -/
theorem tameBranch_jacobian (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    ∃ p q : TameBranchRing g P N a,
      p * aeval (tameBranchX g P N a) (tameBranchRadicand P a).derivative +
        q * (N : TameBranchRing g P N a) *
          tameBranchRoot g P N a ^ (N - 1) = 1 := by
  let S := TameBranchRing g P N a
  let x : S := tameBranchX g P N a
  let z : S := tameBranchRoot g P N a
  let u : Sˣ := (Units.map (algebraMap (TameBaseRing g) S).toMonoidHom
    (tameBaseUnit g P hP)) ^ a
  let n : Sˣ := Units.map (algebraMap K S).toMonoidHom hn.unit
  let v : S := aeval x (P ^ a).derivative
  have hu : (u : S) = (algebraMap K[X] S P) ^ a := by
    simp [u, tameBaseUnit_val, IsScalarTower.algebraMap_apply K[X] (TameBaseRing g) S]
  have hn' : (n : S) = (N : S) := by
    calc
      (n : S) = algebraMap K S (hn.unit : K) := by simp [n]
      _ = algebraMap K S (N : K) := congrArg (algebraMap K S) hn.unit_spec
      _ = (N : S) := by simp
  have hz : z ^ N = x * (u : S) := by
    rw [tameBranchRoot_pow, hu]
  have hd : aeval x (tameBranchRadicand P a).derivative =
      (u : S) + x * v := by
    have hp : aeval x P = algebraMap K[X] S P := by
      exact tame_aeval_X (Q := tameBranchRadicand P a) g N P
    change aeval x (X * P ^ a).derivative = _
    rw [derivative_mul]
    simp only [derivative_X, one_mul, map_add, map_mul, aeval_X]
    rw [map_pow, hp, ← hu]
  have h := euler_jacobian_bezout u n x z v N hN hz
  refine ⟨(u⁻¹ : Sˣ),
    -((u⁻¹ : Sˣ) ^ 2 : S) * v * z * (n⁻¹ : Sˣ), ?_⟩
  rw [← hd, hn'] at h
  simpa only [sub_eq_add_neg, neg_mul, mul_assoc] using h

/-- The normalized local tame branch is smooth over the coefficient ring. -/
theorem tameBranchRing_smooth (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Algebra.Smooth K (TameBranchRing g P N a) := by
  obtain ⟨p, q, hjac⟩ := tameBranch_jacobian g P N a hP hN hn
  exact RingTheory.Smooth.smooth_localizedKummer g
    (tameBranchRadicand P a) N hN p q
    (by simpa only [tameBranchX, tameBranchRoot] using hjac)

/-- The singular branch maps to its smooth chart by `v ↦ z^r/U^b`. -/
def tameSingularToBranch (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    TameSingularRing g P N r →ₐ[TameBaseRing g] TameBranchRing g P N a := by
  let u : (TameBranchRing g P N a)ˣ :=
    Units.map (algebraMap (TameBaseRing g) (TameBranchRing g P N a)).toMonoidHom
      (tameBaseUnit g P hP)
  let v : TameBranchRing g P N a :=
    tameBranchRoot g P N a ^ r * (u⁻¹ ^ b : _)
  have hu : (u : TameBranchRing g P N a) =
      algebraMap K[X] (TameBranchRing g P N a) P := by
    simp [u, tameBaseUnit_val,
      IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
        (TameBranchRing g P N a)]
  have hz : tameBranchRoot g P N a ^ N =
      tameBranchX g P N a * (u : TameBranchRing g P N a) ^ a := by
    rw [tameBranchRoot_pow, hu]
  apply AdjoinRoot.liftAlgHom
    (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N)
    (Algebra.ofId (TameBaseRing g) _) v
  change aeval v
    (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N) = 0
  simp only [RingTheory.Smooth.localizedKummerEquation, map_sub, map_pow,
    aeval_X, aeval_C]
  rw [sub_eq_zero]
  dsimp only [v]
  rw [← IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
    (TameBranchRing g P N a)]
  simp only [tameSingularRadicand, map_mul, map_pow]
  change _ = tameBranchX g P N a ^ r *
    algebraMap K[X] (TameBranchRing g P N a) P
  rw [← hu]
  exact eulerRoot_pow_bezout u (tameBranchX g P N a)
    (tameBranchRoot g P N a) N r a b hbezout hz

@[simp] theorem tameSingularToBranch_root (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    tameSingularToBranch g P N r a b hP hbezout (tameSingularRoot g P N r) =
      tameBranchRoot g P N a ^ r *
        algebraMap (TameBaseRing g) (TameBranchRing g P N a)
          (((tameBaseUnit g P hP)⁻¹ ^ b : (TameBaseRing g)ˣ) : TameBaseRing g) := by
  unfold tameSingularToBranch tameSingularRoot
  rw [AdjoinRoot.liftAlgHom_root]
  simp [map_pow]

@[simp] theorem tameSingularToBranch_x (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    tameSingularToBranch g P N r a b hP hbezout
      (tameSingularX g P N r) = tameBranchX g P N a := by
  simp [tameSingularToBranch, tameSingularX, tameBranchX,
    RingTheory.Smooth.localizedKummerX,
    IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
      (TameBranchRing g P N a)]

/-- The normalized branch chart restricted to the principal open `u ≠ 0`. -/
abbrev TameBranchOpen (g P : K[X]) (N a : ℕ) :=
  Localization.Away (tameBranchX g P N a)

/-- The singular branch chart restricted to the same principal open. -/
abbrev TameSingularOpen (g P : K[X]) (N r : ℕ) :=
  Localization.Away (tameSingularX g P N r)

/-- The invertible base coordinate on the normalized overlap. -/
def tameBranchOpenXUnit (g P : K[X]) (N a : ℕ) :
    (TameBranchOpen g P N a)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (tameBranchX g P N a)).unit

@[simp] theorem tameBranchOpenXUnit_val (g P : K[X]) (N a : ℕ) :
    (tameBranchOpenXUnit g P N a : TameBranchOpen g P N a) =
      algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchX g P N a) := by
  simp [tameBranchOpenXUnit]

/-- The invertible base coordinate on the singular overlap. -/
def tameSingularOpenXUnit (g P : K[X]) (N r : ℕ) :
    (TameSingularOpen g P N r)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (tameSingularX g P N r)).unit

@[simp] theorem tameSingularOpenXUnit_val (g P : K[X]) (N r : ℕ) :
    (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) =
      algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularX g P N r) := by
  simp [tameSingularOpenXUnit]

/-- The unit factor on the normalized principal-open overlap. -/
def tameBranchOpenUUnit (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (TameBranchOpen g P N a)ˣ :=
  Units.map (algebraMap (TameBaseRing g) (TameBranchOpen g P N a)).toMonoidHom
    (tameBaseUnit g P hP)

/-- The unit factor on the singular principal-open overlap. -/
def tameSingularOpenUUnit (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (TameSingularOpen g P N r)ˣ :=
  Units.map (algebraMap (TameBaseRing g) (TameSingularOpen g P N r)).toMonoidHom
    (tameBaseUnit g P hP)

@[simp] theorem tameBranchOpenUUnit_val (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (tameBranchOpenUUnit g P N a hP : TameBranchOpen g P N a) =
      algebraMap K[X] (TameBranchOpen g P N a) P := by
  simp [tameBranchOpenUUnit, tameBaseUnit_val,
    IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
      (TameBranchOpen g P N a)]

@[simp] theorem tameSingularOpenUUnit_val (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (tameSingularOpenUUnit g P N r hP : TameSingularOpen g P N r) =
      algebraMap K[X] (TameSingularOpen g P N r) P := by
  simp [tameSingularOpenUUnit, tameBaseUnit_val,
    IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
      (TameSingularOpen g P N r)]

/-- The normalized equation in the unit group on `u ≠ 0`. -/
theorem tameBranchOpenRoot_pow (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchRoot g P N a)) ^ N =
      (tameBranchOpenXUnit g P N a : TameBranchOpen g P N a) *
        (tameBranchOpenUUnit g P N a hP : TameBranchOpen g P N a) ^ a := by
  rw [← map_pow, tameBranchRoot_pow, map_mul, map_pow]
  rw [tameBranchOpenXUnit_val, tameBranchOpenUUnit_val]
  rw [IsScalarTower.algebraMap_apply K[X] (TameBranchRing g P N a)
    (TameBranchOpen g P N a) P]

/-- The singular equation in the unit group on `u ≠ 0`. -/
theorem tameSingularOpenRoot_pow (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) :
    (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularRoot g P N r)) ^ N =
      (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) ^ r *
        (tameSingularOpenUUnit g P N r hP : TameSingularOpen g P N r) := by
  rw [← map_pow, tameSingularRoot_pow, map_mul, map_pow]
  simp [tameSingularOpenXUnit_val, tameSingularOpenUUnit, tameBaseUnit_val,
    tameSingularX, RingTheory.Smooth.localizedKummerX,
    IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
      (TameSingularRing g P N r),
    IsScalarTower.algebraMap_apply (TameBaseRing g)
      (TameSingularRing g P N r) (TameSingularOpen g P N r)]

/-- The normalized root is a unit after inverting the branch coordinate. -/
theorem isUnit_tameBranchOpenRoot (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    IsUnit (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
      (tameBranchRoot g P N a)) := by
  apply (isUnit_pow_iff hN).mp
  rw [tameBranchOpenRoot_pow g P N a hP]
  exact (tameBranchOpenXUnit g P N a).isUnit.mul
    ((tameBranchOpenUUnit g P N a hP).isUnit.pow a)

/-- The singular root is a unit after inverting the branch coordinate. -/
theorem isUnit_tameSingularOpenRoot (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    IsUnit (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
      (tameSingularRoot g P N r)) := by
  apply (isUnit_pow_iff hN).mp
  rw [tameSingularOpenRoot_pow g P N r hP]
  exact ((tameSingularOpenXUnit g P N r).isUnit.pow r).mul
    (tameSingularOpenUUnit g P N r hP).isUnit

/-- The normalized covering coordinate as a unit on the overlap. -/
def tameBranchOpenRootUnit (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    (TameBranchOpen g P N a)ˣ :=
  (isUnit_tameBranchOpenRoot g P N a hP hN).unit

@[simp] theorem tameBranchOpenRootUnit_val (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    (tameBranchOpenRootUnit g P N a hP hN : TameBranchOpen g P N a) =
      algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchRoot g P N a) := by
  simp [tameBranchOpenRootUnit]

/-- The original covering coordinate as a unit on the singular overlap. -/
def tameSingularOpenRootUnit (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    (TameSingularOpen g P N r)ˣ :=
  (isUnit_tameSingularOpenRoot g P N r hP hN).unit

@[simp] theorem tameSingularOpenRootUnit_val (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    (tameSingularOpenRootUnit g P N r hP hN : TameSingularOpen g P N r) =
      algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularRoot g P N r) := by
  simp [tameSingularOpenRootUnit]

/-- The normalized root equation as an equality of overlap units. -/
theorem tameBranchOpenRootUnit_pow (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    tameBranchOpenRootUnit g P N a hP hN ^ N =
      tameBranchOpenXUnit g P N a * tameBranchOpenUUnit g P N a hP ^ a := by
  apply Units.ext
  change (tameBranchOpenRootUnit g P N a hP hN : TameBranchOpen g P N a) ^ N =
    (tameBranchOpenXUnit g P N a : TameBranchOpen g P N a) *
      (tameBranchOpenUUnit g P N a hP : TameBranchOpen g P N a) ^ a
  rw [tameBranchOpenRootUnit_val]
  exact tameBranchOpenRoot_pow g P N a hP

/-- The singular root equation as an equality of overlap units. -/
theorem tameSingularOpenRootUnit_pow (g P : K[X]) (N r : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    tameSingularOpenRootUnit g P N r hP hN ^ N =
      tameSingularOpenXUnit g P N r ^ r * tameSingularOpenUUnit g P N r hP := by
  apply Units.ext
  change (tameSingularOpenRootUnit g P N r hP hN : TameSingularOpen g P N r) ^ N =
    (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) ^ r *
      (tameSingularOpenUUnit g P N r hP : TameSingularOpen g P N r)
  rw [tameSingularOpenRootUnit_val]
  exact tameSingularOpenRoot_pow g P N r hP

/-- On the punctured singular chart, the inverse normalized coordinate is
`z=v^a/u^b`. -/
def tameInverseBranchCoordinate (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0) :
    TameSingularOpen g P N r :=
  ((tameSingularOpenRootUnit g P N r hP hN ^ a *
      (tameSingularOpenXUnit g P N r)⁻¹ ^ b :
      (TameSingularOpen g P N r)ˣ) : TameSingularOpen g P N r)

/-- The inverse coordinate satisfies the normalized equation. -/
theorem tameInverseBranchCoordinate_pow (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameInverseBranchCoordinate g P N r a b hP hN ^ N =
      algebraMap (TameBaseRing g) (TameSingularOpen g P N r)
        (algebraMap K[X] (TameBaseRing g) (tameBranchRadicand P a)) := by
  have h := congrArg Units.val
    (eulerUnit_inverse_root (tameSingularOpenXUnit g P N r)
      (tameSingularOpenUUnit g P N r hP)
      (tameSingularOpenRootUnit g P N r hP hN)
      N r a b hbezout (tameSingularOpenRootUnit_pow g P N r hP hN))
  change tameInverseBranchCoordinate g P N r a b hP hN ^ N =
    (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) *
      (tameSingularOpenUUnit g P N r hP : TameSingularOpen g P N r) ^ a at h
  rw [h]
  simp [tameBranchRadicand, tameSingularOpenXUnit_val,
    tameSingularOpenUUnit_val, tameSingularX,
    RingTheory.Smooth.localizedKummerX,
    IsScalarTower.algebraMap_apply K[X] (TameBaseRing g)
      (TameSingularOpen g P N r),
    IsScalarTower.algebraMap_apply (TameBaseRing g)
      (TameSingularRing g P N r) (TameSingularOpen g P N r)]

/-- The normalized root algebra restricts to the punctured singular chart,
with the coordinate formula `z=v^a/u^b`. -/
def tameBranchToSingularOpen (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    TameBranchRing g P N a →ₐ[TameBaseRing g] TameSingularOpen g P N r := by
  apply AdjoinRoot.liftAlgHom
    (RingTheory.Smooth.localizedKummerEquation g (tameBranchRadicand P a) N)
    (Algebra.ofId (TameBaseRing g) _)
    (tameInverseBranchCoordinate g P N r a b hP hN)
  simp only [RingTheory.Smooth.localizedKummerEquation, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_C, sub_eq_zero]
  exact tameInverseBranchCoordinate_pow g P N r a b hP hN hbezout

@[simp] theorem tameBranchToSingularOpen_root (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameBranchToSingularOpen g P N r a b hP hN hbezout
      (tameBranchRoot g P N a) =
        tameInverseBranchCoordinate g P N r a b hP hN := by
  simp [tameBranchToSingularOpen, tameBranchRoot]

@[simp] theorem tameBranchToSingularOpen_x (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameBranchToSingularOpen g P N r a b hP hN hbezout
      (tameBranchX g P N a) =
        (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) := by
  change (tameBranchToSingularOpen g P N r a b hP hN hbezout)
      (algebraMap (TameBaseRing g) (TameBranchRing g P N a) (tameBaseX g)) =
    algebraMap (TameBaseRing g) (TameSingularOpen g P N r) (tameBaseX g)
  exact (tameBranchToSingularOpen g P N r a b hP hN hbezout).commutes (tameBaseX g)

/-- Restrict the normalized-to-singular map to `u ≠ 0`. -/
def tameBranchOpenToSingularOpen (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    TameBranchOpen g P N a →+* TameSingularOpen g P N r :=
  Localization.awayLift
    (tameBranchToSingularOpen g P N r a b hP hN hbezout).toRingHom
    (tameBranchX g P N a) (by
      change IsUnit (tameBranchToSingularOpen g P N r a b hP hN hbezout
        (tameBranchX g P N a))
      rw [tameBranchToSingularOpen_x]
      exact (tameSingularOpenXUnit g P N r).isUnit)

/-- Restrict the singular-to-normalized map to `u ≠ 0`. -/
def tameSingularOpenToBranchOpen (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    TameSingularOpen g P N r →+* TameBranchOpen g P N a :=
  Localization.awayLift
    ((algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)).comp
      (tameSingularToBranch g P N r a b hP hbezout).toRingHom)
    (tameSingularX g P N r) (by
      change IsUnit (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameSingularToBranch g P N r a b hP hbezout (tameSingularX g P N r)))
      rw [tameSingularToBranch_x]
      simpa only [tameBranchOpenXUnit_val] using
        (tameBranchOpenXUnit g P N a).isUnit)

/-- The inverse overlap map fixes the localized base. -/
@[simp] theorem tameBranchOpenToSingularOpen_base (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) (v : TameBaseRing g) :
    tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (algebraMap (TameBaseRing g) (TameBranchOpen g P N a) v) =
        algebraMap (TameBaseRing g) (TameSingularOpen g P N r) v := by
  change tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
    (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
      (algebraMap (TameBaseRing g) (TameBranchRing g P N a) v)) = _
  simp [tameBranchOpenToSingularOpen, tameBranchToSingularOpen,
    IsLocalization.Away.lift_eq, AdjoinRoot.lift_of]

/-- The forward overlap map fixes the localized base. -/
@[simp] theorem tameSingularOpenToBranchOpen_base (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) (v : TameBaseRing g) :
    tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (algebraMap (TameBaseRing g) (TameSingularOpen g P N r) v) =
        algebraMap (TameBaseRing g) (TameBranchOpen g P N a) v := by
  change tameSingularOpenToBranchOpen g P N r a b hP hbezout
    (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
      (algebraMap (TameBaseRing g) (TameSingularRing g P N r) v)) = _
  simp [tameSingularOpenToBranchOpen, tameSingularToBranch,
    IsLocalization.Away.lift_eq, AdjoinRoot.lift_of]
  exact (IsScalarTower.algebraMap_apply (TameBaseRing g)
    (TameBranchRing g P N a) (TameBranchOpen g P N a) v).symm

/-- The inverse overlap map sends `z` to `v^a/u^b`. -/
@[simp] theorem tameBranchOpenToSingularOpen_root (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchRoot g P N a)) =
          tameInverseBranchCoordinate g P N r a b hP hN := by
  simp [tameBranchOpenToSingularOpen, IsLocalization.Away.lift_eq]

/-- The forward overlap map sends `v` to `z^r/U^b`. -/
@[simp] theorem tameSingularOpenToBranchOpen_root (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularRoot g P N r)) =
          (tameBranchOpenRootUnit g P N a hP hN ^ r *
            (tameBranchOpenUUnit g P N a hP)⁻¹ ^ b :
            (TameBranchOpen g P N a)ˣ) := by
  rw [show tameSingularOpenToBranchOpen g P N r a b hP hbezout
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
          (tameSingularRoot g P N r)) =
      algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameSingularToBranch g P N r a b hP hbezout
          (tameSingularRoot g P N r)) from by
            simp [tameSingularOpenToBranchOpen, IsLocalization.Away.lift_eq]]
  rw [tameSingularToBranch_root, map_mul, map_pow]
  simp [tameBranchOpenRootUnit_val, tameBranchOpenUUnit,
    map_pow,
    IsScalarTower.algebraMap_apply (TameBaseRing g)
      (TameBranchRing g P N a) (TameBranchOpen g P N a)]

@[simp] theorem tameBranchOpenToSingularOpen_x (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchX g P N a)) =
      (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) := by
  rw [show tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchX g P N a)) =
        tameBranchToSingularOpen g P N r a b hP hN hbezout
          (tameBranchX g P N a) from by
            simp [tameBranchOpenToSingularOpen, IsLocalization.Away.lift_eq]]
  exact tameBranchToSingularOpen_x g P N r a b hP hN hbezout

@[simp] theorem tameSingularOpenToBranchOpen_x (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularX g P N r)) =
      (tameBranchOpenXUnit g P N a : TameBranchOpen g P N a) := by
  simp [tameSingularOpenToBranchOpen, IsLocalization.Away.lift_eq]

theorem tameBranchOpenToSingularOpen_xUnit (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    Units.map (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout).toMonoidHom
      (tameBranchOpenXUnit g P N a) = tameSingularOpenXUnit g P N r := by
  apply Units.ext
  change tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
    (tameBranchOpenXUnit g P N a : TameBranchOpen g P N a) =
      (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r)
  rw [tameBranchOpenXUnit_val]
  exact tameBranchOpenToSingularOpen_x g P N r a b hP hN hbezout

theorem tameSingularOpenToBranchOpen_xUnit (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    Units.map (tameSingularOpenToBranchOpen g P N r a b hP hbezout).toMonoidHom
      (tameSingularOpenXUnit g P N r) = tameBranchOpenXUnit g P N a := by
  apply Units.ext
  change tameSingularOpenToBranchOpen g P N r a b hP hbezout
    (tameSingularOpenXUnit g P N r : TameSingularOpen g P N r) =
      (tameBranchOpenXUnit g P N a : TameBranchOpen g P N a)
  rw [tameSingularOpenXUnit_val]
  exact tameSingularOpenToBranchOpen_x g P N r a b hP hbezout

theorem tameBranchOpenToSingularOpen_uUnit (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    Units.map (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout).toMonoidHom
      (tameBranchOpenUUnit g P N a hP) = tameSingularOpenUUnit g P N r hP := by
  apply Units.ext
  change tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
    (algebraMap (TameBaseRing g) (TameBranchOpen g P N a)
      (tameBaseUnit g P hP : TameBaseRing g)) = _
  rw [tameBranchOpenToSingularOpen_base]
  rfl

theorem tameSingularOpenToBranchOpen_uUnit (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    Units.map (tameSingularOpenToBranchOpen g P N r a b hP hbezout).toMonoidHom
      (tameSingularOpenUUnit g P N r hP) = tameBranchOpenUUnit g P N a hP := by
  apply Units.ext
  change tameSingularOpenToBranchOpen g P N r a b hP hbezout
    (algebraMap (TameBaseRing g) (TameSingularOpen g P N r)
      (tameBaseUnit g P hP : TameBaseRing g)) = _
  rw [tameSingularOpenToBranchOpen_base]
  rfl

theorem tameBranchOpenToSingularOpen_rootUnit (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    Units.map (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout).toMonoidHom
      (tameBranchOpenRootUnit g P N a hP hN) =
        tameSingularOpenRootUnit g P N r hP hN ^ a *
          (tameSingularOpenXUnit g P N r)⁻¹ ^ b := by
  apply Units.ext
  change tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
    (tameBranchOpenRootUnit g P N a hP hN : TameBranchOpen g P N a) =
      tameInverseBranchCoordinate g P N r a b hP hN
  rw [tameBranchOpenRootUnit_val, tameBranchOpenToSingularOpen_root]

theorem tameSingularOpenToBranchOpen_rootUnit (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    Units.map (tameSingularOpenToBranchOpen g P N r a b hP hbezout).toMonoidHom
      (tameSingularOpenRootUnit g P N r hP hN) =
        tameBranchOpenRootUnit g P N a hP hN ^ r *
          (tameBranchOpenUUnit g P N a hP)⁻¹ ^ b := by
  apply Units.ext
  change tameSingularOpenToBranchOpen g P N r a b hP hbezout
    (tameSingularOpenRootUnit g P N r hP hN : TameSingularOpen g P N r) = _
  rw [tameSingularOpenRootUnit_val, tameSingularOpenToBranchOpen_root]

/-- The two overlap maps recover the original singular coordinate. -/
theorem tameBranchOpenToSingularOpen_singularRoot (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (tameSingularOpenToBranchOpen g P N r a b hP hbezout
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
          (tameSingularRoot g P N r))) =
      algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularRoot g P N r) := by
  let f := tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
  have h : Units.map f.toMonoidHom
      (tameBranchOpenRootUnit g P N a hP hN ^ r *
        (tameBranchOpenUUnit g P N a hP)⁻¹ ^ b) =
        tameSingularOpenRootUnit g P N r hP hN := by
    simp only [map_mul, map_pow, map_inv]
    rw [tameBranchOpenToSingularOpen_rootUnit,
      tameBranchOpenToSingularOpen_uUnit]
    exact eulerUnit_recover_original
      (tameSingularOpenXUnit g P N r)
      (tameSingularOpenUUnit g P N r hP)
      (tameSingularOpenRootUnit g P N r hP hN)
      N r a b hbezout (tameSingularOpenRootUnit_pow g P N r hP hN)
  rw [tameSingularOpenToBranchOpen_root]
  exact (congrArg Units.val h).trans
    (tameSingularOpenRootUnit_val g P N r hP hN)

/-- The two overlap maps recover the normalized branch coordinate. -/
theorem tameSingularOpenToBranchOpen_branchRoot (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
        (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
          (tameBranchRoot g P N a))) =
      algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchRoot g P N a) := by
  let f := tameSingularOpenToBranchOpen g P N r a b hP hbezout
  have h : Units.map f.toMonoidHom
      (tameSingularOpenRootUnit g P N r hP hN ^ a *
        (tameSingularOpenXUnit g P N r)⁻¹ ^ b) =
        tameBranchOpenRootUnit g P N a hP hN := by
    simp only [map_mul, map_pow, map_inv]
    rw [tameSingularOpenToBranchOpen_rootUnit,
      tameSingularOpenToBranchOpen_xUnit]
    exact eulerUnit_recover_branch
      (tameBranchOpenXUnit g P N a)
      (tameBranchOpenUUnit g P N a hP)
      (tameBranchOpenRootUnit g P N a hP hN)
      N r a b hbezout (tameBranchOpenRootUnit_pow g P N a hP hN)
  rw [tameBranchOpenToSingularOpen_root]
  exact congrArg Units.val h

/-- The punctured singular and normalized coordinate algebras are inverse. -/
theorem tameBranchOpenToSingularOpen_comp (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout).comp
      (tameSingularOpenToBranchOpen g P N r a b hP hbezout) =
        RingHom.id (TameSingularOpen g P N r) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tameSingularX g P N r))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (tameSingularOpenToBranchOpen g P N r a b hP hbezout
        (algebraMap (TameBaseRing g) (TameSingularOpen g P N r) v)) = _
    rw [tameSingularOpenToBranchOpen_base,
      tameBranchOpenToSingularOpen_base]
    rfl
  · change tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
      (tameSingularOpenToBranchOpen g P N r a b hP hbezout
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
          (tameSingularRoot g P N r))) = _
    exact tameBranchOpenToSingularOpen_singularRoot g P N r a b hP hN hbezout

/-- The opposite composite is the identity on the normalized overlap. -/
theorem tameSingularOpenToBranchOpen_comp (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameSingularOpenToBranchOpen g P N r a b hP hbezout).comp
      (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout) =
        RingHom.id (TameBranchOpen g P N a) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tameBranchX g P N a))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
        (algebraMap (TameBaseRing g) (TameBranchOpen g P N a) v)) = _
    rw [tameBranchOpenToSingularOpen_base,
      tameSingularOpenToBranchOpen_base]
    rfl
  · change tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
        (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
          (tameBranchRoot g P N a))) = _
    exact tameSingularOpenToBranchOpen_branchRoot g P N r a b hP hN hbezout

/-- The inverse overlap maps as a ring equivalence. -/
def tameBranchOpenRingEquivSingularOpen (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    TameBranchOpen g P N a ≃+* TameSingularOpen g P N r where
  toFun := tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
  invFun := tameSingularOpenToBranchOpen g P N r a b hP hbezout
  left_inv v := by
    have h := congrArg (fun f : TameBranchOpen g P N a →+* TameBranchOpen g P N a => f v)
      (tameSingularOpenToBranchOpen_comp g P N r a b hP hN hbezout)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg
      (fun f : TameSingularOpen g P N r →+* TameSingularOpen g P N r => f v)
      (tameBranchOpenToSingularOpen_comp g P N r a b hP hN hbezout)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout)
  map_add' := map_add (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout)

/-- The overlap equivalence respects the localized polynomial base. -/
def tameBranchOpenEquivSingularOpen (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    TameBranchOpen g P N a ≃ₐ[TameBaseRing g] TameSingularOpen g P N r :=
  AlgEquiv.ofRingEquiv
    (f := tameBranchOpenRingEquivSingularOpen g P N r a b hP hN hbezout) (by
    intro v
    exact tameBranchOpenToSingularOpen_base g P N r a b hP hN hbezout v)

/-- The original deck action scales the singular covering coordinate `v` by `ζ`. -/
def tameSingularDeckAlgebraAction (g P : K[X]) (N r : ℕ) [NeZero N] :
    rootsOfUnity N K →* (TameSingularRing g P N r ≃ₐ[TameBaseRing g]
      TameSingularRing g P N r) :=
  (AdjoinRoot.rootScaling N
    (algebraMap K[X] (TameBaseRing g) (tameSingularRadicand P r))).comp
      (rootsOfUnity.mapHom N
        ((algebraMap K[X] (TameBaseRing g)).comp Polynomial.C))

/-- The original `v`-deck action scales the normalized root by `ζ^a`. -/
def tameBranchDeckAlgebraAction (g P : K[X]) (N a : ℕ) [NeZero N] :
    rootsOfUnity N K →* (TameBranchRing g P N a ≃ₐ[TameBaseRing g]
      TameBranchRing g P N a) :=
  ((AdjoinRoot.rootScaling N
    (algebraMap K[X] (TameBaseRing g) (tameBranchRadicand P a))).comp
      (rootsOfUnity.mapHom N
        ((algebraMap K[X] (TameBaseRing g)).comp Polynomial.C))).comp
          (powMonoidHom (α := rootsOfUnity N K) a)

/-- The singular deck action has weight one on the original coordinate. -/
theorem tameSingularDeckAlgebraAction_root (g P : K[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N K) :
    tameSingularDeckAlgebraAction g P N r ζ (tameSingularRoot g P N r) =
      (algebraMap K[X] (TameBaseRing g) (C ((ζ : Kˣ) : K))) •
        tameSingularRoot g P N r := by
  exact AdjoinRoot.rootScaling_root N
    (algebraMap K[X] (TameBaseRing g) (tameSingularRadicand P r))
    (rootsOfUnity.mapHom N
      ((algebraMap K[X] (TameBaseRing g)).comp Polynomial.C) ζ)

/-- The normalized root has weight `a` for the original deck parameter. -/
theorem tameBranchDeckAlgebraAction_root (g P : K[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N K) :
    tameBranchDeckAlgebraAction g P N a ζ (tameBranchRoot g P N a) =
      (algebraMap K[X] (TameBaseRing g) (C (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K))) •
        tameBranchRoot g P N a := by
  exact AdjoinRoot.rootScaling_root N
    (algebraMap K[X] (TameBaseRing g) (tameBranchRadicand P a))
    (rootsOfUnity.mapHom N
      ((algebraMap K[X] (TameBaseRing g)).comp Polynomial.C) (ζ ^ a))

/-- The reindexed action has weight one on the original singular coordinate. -/
theorem tameBranchDeckAlgebraAction_singularRoot (g P : K[X]) (N r a b : ℕ)
    [NeZero N] (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) (ζ : rootsOfUnity N K) :
    tameBranchDeckAlgebraAction g P N a ζ
        (tameSingularToBranch g P N r a b hP hbezout (tameSingularRoot g P N r)) =
      (algebraMap K[X] (TameBaseRing g) (C ((ζ : Kˣ) : K))) •
        tameSingularToBranch g P N r a b hP hbezout (tameSingularRoot g P N r) := by
  let R := TameBaseRing g
  let Z := TameBranchRing g P N a
  let d := tameBranchDeckAlgebraAction g P N a ζ
  let c : R := algebraMap K[X] R (C ((ζ : Kˣ) : K))
  let ca : R := algebraMap K[X] R (C (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K))
  let u : R := (((tameBaseUnit g P hP)⁻¹ ^ b : Rˣ) : R)
  have hζ := AdjoinRoot.rootsOfUnity_pow_bezout N r a b hbezout ζ
  have hc : ca ^ r = c := by
    dsimp [ca, c]
    have hζK : ((((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) ^ r) =
        ((ζ : Kˣ) : K) := by
      exact_mod_cast hζ
    calc
      (algebraMap K[X] R (C (((ζ ^ a : rootsOfUnity N K) : Kˣ) : K))) ^ r =
          algebraMap K[X] R (C ((((ζ ^ a : rootsOfUnity N K) : Kˣ) : K) ^ r)) := by
        rw [map_pow, map_pow]
      _ = algebraMap K[X] R (C ((ζ : Kˣ) : K)) := by rw [hζK]
  rw [tameSingularToBranch_root, map_mul, map_pow, d.commutes,
    tameBranchDeckAlgebraAction_root]
  simp only [Algebra.smul_def]
  change ((algebraMap R Z ca) * tameBranchRoot g P N a) ^ r *
      algebraMap R Z u =
    algebraMap R Z c * (tameBranchRoot g P N a ^ r * algebraMap R Z u)
  rw [mul_pow, ← map_pow, hc]
  ring

/-- The singular-to-normalized algebra map respects the original deck action. -/
theorem tameSingularToBranch_deck (g P : K[X]) (N r a b : ℕ) [NeZero N]
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) (ζ : rootsOfUnity N K) :
    (tameSingularToBranch g P N r a b hP hbezout).comp
        (tameSingularDeckAlgebraAction g P N r ζ).toAlgHom =
      (tameBranchDeckAlgebraAction g P N a ζ).toAlgHom.comp
        (tameSingularToBranch g P N r a b hP hbezout) := by
  apply AdjoinRoot.algHom_ext
  change tameSingularToBranch g P N r a b hP hbezout
      (tameSingularDeckAlgebraAction g P N r ζ (tameSingularRoot g P N r)) =
    tameBranchDeckAlgebraAction g P N a ζ
      (tameSingularToBranch g P N r a b hP hbezout (tameSingularRoot g P N r))
  rw [tameSingularDeckAlgebraAction_root]
  simp only [Algebra.smul_def, map_mul,
    (tameSingularToBranch g P N r a b hP hbezout).commutes]
  simpa only [Algebra.smul_def,
    IsScalarTower.algebraMap_apply K[X] (TameBaseRing g) (TameBranchRing g P N a)]
    using (tameBranchDeckAlgebraAction_singularRoot g P N r a b hP hbezout ζ).symm

@[simp] theorem tameBranchDeckAlgebraAction_x (g P : K[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N K) :
    tameBranchDeckAlgebraAction g P N a ζ (tameBranchX g P N a) =
      tameBranchX g P N a := by
  change tameBranchDeckAlgebraAction g P N a ζ
    (algebraMap (TameBaseRing g) (TameBranchRing g P N a) (tameBaseX g)) = _
  exact (tameBranchDeckAlgebraAction g P N a ζ).commutes (tameBaseX g)

@[simp] theorem tameSingularDeckAlgebraAction_x (g P : K[X]) (N r : ℕ)
    [NeZero N] (ζ : rootsOfUnity N K) :
    tameSingularDeckAlgebraAction g P N r ζ (tameSingularX g P N r) =
      tameSingularX g P N r := by
  change tameSingularDeckAlgebraAction g P N r ζ
    (algebraMap (TameBaseRing g) (TameSingularRing g P N r) (tameBaseX g)) = _
  exact (tameSingularDeckAlgebraAction g P N r ζ).commutes (tameBaseX g)

/-- The reindexed original deck action restricted to the normalized overlap. -/
def tameBranchOpenDeck (g P : K[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N K) : TameBranchOpen g P N a →+* TameBranchOpen g P N a :=
  Localization.awayLift
    ((algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)).comp
      (tameBranchDeckAlgebraAction g P N a ζ).toRingHom)
    (tameBranchX g P N a) (by
      change IsUnit (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchDeckAlgebraAction g P N a ζ (tameBranchX g P N a)))
      rw [tameBranchDeckAlgebraAction_x]
      exact (tameBranchOpenXUnit g P N a).isUnit)

/-- The original deck action restricted to the singular overlap. -/
def tameSingularOpenDeck (g P : K[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N K) :
    TameSingularOpen g P N r →+* TameSingularOpen g P N r :=
  Localization.awayLift
    ((algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)).comp
      (tameSingularDeckAlgebraAction g P N r ζ).toRingHom)
    (tameSingularX g P N r) (by
      change IsUnit (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularDeckAlgebraAction g P N r ζ (tameSingularX g P N r)))
      rw [tameSingularDeckAlgebraAction_x]
      exact (tameSingularOpenXUnit g P N r).isUnit)

@[simp] theorem tameBranchOpenDeck_algebraMap (g P : K[X]) (N a : ℕ)
    [NeZero N] (ζ : rootsOfUnity N K) (w : TameBranchRing g P N a) :
    tameBranchOpenDeck g P N a ζ
      (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a) w) =
      algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameBranchDeckAlgebraAction g P N a ζ w) := by
  simp [tameBranchOpenDeck, IsLocalization.Away.lift_eq]

@[simp] theorem tameSingularOpenDeck_algebraMap (g P : K[X]) (N r : ℕ)
    [NeZero N] (ζ : rootsOfUnity N K) (w : TameSingularRing g P N r) :
    tameSingularOpenDeck g P N r ζ
      (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) w) =
      algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
        (tameSingularDeckAlgebraAction g P N r ζ w) := by
  simp [tameSingularOpenDeck, IsLocalization.Away.lift_eq]

@[simp] theorem tameSingularOpenToBranchOpen_algebraMap (g P : K[X])
    (N r a b : ℕ) (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) (w : TameSingularRing g P N r) :
    tameSingularOpenToBranchOpen g P N r a b hP hbezout
      (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) w) =
      algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
        (tameSingularToBranch g P N r a b hP hbezout w) := by
  simp [tameSingularOpenToBranchOpen, IsLocalization.Away.lift_eq]

/-- The punctured singular-to-normalized map preserves the original deck action. -/
theorem tameSingularOpenToBranchOpen_deck (g P : K[X]) (N r a b : ℕ)
    [NeZero N] (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) (ζ : rootsOfUnity N K) :
    (tameBranchOpenDeck g P N a ζ).comp
        (tameSingularOpenToBranchOpen g P N r a b hP hbezout) =
      (tameSingularOpenToBranchOpen g P N r a b hP hbezout).comp
        (tameSingularOpenDeck g P N r ζ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tameSingularX g P N r))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    simp only [RingHom.comp_apply, tameSingularOpenToBranchOpen_algebraMap,
      tameBranchOpenDeck_algebraMap, tameSingularOpenDeck_algebraMap]
    have h := congrArg (fun f : TameSingularRing g P N r →ₐ[TameBaseRing g]
        TameBranchRing g P N a => f (AdjoinRoot.of
          (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N) v))
      (tameSingularToBranch_deck g P N r a b hP hbezout ζ)
    exact congrArg (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a))
      (by simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using h.symm)
  · simp only [RingHom.comp_apply, tameSingularOpenToBranchOpen_algebraMap,
      tameBranchOpenDeck_algebraMap, tameSingularOpenDeck_algebraMap]
    have h := congrArg (fun f : TameSingularRing g P N r →ₐ[TameBaseRing g]
        TameBranchRing g P N a => f (AdjoinRoot.root
          (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N)))
      (tameSingularToBranch_deck g P N r a b hP hbezout ζ)
    exact congrArg (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a))
      (by simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using h.symm)

/-- The inverse normalized-to-singular overlap map is also deck equivariant. -/
theorem tameBranchOpenToSingularOpen_deck (g P : K[X]) (N r a b : ℕ)
    [NeZero N] (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    ∀ ζ : rootsOfUnity N K,
      (tameSingularOpenDeck g P N r ζ).comp
          (tameBranchOpenToSingularOpen g P N r a b hP (NeZero.ne N) hbezout) =
        (tameBranchOpenToSingularOpen g P N r a b hP (NeZero.ne N) hbezout).comp
          (tameBranchOpenDeck g P N a ζ) := by
  intro ζ
  let F := tameSingularOpenToBranchOpen g P N r a b hP hbezout
  let G := tameBranchOpenToSingularOpen g P N r a b hP (NeZero.ne N) hbezout
  let dS := tameSingularOpenDeck g P N r ζ
  let dZ := tameBranchOpenDeck g P N a ζ
  have hFG : F.comp G = RingHom.id (TameBranchOpen g P N a) :=
    tameSingularOpenToBranchOpen_comp g P N r a b hP (NeZero.ne N) hbezout
  have hGF : G.comp F = RingHom.id (TameSingularOpen g P N r) :=
    tameBranchOpenToSingularOpen_comp g P N r a b hP (NeZero.ne N) hbezout
  have hdeck : dZ.comp F = F.comp dS :=
    tameSingularOpenToBranchOpen_deck g P N r a b hP hbezout ζ
  change dS.comp G = G.comp dZ
  ext w
  have h := congrArg (fun f : TameSingularOpen g P N r →+*
      TameBranchOpen g P N a => f (G w)) hdeck
  have h' := congrArg G h
  have hFGw : F (G w) = w := by
    have h := congrArg (fun f : TameBranchOpen g P N a →+*
        TameBranchOpen g P N a => f w) hFG
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  have hGFw (v : TameSingularOpen g P N r) : G (F v) = v := by
    have h := congrArg (fun f : TameSingularOpen g P N r →+*
        TameSingularOpen g P N r => f v) hGF
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  simpa only [RingHom.comp_apply, hFGw, hGFw] using h'.symm

/-- The normalized branch as an affine scheme. -/
def tameBranchScheme (g P : K[X]) (N a : ℕ) : Scheme :=
  Spec (CommRingCat.of (TameBranchRing g P N a))

/-- The singular branch as an affine scheme. -/
def tameSingularScheme (g P : K[X]) (N r : ℕ) : Scheme :=
  Spec (CommRingCat.of (TameSingularRing g P N r))

/-- The scheme of the normalized principal-open overlap. -/
def tameBranchOpenScheme (g P : K[X]) (N a : ℕ) : Scheme :=
  Spec (CommRingCat.of (TameBranchOpen g P N a))

/-- The scheme of the punctured singular chart. -/
def tameSingularOpenScheme (g P : K[X]) (N r : ℕ) : Scheme :=
  Spec (CommRingCat.of (TameSingularOpen g P N r))

/-- The normalized chart maps to the singular chart, contravariantly from
`v ↦ z^r/U^b`. -/
def tameBranchToSingularScheme (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    tameBranchScheme g P N a ⟶ tameSingularScheme g P N r :=
  Spec.map (CommRingCat.ofHom
    (tameSingularToBranch g P N r a b hP hbezout).toRingHom)

/-- The punctured normalized and singular schemes are isomorphic through the
two explicit coordinate substitutions. -/
def tameBranchOpenIsoSingularOpen (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    tameBranchOpenScheme g P N a ≅ tameSingularOpenScheme g P N r :=
  Scheme.Spec.mapIso
    (tameBranchOpenEquivSingularOpen g P N r a b hP hN hbezout).symm.toCommRingCatIso.op

/-- The forward scheme overlap uses the singular-to-normalized ring map. -/
theorem tameBranchOpenIsoSingularOpen_hom (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameBranchOpenIsoSingularOpen g P N r a b hP hN hbezout).hom =
      Spec.map (CommRingCat.ofHom
        (tameSingularOpenToBranchOpen g P N r a b hP hbezout)) := rfl

/-- The inverse scheme overlap uses `z ↦ v^a/u^b`. -/
theorem tameBranchOpenIsoSingularOpen_inv (g P : K[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameBranchOpenIsoSingularOpen g P N r a b hP hN hbezout).inv =
      Spec.map (CommRingCat.ofHom
        (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout)) := rfl

/-- The normalized overlap includes into the full branch chart. -/
def tameBranchOpenInclusion (g P : K[X]) (N a : ℕ) :
    tameBranchOpenScheme g P N a ⟶ tameBranchScheme g P N a :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)))

/-- The overlap inclusion is an open immersion. -/
instance tameBranchOpenInclusion_isOpenImmersion (g P : K[X]) (N a : ℕ) :
    IsOpenImmersion (tameBranchOpenInclusion g P N a) :=
  IsOpenImmersion.of_isLocalization (tameBranchX g P N a)

/-- The image of the overlap is the principal open `D(u)`. -/
theorem tameBranchOpenInclusion_opensRange (g P : K[X]) (N a : ℕ) :
    (tameBranchOpenInclusion g P N a).opensRange =
      PrimeSpectrum.basicOpen (tameBranchX g P N a) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (TameBranchOpen g P N a)
    (tameBranchX g P N a)

/-- The structure morphism of the actual normalized affine scheme. -/
def tameBranchStructureMap (g P : K[X]) (N a : ℕ) :
    tameBranchScheme g P N a ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (TameBranchRing g P N a)))

/-- The structural morphism of the normalized chart is smooth. -/
theorem tameBranchStructureMap_smooth (g P : K[X]) (N a : ℕ)
    (hP : IsUnit (algebraMap K[X] (TameBaseRing g) P))
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Smooth (tameBranchStructureMap g P N a) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
  exact RingHom.smooth_algebraMap.mpr (tameBranchRing_smooth g P N a hP hN hn)

end HilbertModularity.Hypergeometric.EulerCover
