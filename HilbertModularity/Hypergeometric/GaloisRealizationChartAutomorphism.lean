/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationChartReflection
import Mathlib.Tactic.Group

/-! # The reflected Euler chart map

The rational reflection of [GPRV, Proposition 9.5] is regular on the branch-open
Euler coordinate algebra. The map is built with the localization and root-algebra
universal properties, before comparing it with the function-field reflection.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

private theorem isUnit_one_sub_unit_inv {R : Type*} [CommRing R]
    (u : Rˣ) (h : IsUnit (1 - (u : R))) :
    IsUnit (1 - ((u⁻¹ : Rˣ) : R)) := by
  have heq : 1 - ((u⁻¹ : Rˣ) : R) =
      (1 - (u : R)) * ((-u⁻¹ : Rˣ) : R) := by
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
    calc
      1 - ((u⁻¹ : Rˣ) : R) =
          ((u : R) * ((u⁻¹ : Rˣ) : R)) - ((u⁻¹ : Rˣ) : R) := by rw [hu]
      _ = (1 - (u : R)) * ((-u⁻¹ : Rˣ) : R) := by simp only [Units.val_neg]; ring
  rw [heq]
  exact h.mul (Units.isUnit _)

/-- Polynomial evaluation at the reflected chart coordinate. -/
def reflectionChartPolynomialHom (N m : ℕ) (t : K) (ht : t ≠ 0) :
    K[X] →+* CoverRing N m t :=
  Polynomial.eval₂RingHom (algebraMap K (CoverRing N m t))
    (reflectionXChartUnit N m t ht : CoverRing N m t)

/-- The reflected coordinate avoids all three finite branch sections. -/
theorem reflectionChart_branchProduct_isUnit (N m : ℕ) (t : K)
    (ht : t ≠ 0) :
    IsUnit (reflectionChartPolynomialHom N m t ht (branchProduct t)) := by
  let U : (CoverRing N m t)ˣ := coverConstantUnit N m t ht * coverXUnit N m t
  have hU : (U : CoverRing N m t) =
      algebraMap K (CoverRing N m t) t *
        algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap K[X] (BaseRing t) X) := by
    simp [U]
  have hbase : IsUnit (1 - (U : CoverRing N m t)) := by
    rw [hU]
    have h := (isUnit_oneMinusTX t).map
      (algebraMap (BaseRing t) (CoverRing N m t))
    have hc : algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) (C t)) =
        algebraMap K (CoverRing N m t) t := by
      rw [← IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t)]
      exact IsScalarTower.algebraMap_apply K K[X] (CoverRing N m t) t
    have hc' : algebraMap K[X] (CoverRing N m t) (C t) =
        algebraMap K (CoverRing N m t) t := by
      exact IsScalarTower.algebraMap_apply K K[X] (CoverRing N m t) t
    simpa only [oneMinusTX, map_sub, map_one, map_mul,
      ← IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t), hc']
      using h
  have hx : IsUnit ((reflectionXChartUnit N m t ht : (CoverRing N m t)ˣ) :
      CoverRing N m t) := Units.isUnit _
  have h1x : IsUnit (1 - (reflectionXChartUnit N m t ht : CoverRing N m t)) := by
    rw [reflectionXChartUnit_eq]
    exact isUnit_one_sub_unit_inv U hbase
  have htx : algebraMap K (CoverRing N m t) t *
      (reflectionXChartUnit N m t ht : CoverRing N m t) =
      ((coverXUnit N m t)⁻¹ : (CoverRing N m t)ˣ) := by
    have hu : coverConstantUnit N m t ht * U⁻¹ = (coverXUnit N m t)⁻¹ := by
      simp [U, mul_inv_rev, mul_comm]
    have hv := congrArg (fun u : (CoverRing N m t)ˣ => (u : CoverRing N m t)) hu
    rw [reflectionXChartUnit_eq]
    simpa only [Units.val_mul, coverConstantUnit_val] using hv
  have h1tx : IsUnit (1 - algebraMap K (CoverRing N m t) t *
      (reflectionXChartUnit N m t ht : CoverRing N m t)) := by
    rw [htx]
    have h := (isUnit_oneMinusX t).map
      (algebraMap (BaseRing t) (CoverRing N m t))
    have hbaseX : IsUnit (1 - (coverXUnit N m t : CoverRing N m t)) := by
      simpa [oneMinusX, coverXUnit_val, map_sub] using h
    exact isUnit_one_sub_unit_inv (coverXUnit N m t) hbaseX
  simpa [reflectionChartPolynomialHom, branchProduct, eval₂_mul,
    eval₂_sub] using (hx.mul h1x).mul h1tx

/-- Reflection on the localized polynomial base. -/
def reflectionChartBaseHom (N m : ℕ) (t : K) (ht : t ≠ 0) :
    BaseRing t →+* CoverRing N m t :=
  Localization.awayLift (reflectionChartPolynomialHom N m t ht)
    (branchProduct t) (reflectionChart_branchProduct_isUnit N m t ht)

@[simp] theorem reflectionChartBaseHom_algebraMap (N m : ℕ) (t : K)
    (ht : t ≠ 0) (q : K[X]) :
    reflectionChartBaseHom N m t ht (algebraMap K[X] (BaseRing t) q) =
      reflectionChartPolynomialHom N m t ht q := by
  unfold reflectionChartBaseHom
  exact IsLocalization.Away.lift_eq (branchProduct t) _ q

/-- The defining radicand evaluated at the reflected chart coordinate. -/
theorem reflectionChartBaseHom_radicand (N m : ℕ) (t : K) (ht : t ≠ 0) :
    reflectionChartBaseHom N m t ht (radicand N m t) =
      (reflectionXChartUnit N m t ht : CoverRing N m t) ^ m *
        (1 - (reflectionXChartUnit N m t ht : CoverRing N m t)) ^ (N - m) *
        (1 - algebraMap K (CoverRing N m t) t *
          (reflectionXChartUnit N m t ht : CoverRing N m t)) ^ m := by
  rw [radicand, reflectionChartBaseHom_algebraMap]
  simp [branchPolynomial, reflectionChartPolynomialHom, eval₂_sub, eval₂_pow]

/-- The reflected chart coordinates satisfy the Euler equation inside its
coordinate ring.  The generic-point calculation proves the identity, and
injectivity of the coordinate ring into its function field brings it back. -/
theorem reflectionChart_equation (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    (reflectionYChartUnit N m t hN ht : CoverRing N m t) ^ N =
      (reflectionXChartUnit N m t ht : CoverRing N m t) ^ m *
        (1 - (reflectionXChartUnit N m t ht : CoverRing N m t)) ^ (N - m) *
        (1 - algebraMap K (CoverRing N m t) t *
          (reflectionXChartUnit N m t ht : CoverRing N m t)) ^ m := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  apply IsFractionRing.injective (CoverRing N m t) (CoverFunctionField N m t)
  let p := genericOpenEulerPoint N m t hN hmPos hm hcop
  have htF : algebraMap K (CoverFunctionField N m t) t ≠ 0 :=
    (map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht
  have heq := (reflectOpenEulerPoint N m (Nat.le_of_lt hm) htF p).equation
  simpa only [map_pow, map_mul, map_sub, map_one,
    reflectionXChartUnit_toFunctionField N m t hN hmPos hm hcop ht,
    reflectionYChartUnit_toFunctionField N m t hN hmPos hm hcop ht,
    ← IsScalarTower.algebraMap_apply K (CoverRing N m t)
      (CoverFunctionField N m t), p, genericOpenEulerPoint_x,
    genericOpenEulerPoint_y, reflectOpenEulerPoint_x,
    reflectOpenEulerPoint_y] using heq

/-- Reflection defines an endomorphism of the actual branch-open Euler
coordinate ring. -/
def reflectionChartCoverHom (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    CoverRing N m t →+* CoverRing N m t :=
  AdjoinRoot.lift (reflectionChartBaseHom N m t ht)
    (reflectionYChartUnit N m t hN ht : CoverRing N m t) (by
      simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [reflectionChartBaseHom_radicand,
        ← reflectionChart_equation N m t hN hmPos hm hcop ht, sub_self])

@[simp] theorem reflectionChartCoverHom_root (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    reflectionChartCoverHom N m t hN hmPos hm hcop ht (coverRoot N m t) =
      (reflectionYChartUnit N m t hN ht : CoverRing N m t) := by
  simp [reflectionChartCoverHom, coverRoot, AdjoinRoot.lift_root]

@[simp] theorem reflectionChartCoverHom_base (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0)
    (a : BaseRing t) :
    reflectionChartCoverHom N m t hN hmPos hm hcop ht
      (algebraMap (BaseRing t) (CoverRing N m t) a) =
      reflectionChartBaseHom N m t ht a := by
  simp [reflectionChartCoverHom, AdjoinRoot.lift_of]

@[simp] theorem reflectionChartCoverHom_x (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    reflectionChartCoverHom N m t hN hmPos hm hcop ht
      (algebraMap K[X] (CoverRing N m t) X) =
      (reflectionXChartUnit N m t ht : CoverRing N m t) := by
  rw [IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t),
    reflectionChartCoverHom_base, reflectionChartBaseHom_algebraMap]
  simp [reflectionChartPolynomialHom]

@[simp] theorem reflectionChartCoverHom_const (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0)
    (a : K) :
    reflectionChartCoverHom N m t hN hmPos hm hcop ht
      (algebraMap K (CoverRing N m t) a) =
      algebraMap K (CoverRing N m t) a := by
  rw [IsScalarTower.algebraMap_apply K K[X] (CoverRing N m t),
    IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t),
    reflectionChartCoverHom_base, reflectionChartBaseHom_algebraMap]
  simp only [Polynomial.algebraMap_eq]
  simp [reflectionChartPolynomialHom]
  change algebraMap K (CoverRing N m t) a =
    algebraMap (BaseRing t) (CoverRing N m t)
      (algebraMap K[X] (BaseRing t) (C a))
  rw [← IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t)]
  simpa only [Polynomial.algebraMap_eq] using
    (IsScalarTower.algebraMap_apply K K[X] (CoverRing N m t) a)

/-- The chart reflection extends the previously constructed involution of
the Euler function field. -/
theorem reflectionChartCoverHom_toFunctionField (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (algebraMap (CoverRing N m t) (CoverFunctionField N m t)).comp
        (reflectionChartCoverHom N m t hN hmPos hm hcop ht) =
      (genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht).comp
        (algebraMap (CoverRing N m t) (CoverFunctionField N m t)) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  have hpoly (q : K[X]) :
      algebraMap K[X] (CoverRing N m t) q =
        algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap K[X] (BaseRing t) q) :=
    IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t) q
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      change algebraMap (CoverRing N m t) (CoverFunctionField N m t)
          (reflectionChartCoverHom N m t hN hmPos hm hcop ht
            (algebraMap (BaseRing t) (CoverRing N m t)
              (algebraMap K[X] (BaseRing t) (C a)))) =
        genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
          (algebraMap (CoverRing N m t) (CoverFunctionField N m t)
            (algebraMap (BaseRing t) (CoverRing N m t)
              (algebraMap K[X] (BaseRing t) (C a))))
      rw [← hpoly (C a)]
      have hC : algebraMap K[X] (CoverRing N m t) (C a) =
          algebraMap K (CoverRing N m t) a := by
        simpa only [Polynomial.algebraMap_eq] using
          (IsScalarTower.algebraMap_apply K K[X] (CoverRing N m t) a).symm
      rw [hC]
      rw [reflectionChartCoverHom_const]
      simpa only [← IsScalarTower.algebraMap_apply K (CoverRing N m t)
        (CoverFunctionField N m t)] using
        (genericReflectionFunctionFieldHom_const N m t hN hmPos hm hcop ht a).symm
    · simp only [RingHom.comp_apply]
      change algebraMap (CoverRing N m t) (CoverFunctionField N m t)
          (reflectionChartCoverHom N m t hN hmPos hm hcop ht
            (algebraMap (BaseRing t) (CoverRing N m t)
              (algebraMap K[X] (BaseRing t) X))) =
        genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
          (algebraMap (CoverRing N m t) (CoverFunctionField N m t)
            (algebraMap (BaseRing t) (CoverRing N m t)
              (algebraMap K[X] (BaseRing t) X)))
      rw [← hpoly X]
      rw [reflectionChartCoverHom_x]
      exact (genericReflectionFunctionFieldHom_x_eq_chart N m t hN hmPos hm hcop ht).symm
  · change algebraMap (CoverRing N m t) (CoverFunctionField N m t)
        (reflectionChartCoverHom N m t hN hmPos hm hcop ht (coverRoot N m t)) =
      genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
        (algebraMap (CoverRing N m t) (CoverFunctionField N m t) (coverRoot N m t))
    rw [reflectionChartCoverHom_root]
    exact (genericReflectionFunctionFieldHom_root_eq_chart N m t hN hmPos hm hcop ht).symm

/-- The reflected map is an involution of the branch-open coordinate ring.
This follows from its compatibility with the function-field involution and
the injectivity of the coordinate ring into that field. -/
theorem reflectionChartCoverHom_involutive (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    (reflectionChartCoverHom N m t hN hmPos hm hcop ht).comp
      (reflectionChartCoverHom N m t hN hmPos hm hcop ht) =
        RingHom.id (CoverRing N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let r := reflectionChartCoverHom N m t hN hmPos hm hcop ht
  let R := genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
  let j := algebraMap (CoverRing N m t) (CoverFunctionField N m t)
  have hcompat (a : CoverRing N m t) : j (r a) = R (j a) := by
    have h := congrArg (fun f : CoverRing N m t →+* CoverFunctionField N m t => f a)
      (reflectionChartCoverHom_toFunctionField N m t hN hmPos hm hcop ht)
    simpa only [j, r, R, RingHom.comp_apply] using h
  have hfield (a : CoverFunctionField N m t) : R (R a) = a := by
    have h := congrArg
      (fun f : CoverFunctionField N m t →+* CoverFunctionField N m t => f a)
      (genericReflectionFunctionFieldHom_involutive N m t hN hmPos hm hcop ht)
    simpa only [R, RingHom.comp_apply, RingHom.id_apply] using h
  apply RingHom.ext
  intro a
  apply IsFractionRing.injective (CoverRing N m t) (CoverFunctionField N m t)
  change j (r (r a)) = j a
  calc
    j (r (r a)) = R (j (r a)) := hcompat (r a)
    _ = R (R (j a)) := by rw [hcompat]
    _ = j a := hfield (j a)

/-- The actual branch-open Euler chart has an involutive reflection
automorphism, agreeing with the previously proved function-field map. -/
def reflectionChartCoverEquiv (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    CoverRing N m t ≃+* CoverRing N m t := by
  let r := reflectionChartCoverHom N m t hN hmPos hm hcop ht
  have hinv (a : CoverRing N m t) : r (r a) = a := by
    have h := congrArg (fun f : CoverRing N m t →+* CoverRing N m t => f a)
      (reflectionChartCoverHom_involutive N m t hN hmPos hm hcop ht)
    simpa only [r, RingHom.comp_apply, RingHom.id_apply] using h
  exact
    { toFun := r
      invFun := r
      left_inv := hinv
      right_inv := hinv
      map_mul' := r.map_mul
      map_add' := r.map_add }

@[simp] theorem reflectionChartCoverEquiv_toRingHom (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    (reflectionChartCoverEquiv N m t hN hmPos hm hcop ht :
      CoverRing N m t →+* CoverRing N m t) =
        reflectionChartCoverHom N m t hN hmPos hm hcop ht := by
  apply RingHom.ext
  intro a
  unfold reflectionChartCoverEquiv
  rfl

end HilbertModularity.Hypergeometric.EulerCover
