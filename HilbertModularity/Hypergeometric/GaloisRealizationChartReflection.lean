/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationReflectionInjectivity
public import HilbertModularity.Hypergeometric.EulerCover.ZeroBranch

/-! # The reflection coordinates in the Euler chart algebra

The rational formulas of [GPRV, Proposition 9.5] have no poles on the branch-open
Euler chart.  We first express them as units of its actual coordinate algebra;
this is the algebraic prerequisite for an involution of that chart and for
identifying its extension to the smooth proper family.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- A nonzero constant, viewed as a unit in the Euler coordinate algebra. -/
def coverConstantUnit (N m : ℕ) (t : K) (ht : t ≠ 0) :
    (CoverRing N m t)ˣ :=
  Units.map (algebraMap K (CoverRing N m t)).toMonoidHom (Units.mk0 t ht)

@[simp] theorem coverConstantUnit_val (N m : ℕ) (t : K) (ht : t ≠ 0) :
    (coverConstantUnit N m t ht : CoverRing N m t) =
      algebraMap K (CoverRing N m t) t := by
  simp [coverConstantUnit]

/-- The reflected `x` coordinate, already regular on the branch-open chart. -/
def reflectionXChartUnit (N m : ℕ) (t : K) (ht : t ≠ 0) :
    (CoverRing N m t)ˣ :=
  (coverConstantUnit N m t ht * coverXUnit N m t)⁻¹

/-- The unit expression for the reflected chart coordinate. -/
theorem reflectionXChartUnit_eq (N m : ℕ) (t : K) (ht : t ≠ 0) :
    reflectionXChartUnit N m t ht =
      (coverConstantUnit N m t ht * coverXUnit N m t)⁻¹ :=
  (rfl)

/-- The reflected `y` coordinate, already regular on the branch-open chart. -/
def reflectionYChartUnit (N m : ℕ) (t : K) (hN : N ≠ 0)
    (ht : t ≠ 0) : (CoverRing N m t)ˣ :=
  -((Units.map (algebraMap (BaseRing t) (CoverRing N m t)).toMonoidHom
        (oneMinusXUnit t) *
      Units.map (algebraMap (BaseRing t) (CoverRing N m t)).toMonoidHom
        (oneMinusTXUnit t)) *
      (coverConstantUnit N m t ht * coverXUnit N m t *
        coverRootUnit N m t hN)⁻¹)

/-- The three algebra maps from the polynomial base to the function field
agree on every polynomial, including the branch coordinates. -/
theorem coverPolynomialMap_toFunctionField (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (p : K[X]) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    algebraMap (CoverRing N m t) (CoverFunctionField N m t)
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) p)) =
      algebraMap K[X] (CoverFunctionField N m t) p := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [← IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N m t),
    ← IsScalarTower.algebraMap_apply K[X] (CoverRing N m t)
      (CoverFunctionField N m t)]

/-- The algebraic reflected `x` has the stated rational image in the
function field. -/
theorem reflectionXChartUnit_toFunctionField (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    algebraMap (CoverRing N m t) (CoverFunctionField N m t)
      (reflectionXChartUnit N m t ht : CoverRing N m t) =
      reflectionX (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  simp [reflectionXChartUnit, coverConstantUnit_val, coverXUnit_val,
    reflectionX_eq, coverFunctionFieldX,
    ← IsScalarTower.algebraMap_apply, ht]
  all_goals exact coverPolynomialMap_toFunctionField N m t hN hmPos hm hcop X

/-- The algebraic reflected `y` has the stated rational image in the
function field. -/
theorem reflectionYChartUnit_toFunctionField (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    algebraMap (CoverRing N m t) (CoverFunctionField N m t)
      (reflectionYChartUnit N m t hN ht : CoverRing N m t) =
      reflectionY (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) (coverFunctionFieldRoot N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  simp [reflectionYChartUnit, coverConstantUnit_val, coverXUnit_val,
    coverRootUnit_val, reflectionY_eq, oneMinusXUnit_val,
    oneMinusTXUnit_val, oneMinusX, oneMinusTX, coverFunctionFieldX,
    coverFunctionFieldRoot, div_eq_mul_inv,
    ← IsScalarTower.algebraMap_apply]
  have hx :
      algebraMap (CoverRing N m t) (CoverFunctionField N m t)
        (AdjoinRoot.of (coverPolynomial N m t)
          (algebraMap K[X] (BaseRing t) X)) =
        algebraMap K[X] (CoverFunctionField N m t) X := by
    exact coverPolynomialMap_toFunctionField N m t hN hmPos hm hcop X
  have hc :
      algebraMap (CoverRing N m t) (CoverFunctionField N m t)
        (AdjoinRoot.of (coverPolynomial N m t)
          (algebraMap K[X] (BaseRing t) (C t))) =
        algebraMap K[X] (CoverFunctionField N m t) (C t) := by
    exact coverPolynomialMap_toFunctionField N m t hN hmPos hm hcop (C t)
  rw [hx, hc]
  have hct : algebraMap K[X] (CoverFunctionField N m t) (C t) =
      algebraMap K (CoverFunctionField N m t) t := by
    simpa using (IsScalarTower.algebraMap_apply K K[X]
      (CoverFunctionField N m t) t).symm
  simp [hct]

/-- On the generic point, the field reflection sends `x` to the regular
coordinate represented by `reflectionXChartUnit`. -/
theorem genericReflectionFunctionFieldHom_x_eq_chart (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
        (coverFunctionFieldX N m t) =
      algebraMap (CoverRing N m t) (CoverFunctionField N m t)
        (reflectionXChartUnit N m t ht : CoverRing N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [genericReflectionFunctionFieldHom_x,
    reflectionXChartUnit_toFunctionField N m t hN hmPos hm hcop ht]

/-- The same generic reflection sends the root coordinate to the regular
coordinate represented by `reflectionYChartUnit`. -/
theorem genericReflectionFunctionFieldHom_root_eq_chart (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
        (coverFunctionFieldRoot N m t) =
      algebraMap (CoverRing N m t) (CoverFunctionField N m t)
        (reflectionYChartUnit N m t hN ht : CoverRing N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [genericReflectionFunctionFieldHom_root,
    reflectionYChartUnit_toFunctionField N m t hN hmPos hm hcop ht]

end HilbertModularity.Hypergeometric.EulerCover
