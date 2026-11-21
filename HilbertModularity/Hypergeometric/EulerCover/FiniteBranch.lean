/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.TameBranch
public import HilbertModularity.Hypergeometric.EulerCover.DeckTransformations
import Mathlib.Tactic.Ring

/-! # The finite nonzero branch coordinates of the Euler cover

The affine changes `u = 1-x` and `u = 1-tx` put the Euler equation
into tame branch form at `x=1` and `x=1/t`. In the second change the
radicand carries the full factor `t⁻ᴺ`; no scalar root is chosen.
These are the finite branch coordinates in
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [CommRing K]

/-- The inverse of the parameter on the unit locus. The value away from that
locus only makes the polynomial substitution a total definition; all chart
comparisons require `IsUnit t`. -/
def inverseParameterCoefficient (t : K) : K :=
  by
    classical
    exact if ht : IsUnit t then (↑(ht.unit⁻¹) : K) else 0

/-- On the parameter locus of the Euler family, the chosen coefficient is
the actual inverse of `t`. -/
theorem inverseParameterCoefficient_mul (t : K) (ht : IsUnit t) :
    inverseParameterCoefficient t * t = 1 := by
  simp only [inverseParameterCoefficient, dite_eq_left ht]
  simpa only [ht.unit_spec] using Units.inv_mul ht.unit

/-- Over a field, the coefficient in the `1/t` chart is the usual inverse. -/
theorem inverseParameterCoefficient_eq_inv {F : Type*} [Field F]
    (t : F) (ht : t ≠ 0) : inverseParameterCoefficient t = t⁻¹ := by
  have hunit : IsUnit t := isUnit_iff_ne_zero.mpr ht
  calc
    inverseParameterCoefficient t = inverseParameterCoefficient t * (t * t⁻¹) := by
      rw [mul_inv_cancel₀ ht, mul_one]
    _ = (inverseParameterCoefficient t * t) * t⁻¹ := by ring
    _ = t⁻¹ := by rw [inverseParameterCoefficient_mul t hunit, one_mul]

theorem mul_inverseParameterCoefficient (t : K) (ht : IsUnit t) :
    t * inverseParameterCoefficient t = 1 := by
  rw [mul_comm]
  exact inverseParameterCoefficient_mul t ht

theorem isUnit_inverseParameterCoefficient (t : K) (ht : IsUnit t) :
    IsUnit (inverseParameterCoefficient t) := by
  simp only [inverseParameterCoefficient, dite_eq_left ht]
  exact (ht.unit⁻¹).isUnit

/-- Substitution of `x=1-u` in a polynomial with original coordinate `x`. -/
def oneSubstitution : K[X] →+* K[X] :=
  eval₂RingHom C (1 - X)

@[simp] theorem oneSubstitution_X :
    (oneSubstitution : K[X] →+* K[X]) X = 1 - X := by
  simp [oneSubstitution]

@[simp] theorem oneSubstitution_C (c : K) :
    (oneSubstitution : K[X] →+* K[X]) (C c) = C c := by
  simp [oneSubstitution]

/-- The nonvanishing product on the chart centered at `x=1`. -/
def oneBranchProduct (t : K) : K[X] :=
  (1 - X) * (1 - C t + C t * X)

/-- The invertible part of the Euler radicand at `x=1`. -/
def oneBranchFactorPolynomial (m : ℕ) (t : K) : K[X] :=
  (1 - X) ^ m * (1 - C t + C t * X) ^ m

/-- The affine change `x=1-u` carries the original branch product to
`u` times the two remaining factors. -/
theorem oneSubstitution_branchProduct (t : K) :
    (oneSubstitution : K[X] →+* K[X]) (branchProduct t) =
      X * oneBranchProduct t := by
  simp [oneSubstitution, branchProduct, oneBranchProduct]
  ring

/-- The original Euler radicand at `x=1` has branch exponent `N-m`. -/
theorem oneSubstitution_branchPolynomial (N m : ℕ) (t : K) :
    (oneSubstitution : K[X] →+* K[X]) (branchPolynomial N m t) =
      X ^ (N - m) * oneBranchFactorPolynomial m t := by
  simp only [branchPolynomial, map_mul, map_pow, map_sub, map_one,
    oneSubstitution_X, oneSubstitution_C]
  have hu : 1 - (1 - X : K[X]) = X := by ring
  have hv : 1 - C t * (1 - X : K[X]) = 1 - C t + C t * X := by ring
  rw [hu, hv]
  simp only [oneBranchFactorPolynomial]
  ring

/-- The unit factor at one becomes `x^m(1-tx)^m` under the reverse change. -/
theorem oneSubstitution_factorPolynomial (m : ℕ) (t : K) :
    (oneSubstitution : K[X] →+* K[X])
      (oneBranchFactorPolynomial m t) = X ^ m * (1 - C t * X) ^ m := by
  simp only [oneBranchFactorPolynomial, map_mul, map_pow, map_sub, map_add,
    map_one, oneSubstitution_X, oneSubstitution_C]
  have hu : 1 - (1 - X : K[X]) = X := by ring
  have hv : 1 - C t + C t * (1 - X : K[X]) = 1 - C t * X := by ring
  rw [hu, hv]

/-- The coordinate ring retaining `u=1-x` near the branch at one. -/
abbrev OneBaseRing (t : K) := Localization.Away (oneBranchProduct t)

/-- The branch parameter `u=1-x` on the chart centered at one. -/
def oneBaseU (t : K) : OneBaseRing t :=
  algebraMap K[X] (OneBaseRing t) X

/-- The unit part of the Euler radicand on the chart centered at one. -/
@[expose] def oneBranchFactor (m : ℕ) (t : K) : OneBaseRing t :=
  algebraMap K[X] (OneBaseRing t) (oneBranchFactorPolynomial m t)

theorem isUnit_oneBranchFactor (m : ℕ) (t : K) :
    IsUnit (oneBranchFactor m t) := by
  have h : IsUnit (algebraMap K[X] (OneBaseRing t) (oneBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (oneBranchProduct t)
  simp only [oneBranchProduct, map_mul, IsUnit.mul_iff] at h
  simpa only [oneBranchFactor, oneBranchFactorPolynomial, map_mul, map_pow] using
    (h.1.pow m).mul (h.2.pow m)

/-- The exact invertible factor at `x=1`, as an element of the unit group. -/
def oneBranchUnit (m : ℕ) (t : K) : (OneBaseRing t)ˣ :=
  (isUnit_oneBranchFactor m t).unit

@[simp] theorem oneBranchUnit_val (m : ℕ) (t : K) :
    (oneBranchUnit m t : OneBaseRing t) = oneBranchFactor m t := by
  simp [oneBranchUnit]

/-- Reversing `u=1-x` sends the two retained factors to `x(1-tx)`. -/
theorem oneSubstitution_oneBranchProduct (t : K) :
    (oneSubstitution : K[X] →+* K[X]) (oneBranchProduct t) =
      X * (1 - C t * X) := by
  simp [oneSubstitution, oneBranchProduct]
  ring

/-- The one-chart polynomial ring maps to the actual branch-complement
coordinate ring by `u ↦ 1-x`. -/
def onePolynomialToCoverBase (t : K) : K[X] →+* BaseRing t :=
  (algebraMap K[X] (BaseRing t)).comp oneSubstitution

/-- Both factors retained at one are invertible in the actual Euler base. -/
theorem isUnit_oneBranchProduct_coverBase (t : K) :
    IsUnit (onePolynomialToCoverBase t (oneBranchProduct t)) := by
  have h : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  change IsUnit (algebraMap K[X] (BaseRing t)
    ((oneSubstitution : K[X] →+* K[X]) (oneBranchProduct t)))
  rw [oneSubstitution_oneBranchProduct, map_mul]
  exact h.1.1.mul h.2

/-- The actual localization map from the one-chart base to the Euler base. -/
def oneBaseToCoverBase (t : K) : OneBaseRing t →+* BaseRing t :=
  Localization.awayLift (onePolynomialToCoverBase t) (oneBranchProduct t)
    (isUnit_oneBranchProduct_coverBase t)

@[simp] theorem oneBaseToCoverBase_polynomial (t : K) (p : K[X]) :
    oneBaseToCoverBase t (algebraMap K[X] (OneBaseRing t) p) =
      algebraMap K[X] (BaseRing t)
        ((oneSubstitution : K[X] →+* K[X]) p) := by
  simp [oneBaseToCoverBase, onePolynomialToCoverBase,
    Localization.awayLift, IsLocalization.Away.lift_eq]

@[simp] theorem oneBaseToCoverBase_u (t : K) :
    oneBaseToCoverBase t (oneBaseU t) =
      1 - algebraMap K[X] (BaseRing t) X := by
  rw [oneBaseU, oneBaseToCoverBase_polynomial, oneSubstitution_X]
  simp

/-- On the original branch complement, the factor `U` at one becomes
`x^m(1-tx)^m`. -/
theorem oneBaseToCoverBase_factor (m : ℕ) (t : K) :
    oneBaseToCoverBase t (oneBranchFactor m t) =
      (algebraMap K[X] (BaseRing t) X) ^ m *
        (1 - algebraMap K[X] (BaseRing t) (C t) *
          algebraMap K[X] (BaseRing t) X) ^ m := by
  rw [oneBranchFactor, oneBaseToCoverBase_polynomial]
  rw [oneSubstitution_factorPolynomial]
  simp only [map_mul, map_pow, map_sub, map_one]

/-- The original radicand is `u^(N-m) U` on the one-chart overlap. -/
theorem radicand_eq_oneBranchFactor (N m : ℕ) (t : K) :
    radicand N m t =
      oneBaseToCoverBase t (oneBaseU t) ^ (N - m) *
        oneBaseToCoverBase t (oneBranchUnit m t : OneBaseRing t) := by
  rw [oneBranchUnit_val, oneBaseToCoverBase_u, oneBaseToCoverBase_factor]
  simp only [radicand, branchPolynomial, map_mul, map_pow, map_sub, map_one]
  ring

/-- The one-chart base with its branch parameter inverted. -/
abbrev OneBaseOpen (t : K) := Localization.Away (oneBaseU t)

/-- The branch parameter is a unit on this open. -/
def oneBaseOpenUUnit (t : K) : (OneBaseOpen t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (oneBaseU t)).unit

@[simp] theorem oneBaseOpenUUnit_val (t : K) :
    (oneBaseOpenUUnit t : OneBaseOpen t) =
      algebraMap (OneBaseRing t) (OneBaseOpen t) (oneBaseU t) := by
  simp [oneBaseOpenUUnit]

/-- The reverse affine change maps original polynomials into the open
one-chart base. -/
def polynomialToOneBaseOpen (t : K) : K[X] →+* OneBaseOpen t :=
  ((algebraMap (OneBaseRing t) (OneBaseOpen t)).comp
    (algebraMap K[X] (OneBaseRing t))).comp oneSubstitution

/-- All three original branch factors are units on this open. -/
theorem isUnit_branchProduct_oneBaseOpen (t : K) :
    IsUnit (polynomialToOneBaseOpen t (branchProduct t)) := by
  change IsUnit (algebraMap (OneBaseRing t) (OneBaseOpen t)
    (algebraMap K[X] (OneBaseRing t)
      ((oneSubstitution : K[X] →+* K[X]) (branchProduct t))))
  rw [oneSubstitution_branchProduct, map_mul, map_mul]
  have h : IsUnit (algebraMap K[X] (OneBaseRing t) (oneBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (oneBranchProduct t)
  exact (oneBaseOpenUUnit t).isUnit.mul
    (h.map (algebraMap (OneBaseRing t) (OneBaseOpen t)))

/-- The original Euler base restricts to the open centered at `x=1`. -/
def coverBaseToOneBaseOpen (t : K) : BaseRing t →+* OneBaseOpen t :=
  Localization.awayLift (polynomialToOneBaseOpen t)
    (branchProduct t) (isUnit_branchProduct_oneBaseOpen t)

@[simp] theorem coverBaseToOneBaseOpen_polynomial (t : K) (p : K[X]) :
    coverBaseToOneBaseOpen t (algebraMap K[X] (BaseRing t) p) =
      polynomialToOneBaseOpen t p := by
  simp [coverBaseToOneBaseOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The parameter `u=1-x` is invertible in the original Euler base. -/
theorem isUnit_oneBaseU_coverBase (t : K) :
    IsUnit (oneBaseToCoverBase t (oneBaseU t)) := by
  have h : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  rw [oneBaseToCoverBase_u]
  simpa only [map_sub, map_one] using h.1.2

/-- Restriction from the one-chart open to the actual Euler base. -/
def oneBaseOpenToCoverBase (t : K) : OneBaseOpen t →+* BaseRing t :=
  Localization.awayLift (oneBaseToCoverBase t) (oneBaseU t)
    (isUnit_oneBaseU_coverBase t)

@[simp] theorem oneBaseOpenToCoverBase_oneBase (t : K) (v : OneBaseRing t) :
    oneBaseOpenToCoverBase t
      (algebraMap (OneBaseRing t) (OneBaseOpen t) v) =
        oneBaseToCoverBase t v := by
  simp [oneBaseOpenToCoverBase, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The affine coordinate change `u=1-x` is its own inverse. -/
theorem oneSubstitution_involutive :
    (oneSubstitution (K := K)).comp oneSubstitution = RingHom.id K[X] := by
  ext
  · simp [oneSubstitution]
  · simp [oneSubstitution]

/-- The one-chart restriction and the reverse affine change compose to the
identity on the original Euler base. -/
theorem oneBaseOpenToCoverBase_coverBaseToOneBaseOpen (t : K) :
    (oneBaseOpenToCoverBase t).comp (coverBaseToOneBaseOpen t) =
      RingHom.id (BaseRing t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
  apply RingHom.ext
  intro p
  change oneBaseOpenToCoverBase t
    (coverBaseToOneBaseOpen t (algebraMap K[X] (BaseRing t) p)) = _
  rw [coverBaseToOneBaseOpen_polynomial]
  change oneBaseOpenToCoverBase t
    (algebraMap (OneBaseRing t) (OneBaseOpen t)
      (algebraMap K[X] (OneBaseRing t) (oneSubstitution p))) = _
  rw [oneBaseOpenToCoverBase_oneBase, oneBaseToCoverBase_polynomial]
  have hp := congrArg (fun f : K[X] →+* K[X] => f p)
    (oneSubstitution_involutive (K := K))
  simpa only [RingHom.comp_apply, RingHom.id_apply] using congrArg
    (algebraMap K[X] (BaseRing t)) hp

/-- The two affine changes also compose to the identity on the open
one-chart base. -/
theorem coverBaseToOneBaseOpen_oneBaseOpenToCoverBase (t : K) :
    (coverBaseToOneBaseOpen t).comp (oneBaseOpenToCoverBase t) =
      RingHom.id (OneBaseOpen t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (oneBaseU t))
  apply IsLocalization.ringHom_ext (Submonoid.powers (oneBranchProduct t))
  apply RingHom.ext
  intro p
  change coverBaseToOneBaseOpen t
    (oneBaseOpenToCoverBase t
      (algebraMap (OneBaseRing t) (OneBaseOpen t)
        (algebraMap K[X] (OneBaseRing t) p))) = _
  rw [oneBaseOpenToCoverBase_oneBase, oneBaseToCoverBase_polynomial,
    coverBaseToOneBaseOpen_polynomial]
  change algebraMap (OneBaseRing t) (OneBaseOpen t)
    (algebraMap K[X] (OneBaseRing t)
      (oneSubstitution (oneSubstitution p))) = _
  have hp := congrArg (fun f : K[X] →+* K[X] => f p)
    (oneSubstitution_involutive (K := K))
  simpa only [RingHom.comp_apply, RingHom.id_apply] using congrArg
    (fun q : K[X] => algebraMap (OneBaseRing t) (OneBaseOpen t)
      (algebraMap K[X] (OneBaseRing t) q)) hp

/-- The two actual localizations of the polynomial base are isomorphic
under the change `x=1-u`. -/
def oneBaseOpenEquivCoverBase (t : K) : OneBaseOpen t ≃+* BaseRing t where
  toFun := oneBaseOpenToCoverBase t
  invFun := coverBaseToOneBaseOpen t
  left_inv v := by
    have h := congrArg (fun f : OneBaseOpen t →+* OneBaseOpen t => f v)
      (coverBaseToOneBaseOpen_oneBaseOpenToCoverBase t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg (fun f : BaseRing t →+* BaseRing t => f v)
      (oneBaseOpenToCoverBase_coverBaseToOneBaseOpen t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (oneBaseOpenToCoverBase t)
  map_add' := map_add (oneBaseOpenToCoverBase t)

/-- Substitution of `x=(1-u)/t` in a polynomial with original coordinate
`x`. On the chart locus, `t` is a unit and this coefficient is its inverse. -/
def inverseParameterSubstitution (t : K) : K[X] →+* K[X] :=
  eval₂RingHom C (C (inverseParameterCoefficient t) * (1 - X))

@[simp] theorem inverseParameterSubstitution_X (t : K) :
    inverseParameterSubstitution t X = C (inverseParameterCoefficient t) * (1 - X) := by
  simp [inverseParameterSubstitution]

@[simp] theorem inverseParameterSubstitution_C (t c : K) :
    inverseParameterSubstitution t (C c) = C c := by
  simp [inverseParameterSubstitution]

/-- The two nonbranch factors at `x=1/t`, expressed in `u=1-tx`. -/
def inverseParameterBranchProduct (t : K) : K[X] :=
  (1 - X) * (C t - 1 + X)

/-- The full unit factor at `x=1/t`, including exactly `t⁻ᴺ`. -/
def inverseParameterBranchFactorPolynomial (N m : ℕ) (t : K) : K[X] :=
  C ((inverseParameterCoefficient t) ^ N) * (1 - X) ^ m * (C t - 1 + X) ^ (N - m)

/-- The coefficient identity `1-(1-u)/t=(t-1+u)/t`. -/
theorem inverseParameter_complement (t : K) (ht : IsUnit t) :
    1 - C (inverseParameterCoefficient t) * (1 - X : K[X]) = C (inverseParameterCoefficient t) * (C t - 1 + X) := by
  have h : C (inverseParameterCoefficient t) * C t = (1 : K[X]) := by
    rw [← map_mul]
    simp [inverseParameterCoefficient_mul t ht]
  calc
    1 - C (inverseParameterCoefficient t) * (1 - X : K[X]) =
        C (inverseParameterCoefficient t) * C t - C (inverseParameterCoefficient t) * (1 - X) := by rw [h]
    _ = C (inverseParameterCoefficient t) * (C t - 1 + X) := by ring

/-- The branch product at `x=1/t` is a unit scalar times `u` and the
two retained factors. -/
theorem inverseParameterSubstitution_branchProduct (t : K) (ht : IsUnit t) :
    inverseParameterSubstitution t (branchProduct t) =
      C ((inverseParameterCoefficient t) ^ 2) * X * inverseParameterBranchProduct t := by
  simp only [branchProduct, map_mul, map_sub, map_one,
    inverseParameterSubstitution_X, inverseParameterSubstitution_C]
  rw [inverseParameter_complement t ht]
  have htx : 1 - C t * (C (inverseParameterCoefficient t) * (1 - X : K[X])) = X := by
    have h : C t * C (inverseParameterCoefficient t) = (1 : K[X]) := by
      rw [← map_mul]
      simp [mul_inverseParameterCoefficient t ht]
    rw [← mul_assoc, h]
    ring
  rw [htx]
  simp only [inverseParameterBranchProduct, map_pow]
  ring

/-- The Euler radicand at `x=1/t` has branch exponent `m` and the
full scalar factor `t⁻ᴺ`. -/
theorem inverseParameterSubstitution_branchPolynomial (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    inverseParameterSubstitution t (branchPolynomial N m t) =
      X ^ m * inverseParameterBranchFactorPolynomial N m t := by
  simp only [branchPolynomial, map_mul, map_pow, map_sub, map_one,
    inverseParameterSubstitution_X, inverseParameterSubstitution_C]
  rw [inverseParameter_complement t ht]
  have htx : 1 - C t * (C (inverseParameterCoefficient t) * (1 - X : K[X])) = X := by
    have h : C t * C (inverseParameterCoefficient t) = (1 : K[X]) := by
      rw [← map_mul]
      simp [mul_inverseParameterCoefficient t ht]
    rw [← mul_assoc, h]
    ring
  rw [htx]
  have hp : (C (inverseParameterCoefficient t) : K[X]) ^ m * (C (inverseParameterCoefficient t)) ^ (N - m) =
      C ((inverseParameterCoefficient t) ^ N) := by
    rw [← pow_add, Nat.add_sub_of_le hm, map_pow]
  simp only [inverseParameterBranchFactorPolynomial]
  calc
    (C (inverseParameterCoefficient t) * (1 - X : K[X])) ^ m *
        (C (inverseParameterCoefficient t) * (C t - 1 + X)) ^ (N - m) * X ^ m =
      X ^ m * ((C (inverseParameterCoefficient t)) ^ m * (C (inverseParameterCoefficient t)) ^ (N - m)) *
        (1 - X) ^ m * (C t - 1 + X) ^ (N - m) := by
          rw [mul_pow, mul_pow]
          ring
    _ = X ^ m * (C ((inverseParameterCoefficient t) ^ N) * (1 - X) ^ m *
        (C t - 1 + X) ^ (N - m)) := by rw [hp]; ring

/-- The coordinate ring retaining `u=1-tx` near the branch at `1/t`. -/
abbrev InverseParameterBaseRing (t : K) :=
  Localization.Away (inverseParameterBranchProduct t)

/-- The branch parameter `u=1-tx` on this chart. -/
def inverseParameterBaseU (t : K) : InverseParameterBaseRing t :=
  algebraMap K[X] (InverseParameterBaseRing t) X

/-- The exact unit factor in the Euler equation at `x=1/t`. -/
@[expose] def inverseParameterBranchFactor (N m : ℕ) (t : K) :
    InverseParameterBaseRing t :=
  algebraMap K[X] (InverseParameterBaseRing t)
    (inverseParameterBranchFactorPolynomial N m t)

theorem isUnit_inverseParameterBranchFactor (N m : ℕ) (t : K) (ht : IsUnit t) :
    IsUnit (inverseParameterBranchFactor N m t) := by
  have h : IsUnit (algebraMap K[X] (InverseParameterBaseRing t)
      (inverseParameterBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (inverseParameterBranchProduct t)
  simp only [inverseParameterBranchProduct, map_mul, IsUnit.mul_iff] at h
  have htunit : IsUnit (C ((inverseParameterCoefficient t) ^ N) : K[X]) := by
    exact ((isUnit_inverseParameterCoefficient t ht).pow N).map C
  simpa only [inverseParameterBranchFactor,
    inverseParameterBranchFactorPolynomial, map_mul, map_pow] using
    ((htunit.map (algebraMap K[X] (InverseParameterBaseRing t))).mul
      (h.1.pow m)).mul (h.2.pow (N - m))

/-- The exact unit factor at `x=1/t`, as an element of the unit group. -/
def inverseParameterBranchUnit (N m : ℕ) (t : K) (ht : IsUnit t) :
    (InverseParameterBaseRing t)ˣ :=
  (isUnit_inverseParameterBranchFactor N m t ht).unit

@[simp] theorem inverseParameterBranchUnit_val (N m : ℕ) (t : K) (ht : IsUnit t) :
    (inverseParameterBranchUnit N m t ht : InverseParameterBaseRing t) =
      inverseParameterBranchFactor N m t := by
  simp [inverseParameterBranchUnit]

/-- The inverse polynomial change `u=1-tx`. -/
def inverseParameterReverseSubstitution (t : K) : K[X] →+* K[X] :=
  eval₂RingHom C (1 - C t * X)

@[simp] theorem inverseParameterReverseSubstitution_X (t : K) :
    inverseParameterReverseSubstitution t X = 1 - C t * X := by
  simp [inverseParameterReverseSubstitution]

@[simp] theorem inverseParameterReverseSubstitution_C (t c : K) :
    inverseParameterReverseSubstitution t (C c) = C c := by
  simp [inverseParameterReverseSubstitution]

/-- The two retained inverse-parameter factors map to
`t²x(1-x)` in the original coordinate. -/
theorem inverseParameterReverseSubstitution_branchProduct (t : K) :
    inverseParameterReverseSubstitution t
      (inverseParameterBranchProduct t) =
        C (t ^ 2) * X * (1 - X) := by
  simp [inverseParameterReverseSubstitution,
    inverseParameterBranchProduct]
  ring

/-- The full factor at `1/t` becomes `x^m(1-x)^(N-m)` in the original
coordinate; the two substituted powers cancel exactly the `t⁻ᴺ` scalar. -/
theorem inverseParameterReverseSubstitution_factorPolynomial (N m : ℕ)
    (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    inverseParameterReverseSubstitution t
      (inverseParameterBranchFactorPolynomial N m t) =
        X ^ m * (1 - X) ^ (N - m) := by
  have hscalar : (inverseParameterCoefficient t) ^ N * t ^ m * t ^ (N - m) = 1 := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hm, ← mul_pow]
    simp [inverseParameterCoefficient_mul t ht]
  have hC : C ((inverseParameterCoefficient t) ^ N) * (C t : K[X]) ^ m * (C t) ^ (N - m) = 1 := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, hscalar, map_one]
  simp only [inverseParameterBranchFactorPolynomial, map_mul, map_pow,
    map_sub, map_add, map_one, inverseParameterReverseSubstitution_X,
    inverseParameterReverseSubstitution_C]
  have hu : 1 - (1 - C t * X : K[X]) = C t * X := by ring
  have hv : C t - 1 + (1 - C t * X : K[X]) = C t * (1 - X) := by ring
  rw [hu, hv, mul_pow, mul_pow]
  rw [← map_pow (C : K →+* K[X]) (inverseParameterCoefficient t) N]
  calc
    C ((inverseParameterCoefficient t) ^ N) * ((C t) ^ m * X ^ m) *
        ((C t) ^ (N - m) * (1 - X) ^ (N - m)) =
      (C ((inverseParameterCoefficient t) ^ N) * (C t) ^ m * (C t) ^ (N - m)) *
        X ^ m * (1 - X) ^ (N - m) := by ring
    _ = X ^ m * (1 - X) ^ (N - m) := by rw [hC]; ring

/-- The inverse-parameter polynomial base maps to the actual branch
complement by `u ↦ 1-tx`. -/
def inverseParameterPolynomialToCoverBase (t : K) : K[X] →+* BaseRing t :=
  (algebraMap K[X] (BaseRing t)).comp
    (inverseParameterReverseSubstitution t)

/-- The retained inverse-parameter factors are invertible on the actual
branch complement. -/
theorem isUnit_inverseParameterBranchProduct_coverBase (t : K) (ht : IsUnit t) :
    IsUnit (inverseParameterPolynomialToCoverBase t
      (inverseParameterBranchProduct t)) := by
  have h : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  change IsUnit (algebraMap K[X] (BaseRing t)
    (inverseParameterReverseSubstitution t (inverseParameterBranchProduct t)))
  rw [inverseParameterReverseSubstitution_branchProduct]
  simp only [map_mul]
  have hscalar : IsUnit (C (t ^ 2) : K[X]) :=
    ((ht.pow 2).map C)
  exact ((hscalar.map (algebraMap K[X] (BaseRing t))).mul h.1.1).mul h.1.2

/-- The actual localization map from the inverse-parameter chart base to
the Euler base. -/
def inverseParameterBaseToCoverBase (t : K) (ht : IsUnit t) :
    InverseParameterBaseRing t →+* BaseRing t :=
  Localization.awayLift (inverseParameterPolynomialToCoverBase t)
    (inverseParameterBranchProduct t)
    (isUnit_inverseParameterBranchProduct_coverBase t ht)

@[simp] theorem inverseParameterBaseToCoverBase_polynomial
    (t : K) (ht : IsUnit t) (p : K[X]) :
    inverseParameterBaseToCoverBase t ht
      (algebraMap K[X] (InverseParameterBaseRing t) p) =
        algebraMap K[X] (BaseRing t)
          (inverseParameterReverseSubstitution t p) := by
  simp [inverseParameterBaseToCoverBase, inverseParameterPolynomialToCoverBase,
    Localization.awayLift, IsLocalization.Away.lift_eq]

@[simp] theorem inverseParameterBaseToCoverBase_u (t : K) (ht : IsUnit t) :
    inverseParameterBaseToCoverBase t ht (inverseParameterBaseU t) =
      1 - algebraMap K[X] (BaseRing t) (C t) *
        algebraMap K[X] (BaseRing t) X := by
  rw [inverseParameterBaseU,
    inverseParameterBaseToCoverBase_polynomial,
    inverseParameterReverseSubstitution_X]
  simp

/-- On the original branch complement the full unit factor at `1/t`
becomes `x^m(1-x)^(N-m)`. -/
theorem inverseParameterBaseToCoverBase_factor (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    inverseParameterBaseToCoverBase t ht
        (inverseParameterBranchFactor N m t) =
      (algebraMap K[X] (BaseRing t) X) ^ m *
        (1 - algebraMap K[X] (BaseRing t) X) ^ (N - m) := by
  rw [inverseParameterBranchFactor,
    inverseParameterBaseToCoverBase_polynomial,
    inverseParameterReverseSubstitution_factorPolynomial N m t ht hm]
  simp only [map_mul, map_pow, map_sub, map_one]

/-- The original radicand is `u^m U` on the inverse-parameter overlap. -/
theorem radicand_eq_inverseParameterBranchFactor (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    radicand N m t =
      inverseParameterBaseToCoverBase t ht
        (inverseParameterBaseU t) ^ m *
      inverseParameterBaseToCoverBase t ht
        (inverseParameterBranchUnit N m t ht : InverseParameterBaseRing t) := by
  rw [inverseParameterBranchUnit_val,
    inverseParameterBaseToCoverBase_u,
    inverseParameterBaseToCoverBase_factor N m t ht hm]
  simp only [radicand, branchPolynomial, map_mul, map_pow, map_sub, map_one]
  ring

/-- The inverse-parameter chart base with `u=1-tx` inverted. -/
abbrev InverseParameterBaseOpen (t : K) :=
  Localization.Away (inverseParameterBaseU t)

/-- The branch parameter is a unit on the inverse-parameter open. -/
def inverseParameterBaseOpenUUnit (t : K) : (InverseParameterBaseOpen t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (inverseParameterBaseU t)).unit

@[simp] theorem inverseParameterBaseOpenUUnit_val (t : K) :
    (inverseParameterBaseOpenUUnit t : InverseParameterBaseOpen t) =
      algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t)
        (inverseParameterBaseU t) := by
  simp [inverseParameterBaseOpenUUnit]

/-- Original polynomials map into the inverse-parameter open by
`x=(1-u)/t`. -/
def polynomialToInverseParameterBaseOpen (t : K) :
    K[X] →+* InverseParameterBaseOpen t :=
  ((algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t)).comp
    (algebraMap K[X] (InverseParameterBaseRing t))).comp
      (inverseParameterSubstitution t)

/-- The original branch product becomes a unit on the inverse-parameter
open, including its scalar factor `t⁻²`. -/
theorem isUnit_branchProduct_inverseParameterBaseOpen (t : K) (ht : IsUnit t) :
    IsUnit (polynomialToInverseParameterBaseOpen t (branchProduct t)) := by
  change IsUnit (algebraMap (InverseParameterBaseRing t)
    (InverseParameterBaseOpen t)
    (algebraMap K[X] (InverseParameterBaseRing t)
      (inverseParameterSubstitution t (branchProduct t))))
  rw [inverseParameterSubstitution_branchProduct t ht, map_mul, map_mul,
    map_mul, map_mul]
  have hscalar : IsUnit (C ((inverseParameterCoefficient t) ^ 2) : K[X]) :=
    ((isUnit_inverseParameterCoefficient t ht).pow 2).map C
  have hproduct : IsUnit (algebraMap K[X] (InverseParameterBaseRing t)
      (inverseParameterBranchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (inverseParameterBranchProduct t)
  exact ((hscalar.map (algebraMap K[X] (InverseParameterBaseRing t))).map
    (algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t))).mul
      (inverseParameterBaseOpenUUnit t).isUnit |>.mul
        (hproduct.map (algebraMap (InverseParameterBaseRing t)
          (InverseParameterBaseOpen t)))

/-- The Euler base restricts to the open centered at `x=1/t`. -/
def coverBaseToInverseParameterBaseOpen (t : K) (ht : IsUnit t) :
    BaseRing t →+* InverseParameterBaseOpen t :=
  Localization.awayLift (polynomialToInverseParameterBaseOpen t)
    (branchProduct t) (isUnit_branchProduct_inverseParameterBaseOpen t ht)

@[simp] theorem coverBaseToInverseParameterBaseOpen_polynomial (t : K)
    (ht : IsUnit t) (p : K[X]) :
    coverBaseToInverseParameterBaseOpen t ht
      (algebraMap K[X] (BaseRing t) p) =
        polynomialToInverseParameterBaseOpen t p := by
  simp [coverBaseToInverseParameterBaseOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The parameter `u=1-tx` is invertible in the original Euler base. -/
theorem isUnit_inverseParameterBaseU_coverBase (t : K) (ht : IsUnit t) :
    IsUnit (inverseParameterBaseToCoverBase t ht (inverseParameterBaseU t)) := by
  have h : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  simp only [branchProduct, map_mul, IsUnit.mul_iff] at h
  rw [inverseParameterBaseToCoverBase_u]
  simpa only [map_sub, map_one, map_mul] using h.2

/-- Restriction from the inverse-parameter open to the Euler base. -/
def inverseParameterBaseOpenToCoverBase (t : K) (ht : IsUnit t) :
    InverseParameterBaseOpen t →+* BaseRing t :=
  Localization.awayLift (inverseParameterBaseToCoverBase t ht)
    (inverseParameterBaseU t) (isUnit_inverseParameterBaseU_coverBase t ht)

@[simp] theorem inverseParameterBaseOpenToCoverBase_base (t : K)
    (ht : IsUnit t) (v : InverseParameterBaseRing t) :
    inverseParameterBaseOpenToCoverBase t ht
      (algebraMap (InverseParameterBaseRing t)
        (InverseParameterBaseOpen t) v) =
          inverseParameterBaseToCoverBase t ht v := by
  simp [inverseParameterBaseOpenToCoverBase, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The two inverse-parameter substitutions undo one another when `t` is nonzero. -/
theorem inverseParameterSubstitution_reverse (t : K) (ht : IsUnit t) :
    (inverseParameterSubstitution t).comp
      (inverseParameterReverseSubstitution t) = RingHom.id K[X] := by
  ext
  · simp [inverseParameterSubstitution, inverseParameterReverseSubstitution]
  · have h : (C t : K[X]) * C (inverseParameterCoefficient t) = 1 := by
      rw [← map_mul]
      simp [mul_inverseParameterCoefficient t ht]
    simp [inverseParameterSubstitution, inverseParameterReverseSubstitution,
      ← mul_assoc, h]

/-- The reverse affine substitution also undoes the forward substitution. -/
theorem inverseParameterReverse_substitution (t : K) (ht : IsUnit t) :
    (inverseParameterReverseSubstitution t).comp
      (inverseParameterSubstitution t) = RingHom.id K[X] := by
  ext
  · simp [inverseParameterSubstitution, inverseParameterReverseSubstitution]
  · have h : (C (inverseParameterCoefficient t) : K[X]) * C t = 1 := by
      rw [← map_mul]
      simp [inverseParameterCoefficient_mul t ht]
    simp [inverseParameterSubstitution, inverseParameterReverseSubstitution,
      ← mul_assoc, h]

/-- The restriction and reverse affine change compose to the identity on
the original Euler base. -/
theorem inverseParameterBaseOpenToCoverBase_coverBaseToOpen
    (t : K) (ht : IsUnit t) :
    (inverseParameterBaseOpenToCoverBase t ht).comp
      (coverBaseToInverseParameterBaseOpen t ht) =
        RingHom.id (BaseRing t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
  apply RingHom.ext
  intro p
  change inverseParameterBaseOpenToCoverBase t ht
    (coverBaseToInverseParameterBaseOpen t ht
      (algebraMap K[X] (BaseRing t) p)) = _
  rw [coverBaseToInverseParameterBaseOpen_polynomial]
  change inverseParameterBaseOpenToCoverBase t ht
    (algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t)
      (algebraMap K[X] (InverseParameterBaseRing t)
        (inverseParameterSubstitution t p))) = _
  rw [inverseParameterBaseOpenToCoverBase_base,
    inverseParameterBaseToCoverBase_polynomial]
  have hp := congrArg (fun f : K[X] →+* K[X] => f p)
    (inverseParameterReverse_substitution t ht)
  simpa only [RingHom.comp_apply, RingHom.id_apply] using congrArg
    (algebraMap K[X] (BaseRing t)) hp

/-- The two affine changes compose to the identity on the open chart base. -/
theorem coverBaseToInverseParameterBaseOpen_inverseParameterBaseOpenToCoverBase
    (t : K) (ht : IsUnit t) :
    (coverBaseToInverseParameterBaseOpen t ht).comp
      (inverseParameterBaseOpenToCoverBase t ht) =
        RingHom.id (InverseParameterBaseOpen t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (inverseParameterBaseU t))
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (inverseParameterBranchProduct t))
  apply RingHom.ext
  intro p
  change coverBaseToInverseParameterBaseOpen t ht
    (inverseParameterBaseOpenToCoverBase t ht
      (algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t)
        (algebraMap K[X] (InverseParameterBaseRing t) p))) = _
  rw [inverseParameterBaseOpenToCoverBase_base,
    inverseParameterBaseToCoverBase_polynomial,
    coverBaseToInverseParameterBaseOpen_polynomial]
  change algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t)
    (algebraMap K[X] (InverseParameterBaseRing t)
      (inverseParameterSubstitution t
        (inverseParameterReverseSubstitution t p))) = _
  have hp := congrArg (fun f : K[X] →+* K[X] => f p)
    (inverseParameterSubstitution_reverse t ht)
  simpa only [RingHom.comp_apply, RingHom.id_apply] using congrArg
    (fun q : K[X] => algebraMap (InverseParameterBaseRing t)
      (InverseParameterBaseOpen t)
      (algebraMap K[X] (InverseParameterBaseRing t) q)) hp

/-- The actual Euler base is the localization of the inverse-parameter
chart at `u=1-tx`. -/
def inverseParameterBaseOpenEquivCoverBase (t : K) (ht : IsUnit t) :
    InverseParameterBaseOpen t ≃+* BaseRing t where
  toFun := inverseParameterBaseOpenToCoverBase t ht
  invFun := coverBaseToInverseParameterBaseOpen t ht
  left_inv v := by
    have h := congrArg
      (fun f : InverseParameterBaseOpen t →+* InverseParameterBaseOpen t => f v)
      (coverBaseToInverseParameterBaseOpen_inverseParameterBaseOpenToCoverBase t ht)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg (fun f : BaseRing t →+* BaseRing t => f v)
      (inverseParameterBaseOpenToCoverBase_coverBaseToOpen t ht)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (inverseParameterBaseOpenToCoverBase t ht)
  map_add' := map_add (inverseParameterBaseOpenToCoverBase t ht)

/-! ## The original singular coordinate on each finite branch base -/

/-- The original Euler equation after the substitution `u=1-x`. Its
covering coordinate is still the manuscript's `y`. -/
@[expose] def oneSingularPolynomial (N m : ℕ) (t : K) : (OneBaseRing t)[X] :=
  RingTheory.Smooth.localizedKummerEquation (oneBranchProduct t)
    (X ^ (N - m) * oneBranchFactorPolynomial m t) N

/-- The actual singular Euler root algebra on the base centered at one. -/
abbrev OneSingularRing (N m : ℕ) (t : K) :=
  AdjoinRoot (oneSingularPolynomial N m t)

/-- The original covering coordinate on the singular one chart. -/
def oneSingularRoot (N m : ℕ) (t : K) : OneSingularRing N m t :=
  AdjoinRoot.root (oneSingularPolynomial N m t)

theorem oneSingularRoot_pow (N m : ℕ) (t : K) :
    oneSingularRoot N m t ^ N =
      algebraMap (OneBaseRing t) (OneSingularRing N m t)
        (oneBaseU t ^ (N - m) * (oneBranchUnit m t : OneBaseRing t)) :=
  by
    calc
      _ = algebraMap (OneBaseRing t) (OneSingularRing N m t)
          (algebraMap K[X] (OneBaseRing t)
            (X ^ (N - m) * oneBranchFactorPolynomial m t)) := by
            exact AdjoinRoot.root_X_pow_sub_C_pow N _
      _ = _ := by
        simp only [oneBaseU, oneBranchUnit_val, oneBranchFactor, map_mul, map_pow]

/-- Restriction of the one-chart base to the actual Euler cover. -/
def oneBaseToCover (N m : ℕ) (t : K) : OneBaseRing t →+* CoverRing N m t :=
  (algebraMap (BaseRing t) (CoverRing N m t)).comp (oneBaseToCoverBase t)

/-- On the original Euler cover, the singular one-chart coordinate is `y`. -/
def oneSingularToCover (N m : ℕ) (t : K) :
    OneSingularRing N m t →+* CoverRing N m t :=
  AdjoinRoot.lift (oneBaseToCover N m t) (coverRoot N m t) (by
    simp only [oneSingularPolynomial, RingTheory.Smooth.localizedKummerEquation,
      eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [sub_eq_zero, coverRoot_pow, radicand_eq_oneBranchFactor,
      map_mul, map_pow]
    simp only [oneBaseToCover, RingHom.comp_apply, map_mul, map_pow,
      oneBaseU, oneBranchUnit_val, oneBranchFactor])

@[simp] theorem oneSingularToCover_root (N m : ℕ) (t : K) :
    oneSingularToCover N m t (oneSingularRoot N m t) = coverRoot N m t := by
  simp [oneSingularToCover, oneSingularRoot]

@[simp] theorem oneSingularToCover_oneBase (N m : ℕ) (t : K)
    (v : OneBaseRing t) :
    oneSingularToCover N m t
      (algebraMap (OneBaseRing t) (OneSingularRing N m t) v) =
        oneBaseToCover N m t v := by
  simp [oneSingularToCover, AdjoinRoot.lift_of]

/-- The original Euler equation after `u=1-tx`, with its exact
`t⁻ᴺ` factor and the unchanged covering coordinate `y`. -/
@[expose] def inverseParameterSingularPolynomial (N m : ℕ) (t : K) :
    (InverseParameterBaseRing t)[X] :=
  RingTheory.Smooth.localizedKummerEquation (inverseParameterBranchProduct t)
    (X ^ m * inverseParameterBranchFactorPolynomial N m t) N

/-- The singular Euler root algebra centered at `x=1/t`. -/
abbrev InverseParameterSingularRing (N m : ℕ) (t : K) :=
  AdjoinRoot (inverseParameterSingularPolynomial N m t)

/-- The original covering coordinate on the singular `1/t` chart. -/
def inverseParameterSingularRoot (N m : ℕ) (t : K) :
    InverseParameterSingularRing N m t :=
  AdjoinRoot.root (inverseParameterSingularPolynomial N m t)

theorem inverseParameterSingularRoot_pow (N m : ℕ) (t : K) :
    inverseParameterSingularRoot N m t ^ N =
      algebraMap (InverseParameterBaseRing t)
        (InverseParameterSingularRing N m t)
        (inverseParameterBaseU t ^ m *
          (inverseParameterBranchFactor N m t : InverseParameterBaseRing t)) :=
  by
    calc
      _ = algebraMap (InverseParameterBaseRing t)
          (InverseParameterSingularRing N m t)
          (algebraMap K[X] (InverseParameterBaseRing t)
            (X ^ m * inverseParameterBranchFactorPolynomial N m t)) := by
            exact AdjoinRoot.root_X_pow_sub_C_pow N _
      _ = _ := by
        simp only [inverseParameterBaseU, inverseParameterBranchFactor,
          map_mul, map_pow]

/-- Restriction of the `1/t`-chart base to the actual Euler cover. -/
def inverseParameterBaseToCover (N m : ℕ) (t : K) (ht : IsUnit t) :
    InverseParameterBaseRing t →+* CoverRing N m t :=
  (algebraMap (BaseRing t) (CoverRing N m t)).comp
    (inverseParameterBaseToCoverBase t ht)

/-- The original `y` coordinate maps identically to the actual Euler cover. -/
def inverseParameterSingularToCover (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    InverseParameterSingularRing N m t →+* CoverRing N m t :=
  AdjoinRoot.lift (inverseParameterBaseToCover N m t ht)
    (coverRoot N m t) (by
      simp only [inverseParameterSingularPolynomial,
        RingTheory.Smooth.localizedKummerEquation, eval₂_sub, eval₂_pow,
        eval₂_X, eval₂_C]
      rw [sub_eq_zero, coverRoot_pow,
        radicand_eq_inverseParameterBranchFactor N m t ht hm,
        map_mul, map_pow]
      rw [inverseParameterBranchUnit_val]
      simp only [inverseParameterBaseToCover, RingHom.comp_apply,
        inverseParameterBaseU, inverseParameterBranchFactor,
        map_mul, map_pow])

@[simp] theorem inverseParameterSingularToCover_root (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    inverseParameterSingularToCover N m t ht hm
      (inverseParameterSingularRoot N m t) = coverRoot N m t := by
  simp [inverseParameterSingularToCover, inverseParameterSingularRoot]

@[simp] theorem inverseParameterSingularToCover_base (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (v : InverseParameterBaseRing t) :
    inverseParameterSingularToCover N m t ht hm
      (algebraMap (InverseParameterBaseRing t) (InverseParameterSingularRing N m t) v) =
        inverseParameterBaseToCover N m t ht v := by
  simp [inverseParameterSingularToCover, AdjoinRoot.lift_of]

/-! ## The punctured singular chart at one -/

/-- The branch parameter inside the singular algebra at one. -/
@[expose] def oneSingularU (N m : ℕ) (t : K) : OneSingularRing N m t :=
  tameSingularX (oneBranchProduct t) (oneBranchFactorPolynomial m t) N (N - m)

@[simp] theorem oneSingularU_eq_base (N m : ℕ) (t : K) :
    oneSingularU N m t =
      algebraMap (OneBaseRing t) (OneSingularRing N m t) (oneBaseU t) := by
  rfl

/-- The singular chart at one restricted to its punctured branch parameter. -/
abbrev OneSingularOpen (N m : ℕ) (t : K) :=
  Localization.Away (oneSingularU N m t)

/-- The localized singular chart receives its original polynomial base. -/
def oneBaseToSingularOpen (N m : ℕ) (t : K) :
    OneBaseRing t →+* OneSingularOpen N m t :=
  (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)).comp
    (algebraMap (OneBaseRing t) (OneSingularRing N m t))

/-- The branch parameter becomes invertible on the singular overlap. -/
def oneSingularOpenUUnit (N m : ℕ) (t : K) :
    (OneSingularOpen N m t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (oneSingularU N m t)).unit

@[simp] theorem oneSingularOpenUUnit_val (N m : ℕ) (t : K) :
    (oneSingularOpenUUnit N m t : OneSingularOpen N m t) =
      oneBaseToSingularOpen N m t (oneBaseU t) := by
  simp only [oneSingularOpenUUnit, oneBaseToSingularOpen, RingHom.comp_apply]
  rfl

/-- The punctured one-chart base maps into the singular covering overlap. -/
def oneBaseOpenToSingularOpen (N m : ℕ) (t : K) :
    OneBaseOpen t →+* OneSingularOpen N m t :=
  Localization.awayLift (oneBaseToSingularOpen N m t) (oneBaseU t) (by
    change IsUnit (oneSingularOpenUUnit N m t : OneSingularOpen N m t)
    exact (oneSingularOpenUUnit N m t).isUnit)

@[simp] theorem oneBaseOpenToSingularOpen_oneBase (N m : ℕ) (t : K)
    (v : OneBaseRing t) :
    oneBaseOpenToSingularOpen N m t
        (algebraMap (OneBaseRing t) (OneBaseOpen t) v) =
      oneBaseToSingularOpen N m t v := by
  simp [oneBaseOpenToSingularOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The actual Euler base acts on the singular overlap through the
substitution `u=1-x`. -/
def coverBaseToOneSingularOpen (N m : ℕ) (t : K) :
    BaseRing t →+* OneSingularOpen N m t :=
  (oneBaseOpenToSingularOpen N m t).comp (coverBaseToOneBaseOpen t)

@[simp] theorem coverBaseToOneSingularOpen_oneBase (N m : ℕ) (t : K)
    (v : OneBaseRing t) :
    coverBaseToOneSingularOpen N m t (oneBaseToCoverBase t v) =
      oneBaseToSingularOpen N m t v := by
  have h := congrArg
    (fun f : OneBaseOpen t →+* OneBaseOpen t =>
      (oneBaseOpenToSingularOpen N m t).comp f)
    (coverBaseToOneBaseOpen_oneBaseOpenToCoverBase t)
  have hv := congrArg
    (fun f : OneBaseOpen t →+* OneSingularOpen N m t =>
      f (algebraMap (OneBaseRing t) (OneBaseOpen t) v)) h
  simpa only [coverBaseToOneSingularOpen, RingHom.comp_apply, RingHom.id_apply,
    oneBaseOpenToCoverBase_oneBase,
    oneBaseOpenToSingularOpen_oneBase] using hv

/-- The original equation holds in the singular overlap with unchanged
cover coordinate `y`. -/
theorem oneSingularOpenRoot_pow (N m : ℕ) (t : K) :
    (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
      (oneSingularRoot N m t)) ^ N =
        coverBaseToOneSingularOpen N m t (radicand N m t) := by
  rw [radicand_eq_oneBranchFactor, map_mul, map_pow,
    coverBaseToOneSingularOpen_oneBase,
    coverBaseToOneSingularOpen_oneBase]
  rw [← map_pow, oneSingularRoot_pow]
  simp [oneBaseToSingularOpen, map_mul, map_pow,
    oneBranchUnit_val]

/-- The original Euler algebra maps to the punctured singular one-chart,
fixing the manuscript's coordinate `y`. -/
def coverToOneSingularOpen (N m : ℕ) (t : K) :
    CoverRing N m t →+* OneSingularOpen N m t :=
  AdjoinRoot.lift (coverBaseToOneSingularOpen N m t)
    (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
      (oneSingularRoot N m t)) (by
    simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [sub_eq_zero]
    exact oneSingularOpenRoot_pow N m t)

@[simp] theorem coverToOneSingularOpen_root (N m : ℕ) (t : K) :
    coverToOneSingularOpen N m t (coverRoot N m t) =
      algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
        (oneSingularRoot N m t) := by
  simp [coverToOneSingularOpen, coverRoot]

/-- The singular one-chart maps to the Euler cover after inverting `u`. -/
def oneSingularOpenToCover (N m : ℕ) (t : K) :
    OneSingularOpen N m t →+* CoverRing N m t :=
  Localization.awayLift (oneSingularToCover N m t) (oneSingularU N m t) (by
    rw [oneSingularU_eq_base, oneSingularToCover_oneBase]
    exact (isUnit_oneBaseU_coverBase t).map
      (algebraMap (BaseRing t) (CoverRing N m t)))

@[simp] theorem oneSingularOpenToCover_root (N m : ℕ) (t : K) :
    oneSingularOpenToCover N m t
        (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
          (oneSingularRoot N m t)) = coverRoot N m t := by
  simp [oneSingularOpenToCover, Localization.awayLift,
    IsLocalization.Away.lift_eq]

@[simp] theorem oneSingularOpenToCover_oneBase (N m : ℕ) (t : K)
    (v : OneBaseRing t) :
    oneSingularOpenToCover N m t (oneBaseToSingularOpen N m t v) =
      oneBaseToCover N m t v := by
  simp [oneSingularOpenToCover, oneBaseToSingularOpen,
    oneSingularToCover, IsLocalization.Away.lift_eq, AdjoinRoot.lift_of]

@[simp] theorem oneSingularOpenToCover_coverBase (N m : ℕ) (t : K)
    (v : BaseRing t) :
    oneSingularOpenToCover N m t (coverBaseToOneSingularOpen N m t v) =
      algebraMap (BaseRing t) (CoverRing N m t) v := by
  have h : (oneSingularOpenToCover N m t).comp
      (oneBaseOpenToSingularOpen N m t) =
        (algebraMap (BaseRing t) (CoverRing N m t)).comp
          (oneBaseOpenToCoverBase t) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (oneBaseU t))
    apply RingHom.ext
    intro w
    simp only [RingHom.comp_apply, oneBaseOpenToSingularOpen_oneBase,
      oneSingularOpenToCover_oneBase, oneBaseOpenToCoverBase_oneBase,
      oneBaseToCover, RingHom.comp_apply]
  have hv := congrArg
    (fun f : OneBaseOpen t →+* CoverRing N m t =>
      f (coverBaseToOneBaseOpen t v)) h
  have hbase := congrArg (fun f : BaseRing t →+* BaseRing t => f v)
    (oneBaseOpenToCoverBase_coverBaseToOneBaseOpen t)
  simp only [RingHom.comp_apply, RingHom.id_apply] at hbase
  simpa only [coverBaseToOneSingularOpen, RingHom.comp_apply,
    hbase] using hv

@[simp] theorem coverToOneSingularOpen_oneBase (N m : ℕ) (t : K)
    (v : OneBaseRing t) :
    coverToOneSingularOpen N m t (oneBaseToCover N m t v) =
      oneBaseToSingularOpen N m t v := by
  simp only [oneBaseToCover, RingHom.comp_apply]
  change coverToOneSingularOpen N m t
    (algebraMap (BaseRing t) (CoverRing N m t)
      (oneBaseToCoverBase t v)) = _
  rw [show coverToOneSingularOpen N m t
      (algebraMap (BaseRing t) (CoverRing N m t)
        (oneBaseToCoverBase t v)) =
      coverBaseToOneSingularOpen N m t (oneBaseToCoverBase t v) from by
        simp [coverToOneSingularOpen, AdjoinRoot.lift_of]]
  exact coverBaseToOneSingularOpen_oneBase N m t v

/-- The original Euler cover and the punctured singular one-chart agree. -/
theorem oneSingularOpenToCover_coverToOneSingularOpen (N m : ℕ) (t : K) :
    (oneSingularOpenToCover N m t).comp (coverToOneSingularOpen N m t) =
      RingHom.id (CoverRing N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    simp [coverToOneSingularOpen, AdjoinRoot.lift_of]
  · change oneSingularOpenToCover N m t
      (coverToOneSingularOpen N m t (coverRoot N m t)) = _
    rw [coverToOneSingularOpen_root, oneSingularOpenToCover_root]
    rfl

theorem coverToOneSingularOpen_oneSingularOpenToCover (N m : ℕ) (t : K) :
    (coverToOneSingularOpen N m t).comp (oneSingularOpenToCover N m t) =
      RingHom.id (OneSingularOpen N m t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (oneSingularU N m t))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change coverToOneSingularOpen N m t
      (oneSingularOpenToCover N m t
        (oneBaseToSingularOpen N m t v)) = _
    rw [oneSingularOpenToCover_oneBase, coverToOneSingularOpen_oneBase]
    rfl
  · change coverToOneSingularOpen N m t
      (oneSingularOpenToCover N m t
        (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
          (oneSingularRoot N m t))) = _
    rw [oneSingularOpenToCover_root, coverToOneSingularOpen_root]
    rfl

/-- The punctured singular algebra at one is the actual Euler cover. -/
def oneSingularOpenEquivCover (N m : ℕ) (t : K) :
    OneSingularOpen N m t ≃+* CoverRing N m t where
  toFun := oneSingularOpenToCover N m t
  invFun := coverToOneSingularOpen N m t
  left_inv v := by
    have h := congrArg
      (fun f : OneSingularOpen N m t →+* OneSingularOpen N m t => f v)
      (coverToOneSingularOpen_oneSingularOpenToCover N m t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg
      (fun f : CoverRing N m t →+* CoverRing N m t => f v)
      (oneSingularOpenToCover_coverToOneSingularOpen N m t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (oneSingularOpenToCover N m t)
  map_add' := map_add (oneSingularOpenToCover N m t)

theorem oneBaseToSingularOpen_coeff (N m : ℕ) (t c : K) :
    oneBaseToSingularOpen N m t (algebraMap K (OneBaseRing t) c) =
      algebraMap K (OneSingularOpen N m t) c := by
  change (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t))
    (algebraMap (OneBaseRing t) (OneSingularRing N m t)
      (algebraMap K (OneBaseRing t) c)) = _
  rw [← IsScalarTower.algebraMap_apply K (OneBaseRing t)
    (OneSingularRing N m t) c]
  exact (IsScalarTower.algebraMap_apply K (OneSingularRing N m t)
    (OneSingularOpen N m t) c).symm

/-- Under the one-chart overlap, the original coordinate is `x=1-u`. -/
theorem coverToOneSingularOpen_x (N m : ℕ) (t : K) :
    coverToOneSingularOpen N m t
        (algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap K[X] (BaseRing t) X)) =
      1 - oneBaseToSingularOpen N m t (oneBaseU t) := by
  rw [show coverToOneSingularOpen N m t
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) X)) =
      coverBaseToOneSingularOpen N m t
        (algebraMap K[X] (BaseRing t) X) from by
          simp [coverToOneSingularOpen, AdjoinRoot.lift_of]]
  simp [coverBaseToOneSingularOpen, coverBaseToOneBaseOpen_polynomial,
    polynomialToOneBaseOpen, oneSubstitution, oneBaseToSingularOpen,
    oneBaseU]

/-! ## The punctured singular chart at the inverse parameter -/

/-- The branch parameter inside the singular algebra at `1/t`. -/
@[expose] def inverseParameterSingularU (N m : ℕ) (t : K) : InverseParameterSingularRing N m t :=
  tameSingularX (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m

@[simp] theorem inverseParameterSingularU_eq_base (N m : ℕ) (t : K) :
    inverseParameterSingularU N m t =
      algebraMap (InverseParameterBaseRing t) (InverseParameterSingularRing N m t)
        (inverseParameterBaseU t) := by
  rfl

/-- The singular chart at `1/t` restricted to its punctured branch parameter. -/
abbrev InverseParameterSingularOpen (N m : ℕ) (t : K) :=
  Localization.Away (inverseParameterSingularU N m t)

/-- The localized singular chart receives its original polynomial base. -/
def inverseParameterBaseToSingularOpen (N m : ℕ) (t : K) :
    InverseParameterBaseRing t →+* InverseParameterSingularOpen N m t :=
  (algebraMap (InverseParameterSingularRing N m t) (InverseParameterSingularOpen N m t)).comp
    (algebraMap (InverseParameterBaseRing t) (InverseParameterSingularRing N m t))

/-- The branch parameter becomes invertible on the singular overlap. -/
def inverseParameterSingularOpenUUnit (N m : ℕ) (t : K) :
    (InverseParameterSingularOpen N m t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (inverseParameterSingularU N m t)).unit

@[simp] theorem inverseParameterSingularOpenUUnit_val (N m : ℕ) (t : K) :
    (inverseParameterSingularOpenUUnit N m t : InverseParameterSingularOpen N m t) =
      inverseParameterBaseToSingularOpen N m t (inverseParameterBaseU t) := by
  simp only [inverseParameterSingularOpenUUnit, inverseParameterBaseToSingularOpen,
    RingHom.comp_apply]
  rfl

/-- The punctured inverse-parameter chart base maps into the singular covering overlap. -/
def inverseParameterBaseOpenToSingularOpen (N m : ℕ) (t : K) :
    InverseParameterBaseOpen t →+* InverseParameterSingularOpen N m t :=
  Localization.awayLift (inverseParameterBaseToSingularOpen N m t) (inverseParameterBaseU t) (by
    change IsUnit (inverseParameterSingularOpenUUnit N m t : InverseParameterSingularOpen N m t)
    exact (inverseParameterSingularOpenUUnit N m t).isUnit)

@[simp] theorem inverseParameterBaseOpenToSingularOpen_base (N m : ℕ) (t : K)
    (v : InverseParameterBaseRing t) :
    inverseParameterBaseOpenToSingularOpen N m t
        (algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t) v) =
      inverseParameterBaseToSingularOpen N m t v := by
  simp [inverseParameterBaseOpenToSingularOpen, Localization.awayLift,
    IsLocalization.Away.lift_eq]

/-- The actual Euler base acts on the singular overlap through the
substitution `u=1-tx`. -/
def coverBaseToInverseParameterSingularOpen (N m : ℕ) (t : K) (ht : IsUnit t) :
    BaseRing t →+* InverseParameterSingularOpen N m t :=
  (inverseParameterBaseOpenToSingularOpen N m t).comp (coverBaseToInverseParameterBaseOpen t ht)

@[simp] theorem coverBaseToInverseParameterSingularOpen_base (N m : ℕ) (t : K) (ht : IsUnit t)
    (v : InverseParameterBaseRing t) :
    coverBaseToInverseParameterSingularOpen N m t ht (inverseParameterBaseToCoverBase t ht v) =
      inverseParameterBaseToSingularOpen N m t v := by
  have h := congrArg
    (fun f : InverseParameterBaseOpen t →+* InverseParameterBaseOpen t =>
      (inverseParameterBaseOpenToSingularOpen N m t).comp f)
    (coverBaseToInverseParameterBaseOpen_inverseParameterBaseOpenToCoverBase t ht)
  have hv := congrArg
    (fun f : InverseParameterBaseOpen t →+* InverseParameterSingularOpen N m t =>
      f (algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t) v)) h
  simpa only [coverBaseToInverseParameterSingularOpen, RingHom.comp_apply, RingHom.id_apply,
    inverseParameterBaseOpenToCoverBase_base,
    inverseParameterBaseOpenToSingularOpen_base] using hv

/-- The original equation holds in the singular overlap with unchanged
cover coordinate `y`. -/
theorem inverseParameterSingularOpenRoot_pow (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    (algebraMap (InverseParameterSingularRing N m t) (InverseParameterSingularOpen N m t)
      (inverseParameterSingularRoot N m t)) ^ N =
        coverBaseToInverseParameterSingularOpen N m t ht (radicand N m t) := by
  rw [radicand_eq_inverseParameterBranchFactor N m t ht hm, map_mul, map_pow,
    coverBaseToInverseParameterSingularOpen_base,
    coverBaseToInverseParameterSingularOpen_base]
  rw [← map_pow, inverseParameterSingularRoot_pow]
  simp [inverseParameterBaseToSingularOpen, map_mul, map_pow,
    inverseParameterBranchUnit_val]

/-- The original Euler algebra maps to the punctured singular inverse-parameter chart,
fixing the manuscript's coordinate `y`. -/
def coverToInverseParameterSingularOpen (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    CoverRing N m t →+* InverseParameterSingularOpen N m t :=
  AdjoinRoot.lift (coverBaseToInverseParameterSingularOpen N m t ht)
    (algebraMap (InverseParameterSingularRing N m t) (InverseParameterSingularOpen N m t)
      (inverseParameterSingularRoot N m t)) (by
    simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [sub_eq_zero]
    exact inverseParameterSingularOpenRoot_pow N m t ht hm)

@[simp] theorem coverToInverseParameterSingularOpen_root (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    coverToInverseParameterSingularOpen N m t ht hm (coverRoot N m t) =
      algebraMap (InverseParameterSingularRing N m t) (InverseParameterSingularOpen N m t)
        (inverseParameterSingularRoot N m t) := by
  simp [coverToInverseParameterSingularOpen, coverRoot]

/-- The singular inverse-parameter chart maps to the Euler cover after inverting `u`. -/
def inverseParameterSingularOpenToCover (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    InverseParameterSingularOpen N m t →+* CoverRing N m t :=
  Localization.awayLift (inverseParameterSingularToCover N m t ht hm) (inverseParameterSingularU N m t) (by
    rw [inverseParameterSingularU_eq_base, inverseParameterSingularToCover_base]
    exact (isUnit_inverseParameterBaseU_coverBase t ht).map
      (algebraMap (BaseRing t) (CoverRing N m t)))

@[simp] theorem inverseParameterSingularOpenToCover_root (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    inverseParameterSingularOpenToCover N m t ht hm
        (algebraMap (InverseParameterSingularRing N m t) (InverseParameterSingularOpen N m t)
          (inverseParameterSingularRoot N m t)) = coverRoot N m t := by
  simp [inverseParameterSingularOpenToCover, Localization.awayLift,
    IsLocalization.Away.lift_eq]

@[simp] theorem inverseParameterSingularOpenToCover_base (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N)
    (v : InverseParameterBaseRing t) :
    inverseParameterSingularOpenToCover N m t ht hm (inverseParameterBaseToSingularOpen N m t v) =
      inverseParameterBaseToCover N m t ht v := by
  simp [inverseParameterSingularOpenToCover, inverseParameterBaseToSingularOpen,
    inverseParameterSingularToCover, IsLocalization.Away.lift_eq, AdjoinRoot.lift_of]

@[simp] theorem inverseParameterSingularOpenToCover_coverBase (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N)
    (v : BaseRing t) :
    inverseParameterSingularOpenToCover N m t ht hm (coverBaseToInverseParameterSingularOpen N m t ht v) =
      algebraMap (BaseRing t) (CoverRing N m t) v := by
  have h : (inverseParameterSingularOpenToCover N m t ht hm).comp
      (inverseParameterBaseOpenToSingularOpen N m t) =
        (algebraMap (BaseRing t) (CoverRing N m t)).comp
          (inverseParameterBaseOpenToCoverBase t ht) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (inverseParameterBaseU t))
    apply RingHom.ext
    intro w
    simp only [RingHom.comp_apply, inverseParameterBaseOpenToSingularOpen_base,
      inverseParameterSingularOpenToCover_base, inverseParameterBaseOpenToCoverBase_base,
      inverseParameterBaseToCover, RingHom.comp_apply]
  have hv := congrArg
    (fun f : InverseParameterBaseOpen t →+* CoverRing N m t =>
      f (coverBaseToInverseParameterBaseOpen t ht v)) h
  have hbase := congrArg (fun f : BaseRing t →+* BaseRing t => f v)
    (inverseParameterBaseOpenToCoverBase_coverBaseToOpen t ht)
  simp only [RingHom.comp_apply, RingHom.id_apply] at hbase
  simpa only [coverBaseToInverseParameterSingularOpen, RingHom.comp_apply,
    hbase] using hv

@[simp] theorem coverToInverseParameterSingularOpen_base (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N)
    (v : InverseParameterBaseRing t) :
    coverToInverseParameterSingularOpen N m t ht hm (inverseParameterBaseToCover N m t ht v) =
      inverseParameterBaseToSingularOpen N m t v := by
  simp only [inverseParameterBaseToCover, RingHom.comp_apply]
  change coverToInverseParameterSingularOpen N m t ht hm
    (algebraMap (BaseRing t) (CoverRing N m t)
      (inverseParameterBaseToCoverBase t ht v)) = _
  rw [show coverToInverseParameterSingularOpen N m t ht hm
      (algebraMap (BaseRing t) (CoverRing N m t)
        (inverseParameterBaseToCoverBase t ht v)) =
      coverBaseToInverseParameterSingularOpen N m t ht (inverseParameterBaseToCoverBase t ht v) from by
        simp [coverToInverseParameterSingularOpen, AdjoinRoot.lift_of]]
  exact coverBaseToInverseParameterSingularOpen_base N m t ht v

/-- The original Euler cover and the punctured singular inverse-parameter chart agree. -/
theorem inverseParameterSingularOpenToCover_coverToInverseParameterSingularOpen (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    (inverseParameterSingularOpenToCover N m t ht hm).comp (coverToInverseParameterSingularOpen N m t ht hm) =
      RingHom.id (CoverRing N m t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    simp [coverToInverseParameterSingularOpen, AdjoinRoot.lift_of]
  · change inverseParameterSingularOpenToCover N m t ht hm
      (coverToInverseParameterSingularOpen N m t ht hm (coverRoot N m t)) = _
    rw [coverToInverseParameterSingularOpen_root, inverseParameterSingularOpenToCover_root]
    rfl

theorem coverToInverseParameterSingularOpen_inverseParameterSingularOpenToCover (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    (coverToInverseParameterSingularOpen N m t ht hm).comp (inverseParameterSingularOpenToCover N m t ht hm) =
      RingHom.id (InverseParameterSingularOpen N m t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (inverseParameterSingularU N m t))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change coverToInverseParameterSingularOpen N m t ht hm
      (inverseParameterSingularOpenToCover N m t ht hm
        (inverseParameterBaseToSingularOpen N m t v)) = _
    rw [inverseParameterSingularOpenToCover_base, coverToInverseParameterSingularOpen_base]
    rfl
  · change coverToInverseParameterSingularOpen N m t ht hm
      (inverseParameterSingularOpenToCover N m t ht hm
        (algebraMap (InverseParameterSingularRing N m t) (InverseParameterSingularOpen N m t)
          (inverseParameterSingularRoot N m t))) = _
    rw [inverseParameterSingularOpenToCover_root, coverToInverseParameterSingularOpen_root]
    rfl

/-- The punctured singular algebra at `1/t` is the actual Euler cover. -/
def inverseParameterSingularOpenEquivCover (N m : ℕ) (t : K) (ht : IsUnit t) (hm : m ≤ N) :
    InverseParameterSingularOpen N m t ≃+* CoverRing N m t where
  toFun := inverseParameterSingularOpenToCover N m t ht hm
  invFun := coverToInverseParameterSingularOpen N m t ht hm
  left_inv v := by
    have h := congrArg
      (fun f : InverseParameterSingularOpen N m t →+* InverseParameterSingularOpen N m t => f v)
      (coverToInverseParameterSingularOpen_inverseParameterSingularOpenToCover N m t ht hm)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv v := by
    have h := congrArg
      (fun f : CoverRing N m t →+* CoverRing N m t => f v)
      (inverseParameterSingularOpenToCover_coverToInverseParameterSingularOpen N m t ht hm)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (inverseParameterSingularOpenToCover N m t ht hm)
  map_add' := map_add (inverseParameterSingularOpenToCover N m t ht hm)

theorem inverseParameterBaseToSingularOpen_coeff (N m : ℕ) (t c : K) :
    inverseParameterBaseToSingularOpen N m t
        (algebraMap K (InverseParameterBaseRing t) c) =
      algebraMap K (InverseParameterSingularOpen N m t) c := by
  change (algebraMap (InverseParameterSingularRing N m t)
    (InverseParameterSingularOpen N m t))
    (algebraMap (InverseParameterBaseRing t)
      (InverseParameterSingularRing N m t)
      (algebraMap K (InverseParameterBaseRing t) c)) = _
  rw [← IsScalarTower.algebraMap_apply K (InverseParameterBaseRing t)
    (InverseParameterSingularRing N m t) c]
  exact (IsScalarTower.algebraMap_apply K
    (InverseParameterSingularRing N m t)
    (InverseParameterSingularOpen N m t) c).symm

/-- Under the inverse-parameter overlap, `x=(1-u)/t` exactly. -/
theorem coverToInverseParameterSingularOpen_x (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    coverToInverseParameterSingularOpen N m t ht hm
        (algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap K[X] (BaseRing t) X)) =
      algebraMap K (InverseParameterSingularOpen N m t) (inverseParameterCoefficient t) *
        (1 - inverseParameterBaseToSingularOpen N m t
          (inverseParameterBaseU t)) := by
  rw [show coverToInverseParameterSingularOpen N m t ht hm
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) X)) =
      coverBaseToInverseParameterSingularOpen N m t ht
        (algebraMap K[X] (BaseRing t) X) from by
          simp [coverToInverseParameterSingularOpen, AdjoinRoot.lift_of]]
  change inverseParameterBaseOpenToSingularOpen N m t
    (coverBaseToInverseParameterBaseOpen t ht
      (algebraMap K[X] (BaseRing t) X)) = _
  rw [coverBaseToInverseParameterBaseOpen_polynomial]
  change inverseParameterBaseOpenToSingularOpen N m t
    (algebraMap (InverseParameterBaseRing t) (InverseParameterBaseOpen t)
      (algebraMap K[X] (InverseParameterBaseRing t)
        (inverseParameterSubstitution t X))) = _
  rw [inverseParameterBaseOpenToSingularOpen_base,
    inverseParameterSubstitution_X, map_mul, map_sub, map_one,
    map_mul, map_sub, map_one]
  change inverseParameterBaseToSingularOpen N m t
      (algebraMap K (InverseParameterBaseRing t) (inverseParameterCoefficient t)) *
        (1 - inverseParameterBaseToSingularOpen N m t
          (inverseParameterBaseU t)) = _
  rw [inverseParameterBaseToSingularOpen_coeff]

/-! ## Scheme forms of the original singular overlaps -/

/-- The one-chart overlap map fixes the coefficient ring. -/
theorem coverToOneSingularOpen_coeff (N m : ℕ) (t c : K) :
    coverToOneSingularOpen N m t
      (algebraMap K (CoverRing N m t) c) =
        algebraMap K (OneSingularOpen N m t) c := by
  have hbase :
      oneBaseToCover N m t (algebraMap K (OneBaseRing t) c) =
        algebraMap K (CoverRing N m t) c := by
    change algebraMap (BaseRing t) (CoverRing N m t)
      (oneBaseToCoverBase t (algebraMap K (OneBaseRing t) c)) = _
    have hc : oneBaseToCoverBase t (algebraMap K (OneBaseRing t) c) =
        algebraMap K (BaseRing t) c := by
      change oneBaseToCoverBase t
        (algebraMap K[X] (OneBaseRing t) (C c)) =
          algebraMap K[X] (BaseRing t) (C c)
      rw [oneBaseToCoverBase_polynomial, oneSubstitution_C]
    rw [hc]
    exact IsScalarTower.algebraMap_apply K (BaseRing t) (CoverRing N m t) c
  calc
    coverToOneSingularOpen N m t (algebraMap K (CoverRing N m t) c) =
        coverToOneSingularOpen N m t
          (oneBaseToCover N m t (algebraMap K (OneBaseRing t) c)) := by rw [hbase]
    _ = oneBaseToSingularOpen N m t (algebraMap K (OneBaseRing t) c) :=
      coverToOneSingularOpen_oneBase N m t _
    _ = algebraMap K (OneSingularOpen N m t) c :=
      oneBaseToSingularOpen_coeff N m t c

/-- The inverse-parameter overlap map fixes the coefficient ring. -/
theorem coverToInverseParameterSingularOpen_coeff (N m : ℕ) (t c : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    coverToInverseParameterSingularOpen N m t ht hm
      (algebraMap K (CoverRing N m t) c) =
        algebraMap K (InverseParameterSingularOpen N m t) c := by
  have hbase :
      inverseParameterBaseToCover N m t ht
        (algebraMap K (InverseParameterBaseRing t) c) =
          algebraMap K (CoverRing N m t) c := by
    change algebraMap (BaseRing t) (CoverRing N m t)
      (inverseParameterBaseToCoverBase t ht
        (algebraMap K (InverseParameterBaseRing t) c)) = _
    have hc : inverseParameterBaseToCoverBase t ht
        (algebraMap K (InverseParameterBaseRing t) c) =
        algebraMap K (BaseRing t) c := by
      change inverseParameterBaseToCoverBase t ht
        (algebraMap K[X] (InverseParameterBaseRing t) (C c)) =
          algebraMap K[X] (BaseRing t) (C c)
      rw [inverseParameterBaseToCoverBase_polynomial,
        inverseParameterReverseSubstitution_C]
    rw [hc]
    exact IsScalarTower.algebraMap_apply K (BaseRing t) (CoverRing N m t) c
  calc
    coverToInverseParameterSingularOpen N m t ht hm
        (algebraMap K (CoverRing N m t) c) =
      coverToInverseParameterSingularOpen N m t ht hm
        (inverseParameterBaseToCover N m t ht
          (algebraMap K (InverseParameterBaseRing t) c)) := by rw [hbase]
    _ = inverseParameterBaseToSingularOpen N m t
          (algebraMap K (InverseParameterBaseRing t) c) :=
      coverToInverseParameterSingularOpen_base N m t ht hm _
    _ = algebraMap K (InverseParameterSingularOpen N m t) c :=
      inverseParameterBaseToSingularOpen_coeff N m t c

/-- The original singular chart centered at `x=1`. -/
@[expose] def oneSingularScheme (N m : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (OneSingularRing N m t))

/-- The coefficient-ring projection of the singular one-chart. -/
def oneSingularStructureMap (N m : ℕ) (t : K) :
    oneSingularScheme N m t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (OneSingularRing N m t)))

/-- The punctured original singular chart at `x=1` as an affine scheme. -/
@[expose] def oneSingularOpenScheme (N m : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (OneSingularOpen N m t))

/-- The punctured one-chart is the principal open where `u=1-x` is a unit. -/
def oneSingularOpenInclusion (N m : ℕ) (t : K) :
    oneSingularOpenScheme N m t ⟶ oneSingularScheme N m t :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)))

instance oneSingularOpenInclusion_isOpenImmersion (N m : ℕ) (t : K) :
    IsOpenImmersion (oneSingularOpenInclusion N m t) :=
  IsOpenImmersion.of_isLocalization (oneSingularU N m t)

/-- The one-chart overlap has image exactly `D(u)`. -/
theorem oneSingularOpenInclusion_opensRange (N m : ℕ) (t : K) :
    (oneSingularOpenInclusion N m t).opensRange =
      PrimeSpectrum.basicOpen (oneSingularU N m t) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (OneSingularOpen N m t)
    (oneSingularU N m t)

/-- The coefficient-ring projection of the punctured singular chart at one. -/
def oneSingularOpenStructureMap (N m : ℕ) (t : K) :
    oneSingularOpenScheme N m t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (OneSingularOpen N m t)))

/-- The one-chart open immersion preserves the coefficient-ring projection. -/
theorem oneSingularOpenInclusion_structureMap (N m : ℕ) (t : K) :
    oneSingularOpenInclusion N m t ≫ oneSingularStructureMap N m t =
      oneSingularOpenStructureMap N m t := by
  unfold oneSingularOpenInclusion oneSingularStructureMap
    oneSingularOpenStructureMap
  erw [← Spec.map_comp]
  congr 1

/-- The actual punctured singular one-chart is the original Euler cover. -/
def oneSingularOpenIsoCover (N m : ℕ) (t : K) :
    oneSingularOpenScheme N m t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso (oneSingularOpenEquivCover N m t).symm.toCommRingCatIso.op

theorem oneSingularOpenIsoCover_hom (N m : ℕ) (t : K) :
    (oneSingularOpenIsoCover N m t).hom =
      Spec.map (CommRingCat.ofHom (coverToOneSingularOpen N m t)) := (rfl)

theorem oneSingularOpenIsoCover_inv (N m : ℕ) (t : K) :
    (oneSingularOpenIsoCover N m t).inv =
      Spec.map (CommRingCat.ofHom (oneSingularOpenToCover N m t)) := (rfl)

/-- The one-chart overlap identification preserves the projection to `K`. -/
theorem oneSingularOpenIsoCover_structureMap (N m : ℕ) (t : K) :
    (oneSingularOpenIsoCover N m t).hom ≫ structureMap N m t =
      oneSingularOpenStructureMap N m t := by
  rw [oneSingularOpenIsoCover_hom]
  change Spec.map (CommRingCat.ofHom (coverToOneSingularOpen N m t)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (CoverRing N m t))) = _
  erw [← Spec.map_comp]
  congr 1
  ext c
  change coverToOneSingularOpen N m t
    (algebraMap K (CoverRing N m t) c) =
      algebraMap K (OneSingularOpen N m t) c
  exact coverToOneSingularOpen_coeff N m t c

/-- The original singular chart centered at `x=1/t`. -/
@[expose] def inverseParameterSingularScheme (N m : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (InverseParameterSingularRing N m t))

/-- The coefficient-ring projection of the singular inverse-parameter chart. -/
def inverseParameterSingularStructureMap (N m : ℕ) (t : K) :
    inverseParameterSingularScheme N m t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap K (InverseParameterSingularRing N m t)))

/-- The punctured original singular chart at `x=1/t` as an affine scheme. -/
@[expose] def inverseParameterSingularOpenScheme (N m : ℕ) (t : K) : Scheme :=
  Spec (CommRingCat.of (InverseParameterSingularOpen N m t))

/-- The inverse-parameter overlap is the principal open `D(u)` of its singular chart. -/
def inverseParameterSingularOpenInclusion (N m : ℕ) (t : K) :
    inverseParameterSingularOpenScheme N m t ⟶
      inverseParameterSingularScheme N m t :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (InverseParameterSingularRing N m t)
      (InverseParameterSingularOpen N m t)))

instance inverseParameterSingularOpenInclusion_isOpenImmersion
    (N m : ℕ) (t : K) :
    IsOpenImmersion (inverseParameterSingularOpenInclusion N m t) :=
  IsOpenImmersion.of_isLocalization (inverseParameterSingularU N m t)

/-- The inverse-parameter overlap has image exactly `D(u)`. -/
theorem inverseParameterSingularOpenInclusion_opensRange
    (N m : ℕ) (t : K) :
    (inverseParameterSingularOpenInclusion N m t).opensRange =
      PrimeSpectrum.basicOpen (inverseParameterSingularU N m t) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (InverseParameterSingularOpen N m t)
    (inverseParameterSingularU N m t)

/-- The coefficient-ring projection of the inverse-parameter singular open. -/
def inverseParameterSingularOpenStructureMap (N m : ℕ) (t : K) :
    inverseParameterSingularOpenScheme N m t ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (InverseParameterSingularOpen N m t)))

/-- The inverse-parameter open immersion preserves the projection to `K`. -/
theorem inverseParameterSingularOpenInclusion_structureMap
    (N m : ℕ) (t : K) :
    inverseParameterSingularOpenInclusion N m t ≫
      inverseParameterSingularStructureMap N m t =
        inverseParameterSingularOpenStructureMap N m t := by
  unfold inverseParameterSingularOpenInclusion
    inverseParameterSingularStructureMap
    inverseParameterSingularOpenStructureMap
  erw [← Spec.map_comp]
  congr 1

/-- The actual punctured singular `1/t`-chart is the Euler cover. -/
def inverseParameterSingularOpenIsoCover (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    inverseParameterSingularOpenScheme N m t ≅ affineScheme N m t :=
  Scheme.Spec.mapIso
    (inverseParameterSingularOpenEquivCover N m t ht hm).symm.toCommRingCatIso.op

theorem inverseParameterSingularOpenIsoCover_hom (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    (inverseParameterSingularOpenIsoCover N m t ht hm).hom =
      Spec.map (CommRingCat.ofHom
        (coverToInverseParameterSingularOpen N m t ht hm)) := (rfl)

theorem inverseParameterSingularOpenIsoCover_inv (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    (inverseParameterSingularOpenIsoCover N m t ht hm).inv =
      Spec.map (CommRingCat.ofHom
        (inverseParameterSingularOpenToCover N m t ht hm)) := (rfl)

/-- The inverse-parameter overlap identification preserves the projection to `K`. -/
theorem inverseParameterSingularOpenIsoCover_structureMap (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    (inverseParameterSingularOpenIsoCover N m t ht hm).hom ≫
      structureMap N m t = inverseParameterSingularOpenStructureMap N m t := by
  rw [inverseParameterSingularOpenIsoCover_hom]
  change Spec.map (CommRingCat.ofHom
    (coverToInverseParameterSingularOpen N m t ht hm)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (CoverRing N m t))) = _
  erw [← Spec.map_comp]
  congr 1
  ext c
  change coverToInverseParameterSingularOpen N m t ht hm
    (algebraMap K (CoverRing N m t) c) =
      algebraMap K (InverseParameterSingularOpen N m t) c
  exact coverToInverseParameterSingularOpen_coeff N m t c ht hm

/-! ## Smooth normalized finite branch charts -/

/-- The normalized coordinate algebra near `x=1`, with
`z^N=u((1-u)^m(1-t+tu)^m)^a`. -/
abbrev OneBranchRing (N m a : ℕ) (t : K) :=
  TameBranchRing (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a

/-- The normalized coordinate algebra near `x=1/t`, retaining the exact
factor `t⁻ᴺ` in its invertible radicand. -/
abbrev InverseParameterBranchRing (N m a : ℕ) (t : K) :=
  TameBranchRing (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N a

/-- The smooth one-branch chart maps to the original singular chart by
`y=z^(N-m)/U^b`. -/
def oneSingularToBranch (N m a b : ℕ) (t : K)
    (hbezout : (N - m) * a = 1 + b * N) :
    OneSingularRing N m t →ₐ[OneBaseRing t] OneBranchRing N m a t :=
  tameSingularToBranch (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout

/-- The smooth inverse-parameter chart maps to the original singular chart
by `y=z^m/U^b`. -/
def inverseParameterSingularToBranch (N m a b : ℕ) (t : K) (ht : IsUnit t)
    (hbezout : m * a = 1 + b * N) :
    InverseParameterSingularRing N m t →ₐ[InverseParameterBaseRing t]
      InverseParameterBranchRing N m a t :=
  tameSingularToBranch (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout

/-- The normalized chart at one is smooth over the coefficient ring. -/
theorem oneBranchRing_smooth (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Algebra.Smooth K (OneBranchRing N m a t) :=
  tameBranchRing_smooth (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N a
    (isUnit_oneBranchFactor m t) hN hn

/-- The normalized chart at `1/t` is smooth over the coefficient ring. -/
theorem inverseParameterBranchRing_smooth (N m a : ℕ) (t : K)
    (ht : IsUnit t) (hN : 0 < N) (hn : IsUnit (N : K)) :
    Algebra.Smooth K (InverseParameterBranchRing N m a t) :=
  tameBranchRing_smooth (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N a
    (isUnit_inverseParameterBranchFactor N m t ht) hN hn

/-- On `u ≠ 0`, the normalized branch at one is the actual Euler cover. -/
def oneBranchOpenEquivCover (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    TameBranchOpen (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a
      ≃+* CoverRing N m t :=
  (tameBranchOpenEquivSingularOpen (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hN hbezout).toRingEquiv.trans
      (oneSingularOpenEquivCover N m t)

/-- On `u ≠ 0`, the normalized branch at `1/t` is the actual Euler cover. -/
def inverseParameterBranchOpenEquivCover (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    TameBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a ≃+* CoverRing N m t :=
  (tameBranchOpenEquivSingularOpen (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hN hbezout).toRingEquiv.trans
      (inverseParameterSingularOpenEquivCover N m t ht hm)

/-- The normalized coordinate and its actual radicand at one. -/
theorem oneBranchRoot_pow (N m a : ℕ) (t : K) :
    tameBranchRoot (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a ^ N =
      tameBranchX (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a *
        algebraMap (OneBaseRing t) (OneBranchRing N m a t)
          (oneBranchFactor m t) ^ a := by
  exact tameBranchRoot_pow (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N a

/-- The normalized coordinate and its actual radicand at `1/t`. -/
theorem inverseParameterBranchRoot_pow (N m a : ℕ) (t : K) :
    tameBranchRoot (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N a ^ N =
      tameBranchX (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a *
        algebraMap (InverseParameterBaseRing t)
          (InverseParameterBranchRing N m a t)
          (inverseParameterBranchFactor N m t) ^ a := by
  exact tameBranchRoot_pow (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N a

/-- The original covering coordinate on the normalized chart at one is
`z^(N-m)/U^b`. -/
theorem oneSingularToBranch_root (N m a b : ℕ) (t : K)
    (hbezout : (N - m) * a = 1 + b * N) :
    oneSingularToBranch N m a b t hbezout (oneSingularRoot N m t) =
      tameBranchRoot (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a ^
        (N - m) *
      algebraMap (OneBaseRing t) (OneBranchRing N m a t)
        (((oneBranchUnit m t)⁻¹ ^ b : (OneBaseRing t)ˣ) : OneBaseRing t) := by
  exact tameSingularToBranch_root (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout

/-- The original covering coordinate on the normalized chart at `1/t` is
`z^m/U^b`; the factor `t⁻ᴺ` stays in `U`. -/
theorem inverseParameterSingularToBranch_root (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hbezout : m * a = 1 + b * N) :
    inverseParameterSingularToBranch N m a b t ht hbezout
        (inverseParameterSingularRoot N m t) =
      tameBranchRoot (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a ^ m *
      algebraMap (InverseParameterBaseRing t)
        (InverseParameterBranchRing N m a t)
        (((inverseParameterBranchUnit N m t ht)⁻¹ ^ b :
          (InverseParameterBaseRing t)ˣ) : InverseParameterBaseRing t) := by
  exact tameSingularToBranch_root (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout

/-- The smooth normalized branch at one as an affine scheme. -/
def oneBranchScheme (N m a : ℕ) (t : K) : Scheme :=
  tameBranchScheme (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a

/-- The smooth normalized branch at `1/t` as an affine scheme. -/
def inverseParameterBranchScheme (N m a : ℕ) (t : K) : Scheme :=
  tameBranchScheme (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N a

/-- The normalized one-branch chart maps to its singular Euler chart. -/
def oneBranchToSingularScheme (N m a b : ℕ) (t : K)
    (hbezout : (N - m) * a = 1 + b * N) :
    oneBranchScheme N m a t ⟶ oneSingularScheme N m t :=
  tameBranchToSingularScheme (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout

/-- The normalized `1/t` chart maps to its singular Euler chart. -/
def inverseParameterBranchToSingularScheme (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hbezout : m * a = 1 + b * N) :
    inverseParameterBranchScheme N m a t ⟶
      inverseParameterSingularScheme N m t :=
  tameBranchToSingularScheme (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout

/-- The smooth branch at one has the stated actual coefficient-ring map. -/
theorem oneBranchStructureMap_smooth (N m a : ℕ) (t : K)
    (hN : 0 < N) (hn : IsUnit (N : K)) :
    Smooth (tameBranchStructureMap (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a) :=
  tameBranchStructureMap_smooth (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N a
    (isUnit_oneBranchFactor m t) hN hn

/-- The smooth branch at `1/t` has the stated actual coefficient-ring map. -/
theorem inverseParameterBranchStructureMap_smooth (N m a : ℕ) (t : K)
    (ht : IsUnit t) (hN : 0 < N) (hn : IsUnit (N : K)) :
    Smooth (tameBranchStructureMap (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a) :=
  tameBranchStructureMap_smooth (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N a
    (isUnit_inverseParameterBranchFactor N m t ht) hN hn

/-- The punctured normalized one-branch scheme is the actual Euler cover. -/
def oneBranchOpenIsoCover (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    tameBranchOpenScheme (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a ≅ affineScheme N m t :=
  (tameBranchOpenIsoSingularOpen (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hN hbezout).trans
      (oneSingularOpenIsoCover N m t)

/-- The punctured normalized `1/t` branch scheme is the Euler cover. -/
def inverseParameterBranchOpenIsoCover (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    tameBranchOpenScheme (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a ≅ affineScheme N m t :=
  (tameBranchOpenIsoSingularOpen (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hN hbezout).trans
      (inverseParameterSingularOpenIsoCover N m t ht hm)

/-- The forward normalized overlap at one is the spectrum of the explicit
map from the original Euler coordinate algebra. -/
theorem oneBranchOpenIsoCover_hom (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    (oneBranchOpenIsoCover N m a b t hN hbezout).hom =
      Spec.map (CommRingCat.ofHom
        (oneBranchOpenEquivCover N m a b t hN hbezout).symm.toRingHom) := by
  change (tameBranchOpenIsoSingularOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hN hbezout).hom ≫
      (oneSingularOpenIsoCover N m t).hom = _
  change Spec.map (CommRingCat.ofHom
      (tameSingularOpenToBranchOpen (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N (N - m) a b
        (isUnit_oneBranchFactor m t) hbezout)) ≫
      Spec.map (CommRingCat.ofHom (coverToOneSingularOpen N m t)) = _
  erw [← Spec.map_comp]
  rfl

/-- The forward normalized overlap at `1/t` is the spectrum of its explicit
Euler coordinate map. -/
theorem inverseParameterBranchOpenIsoCover_hom (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (inverseParameterBranchOpenIsoCover N m a b t ht hm hN hbezout).hom =
      Spec.map (CommRingCat.ofHom
        (inverseParameterBranchOpenEquivCover N m a b t ht hm hN hbezout).symm.toRingHom) := by
  change (tameBranchOpenIsoSingularOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hN hbezout).hom ≫
      (inverseParameterSingularOpenIsoCover N m t ht hm).hom = _
  change Spec.map (CommRingCat.ofHom
      (tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N m a b
        (isUnit_inverseParameterBranchFactor N m t ht) hbezout)) ≫
      Spec.map (CommRingCat.ofHom
        (coverToInverseParameterSingularOpen N m t ht hm)) = _
  erw [← Spec.map_comp]
  rfl

/-! ## Coordinates of the normalized overlaps -/

/-- The parameter `u=1-x` is a unit in the original Euler cover. -/
def coverOneUUnit (N m : ℕ) (t : K) : (CoverRing N m t)ˣ :=
  Units.map (algebraMap (BaseRing t) (CoverRing N m t)).toMonoidHom
    (isUnit_oneBaseU_coverBase t).unit

@[simp] theorem coverOneUUnit_val (N m : ℕ) (t : K) :
    (coverOneUUnit N m t : CoverRing N m t) =
      oneBaseToCover N m t (oneBaseU t) := by
  simp [coverOneUUnit, oneBaseToCover]

/-- The parameter `u=1-tx` is a unit in the original Euler cover. -/
def coverInverseParameterUUnit (N m : ℕ) (t : K) (ht : IsUnit t) :
    (CoverRing N m t)ˣ :=
  Units.map (algebraMap (BaseRing t) (CoverRing N m t)).toMonoidHom
    (isUnit_inverseParameterBaseU_coverBase t ht).unit

@[simp] theorem coverInverseParameterUUnit_val (N m : ℕ) (t : K)
    (ht : IsUnit t) :
    (coverInverseParameterUUnit N m t ht : CoverRing N m t) =
      inverseParameterBaseToCover N m t ht (inverseParameterBaseU t) := by
  simp [coverInverseParameterUUnit, inverseParameterBaseToCover]

/-- The original one-chart overlap preserves the invertible parameter. -/
theorem oneSingularOpenToCover_uUnit (N m : ℕ) (t : K) :
    Units.map (oneSingularOpenToCover N m t).toMonoidHom
      (oneSingularOpenUUnit N m t) = coverOneUUnit N m t := by
  apply Units.ext
  change oneSingularOpenToCover N m t
    (oneSingularOpenUUnit N m t : OneSingularOpen N m t) =
      (coverOneUUnit N m t : CoverRing N m t)
  rw [oneSingularOpenUUnit_val, oneSingularOpenToCover_oneBase,
    coverOneUUnit_val]

/-- The original inverse-parameter overlap preserves its invertible parameter. -/
theorem inverseParameterSingularOpenToCover_uUnit (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) :
    Units.map (inverseParameterSingularOpenToCover N m t ht hm).toMonoidHom
      (inverseParameterSingularOpenUUnit N m t) =
        coverInverseParameterUUnit N m t ht := by
  apply Units.ext
  change inverseParameterSingularOpenToCover N m t ht hm
    (inverseParameterSingularOpenUUnit N m t : InverseParameterSingularOpen N m t) =
      (coverInverseParameterUUnit N m t ht : CoverRing N m t)
  rw [inverseParameterSingularOpenUUnit_val,
    inverseParameterSingularOpenToCover_base,
    coverInverseParameterUUnit_val]

/-- The original one-chart overlap preserves the invertible covering root. -/
theorem oneSingularOpenToCover_rootUnit (N m : ℕ) (t : K) (hN : N ≠ 0) :
    Units.map (oneSingularOpenToCover N m t).toMonoidHom
      (tameSingularOpenRootUnit (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N (N - m)
        (isUnit_oneBranchFactor m t) hN) = coverRootUnit N m t hN := by
  apply Units.ext
  simp only [coverRootUnit_val]
  exact oneSingularOpenToCover_root N m t

/-- The inverse-parameter overlap preserves the invertible covering root. -/
theorem inverseParameterSingularOpenToCover_rootUnit (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0) :
    Units.map (inverseParameterSingularOpenToCover N m t ht hm).toMonoidHom
      (tameSingularOpenRootUnit (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N m
        (isUnit_inverseParameterBranchFactor N m t ht) hN) =
          coverRootUnit N m t hN := by
  apply Units.ext
  simp only [coverRootUnit_val]
  exact inverseParameterSingularOpenToCover_root N m t ht hm

/-- The inverse overlap at one sends the original `x` to `1-u`. -/
theorem coverToOneBranchOpen_x (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    (oneBranchOpenEquivCover N m a b t hN hbezout).symm
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) X)) =
      1 - algebraMap (OneBaseRing t)
        (TameBranchOpen (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N a) (oneBaseU t) := by
  change tameSingularOpenToBranchOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hbezout
      (coverToOneSingularOpen N m t
        (algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap K[X] (BaseRing t) X))) = _
  have hbase (v : OneBaseRing t) :
      tameSingularOpenToBranchOpen (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N (N - m) a b
          (isUnit_oneBranchFactor m t) hbezout
          (oneBaseToSingularOpen N m t v) =
        algebraMap (OneBaseRing t)
          (TameBranchOpen (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N a) v := by
    change tameSingularOpenToBranchOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hbezout
      (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
        (algebraMap (OneBaseRing t) (OneSingularRing N m t) v)) = _
    rw [← IsScalarTower.algebraMap_apply (OneBaseRing t)
      (OneSingularRing N m t) (OneSingularOpen N m t) v]
    exact tameSingularOpenToBranchOpen_base (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hbezout v
  rw [coverToOneSingularOpen_x]
  let f := tameSingularOpenToBranchOpen (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout
  change f ((1 : OneSingularOpen N m t) -
    oneBaseToSingularOpen N m t (oneBaseU t)) = _
  calc
    f ((1 : OneSingularOpen N m t) -
        oneBaseToSingularOpen N m t (oneBaseU t)) =
        f 1 - f (oneBaseToSingularOpen N m t (oneBaseU t)) :=
      f.map_sub _ _
    _ = _ := by rw [f.map_one, hbase]

/-- The inverse overlap at `1/t` sends the original `x` to `(1-u)/t`. -/
theorem coverToInverseParameterBranchOpen_x (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (inverseParameterBranchOpenEquivCover N m a b t ht hm hN hbezout).symm
      (algebraMap (BaseRing t) (CoverRing N m t)
        (algebraMap K[X] (BaseRing t) X)) =
      algebraMap K (TameBranchOpen (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N a) (inverseParameterCoefficient t) *
        (1 - algebraMap (InverseParameterBaseRing t)
          (TameBranchOpen (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N a)
          (inverseParameterBaseU t)) := by
  change tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hbezout
      (coverToInverseParameterSingularOpen N m t ht hm
        (algebraMap (BaseRing t) (CoverRing N m t)
          (algebraMap K[X] (BaseRing t) X))) = _
  have hbase (v : InverseParameterBaseRing t) :
      tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N m a b
          (isUnit_inverseParameterBranchFactor N m t ht) hbezout
          (inverseParameterBaseToSingularOpen N m t v) =
        algebraMap (InverseParameterBaseRing t)
          (TameBranchOpen (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N a) v := by
    change tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hbezout
      (algebraMap (InverseParameterSingularRing N m t)
        (InverseParameterSingularOpen N m t)
        (algebraMap (InverseParameterBaseRing t)
          (InverseParameterSingularRing N m t) v)) = _
    rw [← IsScalarTower.algebraMap_apply (InverseParameterBaseRing t)
      (InverseParameterSingularRing N m t)
      (InverseParameterSingularOpen N m t) v]
    exact tameSingularOpenToBranchOpen_base (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hbezout v
  rw [coverToInverseParameterSingularOpen_x N m t ht hm]
  have hcoeff : tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hbezout
      (algebraMap K (InverseParameterSingularOpen N m t) (inverseParameterCoefficient t)) =
      algebraMap K (TameBranchOpen (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N a) (inverseParameterCoefficient t) := by
    rw [← inverseParameterBaseToSingularOpen_coeff N m t (inverseParameterCoefficient t), hbase,
      IsScalarTower.algebraMap_apply K (InverseParameterBaseRing t)
        (TameBranchOpen (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a) (inverseParameterCoefficient t)]
  let f := tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout
  change f (algebraMap K (InverseParameterSingularOpen N m t) (inverseParameterCoefficient t) *
    ((1 : InverseParameterSingularOpen N m t) -
      inverseParameterBaseToSingularOpen N m t
      (inverseParameterBaseU t))) = _
  calc
    f (algebraMap K (InverseParameterSingularOpen N m t) (inverseParameterCoefficient t) *
        ((1 : InverseParameterSingularOpen N m t) -
          inverseParameterBaseToSingularOpen N m t
          (inverseParameterBaseU t))) =
      f (algebraMap K (InverseParameterSingularOpen N m t) (inverseParameterCoefficient t)) *
        f ((1 : InverseParameterSingularOpen N m t) -
          inverseParameterBaseToSingularOpen N m t
          (inverseParameterBaseU t)) := f.map_mul _ _
    _ = f (algebraMap K (InverseParameterSingularOpen N m t) (inverseParameterCoefficient t)) *
        (1 - f (inverseParameterBaseToSingularOpen N m t
          (inverseParameterBaseU t))) := by
      congr 1
      exact (f.map_sub 1
        (inverseParameterBaseToSingularOpen N m t (inverseParameterBaseU t))).trans
          (by rw [f.map_one])
    _ = _ := by rw [hcoeff, hbase]

/-- The original `y` on the normalized overlap at one is `z^(N-m)/U^b`. -/
theorem coverToOneBranchOpen_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    (oneBranchOpenEquivCover N m a b t hN hbezout).symm
      (coverRoot N m t) =
        (tameBranchOpenRootUnit (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N a
            (isUnit_oneBranchFactor m t) hN ^ (N - m) *
          (tameBranchOpenUUnit (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N a
            (isUnit_oneBranchFactor m t))⁻¹ ^ b :
          (TameBranchOpen (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N a)ˣ) := by
  change tameSingularOpenToBranchOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hbezout
      (coverToOneSingularOpen N m t (coverRoot N m t)) = _
  rw [coverToOneSingularOpen_root]
  exact tameSingularOpenToBranchOpen_root (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hN hbezout

/-- The original `y` on the normalized overlap at `1/t` is `z^m/U^b`. -/
theorem coverToInverseParameterBranchOpen_root (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (inverseParameterBranchOpenEquivCover N m a b t ht hm hN hbezout).symm
      (coverRoot N m t) =
        (tameBranchOpenRootUnit (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N a
            (isUnit_inverseParameterBranchFactor N m t ht) hN ^ m *
          (tameBranchOpenUUnit (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N a
            (isUnit_inverseParameterBranchFactor N m t ht))⁻¹ ^ b :
          (TameBranchOpen (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N a)ˣ) := by
  change tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hbezout
      (coverToInverseParameterSingularOpen N m t ht hm (coverRoot N m t)) = _
  rw [coverToInverseParameterSingularOpen_root]
  exact tameSingularOpenToBranchOpen_root (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hN hbezout

/-- On the overlap at one, the inverse normalized coordinate is
`z=y^a/(1-x)^b`. -/
theorem oneBranchOpenToCover_root (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    oneBranchOpenEquivCover N m a b t hN hbezout
      (tameBranchOpenRootUnit (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N a
        (isUnit_oneBranchFactor m t) hN :
        TameBranchOpen (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N a) =
      ((coverRootUnit N m t hN ^ a * (coverOneUUnit N m t)⁻¹ ^ b :
        (CoverRing N m t)ˣ) : CoverRing N m t) := by
  change oneSingularOpenToCover N m t
    (tameBranchOpenToSingularOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hN hbezout
      (algebraMap (TameBranchRing (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N a)
        (TameBranchOpen (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N a)
        (tameBranchRoot (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N a))) = _
  rw [tameBranchOpenToSingularOpen_root
    (oneBranchProduct t) (oneBranchFactorPolynomial m t)
    N (N - m) a b (isUnit_oneBranchFactor m t) hN hbezout]
  let f := oneSingularOpenToCover N m t
  let G := Units.map f.toMonoidHom
  let v := tameSingularOpenRootUnit (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m)
    (isUnit_oneBranchFactor m t) hN
  let u := tameSingularOpenXUnit (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m)
  have h : Units.map f.toMonoidHom
      ((tameSingularOpenRootUnit (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N (N - m)
          (isUnit_oneBranchFactor m t) hN) ^ a *
        (tameSingularOpenXUnit (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N (N - m))⁻¹ ^ b) =
      coverRootUnit N m t hN ^ a * (coverOneUUnit N m t)⁻¹ ^ b := by
    change G (v ^ a * u⁻¹ ^ b) = _
    calc
      G (v ^ a * u⁻¹ ^ b) = G (v ^ a) * G (u⁻¹ ^ b) := G.map_mul _ _
      _ = G v ^ a * G (u⁻¹) ^ b :=
        congrArg₂ (· * ·) (G.map_pow v a) (G.map_pow u⁻¹ b)
      _ = G v ^ a * (G u)⁻¹ ^ b :=
        congrArg (fun w => G v ^ a * w ^ b) (G.map_inv u)
      _ = _ := by rw [oneSingularOpenToCover_rootUnit,
      show Units.map f.toMonoidHom
          (tameSingularOpenXUnit (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N (N - m)) =
          coverOneUUnit N m t from oneSingularOpenToCover_uUnit N m t]
  exact congrArg Units.val h

/-- On the overlap at `1/t`, the inverse normalized coordinate is
`z=y^a/(1-tx)^b`. -/
theorem inverseParameterBranchOpenToCover_root (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    inverseParameterBranchOpenEquivCover N m a b t ht hm hN hbezout
      (tameBranchOpenRootUnit (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N a
        (isUnit_inverseParameterBranchFactor N m t ht) hN :
        TameBranchOpen (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a) =
      ((coverRootUnit N m t hN ^ a *
        (coverInverseParameterUUnit N m t ht)⁻¹ ^ b :
        (CoverRing N m t)ˣ) : CoverRing N m t) := by
  change inverseParameterSingularOpenToCover N m t ht hm
    (tameBranchOpenToSingularOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hN hbezout
      (algebraMap (TameBranchRing (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N a)
        (TameBranchOpen (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a)
        (tameBranchRoot (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a))) = _
  rw [tameBranchOpenToSingularOpen_root
    (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t)
    N m a b (isUnit_inverseParameterBranchFactor N m t ht) hN hbezout]
  let f := inverseParameterSingularOpenToCover N m t ht hm
  let G := Units.map f.toMonoidHom
  let v := tameSingularOpenRootUnit (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m
    (isUnit_inverseParameterBranchFactor N m t ht) hN
  let u := tameSingularOpenXUnit (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m
  have h : Units.map f.toMonoidHom
      ((tameSingularOpenRootUnit (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N m
          (isUnit_inverseParameterBranchFactor N m t ht) hN) ^ a *
        (tameSingularOpenXUnit (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N m)⁻¹ ^ b) =
      coverRootUnit N m t hN ^ a *
        (coverInverseParameterUUnit N m t ht)⁻¹ ^ b := by
    change G (v ^ a * u⁻¹ ^ b) = _
    calc
      G (v ^ a * u⁻¹ ^ b) = G (v ^ a) * G (u⁻¹ ^ b) := G.map_mul _ _
      _ = G v ^ a * G (u⁻¹) ^ b :=
        congrArg₂ (· * ·) (G.map_pow v a) (G.map_pow u⁻¹ b)
      _ = G v ^ a * (G u)⁻¹ ^ b :=
        congrArg (fun w => G v ^ a * w ^ b) (G.map_inv u)
      _ = _ := by rw [inverseParameterSingularOpenToCover_rootUnit,
      show Units.map f.toMonoidHom
          (tameSingularOpenXUnit (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N m) =
          coverInverseParameterUUnit N m t ht from
        inverseParameterSingularOpenToCover_uUnit N m t ht hm]
  exact congrArg Units.val h

/-- The normalized overlap at one fixes every coefficient of `K`. -/
theorem coverToOneBranchOpen_coeff (N m a b : ℕ) (t c : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    (oneBranchOpenEquivCover N m a b t hN hbezout).symm
      (algebraMap K (CoverRing N m t) c) =
        algebraMap K (TameBranchOpen (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N a) c := by
  change tameSingularOpenToBranchOpen (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout
    (coverToOneSingularOpen N m t (algebraMap K (CoverRing N m t) c)) = _
  rw [coverToOneSingularOpen_coeff]
  rw [IsScalarTower.algebraMap_apply K (OneBaseRing t)
    (OneSingularOpen N m t) c]
  have h := tameSingularOpenToBranchOpen_base (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout
    (algebraMap K (OneBaseRing t) c)
  rw [← IsScalarTower.algebraMap_apply K (OneBaseRing t)
    (TameBranchOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a) c] at h
  exact h

/-- The normalized overlap at `1/t` fixes every coefficient of `K`. -/
theorem coverToInverseParameterBranchOpen_coeff (N m a b : ℕ) (t c : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (inverseParameterBranchOpenEquivCover N m a b t ht hm hN hbezout).symm
      (algebraMap K (CoverRing N m t) c) =
        algebraMap K (TameBranchOpen (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N a) c := by
  change tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout
    (coverToInverseParameterSingularOpen N m t ht hm
      (algebraMap K (CoverRing N m t) c)) = _
  rw [coverToInverseParameterSingularOpen_coeff N m t c ht hm]
  rw [IsScalarTower.algebraMap_apply K (InverseParameterBaseRing t)
    (InverseParameterSingularOpen N m t) c]
  have h := tameSingularOpenToBranchOpen_base (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout
    (algebraMap K (InverseParameterBaseRing t) c)
  rw [← IsScalarTower.algebraMap_apply K (InverseParameterBaseRing t)
    (TameBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a) c] at h
  exact h

/-- The coefficient-ring projection of the punctured normalized one-chart. -/
def oneBranchOpenStructureMap (N m a : ℕ) (t : K) :
    tameBranchOpenScheme (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap K (TameBranchOpen (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a)))

/-- The coefficient-ring projection of the punctured normalized `1/t` chart. -/
def inverseParameterBranchOpenStructureMap (N m a : ℕ) (t : K) :
    tameBranchOpenScheme (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a ⟶
        Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap K (TameBranchOpen (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a)))

/-- The normalized one-chart overlap preserves its coefficient projection. -/
theorem oneBranchOpenIsoCover_structureMap (N m a b : ℕ) (t : K)
    (hN : N ≠ 0) (hbezout : (N - m) * a = 1 + b * N) :
    (oneBranchOpenIsoCover N m a b t hN hbezout).hom ≫ structureMap N m t =
      oneBranchOpenStructureMap N m a t := by
  rw [oneBranchOpenIsoCover_hom]
  erw [← Spec.map_comp]
  congr 1
  ext c
  exact coverToOneBranchOpen_coeff N m a b t c hN hbezout

/-- The normalized `1/t` overlap preserves its coefficient projection. -/
theorem inverseParameterBranchOpenIsoCover_structureMap (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) (hN : N ≠ 0)
    (hbezout : m * a = 1 + b * N) :
    (inverseParameterBranchOpenIsoCover N m a b t ht hm hN hbezout).hom ≫
      structureMap N m t = inverseParameterBranchOpenStructureMap N m a t := by
  rw [inverseParameterBranchOpenIsoCover_hom]
  erw [← Spec.map_comp]
  congr 1
  ext c
  exact coverToInverseParameterBranchOpen_coeff N m a b t c ht hm hN hbezout

/-! ## Compatibility with the original Euler deck transformation -/

/-- The original singular action at one fixes the punctured base coordinate ring. -/
private theorem oneSingularOpenDeck_base (N m : ℕ) (t : K) [NeZero N]
    (ζ : rootsOfUnity N K) :
    (tameSingularOpenDeck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) ζ).comp
        (oneBaseOpenToSingularOpen N m t) =
      oneBaseOpenToSingularOpen N m t := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (oneBaseU t))
  apply RingHom.ext
  intro v
  change tameSingularOpenDeck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) ζ
      (oneBaseOpenToSingularOpen N m t
        (algebraMap (OneBaseRing t) (OneBaseOpen t) v)) =
    oneBaseOpenToSingularOpen N m t
      (algebraMap (OneBaseRing t) (OneBaseOpen t) v)
  rw [oneBaseOpenToSingularOpen_oneBase]
  change tameSingularOpenDeck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) ζ
      (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t)
        (algebraMap (OneBaseRing t) (OneSingularRing N m t) v)) = _
  exact (tameSingularOpenDeck_algebraMap (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) ζ _).trans
      (congrArg (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t))
        ((tameSingularDeckAlgebraAction (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N (N - m) ζ).commutes v))

/-- The original singular action at `1/t` fixes the punctured base coordinate ring. -/
private theorem inverseParameterSingularOpenDeck_base (N m : ℕ) (t : K) [NeZero N]
    (ζ : rootsOfUnity N K) :
    (tameSingularOpenDeck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m ζ).comp
        (inverseParameterBaseOpenToSingularOpen N m t) =
      inverseParameterBaseOpenToSingularOpen N m t := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (inverseParameterBaseU t))
  apply RingHom.ext
  intro v
  change tameSingularOpenDeck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m ζ
      (inverseParameterBaseOpenToSingularOpen N m t
        (algebraMap (InverseParameterBaseRing t)
          (InverseParameterBaseOpen t) v)) =
    inverseParameterBaseOpenToSingularOpen N m t
      (algebraMap (InverseParameterBaseRing t)
        (InverseParameterBaseOpen t) v)
  rw [inverseParameterBaseOpenToSingularOpen_base]
  change tameSingularOpenDeck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m ζ
      (algebraMap (InverseParameterSingularRing N m t)
        (InverseParameterSingularOpen N m t)
        (algebraMap (InverseParameterBaseRing t)
          (InverseParameterSingularRing N m t) v)) = _
  exact (tameSingularOpenDeck_algebraMap (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m ζ _).trans
      (congrArg (algebraMap (InverseParameterSingularRing N m t)
        (InverseParameterSingularOpen N m t))
        ((tameSingularDeckAlgebraAction (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N m ζ).commutes v))

/-- The unchanged coordinate `y` makes the singular one-chart overlap
equivariant for the original Euler deck action. -/
theorem coverToOneSingularOpen_deck (N m : ℕ) (t : K) [NeZero N]
    (ζ : rootsOfUnity N K) :
    (tameSingularOpenDeck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) ζ).comp
        (coverToOneSingularOpen N m t) =
      (coverToOneSingularOpen N m t).comp
        (deckAlgebraAction N m t ζ).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro w
    change tameSingularOpenDeck (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N (N - m) ζ
        (coverToOneSingularOpen N m t
          (algebraMap (BaseRing t) (CoverRing N m t) w)) =
      coverToOneSingularOpen N m t
        (deckAlgebraAction N m t ζ
          (algebraMap (BaseRing t) (CoverRing N m t) w))
    rw [show coverToOneSingularOpen N m t
        (algebraMap (BaseRing t) (CoverRing N m t) w) =
          coverBaseToOneSingularOpen N m t w from by
      simp [coverToOneSingularOpen, AdjoinRoot.lift_of]]
    rw [(deckAlgebraAction N m t ζ).commutes w]
    rw [show coverToOneSingularOpen N m t
        (algebraMap (BaseRing t) (CoverRing N m t) w) =
          coverBaseToOneSingularOpen N m t w from by
      simp [coverToOneSingularOpen, AdjoinRoot.lift_of]]
    change tameSingularOpenDeck (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N (N - m) ζ
        (oneBaseOpenToSingularOpen N m t (coverBaseToOneBaseOpen t w)) =
      oneBaseOpenToSingularOpen N m t (coverBaseToOneBaseOpen t w)
    exact congrArg
      (fun f : OneBaseOpen t →+* OneSingularOpen N m t =>
        f (coverBaseToOneBaseOpen t w))
      (oneSingularOpenDeck_base N m t ζ)
  · change tameSingularOpenDeck (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N (N - m) ζ
        (coverToOneSingularOpen N m t (coverRoot N m t)) =
      coverToOneSingularOpen N m t
        (deckAlgebraAction N m t ζ (coverRoot N m t))
    rw [coverToOneSingularOpen_root]
    change tameSingularOpenDeck (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N (N - m) ζ
        (algebraMap (TameSingularRing (oneBranchProduct t)
          (oneBranchFactorPolynomial m t) N (N - m))
          (TameSingularOpen (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N (N - m))
          (tameSingularRoot (oneBranchProduct t)
            (oneBranchFactorPolynomial m t) N (N - m))) = _
    rw [tameSingularOpenDeck_algebraMap,
      tameSingularDeckAlgebraAction_root, deckAlgebraAction_root]
    let c : K := ((ζ : Kˣ) : K)
    change (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t))
      ((algebraMap K[X] (OneBaseRing t) (C c)) • oneSingularRoot N m t) =
      coverToOneSingularOpen N m t
        ((algebraMap K[X] (BaseRing t) (C c)) • coverRoot N m t)
    simp only [Algebra.smul_def, map_mul]
    have hleft :
        (algebraMap (OneSingularRing N m t) (OneSingularOpen N m t))
          (algebraMap (OneBaseRing t) (OneSingularRing N m t)
            (algebraMap K[X] (OneBaseRing t) (C c))) =
          algebraMap K (OneSingularOpen N m t) c := by
      change oneBaseToSingularOpen N m t
        (algebraMap K[X] (OneBaseRing t) (C c)) = _
      change oneBaseToSingularOpen N m t
        (algebraMap K (OneBaseRing t) c) = _
      exact oneBaseToSingularOpen_coeff N m t c
    have hright :
        coverToOneSingularOpen N m t
          (algebraMap (BaseRing t) (CoverRing N m t)
            (algebraMap K[X] (BaseRing t) (C c))) =
          algebraMap K (OneSingularOpen N m t) c := by
      change coverToOneSingularOpen N m t
        (algebraMap K (CoverRing N m t) c) = _
      exact coverToOneSingularOpen_coeff N m t c
    rw [hleft, hright, coverToOneSingularOpen_root]

/-- The unchanged `y` coordinate also makes the singular `1/t` overlap
equivariant for the original Euler deck action. -/
theorem coverToInverseParameterSingularOpen_deck (N m : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) [NeZero N] (ζ : rootsOfUnity N K) :
    (tameSingularOpenDeck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m ζ).comp
        (coverToInverseParameterSingularOpen N m t ht hm) =
      (coverToInverseParameterSingularOpen N m t ht hm).comp
        (deckAlgebraAction N m t ζ).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro w
    change tameSingularOpenDeck (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N m ζ
        (coverToInverseParameterSingularOpen N m t ht hm
          (algebraMap (BaseRing t) (CoverRing N m t) w)) =
      coverToInverseParameterSingularOpen N m t ht hm
        (deckAlgebraAction N m t ζ
          (algebraMap (BaseRing t) (CoverRing N m t) w))
    rw [show coverToInverseParameterSingularOpen N m t ht hm
        (algebraMap (BaseRing t) (CoverRing N m t) w) =
          coverBaseToInverseParameterSingularOpen N m t ht w from by
      simp [coverToInverseParameterSingularOpen, AdjoinRoot.lift_of]]
    rw [(deckAlgebraAction N m t ζ).commutes w]
    rw [show coverToInverseParameterSingularOpen N m t ht hm
        (algebraMap (BaseRing t) (CoverRing N m t) w) =
          coverBaseToInverseParameterSingularOpen N m t ht w from by
      simp [coverToInverseParameterSingularOpen, AdjoinRoot.lift_of]]
    change tameSingularOpenDeck (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N m ζ
        (inverseParameterBaseOpenToSingularOpen N m t
          (coverBaseToInverseParameterBaseOpen t ht w)) =
      inverseParameterBaseOpenToSingularOpen N m t
        (coverBaseToInverseParameterBaseOpen t ht w)
    exact congrArg
      (fun f : InverseParameterBaseOpen t →+* InverseParameterSingularOpen N m t =>
        f (coverBaseToInverseParameterBaseOpen t ht w))
      (inverseParameterSingularOpenDeck_base N m t ζ)
  · change tameSingularOpenDeck (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N m ζ
        (coverToInverseParameterSingularOpen N m t ht hm (coverRoot N m t)) =
      coverToInverseParameterSingularOpen N m t ht hm
        (deckAlgebraAction N m t ζ (coverRoot N m t))
    rw [coverToInverseParameterSingularOpen_root]
    change tameSingularOpenDeck (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N m ζ
        (algebraMap (TameSingularRing (inverseParameterBranchProduct t)
          (inverseParameterBranchFactorPolynomial N m t) N m)
          (TameSingularOpen (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N m)
          (tameSingularRoot (inverseParameterBranchProduct t)
            (inverseParameterBranchFactorPolynomial N m t) N m)) = _
    rw [tameSingularOpenDeck_algebraMap, tameSingularDeckAlgebraAction_root,
      deckAlgebraAction_root]
    let c : K := ((ζ : Kˣ) : K)
    change (algebraMap (InverseParameterSingularRing N m t)
      (InverseParameterSingularOpen N m t))
      ((algebraMap K[X] (InverseParameterBaseRing t) (C c)) •
        inverseParameterSingularRoot N m t) =
      coverToInverseParameterSingularOpen N m t ht hm
        ((algebraMap K[X] (BaseRing t) (C c)) • coverRoot N m t)
    simp only [Algebra.smul_def, map_mul]
    have hleft :
        (algebraMap (InverseParameterSingularRing N m t)
          (InverseParameterSingularOpen N m t))
          (algebraMap (InverseParameterBaseRing t)
            (InverseParameterSingularRing N m t)
            (algebraMap K[X] (InverseParameterBaseRing t) (C c))) =
          algebraMap K (InverseParameterSingularOpen N m t) c := by
      change inverseParameterBaseToSingularOpen N m t
        (algebraMap K[X] (InverseParameterBaseRing t) (C c)) = _
      change inverseParameterBaseToSingularOpen N m t
        (algebraMap K (InverseParameterBaseRing t) c) = _
      exact inverseParameterBaseToSingularOpen_coeff N m t c
    have hright :
        coverToInverseParameterSingularOpen N m t ht hm
          (algebraMap (BaseRing t) (CoverRing N m t)
            (algebraMap K[X] (BaseRing t) (C c))) =
          algebraMap K (InverseParameterSingularOpen N m t) c := by
      change coverToInverseParameterSingularOpen N m t ht hm
        (algebraMap K (CoverRing N m t) c) = _
      exact coverToInverseParameterSingularOpen_coeff N m t c ht hm
    rw [hleft, hright, coverToInverseParameterSingularOpen_root]

/-- The normalized overlap at one carries the original `y`-deck action to
the `ζ^a` action on its normalized coordinate. -/
theorem coverToOneBranchOpen_deck (N m a b : ℕ) (t : K)
    [NeZero N] (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    (tameBranchOpenDeck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a ζ).comp
        (oneBranchOpenEquivCover N m a b t (NeZero.ne N) hbezout).symm.toRingHom =
      (oneBranchOpenEquivCover N m a b t (NeZero.ne N) hbezout).symm.toRingHom.comp
        (deckAlgebraAction N m t ζ).toRingHom := by
  apply RingHom.ext
  intro w
  let F := tameSingularOpenToBranchOpen (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) a b
    (isUnit_oneBranchFactor m t) hbezout
  let C := coverToOneSingularOpen N m t
  let dZ := tameBranchOpenDeck (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N a ζ
  let dS := tameSingularOpenDeck (oneBranchProduct t)
    (oneBranchFactorPolynomial m t) N (N - m) ζ
  let dC := (deckAlgebraAction N m t ζ).toRingHom
  change dZ (F (C w)) = F (C (dC w))
  have hF : dZ.comp F = F.comp dS :=
    tameSingularOpenToBranchOpen_deck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N (N - m) a b
      (isUnit_oneBranchFactor m t) hbezout ζ
  have hC : dS.comp C = C.comp dC := coverToOneSingularOpen_deck N m t ζ
  calc
    dZ (F (C w)) = F (dS (C w)) :=
      congrArg (fun f : OneSingularOpen N m t →+* TameBranchOpen
        (oneBranchProduct t) (oneBranchFactorPolynomial m t) N a => f (C w)) hF
    _ = F (C (dC w)) :=
      congrArg F (congrArg (fun f : CoverRing N m t →+*
        OneSingularOpen N m t => f w) hC)

/-- The normalized overlap at `1/t` carries the original `y`-deck action
to the `ζ^a` action on its normalized coordinate. -/
theorem coverToInverseParameterBranchOpen_deck (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) [NeZero N]
    (hbezout : m * a = 1 + b * N) (ζ : rootsOfUnity N K) :
    (tameBranchOpenDeck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a ζ).comp
        (inverseParameterBranchOpenEquivCover N m a b t ht hm
          (NeZero.ne N) hbezout).symm.toRingHom =
      (inverseParameterBranchOpenEquivCover N m a b t ht hm
        (NeZero.ne N) hbezout).symm.toRingHom.comp
        (deckAlgebraAction N m t ζ).toRingHom := by
  apply RingHom.ext
  intro w
  let F := tameSingularOpenToBranchOpen (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m a b
    (isUnit_inverseParameterBranchFactor N m t ht) hbezout
  let C := coverToInverseParameterSingularOpen N m t ht hm
  let dZ := tameBranchOpenDeck (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N a ζ
  let dS := tameSingularOpenDeck (inverseParameterBranchProduct t)
    (inverseParameterBranchFactorPolynomial N m t) N m ζ
  let dC := (deckAlgebraAction N m t ζ).toRingHom
  change dZ (F (C w)) = F (C (dC w))
  have hF : dZ.comp F = F.comp dS :=
    tameSingularOpenToBranchOpen_deck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N m a b
      (isUnit_inverseParameterBranchFactor N m t ht) hbezout ζ
  have hC : dS.comp C = C.comp dC :=
    coverToInverseParameterSingularOpen_deck N m t ht hm ζ
  calc
    dZ (F (C w)) = F (dS (C w)) :=
      congrArg (fun f : InverseParameterSingularOpen N m t →+* TameBranchOpen
        (inverseParameterBranchProduct t) (inverseParameterBranchFactorPolynomial N m t)
        N a => f (C w)) hF
    _ = F (C (dC w)) :=
      congrArg F (congrArg (fun f : CoverRing N m t →+*
        InverseParameterSingularOpen N m t => f w) hC)

/-- The original Euler deck action on the punctured normalized chart at one
acts on `z` through the power `ζ^a`. -/
def oneBranchOpenDeckTransformation (N m a : ℕ) (t : K) [NeZero N]
    (ζ : rootsOfUnity N K) :
    tameBranchOpenScheme (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a ⟶
    tameBranchOpenScheme (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a :=
  Spec.map (CommRingCat.ofHom
    (tameBranchOpenDeck (oneBranchProduct t)
      (oneBranchFactorPolynomial m t) N a ζ))

/-- The original Euler deck action on the punctured normalized chart at
`1/t` acts on `z` through the power `ζ^a`. -/
def inverseParameterBranchOpenDeckTransformation (N m a : ℕ) (t : K) [NeZero N]
    (ζ : rootsOfUnity N K) :
    tameBranchOpenScheme (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a ⟶
    tameBranchOpenScheme (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a :=
  Spec.map (CommRingCat.ofHom
    (tameBranchOpenDeck (inverseParameterBranchProduct t)
      (inverseParameterBranchFactorPolynomial N m t) N a ζ))

/-- The scheme overlap at one intertwines the original `y`-deck action
with the normalized `z ↦ ζ^a z` action. -/
theorem oneBranchOpenIsoCover_deck (N m a b : ℕ) (t : K)
    [NeZero N] (hbezout : (N - m) * a = 1 + b * N)
    (ζ : rootsOfUnity N K) :
    (oneBranchOpenIsoCover N m a b t (NeZero.ne N) hbezout).hom ≫
      (deckTransformation N m t ζ).hom =
    oneBranchOpenDeckTransformation N m a t ζ ≫
      (oneBranchOpenIsoCover N m a b t (NeZero.ne N) hbezout).hom := by
  rw [oneBranchOpenIsoCover_hom, deckTransformation_hom]
  change Spec.map (CommRingCat.ofHom
      (oneBranchOpenEquivCover N m a b t (NeZero.ne N) hbezout).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (deckAlgebraAction N m t ζ).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (tameBranchOpenDeck (oneBranchProduct t)
        (oneBranchFactorPolynomial m t) N a ζ)) ≫
      Spec.map (CommRingCat.ofHom
        (oneBranchOpenEquivCover N m a b t (NeZero.ne N) hbezout).symm.toRingHom)
  erw [← Spec.map_comp]
  erw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (coverToOneBranchOpen_deck N m a b t hbezout ζ).symm

/-- The scheme overlap at `1/t` intertwines the original `y`-deck action
with the normalized `z ↦ ζ^a z` action. -/
theorem inverseParameterBranchOpenIsoCover_deck (N m a b : ℕ) (t : K)
    (ht : IsUnit t) (hm : m ≤ N) [NeZero N]
    (hbezout : m * a = 1 + b * N) (ζ : rootsOfUnity N K) :
    (inverseParameterBranchOpenIsoCover N m a b t ht hm
      (NeZero.ne N) hbezout).hom ≫
      (deckTransformation N m t ζ).hom =
    inverseParameterBranchOpenDeckTransformation N m a t ζ ≫
      (inverseParameterBranchOpenIsoCover N m a b t ht hm
        (NeZero.ne N) hbezout).hom := by
  rw [inverseParameterBranchOpenIsoCover_hom, deckTransformation_hom]
  change Spec.map (CommRingCat.ofHom
      (inverseParameterBranchOpenEquivCover N m a b t ht hm
        (NeZero.ne N) hbezout).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (deckAlgebraAction N m t ζ).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (tameBranchOpenDeck (inverseParameterBranchProduct t)
        (inverseParameterBranchFactorPolynomial N m t) N a ζ)) ≫
      Spec.map (CommRingCat.ofHom
        (inverseParameterBranchOpenEquivCover N m a b t ht hm
          (NeZero.ne N) hbezout).symm.toRingHom)
  erw [← Spec.map_comp]
  erw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    (coverToInverseParameterBranchOpen_deck N m a b t ht hm hbezout ζ).symm

end HilbertModularity.Hypergeometric.EulerCover
