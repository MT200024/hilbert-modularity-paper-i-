/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationInvariantField

/-! # Evaluation of the branch-open Euler algebra at an Euler point

The rational reflection of [GPRV, Proposition 9.5] can act on the actual
function field only after its formulas define a map on the branch-open
coordinate algebra.  This module constructs that map from the universal
properties of localization and the monic Euler root algebra.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K F : Type*} [Field K] [Field F]

/-- Evaluate the polynomial base coordinate at a branch-open Euler point. -/
def openEulerPointPolynomialHom (σ : K →+* F) (N m : ℕ) (t : K)
    (p : OpenEulerPoint N m (σ t)) : K[X] →+* F :=
  Polynomial.eval₂RingHom σ p.x

@[simp] theorem openEulerPointPolynomialHom_X (σ : K →+* F) (N m : ℕ)
    (t : K) (p : OpenEulerPoint N m (σ t)) :
    openEulerPointPolynomialHom σ N m t p X = p.x := by
  simp [openEulerPointPolynomialHom]

@[simp] theorem openEulerPointPolynomialHom_C (σ : K →+* F) (N m : ℕ)
    (t a : K) (p : OpenEulerPoint N m (σ t)) :
    openEulerPointPolynomialHom σ N m t p (C a) = σ a := by
  simp [openEulerPointPolynomialHom]

/-- The branch polynomial is nonzero at a point of the branch complement. -/
theorem openEulerPoint_branchProduct_ne_zero (σ : K →+* F) (N m : ℕ)
    (t : K) (p : OpenEulerPoint N m (σ t)) :
    openEulerPointPolynomialHom σ N m t p (branchProduct t) ≠ 0 := by
  simpa [branchProduct, openEulerPointPolynomialHom] using
    mul_ne_zero (mul_ne_zero p.x_ne_zero p.one_sub_x_ne_zero)
      p.one_sub_tx_ne_zero

/-- Evaluation on the localized base of the Euler cover. -/
def openEulerPointBaseHom (σ : K →+* F) (N m : ℕ) (t : K)
    (p : OpenEulerPoint N m (σ t)) : BaseRing t →+* F :=
  Localization.awayLift (openEulerPointPolynomialHom σ N m t p)
    (branchProduct t)
    (isUnit_iff_ne_zero.mpr (openEulerPoint_branchProduct_ne_zero σ N m t p))

@[simp] theorem openEulerPointBaseHom_algebraMap (σ : K →+* F) (N m : ℕ)
    (t : K) (p : OpenEulerPoint N m (σ t)) (q : K[X]) :
    openEulerPointBaseHom σ N m t p (algebraMap K[X] (BaseRing t) q) =
      openEulerPointPolynomialHom σ N m t p q := by
  unfold openEulerPointBaseHom
  exact IsLocalization.Away.lift_eq (branchProduct t) _ q

/-- The localized radicand evaluates to the right side of the point equation. -/
theorem openEulerPointBaseHom_radicand (σ : K →+* F) (N m : ℕ)
    (t : K) (p : OpenEulerPoint N m (σ t)) :
    openEulerPointBaseHom σ N m t p (radicand N m t) =
      p.x ^ m * (1 - p.x) ^ (N - m) * (1 - σ t * p.x) ^ m := by
  rw [radicand, openEulerPointBaseHom_algebraMap]
  simp [branchPolynomial, openEulerPointPolynomialHom, eval₂_sub, eval₂_pow]

/-- The actual branch-open Euler root algebra evaluates at any branch-open
point satisfying its defining equation. -/
def openEulerPointCoverHom (σ : K →+* F) (N m : ℕ) (t : K)
    (p : OpenEulerPoint N m (σ t)) : CoverRing N m t →+* F :=
  AdjoinRoot.lift (openEulerPointBaseHom σ N m t p) p.y (by
    simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [openEulerPointBaseHom_radicand, ← p.equation, sub_self])

@[simp] theorem openEulerPointCoverHom_root (σ : K →+* F) (N m : ℕ)
    (t : K) (p : OpenEulerPoint N m (σ t)) :
    openEulerPointCoverHom σ N m t p (coverRoot N m t) = p.y := by
  simp [openEulerPointCoverHom, coverRoot, AdjoinRoot.lift_root]

@[simp] theorem openEulerPointCoverHom_base (σ : K →+* F) (N m : ℕ)
    (t : K) (p : OpenEulerPoint N m (σ t)) (a : BaseRing t) :
    openEulerPointCoverHom σ N m t p
      (algebraMap (BaseRing t) (CoverRing N m t) a) =
      openEulerPointBaseHom σ N m t p a := by
  simp [openEulerPointCoverHom, AdjoinRoot.lift_of]

/-- Evaluation at the reflected generic point defines a homomorphism from the
actual branch-open Euler algebra to its function field.  Injectivity, and
therefore extension to a field automorphism, is a separate claim. -/
def genericReflectionCoverHom (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    CoverRing N m t →+* CoverFunctionField N m t := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact openEulerPointCoverHom (algebraMap K (CoverFunctionField N m t)) N m t
    (reflectOpenEulerPoint N m (Nat.le_of_lt hm)
      ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht)
      (genericOpenEulerPoint N m t hN hmPos hm hcop))

/-- The generic reflection map is evaluation at the reflected generic point. -/
theorem genericReflectionCoverHom_eq_openEulerPointCoverHom (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionCoverHom N m t hN hmPos hm hcop ht =
      openEulerPointCoverHom (algebraMap K (CoverFunctionField N m t)) N m t
        (reflectOpenEulerPoint N m (Nat.le_of_lt hm)
          ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht)
          (genericOpenEulerPoint N m t hN hmPos hm hcop)) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rfl

@[simp] theorem genericReflectionCoverHom_root (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionCoverHom N m t hN hmPos hm hcop ht (coverRoot N m t) =
      reflectionY (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) (coverFunctionFieldRoot N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  simp [genericReflectionCoverHom]

@[simp] theorem genericReflectionCoverHom_x (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N)
    (hcop : m.Coprime N) (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionCoverHom N m t hN hmPos hm hcop ht
      (algebraMap K[X] (CoverRing N m t) X) =
      reflectionX (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [genericReflectionCoverHom, IsScalarTower.algebraMap_apply K[X]
    (BaseRing t) (CoverRing N m t), openEulerPointCoverHom_base,
    openEulerPointBaseHom_algebraMap]
  simp [openEulerPointPolynomialHom]

end HilbertModularity.Hypergeometric.EulerCover
