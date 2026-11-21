/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.TameBranch

/-! # Coefficient change for tame Euler branch charts

The local Kummer presentations and their retained coordinates are functorial in
the coefficient ring. This is the relative chart used for the Euler family in
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open Polynomial
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u v
variable {C : Type u} {C' : Type v} [CommRing C] [CommRing C'] (f : C →+* C')

/-- Coefficient change on the localized affine-line coordinate ring. -/
def tameBaseRingMap (g : C[X]) : TameBaseRing g →+* TameBaseRing (g.map f) :=
  Localization.awayLift
    ((algebraMap C'[X] (TameBaseRing (g.map f))).comp (Polynomial.mapRingHom f))
    g (by
      simpa using (IsLocalization.Away.algebraMap_isUnit (g.map f) :
        IsUnit (algebraMap C'[X] (TameBaseRing (g.map f)) (g.map f))))

/-- The localized coefficient map evaluates a polynomial after mapping its coefficients. -/
theorem tameBaseRingMap_algebraMap (g p : C[X]) :
    tameBaseRingMap f g (algebraMap C[X] (TameBaseRing g) p) =
      algebraMap C'[X] (TameBaseRing (g.map f)) (p.map f) := by
  unfold tameBaseRingMap
  exact IsLocalization.Away.lift_eq g _ p

/-- Coefficient change preserves the named affine-line coordinate. -/
@[simp] theorem tameBaseRingMap_x (g : C[X]) :
    tameBaseRingMap f g (tameBaseX g) = tameBaseX (g.map f) := by
  rw [tameBaseX, tameBaseRingMap_algebraMap, map_X]
  rfl

/-- Coefficient change preserves the polynomial unit factor. -/
theorem tameBaseRingMap_polynomial (g P : C[X]) :
    tameBaseRingMap f g (algebraMap C[X] (TameBaseRing g) P) =
      algebraMap C'[X] (TameBaseRing (g.map f)) (P.map f) :=
  tameBaseRingMap_algebraMap f g P

/-- A polynomial unit remains a unit after arbitrary coefficient change. -/
theorem tameBaseRingMap_isUnit (g P : C[X])
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) :
    IsUnit (algebraMap C'[X] (TameBaseRing (g.map f)) (P.map f)) := by
  simpa only [tameBaseRingMap_polynomial] using hP.map (tameBaseRingMap f g)

/-- The chosen unit representing the polynomial factor maps to the chosen
unit in the coefficient-changed chart. -/
theorem tameBaseUnit_map (g P : C[X])
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) :
    Units.map (tameBaseRingMap f g).toMonoidHom (tameBaseUnit g P hP) =
      tameBaseUnit (g.map f) (P.map f) (tameBaseRingMap_isUnit f g P hP) := by
  apply Units.val_injective
  change tameBaseRingMap f g (algebraMap C[X] (TameBaseRing g) P) =
    algebraMap C'[X] (TameBaseRing (g.map f)) (P.map f)
  exact tameBaseRingMap_polynomial f g P

/-- The normalized tame radicand is coefficientwise natural. -/
theorem tameBranchRadicand_map (P : C[X]) (a : ℕ) :
    (tameBranchRadicand P a).map f = tameBranchRadicand (P.map f) a := by
  simp [tameBranchRadicand]

/-- The original singular radicand is coefficientwise natural. -/
theorem tameSingularRadicand_map (P : C[X]) (r : ℕ) :
    (tameSingularRadicand P r).map f = tameSingularRadicand (P.map f) r := by
  simp [tameSingularRadicand]

/-- Mapping coefficients carries the localized Kummer polynomial to its new presentation. -/
theorem localizedKummerEquation_map (g Q : C[X]) (n : ℕ) :
    (RingTheory.Smooth.localizedKummerEquation g Q n).map (tameBaseRingMap f g) =
      RingTheory.Smooth.localizedKummerEquation (g.map f) (Q.map f) n := by
  simp [RingTheory.Smooth.localizedKummerEquation, tameBaseRingMap_algebraMap]

/-- The mapped Kummer equation vanishes in its coefficientwise presentation. -/
theorem localizedKummerEquation_dvd_map (g Q : C[X]) (n : ℕ) :
    RingTheory.Smooth.localizedKummerEquation (g.map f) (Q.map f) n ∣
      (RingTheory.Smooth.localizedKummerEquation g Q n).map (tameBaseRingMap f g) := by
  rw [localizedKummerEquation_map]

/-- The actual localized Kummer algebra maps to its coefficientwise image. -/
def localizedKummerRingMap (g Q : C[X]) (n : ℕ) :
    RingTheory.Smooth.localizedKummerAlgebra g Q n →+*
      RingTheory.Smooth.localizedKummerAlgebra (g.map f) (Q.map f) n :=
  AdjoinRoot.map (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g Q n)
    (RingTheory.Smooth.localizedKummerEquation (g.map f) (Q.map f) n)
    (localizedKummerEquation_dvd_map f g Q n)

/-- The Kummer map fixes the adjoined root as a named coordinate. -/
@[simp] theorem localizedKummerRingMap_root (g Q : C[X]) (n : ℕ) :
    localizedKummerRingMap f g Q n (RingTheory.Smooth.localizedKummerZ g Q n) =
      RingTheory.Smooth.localizedKummerZ (g.map f) (Q.map f) n := by
  exact AdjoinRoot.map_root (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g Q n)
    (RingTheory.Smooth.localizedKummerEquation (g.map f) (Q.map f) n)
    (localizedKummerEquation_dvd_map f g Q n)

/-- The Kummer map commutes with the localized base inclusion. -/
theorem localizedKummerRingMap_base (g Q : C[X]) (n : ℕ) (a : TameBaseRing g) :
    localizedKummerRingMap f g Q n
        (algebraMap (TameBaseRing g) (RingTheory.Smooth.localizedKummerAlgebra g Q n) a) =
      algebraMap (TameBaseRing (g.map f))
        (RingTheory.Smooth.localizedKummerAlgebra (g.map f) (Q.map f) n)
        (tameBaseRingMap f g a) := by
  change localizedKummerRingMap f g Q n
      (AdjoinRoot.of (RingTheory.Smooth.localizedKummerEquation g Q n) a) =
    AdjoinRoot.of (RingTheory.Smooth.localizedKummerEquation (g.map f) (Q.map f) n)
      (tameBaseRingMap f g a)
  exact AdjoinRoot.map_of (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g Q n)
    (RingTheory.Smooth.localizedKummerEquation (g.map f) (Q.map f) n)
    (localizedKummerEquation_dvd_map f g Q n) a

/-- Transport of the target radicand leaves the universal Kummer map unchanged. -/
theorem localizedKummerRingMap_transport (g Q : C[X]) (n : ℕ)
    (Q' : C'[X]) (hQ : Q.map f = Q')
    (hdvd : RingTheory.Smooth.localizedKummerEquation (g.map f) Q' n ∣
      (RingTheory.Smooth.localizedKummerEquation g Q n).map
        (tameBaseRingMap f g))
    (v : RingTheory.Smooth.localizedKummerAlgebra g Q n) :
    (hQ ▸ localizedKummerRingMap f g Q n v) =
      AdjoinRoot.map (tameBaseRingMap f g)
        (RingTheory.Smooth.localizedKummerEquation g Q n)
        (RingTheory.Smooth.localizedKummerEquation (g.map f) Q' n)
        hdvd v := by
  cases hQ
  rfl

/-- Divisibility for the normalized branch equation after coefficient change. -/
theorem tameBranchEquation_dvd_map (g P : C[X]) (N a : ℕ) :
    RingTheory.Smooth.localizedKummerEquation (g.map f)
        (tameBranchRadicand (P.map f) a) N ∣
      (RingTheory.Smooth.localizedKummerEquation g
        (tameBranchRadicand P a) N).map (tameBaseRingMap f g) := by
  rw [localizedKummerEquation_map, tameBranchRadicand_map]

/-- Divisibility for the singular branch equation after coefficient change. -/
theorem tameSingularEquation_dvd_map (g P : C[X]) (N r : ℕ) :
    RingTheory.Smooth.localizedKummerEquation (g.map f)
        (tameSingularRadicand (P.map f) r) N ∣
      (RingTheory.Smooth.localizedKummerEquation g
        (tameSingularRadicand P r) N).map (tameBaseRingMap f g) := by
  rw [localizedKummerEquation_map, tameSingularRadicand_map]

/-- Coefficient change on the normalized tame chart. -/
def tameBranchRingMap (g P : C[X]) (N a : ℕ) :
    TameBranchRing g P N a →+* TameBranchRing (g.map f) (P.map f) N a :=
  AdjoinRoot.map (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g (tameBranchRadicand P a) N)
    (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameBranchRadicand (P.map f) a) N)
    (tameBranchEquation_dvd_map f g P N a)

/-- Coefficient change on the original singular chart. -/
def tameSingularRingMap (g P : C[X]) (N r : ℕ) :
    TameSingularRing g P N r →+* TameSingularRing (g.map f) (P.map f) N r :=
  AdjoinRoot.map (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N)
    (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameSingularRadicand (P.map f) r) N)
    (tameSingularEquation_dvd_map f g P N r)

/-- The normalized covering coordinate is preserved under coefficient change. -/
@[simp] theorem tameBranchRingMap_root (g P : C[X]) (N a : ℕ) :
    tameBranchRingMap f g P N a (tameBranchRoot g P N a) =
      tameBranchRoot (g.map f) (P.map f) N a := by
  exact AdjoinRoot.map_root (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g (tameBranchRadicand P a) N)
    (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameBranchRadicand (P.map f) a) N)
    (tameBranchEquation_dvd_map f g P N a)

/-- The original singular covering coordinate is preserved under coefficient change. -/
@[simp] theorem tameSingularRingMap_root (g P : C[X]) (N r : ℕ) :
    tameSingularRingMap f g P N r (tameSingularRoot g P N r) =
      tameSingularRoot (g.map f) (P.map f) N r := by
  exact AdjoinRoot.map_root (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N)
    (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameSingularRadicand (P.map f) r) N)
    (tameSingularEquation_dvd_map f g P N r)

/-- The normalized chart map restricts to coefficient change on its localized base. -/
theorem tameBranchRingMap_base (g P : C[X]) (N a : ℕ) (v : TameBaseRing g) :
    tameBranchRingMap f g P N a (algebraMap (TameBaseRing g) (TameBranchRing g P N a) v) =
      algebraMap (TameBaseRing (g.map f))
        (TameBranchRing (g.map f) (P.map f) N a) (tameBaseRingMap f g v) := by
  change tameBranchRingMap f g P N a
      (AdjoinRoot.of (RingTheory.Smooth.localizedKummerEquation g
        (tameBranchRadicand P a) N) v) =
    AdjoinRoot.of (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameBranchRadicand (P.map f) a) N) (tameBaseRingMap f g v)
  exact AdjoinRoot.map_of (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g (tameBranchRadicand P a) N)
    (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameBranchRadicand (P.map f) a) N)
    (tameBranchEquation_dvd_map f g P N a) v

/-- The singular chart map restricts to coefficient change on its localized base. -/
theorem tameSingularRingMap_base (g P : C[X]) (N r : ℕ) (v : TameBaseRing g) :
    tameSingularRingMap f g P N r
        (algebraMap (TameBaseRing g) (TameSingularRing g P N r) v) =
      algebraMap (TameBaseRing (g.map f))
        (TameSingularRing (g.map f) (P.map f) N r) (tameBaseRingMap f g v) := by
  change tameSingularRingMap f g P N r
      (AdjoinRoot.of (RingTheory.Smooth.localizedKummerEquation g
        (tameSingularRadicand P r) N) v) =
    AdjoinRoot.of (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameSingularRadicand (P.map f) r) N) (tameBaseRingMap f g v)
  exact AdjoinRoot.map_of (tameBaseRingMap f g)
    (RingTheory.Smooth.localizedKummerEquation g (tameSingularRadicand P r) N)
    (RingTheory.Smooth.localizedKummerEquation (g.map f)
      (tameSingularRadicand (P.map f) r) N)
    (tameSingularEquation_dvd_map f g P N r) v

/-- The affine-line coordinate is preserved on the normalized chart. -/
@[simp] theorem tameBranchRingMap_x (g P : C[X]) (N a : ℕ) :
    tameBranchRingMap f g P N a (tameBranchX g P N a) =
      tameBranchX (g.map f) (P.map f) N a := by
  change tameBranchRingMap f g P N a
      (algebraMap (TameBaseRing g) (TameBranchRing g P N a) (tameBaseX g)) =
    algebraMap (TameBaseRing (g.map f))
      (TameBranchRing (g.map f) (P.map f) N a) (tameBaseX (g.map f))
  rw [tameBranchRingMap_base, tameBaseRingMap_x]

/-- The affine-line coordinate is preserved on the singular chart. -/
@[simp] theorem tameSingularRingMap_x (g P : C[X]) (N r : ℕ) :
    tameSingularRingMap f g P N r (tameSingularX g P N r) =
      tameSingularX (g.map f) (P.map f) N r := by
  change tameSingularRingMap f g P N r
      (algebraMap (TameBaseRing g) (TameSingularRing g P N r) (tameBaseX g)) =
    algebraMap (TameBaseRing (g.map f))
      (TameSingularRing (g.map f) (P.map f) N r) (tameBaseX (g.map f))
  rw [tameSingularRingMap_base, tameBaseRingMap_x]

/-- Coefficient change on the normalized punctured chart. -/
def tameBranchOpenRingMap (g P : C[X]) (N a : ℕ) :
    TameBranchOpen g P N a →+*
      TameBranchOpen (g.map f) (P.map f) N a :=
  Localization.awayLift
    ((algebraMap (TameBranchRing (g.map f) (P.map f) N a)
      (TameBranchOpen (g.map f) (P.map f) N a)).comp
        (tameBranchRingMap f g P N a))
    (tameBranchX g P N a) (by
      change IsUnit (algebraMap (TameBranchRing (g.map f) (P.map f) N a)
        (TameBranchOpen (g.map f) (P.map f) N a)
        (tameBranchRingMap f g P N a (tameBranchX g P N a)))
      rw [tameBranchRingMap_x]
      simpa only [tameBranchOpenXUnit_val] using
        (tameBranchOpenXUnit (g.map f) (P.map f) N a).isUnit)

/-- Coefficient change on the singular punctured chart. -/
def tameSingularOpenRingMap (g P : C[X]) (N r : ℕ) :
    TameSingularOpen g P N r →+*
      TameSingularOpen (g.map f) (P.map f) N r :=
  Localization.awayLift
    ((algebraMap (TameSingularRing (g.map f) (P.map f) N r)
      (TameSingularOpen (g.map f) (P.map f) N r)).comp
        (tameSingularRingMap f g P N r))
    (tameSingularX g P N r) (by
      change IsUnit (algebraMap (TameSingularRing (g.map f) (P.map f) N r)
        (TameSingularOpen (g.map f) (P.map f) N r)
        (tameSingularRingMap f g P N r (tameSingularX g P N r)))
      rw [tameSingularRingMap_x]
      simpa only [tameSingularOpenXUnit_val] using
        (tameSingularOpenXUnit (g.map f) (P.map f) N r).isUnit)

/-- The punctured normalized map agrees with the map of the whole chart. -/
@[simp] theorem tameBranchOpenRingMap_algebraMap (g P : C[X]) (N a : ℕ)
    (v : TameBranchRing g P N a) :
    tameBranchOpenRingMap f g P N a
        (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a) v) =
      algebraMap (TameBranchRing (g.map f) (P.map f) N a)
        (TameBranchOpen (g.map f) (P.map f) N a)
        (tameBranchRingMap f g P N a v) := by
  have hg : IsUnit
      (((algebraMap (TameBranchRing (g.map f) (P.map f) N a)
        (TameBranchOpen (g.map f) (P.map f) N a)).comp
          (tameBranchRingMap f g P N a)) (tameBranchX g P N a)) := by
    rw [RingHom.comp_apply, tameBranchRingMap_x]
    simpa only [tameBranchOpenXUnit_val] using
      (tameBranchOpenXUnit (g.map f) (P.map f) N a).isUnit
  change (IsLocalization.Away.lift (tameBranchX g P N a) hg)
    (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a) v) = _
  exact IsLocalization.Away.lift_eq (tameBranchX g P N a) hg v

/-- The punctured singular map agrees with the map of the whole chart. -/
@[simp] theorem tameSingularOpenRingMap_algebraMap (g P : C[X]) (N r : ℕ)
    (v : TameSingularRing g P N r) :
    tameSingularOpenRingMap f g P N r
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) v) =
      algebraMap (TameSingularRing (g.map f) (P.map f) N r)
        (TameSingularOpen (g.map f) (P.map f) N r)
        (tameSingularRingMap f g P N r v) := by
  have hg : IsUnit
      (((algebraMap (TameSingularRing (g.map f) (P.map f) N r)
        (TameSingularOpen (g.map f) (P.map f) N r)).comp
          (tameSingularRingMap f g P N r)) (tameSingularX g P N r)) := by
    rw [RingHom.comp_apply, tameSingularRingMap_x]
    simpa only [tameSingularOpenXUnit_val] using
      (tameSingularOpenXUnit (g.map f) (P.map f) N r).isUnit
  change (IsLocalization.Away.lift (tameSingularX g P N r) hg)
    (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) v) = _
  exact IsLocalization.Away.lift_eq (tameSingularX g P N r) hg v

/-- The localized base map respects the original coefficient algebra. -/
theorem tameBaseRingMap_coeff (g : C[X]) (c : C) :
    tameBaseRingMap f g (algebraMap C (TameBaseRing g) c) =
      algebraMap C' (TameBaseRing (g.map f)) (f c) := by
  rw [show algebraMap C (TameBaseRing g) c =
    algebraMap C[X] (TameBaseRing g) (Polynomial.C c) from
      IsScalarTower.algebraMap_apply C C[X] (TameBaseRing g) c]
  rw [tameBaseRingMap_algebraMap, Polynomial.map_C]
  exact IsScalarTower.algebraMap_apply C' C'[X] (TameBaseRing (g.map f)) (f c)

/-- Coefficient change preserves the original coefficient structural map of a
localized Kummer algebra. -/
theorem localizedKummerRingMap_coeff (g Q : C[X]) (n : ℕ) (c : C) :
    localizedKummerRingMap f g Q n
        (algebraMap C (RingTheory.Smooth.localizedKummerAlgebra g Q n) c) =
      algebraMap C' (RingTheory.Smooth.localizedKummerAlgebra
        (g.map f) (Q.map f) n) (f c) := by
  rw [show algebraMap C (RingTheory.Smooth.localizedKummerAlgebra g Q n) c =
    algebraMap (TameBaseRing g) (RingTheory.Smooth.localizedKummerAlgebra g Q n)
      (algebraMap C (TameBaseRing g) c) from
      IsScalarTower.algebraMap_apply C (TameBaseRing g)
        (RingTheory.Smooth.localizedKummerAlgebra g Q n) c]
  rw [localizedKummerRingMap_base, tameBaseRingMap_coeff]
  exact IsScalarTower.algebraMap_apply C' (TameBaseRing (g.map f))
    (RingTheory.Smooth.localizedKummerAlgebra (g.map f) (Q.map f) n) (f c)

/-- Coefficient change commutes with the normalization map from the
singular tame chart. -/
theorem tameSingularToBranch_natural (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    (tameBranchRingMap f g P N a).comp
        (tameSingularToBranch g P N r a b hP hbezout).toRingHom =
      (tameSingularToBranch (g.map f) (P.map f) N r a b
        (tameBaseRingMap_isUnit f g P hP) hbezout).toRingHom.comp
        (tameSingularRingMap f g P N r) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change tameBranchRingMap f g P N a
        (tameSingularToBranch g P N r a b hP hbezout
          (algebraMap (TameBaseRing g) (TameSingularRing g P N r) v)) =
      tameSingularToBranch (g.map f) (P.map f) N r a b
        (tameBaseRingMap_isUnit f g P hP) hbezout
        (tameSingularRingMap f g P N r
          (algebraMap (TameBaseRing g) (TameSingularRing g P N r) v))
    rw [(tameSingularToBranch g P N r a b hP hbezout).commutes,
      tameBranchRingMap_base, tameSingularRingMap_base,
      (tameSingularToBranch (g.map f) (P.map f) N r a b
        (tameBaseRingMap_isUnit f g P hP) hbezout).commutes]
  · change tameBranchRingMap f g P N a
      (tameSingularToBranch g P N r a b hP hbezout
        (tameSingularRoot g P N r)) =
      tameSingularToBranch (g.map f) (P.map f) N r a b
        (tameBaseRingMap_isUnit f g P hP) hbezout
        (tameSingularRingMap f g P N r (tameSingularRoot g P N r))
    rw [tameSingularToBranch_root, map_mul, map_pow,
      tameBranchRingMap_root, tameSingularRingMap_root,
      tameSingularToBranch_root, tameBranchRingMap_base]
    congr 1
    have hU : tameBaseRingMap f g
        (↑((tameBaseUnit g P hP)⁻¹ ^ b) : TameBaseRing g) =
        (↑((tameBaseUnit (g.map f) (P.map f)
          (tameBaseRingMap_isUnit f g P hP))⁻¹ ^ b) : TameBaseRing (g.map f)) := by
      calc
        _ = ↑(Units.map (tameBaseRingMap f g).toMonoidHom
            ((tameBaseUnit g P hP)⁻¹ ^ b)) := by rw [Units.coe_map]; rfl
        _ = ↑((Units.map (tameBaseRingMap f g).toMonoidHom
            (tameBaseUnit g P hP))⁻¹ ^ b) := by simp
        _ = _ := by rw [tameBaseUnit_map]
    exact congrArg (algebraMap (TameBaseRing (g.map f))
      (TameBranchRing (g.map f) (P.map f) N a)) hU

/-- The singular-to-normalized punctured overlap is natural in the
coefficient ring. -/
theorem tameSingularOpenToBranchOpen_natural (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    (tameBranchOpenRingMap f g P N a).comp
        (tameSingularOpenToBranchOpen g P N r a b hP hbezout) =
      (tameSingularOpenToBranchOpen (g.map f) (P.map f) N r a b
        (tameBaseRingMap_isUnit f g P hP) hbezout).comp
        (tameSingularOpenRingMap f g P N r) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tameSingularX g P N r))
  apply RingHom.ext
  intro v
  change tameBranchOpenRingMap f g P N a
      (tameSingularOpenToBranchOpen g P N r a b hP hbezout
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) v)) =
    tameSingularOpenToBranchOpen (g.map f) (P.map f) N r a b
      (tameBaseRingMap_isUnit f g P hP) hbezout
      (tameSingularOpenRingMap f g P N r
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) v))
  rw [tameSingularOpenToBranchOpen_algebraMap,
    tameBranchOpenRingMap_algebraMap,
    tameSingularOpenRingMap_algebraMap,
    tameSingularOpenToBranchOpen_algebraMap]
  exact congrArg (algebraMap (TameBranchRing (g.map f) (P.map f) N a)
    (TameBranchOpen (g.map f) (P.map f) N a))
    (RingHom.congr_fun (tameSingularToBranch_natural f g P N r a b hP hbezout) v)

/-- Naturality of the inverse punctured overlap follows from the actual
inverse identities on both sides of coefficient change. -/
theorem tameBranchOpenToSingularOpen_natural (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameSingularOpenRingMap f g P N r).comp
        (tameBranchOpenToSingularOpen g P N r a b hP hN hbezout) =
      (tameBranchOpenToSingularOpen (g.map f) (P.map f) N r a b
        (tameBaseRingMap_isUnit f g P hP) hN hbezout).comp
        (tameBranchOpenRingMap f g P N a) := by
  let F := tameSingularOpenToBranchOpen g P N r a b hP hbezout
  let G := tameBranchOpenToSingularOpen g P N r a b hP hN hbezout
  let F' := tameSingularOpenToBranchOpen (g.map f) (P.map f) N r a b
    (tameBaseRingMap_isUnit f g P hP) hbezout
  let G' := tameBranchOpenToSingularOpen (g.map f) (P.map f) N r a b
    (tameBaseRingMap_isUnit f g P hP) hN hbezout
  have hFG : F.comp G = RingHom.id (TameBranchOpen g P N a) :=
    tameSingularOpenToBranchOpen_comp g P N r a b hP hN hbezout
  have hGF' : G'.comp F' = RingHom.id
      (TameSingularOpen (g.map f) (P.map f) N r) :=
    tameBranchOpenToSingularOpen_comp (g.map f) (P.map f) N r a b
      (tameBaseRingMap_isUnit f g P hP) hN hbezout
  have hF : (tameBranchOpenRingMap f g P N a).comp F =
      F'.comp (tameSingularOpenRingMap f g P N r) :=
    tameSingularOpenToBranchOpen_natural f g P N r a b hP hbezout
  apply RingHom.ext
  intro z
  change tameSingularOpenRingMap f g P N r (G z) =
    G' (tameBranchOpenRingMap f g P N a z)
  symm
  calc
    G' (tameBranchOpenRingMap f g P N a z) =
        G' (tameBranchOpenRingMap f g P N a (F (G z))) := by
          rw [show F (G z) = z from RingHom.congr_fun hFG z]
    _ = G' (F' (tameSingularOpenRingMap f g P N r (G z))) := by
          apply congrArg G'
          simpa only [RingHom.comp_apply] using RingHom.congr_fun hF (G z)
    _ = tameSingularOpenRingMap f g P N r (G z) :=
      RingHom.congr_fun hGF' _

/-- Coefficient change intertwines the original deck action on the singular
chart with the action of the mapped root of unity. -/
theorem tameSingularRingMap_deck (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameSingularRingMap f g P N r).comp
        (tameSingularDeckAlgebraAction g P N r ζ).toRingHom =
      (tameSingularDeckAlgebraAction (g.map f) (P.map f) N r
        (rootsOfUnity.mapHom N f ζ)).toRingHom.comp
        (tameSingularRingMap f g P N r) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change tameSingularRingMap f g P N r
        (tameSingularDeckAlgebraAction g P N r ζ
          (algebraMap (TameBaseRing g) (TameSingularRing g P N r) v)) =
      tameSingularDeckAlgebraAction (g.map f) (P.map f) N r
        (rootsOfUnity.mapHom N f ζ)
        (tameSingularRingMap f g P N r
          (algebraMap (TameBaseRing g) (TameSingularRing g P N r) v))
    rw [(tameSingularDeckAlgebraAction g P N r ζ).commutes,
      tameSingularRingMap_base, (tameSingularDeckAlgebraAction
        (g.map f) (P.map f) N r (rootsOfUnity.mapHom N f ζ)).commutes]
  · change tameSingularRingMap f g P N r
        (tameSingularDeckAlgebraAction g P N r ζ (tameSingularRoot g P N r)) =
      tameSingularDeckAlgebraAction (g.map f) (P.map f) N r
        (rootsOfUnity.mapHom N f ζ)
        (tameSingularRingMap f g P N r (tameSingularRoot g P N r))
    rw [tameSingularDeckAlgebraAction_root, tameSingularRingMap_root,
      tameSingularDeckAlgebraAction_root]
    simp only [Algebra.smul_def, map_mul, tameSingularRingMap_base,
      tameBaseRingMap_algebraMap, map_C]
    rw [tameSingularRingMap_root]
    rfl

/-- The normalized root retains its original deck weight after arbitrary
coefficient change. -/
theorem tameBranchRingMap_deck (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameBranchRingMap f g P N a).comp
        (tameBranchDeckAlgebraAction g P N a ζ).toRingHom =
      (tameBranchDeckAlgebraAction (g.map f) (P.map f) N a
        (rootsOfUnity.mapHom N f ζ)).toRingHom.comp
        (tameBranchRingMap f g P N a) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro v
    change tameBranchRingMap f g P N a
        (tameBranchDeckAlgebraAction g P N a ζ
          (algebraMap (TameBaseRing g) (TameBranchRing g P N a) v)) =
      tameBranchDeckAlgebraAction (g.map f) (P.map f) N a
        (rootsOfUnity.mapHom N f ζ)
        (tameBranchRingMap f g P N a
          (algebraMap (TameBaseRing g) (TameBranchRing g P N a) v))
    rw [(tameBranchDeckAlgebraAction g P N a ζ).commutes,
      tameBranchRingMap_base, (tameBranchDeckAlgebraAction
        (g.map f) (P.map f) N a (rootsOfUnity.mapHom N f ζ)).commutes]
  · change tameBranchRingMap f g P N a
        (tameBranchDeckAlgebraAction g P N a ζ (tameBranchRoot g P N a)) =
      tameBranchDeckAlgebraAction (g.map f) (P.map f) N a
        (rootsOfUnity.mapHom N f ζ)
        (tameBranchRingMap f g P N a (tameBranchRoot g P N a))
    rw [tameBranchDeckAlgebraAction_root, tameBranchRingMap_root,
      tameBranchDeckAlgebraAction_root]
    simp only [Algebra.smul_def, map_mul, tameBranchRingMap_base,
      tameBaseRingMap_algebraMap, map_C]
    rw [tameBranchRingMap_root]
    simp

/-- Coefficient change commutes with the original deck action on the
punctured singular chart. -/
theorem tameSingularOpenRingMap_deck (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameSingularOpenRingMap f g P N r).comp
        (tameSingularOpenDeck g P N r ζ) =
      (tameSingularOpenDeck (g.map f) (P.map f) N r
        (rootsOfUnity.mapHom N f ζ)).comp
        (tameSingularOpenRingMap f g P N r) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tameSingularX g P N r))
  apply RingHom.ext
  intro v
  simp only [RingHom.comp_apply, tameSingularOpenDeck_algebraMap,
    tameSingularOpenRingMap_algebraMap]
  exact congrArg (algebraMap (TameSingularRing (g.map f) (P.map f) N r)
    (TameSingularOpen (g.map f) (P.map f) N r))
    (RingHom.congr_fun (tameSingularRingMap_deck f g P N r ζ) v)

/-- Coefficient change commutes with the reindexed original deck action on
the punctured normalized chart. -/
theorem tameBranchOpenRingMap_deck (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameBranchOpenRingMap f g P N a).comp
        (tameBranchOpenDeck g P N a ζ) =
      (tameBranchOpenDeck (g.map f) (P.map f) N a
        (rootsOfUnity.mapHom N f ζ)).comp
        (tameBranchOpenRingMap f g P N a) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (tameBranchX g P N a))
  apply RingHom.ext
  intro v
  simp only [RingHom.comp_apply, tameBranchOpenDeck_algebraMap,
    tameBranchOpenRingMap_algebraMap]
  exact congrArg (algebraMap (TameBranchRing (g.map f) (P.map f) N a)
    (TameBranchOpen (g.map f) (P.map f) N a))
    (RingHom.congr_fun (tameBranchRingMap_deck f g P N a ζ) v)

section TensorBaseChange

variable [Algebra C C']

/-- Coefficient change on the polynomial coordinate algebra. -/
def tamePolynomialMapAlgHom : C[X] →ₐ[C] C'[X] where
  toRingHom := Polynomial.mapRingHom (algebraMap C C')
  commutes' c := by simp

/-- The forward polynomial coefficient-extension map. -/
def tamePolynomialTensorMap : C' ⊗[C] C[X] →ₐ[C'] C'[X] :=
  Algebra.TensorProduct.lift (Algebra.ofId C' _)
    (tamePolynomialMapAlgHom (C := C) (C' := C')) (fun _ _ => Commute.all _ _)

/-- The inverse map evaluates the polynomial at the retained tensor coordinate. -/
def tamePolynomialTensorInverse : C'[X] →ₐ[C'] C' ⊗[C] C[X] :=
  Polynomial.aeval ((Algebra.TensorProduct.includeRight :
    C[X] →ₐ[C] C' ⊗[C] C[X]) X)

theorem tamePolynomialTensorMap_tmul (c : C') (p : C[X]) :
    tamePolynomialTensorMap (C := C) (C' := C') (c ⊗ₜ[C] p) =
      Polynomial.C c * p.map (algebraMap C C') := by
  simp [tamePolynomialTensorMap, Algebra.TensorProduct.lift_tmul,
    tamePolynomialMapAlgHom]

theorem tamePolynomialTensorMap_comp_inverse :
    (tamePolynomialTensorMap (C := C) (C' := C')).comp
      (tamePolynomialTensorInverse (C := C) (C' := C')) =
        AlgHom.id C' C'[X] := by
  apply Polynomial.algHom_ext
  simp [tamePolynomialTensorInverse, tamePolynomialTensorMap_tmul]

theorem tamePolynomialTensorInverse_map (p : C[X]) :
    tamePolynomialTensorInverse (C := C) (C' := C')
      (p.map (algebraMap C C')) =
      (Algebra.TensorProduct.includeRight :
        C[X] →ₐ[C] C' ⊗[C] C[X]) p := by
  have h : (tamePolynomialTensorInverse (C := C) (C' := C')).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap C C')) =
      (Algebra.TensorProduct.includeRight :
        C[X] →ₐ[C] C' ⊗[C] C[X]).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [tamePolynomialTensorInverse, Algebra.TensorProduct.includeRight_apply]
      simpa only [Polynomial.C_eq_algebraMap, Algebra.smul_def, mul_one] using
        (TensorProduct.smul_tmul (R := C) c (1 : C') (1 : C[X]))
    · simp [tamePolynomialTensorInverse, Algebra.TensorProduct.includeRight_apply]
  exact congrArg (fun k : C[X] →+* C' ⊗[C] C[X] => k p) h

theorem tamePolynomialTensorInverse_comp_map :
    (tamePolynomialTensorInverse (C := C) (C' := C')).comp
      (tamePolynomialTensorMap (C := C) (C' := C')) =
        AlgHom.id C' (C' ⊗[C] C[X]) := by
  apply Algebra.TensorProduct.ext'
  intro c p
  simp [tamePolynomialTensorMap_tmul, tamePolynomialTensorInverse_map,
    Polynomial.C_eq_algebraMap, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Polynomial coordinate algebras commute with arbitrary coefficient extension. -/
def tamePolynomialBaseChangeEquiv : (C' ⊗[C] C[X]) ≃ₐ[C'] C'[X] :=
  AlgEquiv.ofAlgHom
    (tamePolynomialTensorMap (C := C) (C' := C'))
    (tamePolynomialTensorInverse (C := C) (C' := C'))
    (tamePolynomialTensorMap_comp_inverse (C := C) (C' := C'))
    (tamePolynomialTensorInverse_comp_map (C := C) (C' := C'))

/-- The universal coefficient map on a localized Kummer root algebra, viewed
as a homomorphism over the original coefficient ring. -/
def localizedKummerRingMapAlgHom (g Q : C[X]) (n : ℕ) :
    RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
      RingTheory.Smooth.localizedKummerAlgebra
        (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n where
  toRingHom := localizedKummerRingMap (algebraMap C C') g Q n
  commutes' c := localizedKummerRingMap_coeff (algebraMap C C') g Q n c

/-- The canonical map from the scalar extension of a localized Kummer algebra
to its coefficientwise presentation. -/
def localizedKummerTensorMap (g Q : C[X]) (n : ℕ) :
    (C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) →ₐ[C']
      RingTheory.Smooth.localizedKummerAlgebra
        (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n :=
  Algebra.TensorProduct.lift
    (Algebra.ofId C' _)
    (localizedKummerRingMapAlgHom (C' := C') g Q n)
    (fun _ _ => Commute.all _ _)

/-- Coordinates of the new polynomial ring in the tensor algebra. -/
def localizedKummerTensorPolynomialMap (g Q : C[X]) (n : ℕ) :
    C'[X] →+* (C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) :=
  Polynomial.eval₂RingHom
    (algebraMap C' (C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n))
    ((Algebra.TensorProduct.includeRight :
      RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
        C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
      (algebraMap C[X] (RingTheory.Smooth.localizedKummerAlgebra g Q n) X))

/-- A polynomial from the old coefficient ring has the same coordinates after
scalar extension. -/
theorem localizedKummerTensorPolynomialMap_map (g Q : C[X]) (n : ℕ)
    (p : C[X]) :
    localizedKummerTensorPolynomialMap (C' := C') g Q n
        (p.map (algebraMap C C')) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (algebraMap C[X] (RingTheory.Smooth.localizedKummerAlgebra g Q n) p) := by
  have h : (localizedKummerTensorPolynomialMap (C' := C') g Q n).comp
      (Polynomial.mapRingHom (algebraMap C C')) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n).toRingHom.comp
        (algebraMap C[X] (RingTheory.Smooth.localizedKummerAlgebra g Q n)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [localizedKummerTensorPolynomialMap, Polynomial.eval₂RingHom,
        Algebra.TensorProduct.includeRight_apply]
      rw [show (algebraMap C[X] (RingTheory.Smooth.localizedKummerAlgebra g Q n))
        (Polynomial.C c) =
        algebraMap C (RingTheory.Smooth.localizedKummerAlgebra g Q n) c from
        IsScalarTower.algebraMap_apply C C[X]
          (RingTheory.Smooth.localizedKummerAlgebra g Q n) c]
      simpa only [Algebra.smul_def, mul_one] using
        (TensorProduct.smul_tmul (R := C) c (1 : C')
          (1 : RingTheory.Smooth.localizedKummerAlgebra g Q n))
    · simp [localizedKummerTensorPolynomialMap, Polynomial.eval₂RingHom]
  exact congrArg (fun k : C[X] →+*
    C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n => k p) h

/-- The element inverted in the new localized base is already a unit in the
scalar-extended old root algebra. -/
theorem isUnit_localizedKummerTensor_g (g Q : C[X]) (n : ℕ) :
    IsUnit (localizedKummerTensorPolynomialMap (C' := C') g Q n
      (g.map (algebraMap C C'))) := by
  rw [localizedKummerTensorPolynomialMap_map]
  have hu : IsUnit
      (algebraMap C[X] (RingTheory.Smooth.localizedKummerAlgebra g Q n) g) := by
    have h := (IsLocalization.Away.algebraMap_isUnit g :
      IsUnit (algebraMap C[X] (TameBaseRing g) g))
    simpa [IsScalarTower.algebraMap_apply C[X] (TameBaseRing g)
      (RingTheory.Smooth.localizedKummerAlgebra g Q n)] using
      h.map (algebraMap (TameBaseRing g)
        (RingTheory.Smooth.localizedKummerAlgebra g Q n))
  exact hu.map (Algebra.TensorProduct.includeRight :
    RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
      C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n).toRingHom

/-- The localized new base maps back to the tensor algebra. -/
def localizedKummerTensorBaseMap (g Q : C[X]) (n : ℕ) :
    TameBaseRing (g.map (algebraMap C C')) →+*
      C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n :=
  Localization.awayLift
    (localizedKummerTensorPolynomialMap (C' := C') g Q n)
    (g.map (algebraMap C C'))
    (isUnit_localizedKummerTensor_g (C' := C') g Q n)

/-- The tensor base map has the specified polynomial coordinates. -/
theorem localizedKummerTensorBaseMap_algebraMap (g Q : C[X]) (n : ℕ)
    (p : C'[X]) :
    localizedKummerTensorBaseMap (C' := C') g Q n
        (algebraMap C'[X] (TameBaseRing (g.map (algebraMap C C'))) p) =
      localizedKummerTensorPolynomialMap (C' := C') g Q n p := by
  unfold localizedKummerTensorBaseMap
  exact IsLocalization.Away.lift_eq (g.map (algebraMap C C')) _ p

/-- The tensor base map undoes coefficient change on the old localized base. -/
theorem localizedKummerTensorBaseMap_tameBaseRingMap (g Q : C[X]) (n : ℕ)
    (a : TameBaseRing g) :
    localizedKummerTensorBaseMap (C' := C') g Q n
        (tameBaseRingMap (algebraMap C C') g a) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (algebraMap (TameBaseRing g)
          (RingTheory.Smooth.localizedKummerAlgebra g Q n) a) := by
  have h : (localizedKummerTensorBaseMap (C' := C') g Q n).comp
      (tameBaseRingMap (algebraMap C C') g) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n).toRingHom.comp
        (algebraMap (TameBaseRing g)
          (RingTheory.Smooth.localizedKummerAlgebra g Q n)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro p
    change localizedKummerTensorBaseMap (C' := C') g Q n
        (tameBaseRingMap (algebraMap C C') g
          (algebraMap C[X] (TameBaseRing g) p)) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (algebraMap (TameBaseRing g)
          (RingTheory.Smooth.localizedKummerAlgebra g Q n)
          (algebraMap C[X] (TameBaseRing g) p))
    rw [tameBaseRingMap_algebraMap, localizedKummerTensorBaseMap_algebraMap,
      localizedKummerTensorPolynomialMap_map]
    congr 1
  exact congrArg (fun k : TameBaseRing g →+*
    C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n => k a) h

/-- The inverse localized-base map respects the new coefficient algebra. -/
def localizedKummerTensorBaseAlgHom (g Q : C[X]) (n : ℕ) :
    TameBaseRing (g.map (algebraMap C C')) →ₐ[C']
      C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n where
  toRingHom := localizedKummerTensorBaseMap (C' := C') g Q n
  commutes' c := by
    change localizedKummerTensorBaseMap (C' := C') g Q n
      (algebraMap C'[X] (TameBaseRing (g.map (algebraMap C C')))
        (Polynomial.C c)) =
        algebraMap C' (C' ⊗[C]
          RingTheory.Smooth.localizedKummerAlgebra g Q n) c
    rw [localizedKummerTensorBaseMap_algebraMap]
    simp [localizedKummerTensorPolynomialMap, Polynomial.eval₂RingHom]

/-- The old root in the tensor algebra satisfies the new Kummer equation. -/
theorem localizedKummerTensorRoot_pow (g Q : C[X]) (n : ℕ) :
    ((Algebra.TensorProduct.includeRight :
      RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
        C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (RingTheory.Smooth.localizedKummerZ g Q n)) ^ n =
      localizedKummerTensorBaseMap (C' := C') g Q n
        (algebraMap C'[X] (TameBaseRing (g.map (algebraMap C C')))
          (Q.map (algebraMap C C'))) := by
  rw [localizedKummerTensorBaseMap_algebraMap,
    localizedKummerTensorPolynomialMap_map, ← map_pow]
  rw [show (RingTheory.Smooth.localizedKummerZ g Q n) ^ n =
      algebraMap (TameBaseRing g)
        (RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (algebraMap C[X] (TameBaseRing g) Q) from
      AdjoinRoot.root_X_pow_sub_C_pow n _]
  rw [← IsScalarTower.algebraMap_apply C[X] (TameBaseRing g)
    (RingTheory.Smooth.localizedKummerAlgebra g Q n)]

/-- The universal inverse sends the new Kummer root to the old root in the
scalar-extended algebra. -/
def localizedKummerTensorInverse (g Q : C[X]) (n : ℕ) :
    RingTheory.Smooth.localizedKummerAlgebra
      (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n →ₐ[C']
      C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n :=
  AdjoinRoot.liftAlgHom
    (RingTheory.Smooth.localizedKummerEquation
      (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)
    (localizedKummerTensorBaseAlgHom (C' := C') g Q n)
    ((Algebra.TensorProduct.includeRight :
      RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
        C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (RingTheory.Smooth.localizedKummerZ g Q n))
    (by
      simp only [RingTheory.Smooth.localizedKummerEquation, eval₂_sub,
        eval₂_pow, eval₂_X, eval₂_C]
      exact sub_eq_zero.mpr (localizedKummerTensorRoot_pow (C' := C') g Q n))

/-- The tensor inverse sends the new root to the old scalar-extended root. -/
@[simp] theorem localizedKummerTensorInverse_root (g Q : C[X]) (n : ℕ) :
    localizedKummerTensorInverse (C' := C') g Q n
      (RingTheory.Smooth.localizedKummerZ
        (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
        (RingTheory.Smooth.localizedKummerZ g Q n) := by
  simp [localizedKummerTensorInverse, RingTheory.Smooth.localizedKummerZ,
    AdjoinRoot.liftAlgHom_root]

/-- The inverse agrees with the constructed map on the new localized base. -/
theorem localizedKummerTensorInverse_base (g Q : C[X]) (n : ℕ)
    (a : TameBaseRing (g.map (algebraMap C C'))) :
    localizedKummerTensorInverse (C' := C') g Q n
      (algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) a) =
      localizedKummerTensorBaseMap (C' := C') g Q n a := by
  simp [localizedKummerTensorInverse, AdjoinRoot.liftAlgHom,
    localizedKummerTensorBaseAlgHom]

/-- Pulling back the old Kummer algebra by the inverse recovers its canonical
inclusion in the tensor algebra. -/
theorem localizedKummerTensorInverse_ringMap (g Q : C[X]) (n : ℕ)
    (a : RingTheory.Smooth.localizedKummerAlgebra g Q n) :
    localizedKummerTensorInverse (C' := C') g Q n
      (localizedKummerRingMap (algebraMap C C') g Q n a) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) a := by
  have h : (localizedKummerTensorInverse (C' := C') g Q n).toRingHom.comp
      (localizedKummerRingMap (algebraMap C C') g Q n) =
      (Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro b
      change localizedKummerTensorInverse (C' := C') g Q n
        (localizedKummerRingMap (algebraMap C C') g Q n
          (algebraMap (TameBaseRing g)
            (RingTheory.Smooth.localizedKummerAlgebra g Q n) b)) = _
      rw [localizedKummerRingMap_base, localizedKummerTensorInverse_base,
        localizedKummerTensorBaseMap_tameBaseRingMap]
      rfl
    · change localizedKummerTensorInverse (C' := C') g Q n
        (localizedKummerRingMap (algebraMap C C') g Q n
          (RingTheory.Smooth.localizedKummerZ g Q n)) = _
      rw [localizedKummerRingMap_root, localizedKummerTensorInverse_root]
      rfl
  exact congrArg (fun k : RingTheory.Smooth.localizedKummerAlgebra g Q n →+*
    C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n => k a) h

/-- The inverse is left inverse on every pure tensor. -/
theorem localizedKummerTensorInverse_comp_map (g Q : C[X]) (n : ℕ) :
    (localizedKummerTensorInverse (C' := C') g Q n).comp
        (localizedKummerTensorMap (C' := C') g Q n) =
      AlgHom.id C' (C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp [localizedKummerTensorMap, Algebra.TensorProduct.lift_tmul]
  change (c ⊗ₜ[C] (1 : RingTheory.Smooth.localizedKummerAlgebra g Q n)) *
    localizedKummerTensorInverse (C' := C') g Q n
      (localizedKummerRingMap (algebraMap C C') g Q n a) = c ⊗ₜ[C] a
  rw [localizedKummerTensorInverse_ringMap]
  simp [Algebra.TensorProduct.includeRight_apply]

/-- The tensor map restricts to coefficient change on the old root algebra. -/
theorem localizedKummerTensorMap_includeRight (g Q : C[X]) (n : ℕ)
    (a : RingTheory.Smooth.localizedKummerAlgebra g Q n) :
    localizedKummerTensorMap (C' := C') g Q n
      ((Algebra.TensorProduct.includeRight :
        RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
          C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) a) =
      localizedKummerRingMap (algebraMap C C') g Q n a := by
  simp [Algebra.TensorProduct.includeRight_apply, localizedKummerTensorMap,
    Algebra.TensorProduct.lift_tmul, localizedKummerRingMapAlgHom]
  rfl

/-- The tensor map evaluates the new polynomial coordinates correctly. -/
theorem localizedKummerTensorMap_polynomial (g Q : C[X]) (n : ℕ)
    (p : C'[X]) :
    localizedKummerTensorMap (C' := C') g Q n
      (localizedKummerTensorPolynomialMap (C' := C') g Q n p) =
      algebraMap C'[X]
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) p := by
  have h : (localizedKummerTensorMap (C' := C') g Q n).toRingHom.comp
      (localizedKummerTensorPolynomialMap (C' := C') g Q n) =
      algebraMap C'[X]
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [localizedKummerTensorPolynomialMap, Polynomial.eval₂RingHom]
      simpa [IsScalarTower.algebraMap_apply C' C'[X]
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)] using
        (show localizedKummerTensorMap (C' := C') g Q n
          (c ⊗ₜ[C] (1 : RingTheory.Smooth.localizedKummerAlgebra g Q n)) =
          algebraMap C'
            (RingTheory.Smooth.localizedKummerAlgebra
              (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) c from by
            simp [localizedKummerTensorMap, Algebra.TensorProduct.lift_tmul])
    · simp [localizedKummerTensorPolynomialMap, Polynomial.eval₂RingHom]
      change localizedKummerTensorMap (C' := C') g Q n
        ((Algebra.TensorProduct.includeRight :
          RingTheory.Smooth.localizedKummerAlgebra g Q n →ₐ[C]
            C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n)
          (algebraMap C[X]
            (RingTheory.Smooth.localizedKummerAlgebra g Q n) X)) =
        algebraMap C'[X]
          (RingTheory.Smooth.localizedKummerAlgebra
            (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) X
      rw [localizedKummerTensorMap_includeRight]
      calc
        localizedKummerRingMap (algebraMap C C') g Q n
            (algebraMap C[X]
              (RingTheory.Smooth.localizedKummerAlgebra g Q n) X) =
          localizedKummerRingMap (algebraMap C C') g Q n
            (algebraMap (TameBaseRing g)
              (RingTheory.Smooth.localizedKummerAlgebra g Q n)
              (algebraMap C[X] (TameBaseRing g) X)) := by
                rw [IsScalarTower.algebraMap_apply C[X] (TameBaseRing g)
                  (RingTheory.Smooth.localizedKummerAlgebra g Q n)]
        _ = algebraMap (TameBaseRing (g.map (algebraMap C C')))
            (RingTheory.Smooth.localizedKummerAlgebra
              (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)
            (algebraMap C'[X] (TameBaseRing (g.map (algebraMap C C'))) X) := by
              rw [localizedKummerRingMap_base, tameBaseRingMap_algebraMap,
                map_X]
        _ = algebraMap C'[X]
            (RingTheory.Smooth.localizedKummerAlgebra
              (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) X := by
              rw [IsScalarTower.algebraMap_apply C'[X]
                (TameBaseRing (g.map (algebraMap C C')))
                (RingTheory.Smooth.localizedKummerAlgebra
                  (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)]
  exact congrArg (fun k : C'[X] →+*
    RingTheory.Smooth.localizedKummerAlgebra
      (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n => k p) h

/-- The tensor map is inverse on the new localized base. -/
theorem localizedKummerTensorMap_base (g Q : C[X]) (n : ℕ)
    (a : TameBaseRing (g.map (algebraMap C C'))) :
    localizedKummerTensorMap (C' := C') g Q n
      (localizedKummerTensorBaseMap (C' := C') g Q n a) =
      algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) a := by
  have h : (localizedKummerTensorMap (C' := C') g Q n).toRingHom.comp
      (localizedKummerTensorBaseMap (C' := C') g Q n) =
      algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (g.map (algebraMap C C')))
    apply RingHom.ext
    intro p
    change localizedKummerTensorMap (C' := C') g Q n
      (localizedKummerTensorBaseMap (C' := C') g Q n
        (algebraMap C'[X] (TameBaseRing (g.map (algebraMap C C'))) p)) = _
    rw [localizedKummerTensorBaseMap_algebraMap,
      localizedKummerTensorMap_polynomial]
    rfl
  exact congrArg (fun k : TameBaseRing (g.map (algebraMap C C')) →+*
    RingTheory.Smooth.localizedKummerAlgebra
      (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n => k a) h

/-- The tensor map is inverse on the new root algebra. -/
theorem localizedKummerTensorMap_comp_inverse (g Q : C[X]) (n : ℕ) :
    (localizedKummerTensorMap (C' := C') g Q n).comp
        (localizedKummerTensorInverse (C' := C') g Q n) =
      AlgHom.id C'
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) := by
  have h : ((localizedKummerTensorMap (C' := C') g Q n).comp
        (localizedKummerTensorInverse (C' := C') g Q n)).toRingHom =
      (AlgHom.id C'
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change localizedKummerTensorMap (C' := C') g Q n
        (localizedKummerTensorInverse (C' := C') g Q n
          (algebraMap (TameBaseRing (g.map (algebraMap C C')))
            (RingTheory.Smooth.localizedKummerAlgebra
              (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) a)) = _
      rw [localizedKummerTensorInverse_base, localizedKummerTensorMap_base]
      rfl
    · change localizedKummerTensorMap (C' := C') g Q n
        (localizedKummerTensorInverse (C' := C') g Q n
          (RingTheory.Smooth.localizedKummerZ
            (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)) = _
      rw [localizedKummerTensorInverse_root,
        localizedKummerTensorMap_includeRight, localizedKummerRingMap_root]
      rfl
  apply AlgHom.ext
  intro a
  exact congrArg (fun k : RingTheory.Smooth.localizedKummerAlgebra
    (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n →+*
    RingTheory.Smooth.localizedKummerAlgebra
      (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n => k a) h

/-- Arbitrary coefficient extension preserves a localized Kummer presentation,
without flatness or injectivity. -/
def localizedKummerBaseChangeEquiv (g Q : C[X]) (n : ℕ) :
    (C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) ≃ₐ[C']
      RingTheory.Smooth.localizedKummerAlgebra
        (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n :=
  AlgEquiv.ofAlgHom
    (localizedKummerTensorMap (C' := C') g Q n)
    (localizedKummerTensorInverse (C' := C') g Q n)
    (localizedKummerTensorMap_comp_inverse (C' := C') g Q n)
    (localizedKummerTensorInverse_comp_map (C' := C') g Q n)

/-- On pure tensors, coefficient extension evaluates the left scalar and maps
the right algebra element by its canonical presentation map. -/
theorem localizedKummerBaseChangeEquiv_tmul (g Q : C[X]) (n : ℕ)
    (c : C') (a : RingTheory.Smooth.localizedKummerAlgebra g Q n) :
    localizedKummerBaseChangeEquiv (C' := C') g Q n (c ⊗ₜ[C] a) =
      algebraMap C' (RingTheory.Smooth.localizedKummerAlgebra
        (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n) c *
        localizedKummerRingMap (algebraMap C C') g Q n a := by
  simp [localizedKummerBaseChangeEquiv, localizedKummerTensorMap,
    Algebra.TensorProduct.lift_tmul, localizedKummerRingMapAlgHom]
  rfl

/-- The original Kummer root becomes precisely the root in the new
presentation after arbitrary coefficient extension. -/
@[simp] theorem localizedKummerBaseChangeEquiv_root (g Q : C[X]) (n : ℕ) :
    localizedKummerBaseChangeEquiv (C' := C') g Q n
      (1 ⊗ₜ[C] RingTheory.Smooth.localizedKummerZ g Q n) =
      RingTheory.Smooth.localizedKummerZ
        (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n := by
  rw [localizedKummerBaseChangeEquiv_tmul]
  simp

/-- The old localized polynomial base is mapped coefficientwise. -/
theorem localizedKummerBaseChangeEquiv_base (g Q : C[X]) (n : ℕ)
    (a : TameBaseRing g) :
    localizedKummerBaseChangeEquiv (C' := C') g Q n
      (1 ⊗ₜ[C] algebraMap (TameBaseRing g)
        (RingTheory.Smooth.localizedKummerAlgebra g Q n) a) =
      algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) (Q.map (algebraMap C C')) n)
          (tameBaseRingMap (algebraMap C C') g a) := by
  rw [localizedKummerBaseChangeEquiv_tmul]
  simp only [map_one, one_mul]
  exact localizedKummerRingMap_base (algebraMap C C') g Q n a

/-- Transport the generic coefficient equivalence along a polynomial identity. -/
def localizedKummerBaseChangeEquivOfEq (g Q : C[X]) (n : ℕ)
    (Q' : C'[X]) (hQ : Q.map (algebraMap C C') = Q') :
    (C' ⊗[C] RingTheory.Smooth.localizedKummerAlgebra g Q n) ≃ₐ[C']
      RingTheory.Smooth.localizedKummerAlgebra (g.map (algebraMap C C')) Q' n := by
  subst Q'
  exact localizedKummerBaseChangeEquiv (C' := C') g Q n

/-- The transported presentation still has the canonical pure-tensor formula. -/
theorem localizedKummerBaseChangeEquivOfEq_tmul (g Q : C[X]) (n : ℕ)
    (Q' : C'[X]) (hQ : Q.map (algebraMap C C') = Q')
    (c : C') (a : RingTheory.Smooth.localizedKummerAlgebra g Q n) :
    localizedKummerBaseChangeEquivOfEq (C' := C') g Q n Q' hQ
        (c ⊗ₜ[C] a) =
      algebraMap C' (RingTheory.Smooth.localizedKummerAlgebra
        (g.map (algebraMap C C')) Q' n) c *
        (hQ ▸ localizedKummerRingMap (algebraMap C C') g Q n a) := by
  subst Q'
  exact localizedKummerBaseChangeEquiv_tmul (C' := C') g Q n c a

/-- Transporting the polynomial presentation preserves its named root. -/
@[simp] theorem localizedKummerBaseChangeEquivOfEq_root (g Q : C[X]) (n : ℕ)
    (Q' : C'[X]) (hQ : Q.map (algebraMap C C') = Q') :
    localizedKummerBaseChangeEquivOfEq (C' := C') g Q n Q' hQ
      (1 ⊗ₜ[C] RingTheory.Smooth.localizedKummerZ g Q n) =
      RingTheory.Smooth.localizedKummerZ (g.map (algebraMap C C')) Q' n := by
  subst Q'
  exact localizedKummerBaseChangeEquiv_root (C' := C') g Q n

/-- The transported equivalence respects the coefficient-localized base. -/
theorem localizedKummerBaseChangeEquivOfEq_base (g Q : C[X]) (n : ℕ)
    (Q' : C'[X]) (hQ : Q.map (algebraMap C C') = Q') (a : TameBaseRing g) :
    localizedKummerBaseChangeEquivOfEq (C' := C') g Q n Q' hQ
      (1 ⊗ₜ[C] algebraMap (TameBaseRing g)
        (RingTheory.Smooth.localizedKummerAlgebra g Q n) a) =
      algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (RingTheory.Smooth.localizedKummerAlgebra
          (g.map (algebraMap C C')) Q' n)
          (tameBaseRingMap (algebraMap C C') g a) := by
  subst Q'
  exact localizedKummerBaseChangeEquiv_base (C' := C') g Q n a

/-- The normalized relative tame chart commutes with arbitrary coefficient
change. No flatness hypothesis is used. -/
def tameBranchBaseChangeEquiv (g P : C[X]) (N a : ℕ) :
    (C' ⊗[C] TameBranchRing g P N a) ≃ₐ[C']
      TameBranchRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a := by
  exact localizedKummerBaseChangeEquivOfEq (C' := C') g
    (tameBranchRadicand P a) N
    (tameBranchRadicand (P.map (algebraMap C C')) a)
    (tameBranchRadicand_map (algebraMap C C') P a)

/-- The singular relative tame chart commutes with arbitrary coefficient
change. -/
def tameSingularBaseChangeEquiv (g P : C[X]) (N r : ℕ) :
    (C' ⊗[C] TameSingularRing g P N r) ≃ₐ[C']
      TameSingularRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r := by
  exact localizedKummerBaseChangeEquivOfEq (C' := C') g
    (tameSingularRadicand P r) N
    (tameSingularRadicand (P.map (algebraMap C C')) r)
    (tameSingularRadicand_map (algebraMap C C') P r)

/-- A pure tensor in the normalized chart evaluates by coefficient change. -/
theorem tameBranchBaseChangeEquiv_tmul (g P : C[X]) (N a : ℕ)
    (c : C') (v : TameBranchRing g P N a) :
    tameBranchBaseChangeEquiv (C' := C') g P N a (c ⊗ₜ[C] v) =
      algebraMap C' (TameBranchRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a) c *
        tameBranchRingMap (algebraMap C C') g P N a v := by
  unfold tameBranchBaseChangeEquiv
  rw [localizedKummerBaseChangeEquivOfEq_tmul]
  congr 1
  exact localizedKummerRingMap_transport (algebraMap C C') g
    (tameBranchRadicand P a) N
    (tameBranchRadicand (P.map (algebraMap C C')) a)
    (tameBranchRadicand_map (algebraMap C C') P a)
    (tameBranchEquation_dvd_map (algebraMap C C') g P N a) v

/-- A pure tensor in the original singular chart evaluates by coefficient change. -/
theorem tameSingularBaseChangeEquiv_tmul (g P : C[X]) (N r : ℕ)
    (c : C') (v : TameSingularRing g P N r) :
    tameSingularBaseChangeEquiv (C' := C') g P N r (c ⊗ₜ[C] v) =
      algebraMap C' (TameSingularRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r) c *
        tameSingularRingMap (algebraMap C C') g P N r v := by
  unfold tameSingularBaseChangeEquiv
  rw [localizedKummerBaseChangeEquivOfEq_tmul]
  congr 1
  exact localizedKummerRingMap_transport (algebraMap C C') g
    (tameSingularRadicand P r) N
    (tameSingularRadicand (P.map (algebraMap C C')) r)
    (tameSingularRadicand_map (algebraMap C C') P r)
    (tameSingularEquation_dvd_map (algebraMap C C') g P N r) v

/-- Coefficient extension preserves the named normalized root. -/
@[simp] theorem tameBranchBaseChangeEquiv_root (g P : C[X]) (N a : ℕ) :
    tameBranchBaseChangeEquiv (C' := C') g P N a
      (1 ⊗ₜ[C] tameBranchRoot g P N a) =
      tameBranchRoot (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a := by
  exact localizedKummerBaseChangeEquivOfEq_root (C' := C') g
    (tameBranchRadicand P a) N
    (tameBranchRadicand (P.map (algebraMap C C')) a)
    (tameBranchRadicand_map (algebraMap C C') P a)

/-- Coefficient extension preserves the named singular root. -/
@[simp] theorem tameSingularBaseChangeEquiv_root (g P : C[X]) (N r : ℕ) :
    tameSingularBaseChangeEquiv (C' := C') g P N r
      (1 ⊗ₜ[C] tameSingularRoot g P N r) =
      tameSingularRoot (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r := by
  exact localizedKummerBaseChangeEquivOfEq_root (C' := C') g
    (tameSingularRadicand P r) N
    (tameSingularRadicand (P.map (algebraMap C C')) r)
    (tameSingularRadicand_map (algebraMap C C') P r)

/-- The normalized equivalence respects the localized base coordinates. -/
theorem tameBranchBaseChangeEquiv_base (g P : C[X]) (N a : ℕ)
    (v : TameBaseRing g) :
    tameBranchBaseChangeEquiv (C' := C') g P N a
      (1 ⊗ₜ[C] algebraMap (TameBaseRing g) (TameBranchRing g P N a) v) =
      algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (TameBranchRing (g.map (algebraMap C C'))
          (P.map (algebraMap C C')) N a)
        (tameBaseRingMap (algebraMap C C') g v) := by
  exact localizedKummerBaseChangeEquivOfEq_base (C' := C') g
    (tameBranchRadicand P a) N
    (tameBranchRadicand (P.map (algebraMap C C')) a)
    (tameBranchRadicand_map (algebraMap C C') P a) v

/-- The singular equivalence respects the localized base coordinates. -/
theorem tameSingularBaseChangeEquiv_base (g P : C[X]) (N r : ℕ)
    (v : TameBaseRing g) :
    tameSingularBaseChangeEquiv (C' := C') g P N r
      (1 ⊗ₜ[C] algebraMap (TameBaseRing g) (TameSingularRing g P N r) v) =
      algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (TameSingularRing (g.map (algebraMap C C'))
          (P.map (algebraMap C C')) N r)
        (tameBaseRingMap (algebraMap C C') g v) := by
  exact localizedKummerBaseChangeEquivOfEq_base (C' := C') g
    (tameSingularRadicand P r) N
    (tameSingularRadicand (P.map (algebraMap C C')) r)
    (tameSingularRadicand_map (algebraMap C C') P r) v

/-- Scalar extension fixes the affine-line coordinate of the normalized chart. -/
@[simp] theorem tameBranchBaseChangeEquiv_x (g P : C[X]) (N a : ℕ) :
    tameBranchBaseChangeEquiv (C' := C') g P N a
      (1 ⊗ₜ[C] tameBranchX g P N a) =
      tameBranchX (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a := by
  change tameBranchBaseChangeEquiv (C' := C') g P N a
      (1 ⊗ₜ[C] algebraMap (TameBaseRing g) (TameBranchRing g P N a)
        (tameBaseX g)) =
    algebraMap (TameBaseRing (g.map (algebraMap C C')))
      (TameBranchRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a)
      (tameBaseX (g.map (algebraMap C C')))
  rw [tameBranchBaseChangeEquiv_base, tameBaseRingMap_x]

/-- Scalar extension fixes the affine-line coordinate of the singular chart. -/
@[simp] theorem tameSingularBaseChangeEquiv_x (g P : C[X]) (N r : ℕ) :
    tameSingularBaseChangeEquiv (C' := C') g P N r
      (1 ⊗ₜ[C] tameSingularX g P N r) =
      tameSingularX (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r := by
  change tameSingularBaseChangeEquiv (C' := C') g P N r
      (1 ⊗ₜ[C] algebraMap (TameBaseRing g) (TameSingularRing g P N r)
        (tameBaseX g)) =
    algebraMap (TameBaseRing (g.map (algebraMap C C')))
      (TameSingularRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r)
      (tameBaseX (g.map (algebraMap C C')))
  rw [tameSingularBaseChangeEquiv_base, tameBaseRingMap_x]

/-- Scalar extension of the map from the original singular presentation to
the normalized tame presentation. -/
def tameSingularTensorToBranch (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    (C' ⊗[C] TameSingularRing g P N r) →ₐ[C']
      (C' ⊗[C] TameBranchRing g P N a) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    ((tameSingularToBranch g P N r a b hP hbezout).restrictScalars C)

/-- The actual singular-to-normalized map commutes with arbitrary
coefficient extension, including nonflat extensions. -/
theorem tameSingularBaseChangeEquiv_normalization (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P))
    (hbezout : r * a = 1 + b * N) :
    (tameBranchBaseChangeEquiv (C' := C') g P N a).toAlgHom.comp
        (tameSingularTensorToBranch (C' := C') g P N r a b hP hbezout) =
      ((tameSingularToBranch (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r a b
        (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hbezout).restrictScalars C').comp
        (tameSingularBaseChangeEquiv (C' := C') g P N r).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameSingularTensorToBranch,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameBranchBaseChangeEquiv (C' := C') g P N a
      (c ⊗ₜ[C] tameSingularToBranch g P N r a b hP hbezout v) =
    tameSingularToBranch (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r a b
      (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hbezout
      (tameSingularBaseChangeEquiv (C' := C') g P N r (c ⊗ₜ[C] v))
  rw [tameBranchBaseChangeEquiv_tmul, tameSingularBaseChangeEquiv_tmul,
    map_mul]
  congr 1
  · exact ((tameSingularToBranch (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r a b
      (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hbezout).restrictScalars C').commutes c |>.symm
  · exact RingHom.congr_fun
      (tameSingularToBranch_natural (algebraMap C C') g P N r a b hP hbezout) v

/-- Scalar extension of the original normalized-chart deck action. -/
def tameBranchTensorDeck (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (C' ⊗[C] TameBranchRing g P N a) →ₐ[C']
      (C' ⊗[C] TameBranchRing g P N a) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    ((tameBranchDeckAlgebraAction g P N a ζ).restrictScalars C).toAlgHom

/-- Scalar extension of the original singular-chart deck action. -/
def tameSingularTensorDeck (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (C' ⊗[C] TameSingularRing g P N r) →ₐ[C']
      (C' ⊗[C] TameSingularRing g P N r) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    ((tameSingularDeckAlgebraAction g P N r ζ).restrictScalars C).toAlgHom

/-- The coefficient equivalence intertwines the normalized action of the
original deck parameter with the action of its coefficientwise image. -/
theorem tameBranchBaseChangeEquiv_deck (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameBranchBaseChangeEquiv (C' := C') g P N a).toAlgHom.comp
        (tameBranchTensorDeck (C' := C') g P N a ζ) =
      ((tameBranchDeckAlgebraAction (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a
        (rootsOfUnity.mapHom N (algebraMap C C') ζ)).restrictScalars C').toAlgHom.comp
        (tameBranchBaseChangeEquiv (C' := C') g P N a).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameBranchTensorDeck,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameBranchBaseChangeEquiv (C' := C') g P N a
      (c ⊗ₜ[C] tameBranchDeckAlgebraAction g P N a ζ v) =
    tameBranchDeckAlgebraAction (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N a
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)
      (tameBranchBaseChangeEquiv (C' := C') g P N a (c ⊗ₜ[C] v))
  rw [tameBranchBaseChangeEquiv_tmul, tameBranchBaseChangeEquiv_tmul,
    map_mul]
  congr 1
  · exact ((tameBranchDeckAlgebraAction (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N a
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)).restrictScalars C').commutes c |>.symm
  · exact RingHom.congr_fun
      (tameBranchRingMap_deck (algebraMap C C') g P N a ζ) v

/-- The coefficient equivalence intertwines the singular action on the
original `v` coordinate with the action of the mapped root of unity. -/
theorem tameSingularBaseChangeEquiv_deck (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameSingularBaseChangeEquiv (C' := C') g P N r).toAlgHom.comp
        (tameSingularTensorDeck (C' := C') g P N r ζ) =
      ((tameSingularDeckAlgebraAction (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r
        (rootsOfUnity.mapHom N (algebraMap C C') ζ)).restrictScalars C').toAlgHom.comp
        (tameSingularBaseChangeEquiv (C' := C') g P N r).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameSingularTensorDeck,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameSingularBaseChangeEquiv (C' := C') g P N r
      (c ⊗ₜ[C] tameSingularDeckAlgebraAction g P N r ζ v) =
    tameSingularDeckAlgebraAction (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)
      (tameSingularBaseChangeEquiv (C' := C') g P N r (c ⊗ₜ[C] v))
  rw [tameSingularBaseChangeEquiv_tmul, tameSingularBaseChangeEquiv_tmul,
    map_mul]
  congr 1
  · exact ((tameSingularDeckAlgebraAction (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)).restrictScalars C').commutes c |>.symm
  · exact RingHom.congr_fun
      (tameSingularRingMap_deck (algebraMap C C') g P N r ζ) v

/-- Localizing an algebra at one element commutes with an arbitrary extension
of its coefficient ring, followed by an equivalence of the whole algebras. -/
def awayTensorBaseChangeEquiv {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C' B] (x : A)
    (e : (C' ⊗[C] A) ≃ₐ[C'] B) :
    (C' ⊗[C] Localization.Away x) ≃ₐ[C']
      Localization.Away (e (1 ⊗ₜ[C] x)) :=
  (IsLocalization.Away.tensorProductEquivTMulRight C C' x
    (Localization.Away x)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers (1 ⊗ₜ[C] x))
      (T := Submonoid.powers (e (1 ⊗ₜ[C] x)))
      (Localization.Away (1 ⊗ₜ[C] x))
      (Localization.Away (e (1 ⊗ₜ[C] x))) e (by simp [Submonoid.map_powers]))

/-- A named new localization coordinate can replace the transported one. -/
def awayTensorBaseChangeEquivOfEq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C' B] (x : A)
    (e : (C' ⊗[C] A) ≃ₐ[C'] B) (x' : B)
    (hx : e (1 ⊗ₜ[C] x) = x') :
    (C' ⊗[C] Localization.Away x) ≃ₐ[C'] Localization.Away x' := by
  subst x'
  exact awayTensorBaseChangeEquiv (C' := C') x e

/-- The localization equivalence evaluates a scalar-extended element of the
whole algebra by the specified equivalence of whole algebras. -/
theorem awayTensorBaseChangeEquivOfEq_algebraMap
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C' B] (x : A)
    (e : (C' ⊗[C] A) ≃ₐ[C'] B) (x' : B)
    (hx : e (1 ⊗ₜ[C] x) = x') (a : A) :
    awayTensorBaseChangeEquivOfEq (C' := C') x e x' hx
      (1 ⊗ₜ[C] algebraMap A (Localization.Away x) a) =
      algebraMap B (Localization.Away x') (e (1 ⊗ₜ[C] a)) := by
  subst x'
  dsimp [awayTensorBaseChangeEquivOfEq, awayTensorBaseChangeEquiv]
  rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
  exact IsLocalization.algEquivOfAlgEquiv_eq
    (S := Localization.Away ((1 : C') ⊗ₜ[C] x))
    (Q := Localization.Away (e (1 ⊗ₜ[C] x)))
    (h := e) (H := by simp [Submonoid.map_powers]) (1 ⊗ₜ[C] a)

/-- The localized affine-line base commutes with arbitrary coefficient extension. -/
def tameBaseChangeEquiv (g : C[X]) :
    (C' ⊗[C] TameBaseRing g) ≃ₐ[C']
      TameBaseRing (g.map (algebraMap C C')) :=
  awayTensorBaseChangeEquivOfEq (C' := C') g
    (tamePolynomialBaseChangeEquiv (C := C) (C' := C'))
    (g.map (algebraMap C C')) (by
      simpa [tamePolynomialBaseChangeEquiv] using
        (tamePolynomialTensorMap_tmul (C := C) (C' := C') (1 : C') g))

theorem tameBaseChangeEquiv_polynomial (g p : C[X]) :
    tameBaseChangeEquiv (C' := C') g
      (1 ⊗ₜ[C] algebraMap C[X] (TameBaseRing g) p) =
        algebraMap C'[X] (TameBaseRing (g.map (algebraMap C C')))
          (p.map (algebraMap C C')) := by
  rw [tameBaseChangeEquiv, awayTensorBaseChangeEquivOfEq_algebraMap]
  simp [tamePolynomialBaseChangeEquiv, tamePolynomialTensorMap_tmul]

theorem tameBaseChangeEquiv_includeRight (g : C[X]) (a : TameBaseRing g) :
    tameBaseChangeEquiv (C' := C') g (1 ⊗ₜ[C] a) =
      tameBaseRingMap (algebraMap C C') g a := by
  have h : (tameBaseChangeEquiv (C' := C') g).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        TameBaseRing g →ₐ[C] C' ⊗[C] TameBaseRing g).toRingHom =
      tameBaseRingMap (algebraMap C C') g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    apply RingHom.ext
    intro p
    change tameBaseChangeEquiv (C' := C') g
      (1 ⊗ₜ[C] algebraMap C[X] (TameBaseRing g) p) =
        tameBaseRingMap (algebraMap C C') g
          (algebraMap C[X] (TameBaseRing g) p)
    rw [tameBaseChangeEquiv_polynomial, tameBaseRingMap_algebraMap]
  exact congrArg (fun k : TameBaseRing g →+*
    TameBaseRing (g.map (algebraMap C C')) => k a) h

theorem tameBaseChangeEquiv_x (g : C[X]) :
    tameBaseChangeEquiv (C' := C') g (1 ⊗ₜ[C] tameBaseX g) =
      tameBaseX (g.map (algebraMap C C')) := by
  simpa only [tameBaseX, map_X] using
    (tameBaseChangeEquiv_polynomial (C' := C') g X)

/-- The punctured normalized branch chart commutes with arbitrary coefficient
change. -/
def tameBranchOpenBaseChangeEquiv (g P : C[X]) (N a : ℕ) :
    (C' ⊗[C] TameBranchOpen g P N a) ≃ₐ[C']
      TameBranchOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a :=
  awayTensorBaseChangeEquivOfEq (C' := C')
    (tameBranchX g P N a) (tameBranchBaseChangeEquiv (C' := C') g P N a)
    (tameBranchX (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N a)
    (tameBranchBaseChangeEquiv_x (C' := C') g P N a)

/-- The punctured singular branch chart commutes with arbitrary coefficient
change. -/
def tameSingularOpenBaseChangeEquiv (g P : C[X]) (N r : ℕ) :
    (C' ⊗[C] TameSingularOpen g P N r) ≃ₐ[C']
      TameSingularOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r :=
  awayTensorBaseChangeEquivOfEq (C' := C')
    (tameSingularX g P N r) (tameSingularBaseChangeEquiv (C' := C') g P N r)
    (tameSingularX (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r)
    (tameSingularBaseChangeEquiv_x (C' := C') g P N r)

/-- The punctured normalized equivalence restricts to coefficient change on
the whole normalized chart. -/
theorem tameBranchOpenBaseChangeEquiv_algebraMap (g P : C[X]) (N a : ℕ)
    (v : TameBranchRing g P N a) :
    tameBranchOpenBaseChangeEquiv (C' := C') g P N a
      (1 ⊗ₜ[C] algebraMap (TameBranchRing g P N a)
        (TameBranchOpen g P N a) v) =
      algebraMap (TameBranchRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a)
        (TameBranchOpen (g.map (algebraMap C C'))
          (P.map (algebraMap C C')) N a)
        (tameBranchBaseChangeEquiv (C' := C') g P N a (1 ⊗ₜ[C] v)) := by
  exact awayTensorBaseChangeEquivOfEq_algebraMap (C' := C')
    (tameBranchX g P N a) (tameBranchBaseChangeEquiv (C' := C') g P N a)
    (tameBranchX (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N a)
    (tameBranchBaseChangeEquiv_x (C' := C') g P N a) v

/-- The punctured singular equivalence restricts to coefficient change on
the whole singular chart. -/
theorem tameSingularOpenBaseChangeEquiv_algebraMap (g P : C[X]) (N r : ℕ)
    (v : TameSingularRing g P N r) :
    tameSingularOpenBaseChangeEquiv (C' := C') g P N r
      (1 ⊗ₜ[C] algebraMap (TameSingularRing g P N r)
        (TameSingularOpen g P N r) v) =
      algebraMap (TameSingularRing (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r)
        (TameSingularOpen (g.map (algebraMap C C'))
          (P.map (algebraMap C C')) N r)
        (tameSingularBaseChangeEquiv (C' := C') g P N r (1 ⊗ₜ[C] v)) := by
  exact awayTensorBaseChangeEquivOfEq_algebraMap (C' := C')
    (tameSingularX g P N r) (tameSingularBaseChangeEquiv (C' := C') g P N r)
    (tameSingularX (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r)
    (tameSingularBaseChangeEquiv_x (C' := C') g P N r) v

/-- On the punctured normalized chart, the canonical scalar extension is the
coefficientwise map on the whole localization. -/
theorem tameBranchOpenBaseChangeEquiv_includeRight (g P : C[X]) (N a : ℕ)
    (v : TameBranchOpen g P N a) :
    tameBranchOpenBaseChangeEquiv (C' := C') g P N a (1 ⊗ₜ[C] v) =
      tameBranchOpenRingMap (algebraMap C C') g P N a v := by
  have h : (tameBranchOpenBaseChangeEquiv (C' := C') g P N a).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight : TameBranchOpen g P N a →ₐ[C]
          C' ⊗[C] TameBranchOpen g P N a).toRingHom =
      tameBranchOpenRingMap (algebraMap C C') g P N a := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (tameBranchX g P N a))
    apply RingHom.ext
    intro w
    change tameBranchOpenBaseChangeEquiv (C' := C') g P N a
      (1 ⊗ₜ[C] algebraMap (TameBranchRing g P N a)
        (TameBranchOpen g P N a) w) =
      tameBranchOpenRingMap (algebraMap C C') g P N a
        (algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a) w)
    rw [tameBranchOpenBaseChangeEquiv_algebraMap,
      tameBranchBaseChangeEquiv_tmul, tameBranchOpenRingMap_algebraMap]
    simp
  have hv := RingHom.congr_fun h v
  change tameBranchOpenBaseChangeEquiv (C' := C') g P N a (1 ⊗ₜ[C] v) =
    tameBranchOpenRingMap (algebraMap C C') g P N a v at hv
  exact hv

/-- On the punctured singular chart, the canonical scalar extension is the
coefficientwise map on the whole localization. -/
theorem tameSingularOpenBaseChangeEquiv_includeRight (g P : C[X]) (N r : ℕ)
    (v : TameSingularOpen g P N r) :
    tameSingularOpenBaseChangeEquiv (C' := C') g P N r (1 ⊗ₜ[C] v) =
      tameSingularOpenRingMap (algebraMap C C') g P N r v := by
  have h : (tameSingularOpenBaseChangeEquiv (C' := C') g P N r).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight : TameSingularOpen g P N r →ₐ[C]
          C' ⊗[C] TameSingularOpen g P N r).toRingHom =
      tameSingularOpenRingMap (algebraMap C C') g P N r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (tameSingularX g P N r))
    apply RingHom.ext
    intro w
    change tameSingularOpenBaseChangeEquiv (C' := C') g P N r
      (1 ⊗ₜ[C] algebraMap (TameSingularRing g P N r)
        (TameSingularOpen g P N r) w) =
      tameSingularOpenRingMap (algebraMap C C') g P N r
        (algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r) w)
    rw [tameSingularOpenBaseChangeEquiv_algebraMap,
      tameSingularBaseChangeEquiv_tmul, tameSingularOpenRingMap_algebraMap]
    simp
  have hv := RingHom.congr_fun h v
  change tameSingularOpenBaseChangeEquiv (C' := C') g P N r (1 ⊗ₜ[C] v) =
    tameSingularOpenRingMap (algebraMap C C') g P N r v at hv
  exact hv

/-- Pure tensors on the normalized punctured chart have their expected
coefficientwise coordinate formula. -/
theorem tameBranchOpenBaseChangeEquiv_tmul (g P : C[X]) (N a : ℕ)
    (c : C') (v : TameBranchOpen g P N a) :
    tameBranchOpenBaseChangeEquiv (C' := C') g P N a (c ⊗ₜ[C] v) =
      algebraMap C' (TameBranchOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a) c *
        tameBranchOpenRingMap (algebraMap C C') g P N a v := by
  have h := (tameBranchOpenBaseChangeEquiv (C' := C') g P N a).toLinearEquiv.map_smul c
    (1 ⊗ₜ[C] v)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
  simpa only [AlgEquiv.coe_toLinearEquiv, Algebra.smul_def,
    tameBranchOpenBaseChangeEquiv_includeRight] using h

/-- Pure tensors on the singular punctured chart have their expected
coefficientwise coordinate formula. -/
theorem tameSingularOpenBaseChangeEquiv_tmul (g P : C[X]) (N r : ℕ)
    (c : C') (v : TameSingularOpen g P N r) :
    tameSingularOpenBaseChangeEquiv (C' := C') g P N r (c ⊗ₜ[C] v) =
      algebraMap C' (TameSingularOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r) c *
        tameSingularOpenRingMap (algebraMap C C') g P N r v := by
  have h := (tameSingularOpenBaseChangeEquiv (C' := C') g P N r).toLinearEquiv.map_smul c
    (1 ⊗ₜ[C] v)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
  simpa only [AlgEquiv.coe_toLinearEquiv, Algebra.smul_def,
    tameSingularOpenBaseChangeEquiv_includeRight] using h

/-- Extend the singular-to-normalized overlap across a change of coefficient
ring, before identifying either scalar-extended chart with its new presentation. -/
def tameSingularOpenTensorOverlap (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (C' ⊗[C] TameSingularOpen g P N r) →ₐ[C']
      (C' ⊗[C] TameBranchOpen g P N a) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    ((tameBranchOpenEquivSingularOpen g P N r a b hP hN hbezout).symm.restrictScalars C).toAlgHom

/-- Extend the normalized-to-singular overlap across coefficients. -/
def tameBranchOpenTensorOverlap (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (C' ⊗[C] TameBranchOpen g P N a) →ₐ[C']
      (C' ⊗[C] TameSingularOpen g P N r) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    ((tameBranchOpenEquivSingularOpen g P N r a b hP hN hbezout).restrictScalars C).toAlgHom

/-- The canonical coefficient equivalences commute with the full punctured
singular-to-normalized overlap, including arbitrary pure coefficients. -/
theorem tameSingularOpenBaseChangeEquiv_overlap (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameBranchOpenBaseChangeEquiv (C' := C') g P N a).toAlgHom.comp
        (tameSingularOpenTensorOverlap (C' := C') g P N r a b hP hN hbezout) =
      ((tameBranchOpenEquivSingularOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r a b
        (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hN hbezout).symm.restrictScalars C').toAlgHom.comp
        (tameSingularOpenBaseChangeEquiv (C' := C') g P N r).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameSingularOpenTensorOverlap,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameBranchOpenBaseChangeEquiv (C' := C') g P N a
      (c ⊗ₜ[C] tameSingularOpenToBranchOpen g P N r a b hP hbezout v) =
    tameSingularOpenToBranchOpen (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r a b
      (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hbezout
      (tameSingularOpenBaseChangeEquiv (C' := C') g P N r (c ⊗ₜ[C] v))
  rw [tameBranchOpenBaseChangeEquiv_tmul,
    tameSingularOpenBaseChangeEquiv_tmul]
  rw [map_mul]
  congr 1
  · change algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (TameBranchOpen (g.map (algebraMap C C'))
          (P.map (algebraMap C C')) N a)
        (algebraMap C' (TameBaseRing (g.map (algebraMap C C'))) c) =
      tameSingularOpenToBranchOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r a b
        (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hbezout
        (algebraMap (TameBaseRing (g.map (algebraMap C C')))
          (TameSingularOpen (g.map (algebraMap C C'))
            (P.map (algebraMap C C')) N r)
          (algebraMap C' (TameBaseRing (g.map (algebraMap C C'))) c))
    exact ((tameBranchOpenEquivSingularOpen (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r a b
      (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hN hbezout).symm).commutes
        (algebraMap C' (TameBaseRing (g.map (algebraMap C C'))) c) |>.symm
  · exact RingHom.congr_fun
      (tameSingularOpenToBranchOpen_natural (algebraMap C C') g P N r a b hP hbezout) v

/-- The reverse punctured overlap is compatible with the same canonical
coefficient equivalences. -/
theorem tameBranchOpenBaseChangeEquiv_overlap (g P : C[X]) (N r a b : ℕ)
    (hP : IsUnit (algebraMap C[X] (TameBaseRing g) P)) (hN : N ≠ 0)
    (hbezout : r * a = 1 + b * N) :
    (tameSingularOpenBaseChangeEquiv (C' := C') g P N r).toAlgHom.comp
        (tameBranchOpenTensorOverlap (C' := C') g P N r a b hP hN hbezout) =
      ((tameBranchOpenEquivSingularOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r a b
        (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hN hbezout).restrictScalars C').toAlgHom.comp
        (tameBranchOpenBaseChangeEquiv (C' := C') g P N a).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameBranchOpenTensorOverlap,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameSingularOpenBaseChangeEquiv (C' := C') g P N r
      (c ⊗ₜ[C] tameBranchOpenToSingularOpen g P N r a b hP hN hbezout v) =
    tameBranchOpenToSingularOpen (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r a b
      (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hN hbezout
      (tameBranchOpenBaseChangeEquiv (C' := C') g P N a (c ⊗ₜ[C] v))
  rw [tameSingularOpenBaseChangeEquiv_tmul,
    tameBranchOpenBaseChangeEquiv_tmul, map_mul]
  congr 1
  · change algebraMap (TameBaseRing (g.map (algebraMap C C')))
        (TameSingularOpen (g.map (algebraMap C C'))
          (P.map (algebraMap C C')) N r)
        (algebraMap C' (TameBaseRing (g.map (algebraMap C C'))) c) =
      tameBranchOpenToSingularOpen (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r a b
        (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hN hbezout
        (algebraMap (TameBaseRing (g.map (algebraMap C C')))
          (TameBranchOpen (g.map (algebraMap C C'))
            (P.map (algebraMap C C')) N a)
          (algebraMap C' (TameBaseRing (g.map (algebraMap C C'))) c))
    exact ((tameBranchOpenEquivSingularOpen (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r a b
      (tameBaseRingMap_isUnit (algebraMap C C') g P hP) hN hbezout).commutes
        (algebraMap C' (TameBaseRing (g.map (algebraMap C C'))) c)).symm
  · exact RingHom.congr_fun
      (tameBranchOpenToSingularOpen_natural (algebraMap C C') g P N r a b hP hN hbezout) v

/-- The punctured normalized deck map is linear over its coefficient ring. -/
def tameBranchOpenDeckAlgHom (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) : TameBranchOpen g P N a →ₐ[C]
      TameBranchOpen g P N a :=
  AlgHom.mk' (tameBranchOpenDeck g P N a ζ) (by
    intro c v
    simp only [Algebra.smul_def, map_mul]
    congr 1
    rw [show algebraMap C (TameBranchOpen g P N a) c =
        algebraMap (TameBranchRing g P N a) (TameBranchOpen g P N a)
          (algebraMap C (TameBranchRing g P N a) c) from
          IsScalarTower.algebraMap_apply C (TameBranchRing g P N a)
            (TameBranchOpen g P N a) c]
    rw [tameBranchOpenDeck_algebraMap]
    congr 1
    change tameBranchDeckAlgebraAction g P N a ζ
      (algebraMap (TameBaseRing g) (TameBranchRing g P N a)
        (algebraMap C (TameBaseRing g) c)) = _
    exact (tameBranchDeckAlgebraAction g P N a ζ).commutes _)

/-- The punctured singular deck map is linear over its coefficient ring. -/
def tameSingularOpenDeckAlgHom (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) : TameSingularOpen g P N r →ₐ[C]
      TameSingularOpen g P N r :=
  AlgHom.mk' (tameSingularOpenDeck g P N r ζ) (by
    intro c v
    simp only [Algebra.smul_def, map_mul]
    congr 1
    rw [show algebraMap C (TameSingularOpen g P N r) c =
        algebraMap (TameSingularRing g P N r) (TameSingularOpen g P N r)
          (algebraMap C (TameSingularRing g P N r) c) from
          IsScalarTower.algebraMap_apply C (TameSingularRing g P N r)
            (TameSingularOpen g P N r) c]
    rw [tameSingularOpenDeck_algebraMap]
    congr 1
    change tameSingularDeckAlgebraAction g P N r ζ
      (algebraMap (TameBaseRing g) (TameSingularRing g P N r)
        (algebraMap C (TameBaseRing g) c)) = _
    exact (tameSingularDeckAlgebraAction g P N r ζ).commutes _)

/-- Scalar extension of the original normalized deck action. -/
def tameBranchOpenTensorDeck (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (C' ⊗[C] TameBranchOpen g P N a) →ₐ[C']
      (C' ⊗[C] TameBranchOpen g P N a) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    (tameBranchOpenDeckAlgHom g P N a ζ)

/-- Scalar extension of the original singular deck action. -/
def tameSingularOpenTensorDeck (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (C' ⊗[C] TameSingularOpen g P N r) →ₐ[C']
      (C' ⊗[C] TameSingularOpen g P N r) :=
  Algebra.TensorProduct.map (AlgHom.id C' C')
    (tameSingularOpenDeckAlgHom g P N r ζ)

/-- Coefficient extension intertwines the complete punctured normalized deck
action with the action of the mapped root of unity. -/
theorem tameBranchOpenBaseChangeEquiv_deck (g P : C[X]) (N a : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameBranchOpenBaseChangeEquiv (C' := C') g P N a).toAlgHom.comp
        (tameBranchOpenTensorDeck (C' := C') g P N a ζ) =
      (tameBranchOpenDeckAlgHom (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N a
        (rootsOfUnity.mapHom N (algebraMap C C') ζ)).comp
        (tameBranchOpenBaseChangeEquiv (C' := C') g P N a).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameBranchOpenTensorDeck,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameBranchOpenBaseChangeEquiv (C' := C') g P N a
      (c ⊗ₜ[C] tameBranchOpenDeck g P N a ζ v) =
    tameBranchOpenDeck (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N a
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)
      (tameBranchOpenBaseChangeEquiv (C' := C') g P N a (c ⊗ₜ[C] v))
  rw [tameBranchOpenBaseChangeEquiv_tmul,
    tameBranchOpenBaseChangeEquiv_tmul, map_mul]
  congr 1
  · exact (tameBranchOpenDeckAlgHom (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N a
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)).commutes c |>.symm
  · exact RingHom.congr_fun
      (tameBranchOpenRingMap_deck (algebraMap C C') g P N a ζ) v

/-- Coefficient extension intertwines the original singular deck action on
the punctured chart. -/
theorem tameSingularOpenBaseChangeEquiv_deck (g P : C[X]) (N r : ℕ) [NeZero N]
    (ζ : rootsOfUnity N C) :
    (tameSingularOpenBaseChangeEquiv (C' := C') g P N r).toAlgHom.comp
        (tameSingularOpenTensorDeck (C' := C') g P N r ζ) =
      (tameSingularOpenDeckAlgHom (g.map (algebraMap C C'))
        (P.map (algebraMap C C')) N r
        (rootsOfUnity.mapHom N (algebraMap C C') ζ)).comp
        (tameSingularOpenBaseChangeEquiv (C' := C') g P N r).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c v
  simp only [AlgHom.comp_apply, tameSingularOpenTensorDeck,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  change tameSingularOpenBaseChangeEquiv (C' := C') g P N r
      (c ⊗ₜ[C] tameSingularOpenDeck g P N r ζ v) =
    tameSingularOpenDeck (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)
      (tameSingularOpenBaseChangeEquiv (C' := C') g P N r (c ⊗ₜ[C] v))
  rw [tameSingularOpenBaseChangeEquiv_tmul,
    tameSingularOpenBaseChangeEquiv_tmul, map_mul]
  congr 1
  · exact (tameSingularOpenDeckAlgHom (g.map (algebraMap C C'))
      (P.map (algebraMap C C')) N r
      (rootsOfUnity.mapHom N (algebraMap C C') ζ)).commutes c |>.symm
  · exact RingHom.congr_fun
      (tameSingularOpenRingMap_deck (algebraMap C C') g P N r ζ) v

end TensorBaseChange

end HilbertModularity.Hypergeometric.EulerCover
