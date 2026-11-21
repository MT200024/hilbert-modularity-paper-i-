/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFieldReflection
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-! # Injectivity of the generic Euler reflection

The point-level reflection of [GPRV, Proposition 9.5] extends to the function
field once its evaluation on the actual integral Euler algebra is injective.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

/-- The coordinate in the actual Euler function field remains transcendental
over the constant field. -/
theorem coverFunctionFieldX_transcendental (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    Transcendental K (coverFunctionFieldX N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  have hpoly : Function.Injective
      (algebraMap K[X] (CoverFunctionField N m t)) := by
    intro p q hpq
    apply polynomial_to_baseRing_injective t
    apply baseRing_to_coverRing_injective N m t hN
    apply IsFractionRing.injective (CoverRing N m t) (CoverFunctionField N m t)
    calc
      _ = (algebraMap (CoverRing N m t) (CoverFunctionField N m t))
          ((algebraMap K[X] (CoverRing N m t)) p) := by
            exact congrArg _ ((IsScalarTower.algebraMap_apply K[X] (BaseRing t)
              (CoverRing N m t) p).symm)
      _ = algebraMap K[X] (CoverFunctionField N m t) p :=
        (IsScalarTower.algebraMap_apply K[X] (CoverRing N m t)
          (CoverFunctionField N m t) p).symm
      _ = algebraMap K[X] (CoverFunctionField N m t) q := hpq
      _ = (algebraMap (CoverRing N m t) (CoverFunctionField N m t))
          ((algebraMap K[X] (CoverRing N m t)) q) :=
        IsScalarTower.algebraMap_apply K[X] (CoverRing N m t)
          (CoverFunctionField N m t) q
      _ = _ := by
        exact congrArg _ (IsScalarTower.algebraMap_apply K[X] (BaseRing t)
          (CoverRing N m t) q)
  let f : K[X] →ₐ[K] CoverFunctionField N m t :=
    IsScalarTower.toAlgHom K K[X] (CoverFunctionField N m t)
  have heval (p : K[X]) :
      aeval (coverFunctionFieldX N m t) p = f p := by
    change aeval (f X) p = f p
    rw [Polynomial.aeval_def]
    exact Polynomial.eval₂_algebraMap_X p f
  intro h
  obtain ⟨p, hp, hp0⟩ := h
  apply hp
  apply hpoly
  change f p = f 0
  simpa only [heval, map_zero] using hp0

/-- The rational reflection of the generic coordinate is still
transcendental over the constants. -/
theorem reflectionX_coverFunctionFieldX_transcendental (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    Transcendental K
      (reflectionX (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t)) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  have hx := coverFunctionFieldX_transcendental N m t hN hmPos hm hcop
  have hmul : Transcendental K
      ((algebraMap K (CoverFunctionField N m t) t) *
        coverFunctionFieldX N m t) := by
      convert hx.aeval (C t * X) (by simp [ht]) (by simp [ht]) using 1; simp
  intro h
  rw [reflectionX_eq] at h
  exact hmul (IsAlgebraic.inv_iff.mp h)

/-- Evaluation at a transcendental point embeds the polynomial base ring. -/
theorem openEulerPointPolynomialHom_injective_of_transcendental
    {F : Type*} [Field F] [Algebra K F] (N m : ℕ) (t : K)
    (p : OpenEulerPoint N m (algebraMap K F t))
    (hx : Transcendental K p.x) :
    Function.Injective
      (openEulerPointPolynomialHom (algebraMap K F) N m t p) := by
  have heval : openEulerPointPolynomialHom (algebraMap K F) N m t p =
      (aeval p.x).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  intro a b hab
  apply transcendental_iff_injective.mp hx
  rw [heval] at hab
  exact hab

/-- Transcendental evaluation embeds the localized branch complement. -/
theorem openEulerPointBaseHom_injective_of_transcendental
    {F : Type*} [Field F] [Algebra K F] (N m : ℕ) (t : K)
    (p : OpenEulerPoint N m (algebraMap K F t))
    (hx : Transcendental K p.x) :
    Function.Injective
      (openEulerPointBaseHom (algebraMap K F) N m t p) := by
  have hpoly := openEulerPointPolynomialHom_injective_of_transcendental
    N m t p hx
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (M := Submonoid.powers (branchProduct t))
    (openEulerPointBaseHom (algebraMap K F) N m t p)).2
  intro a b
  simp only [openEulerPointBaseHom_algebraMap]
  constructor
  · intro hab
    exact congrArg (openEulerPointPolynomialHom (algebraMap K F) N m t p)
      (polynomial_to_baseRing_injective t hab)
  · intro hab
    exact congrArg (algebraMap K[X] (BaseRing t)) (hpoly hab)

/-- A map from an integral domain integral over its base is injective when
its restriction to the base is injective. -/
private theorem integralAlgHom_injective
    {A B C : Type*} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A C)) (φ : B →ₐ[A] C) :
    Function.Injective φ := by
  apply (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := A)
  ext a
  change φ (algebraMap A B a) = 0 ↔ a = 0
  rw [φ.commutes]
  exact map_eq_zero_iff (algebraMap A C) hinj

/-- An Euler point with transcendental base coordinate embeds the actual
monic Euler algebra into its target field. -/
theorem openEulerPointCoverHom_injective_of_transcendental
    {F : Type*} [Field F] [Algebra K F] (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (p : OpenEulerPoint N m (algebraMap K F t))
    (hx : Transcendental K p.x) :
    Function.Injective
      (openEulerPointCoverHom (algebraMap K F) N m t p) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let f := openEulerPointBaseHom (algebraMap K F) N m t p
  let : Algebra (BaseRing t) F := f.toAlgebra
  let : Algebra.IsIntegral (BaseRing t) (CoverRing N m t) :=
    AdjoinRoot.isIntegral_of_monic (coverPolynomial_monic N m t hN)
  let φ : CoverRing N m t →ₐ[BaseRing t] F :=
    { toRingHom := openEulerPointCoverHom (algebraMap K F) N m t p
      commutes' := by
        intro a
        exact openEulerPointCoverHom_base (algebraMap K F) N m t p a }
  exact integralAlgHom_injective
    (openEulerPointBaseHom_injective_of_transcendental N m t p hx) φ

/-- The explicit generic reflection embeds the actual Euler coordinate
algebra in its function field. -/
theorem genericReflectionCoverHom_injective (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    Function.Injective (genericReflectionCoverHom N m t hN hmPos hm hcop ht) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let p := reflectOpenEulerPoint N m (Nat.le_of_lt hm)
    ((map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht)
    (genericOpenEulerPoint N m t hN hmPos hm hcop)
  have hx : Transcendental K p.x := by
    simpa only [p, reflectOpenEulerPoint_x, genericOpenEulerPoint_x] using
      reflectionX_coverFunctionFieldX_transcendental N m t hN hmPos hm hcop ht
  rw [genericReflectionCoverHom_eq_openEulerPointCoverHom]
  exact openEulerPointCoverHom_injective_of_transcendental
    N m t hN hmPos hm hcop p hx

/-- The explicit reflection extends from the actual Euler coordinate
algebra to its function field. -/
def genericReflectionFunctionFieldHom (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    CoverFunctionField N m t →+* CoverFunctionField N m t := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  exact IsFractionRing.lift
    (g := genericReflectionCoverHom N m t hN hmPos hm hcop ht)
    (genericReflectionCoverHom_injective N m t hN hmPos hm hcop ht)

@[simp] theorem genericReflectionFunctionFieldHom_root (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
      (coverFunctionFieldRoot N m t) =
      reflectionY (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) (coverFunctionFieldRoot N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [coverFunctionFieldRoot, genericReflectionFunctionFieldHom,
    IsFractionRing.lift_algebraMap]
  exact genericReflectionCoverHom_root N m t hN hmPos hm hcop ht

@[simp] theorem genericReflectionFunctionFieldHom_x (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
      (coverFunctionFieldX N m t) =
      reflectionX (algebraMap K (CoverFunctionField N m t) t)
        (coverFunctionFieldX N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [coverFunctionFieldX,
    IsScalarTower.algebraMap_apply K[X] (CoverRing N m t) (CoverFunctionField N m t),
    genericReflectionFunctionFieldHom, IsFractionRing.lift_algebraMap]
  exact genericReflectionCoverHom_x N m t hN hmPos hm hcop ht

@[simp] theorem genericReflectionFunctionFieldHom_const (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) (a : K) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
      (algebraMap K (CoverFunctionField N m t) a) =
      algebraMap K (CoverFunctionField N m t) a := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  rw [IsScalarTower.algebraMap_apply K (CoverRing N m t)
    (CoverFunctionField N m t), genericReflectionFunctionFieldHom,
    IsFractionRing.lift_algebraMap,
    genericReflectionCoverHom_eq_openEulerPointCoverHom,
    IsScalarTower.algebraMap_apply K (BaseRing t) (CoverRing N m t),
    openEulerPointCoverHom_base,
    IsScalarTower.algebraMap_apply K K[X] (BaseRing t),
    openEulerPointBaseHom_algebraMap]
  simp only [Polynomial.algebraMap_eq, openEulerPointPolynomialHom_C]
  rw [IsScalarTower.algebraMap_apply K K[X] (CoverFunctionField N m t),
    Polynomial.algebraMap_eq,
    IsScalarTower.algebraMap_apply K[X] (BaseRing t)
      (CoverFunctionField N m t),
    IsScalarTower.algebraMap_apply (BaseRing t) (CoverRing N m t)
      (CoverFunctionField N m t)]

/-- The reflection of the actual Euler function field squares to the identity. -/
theorem genericReflectionFunctionFieldHom_involutive (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht).comp
      (genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht) =
      RingHom.id (CoverFunctionField N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let r := genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
  let x := coverFunctionFieldX N m t
  let y := coverFunctionFieldRoot N m t
  let τ := algebraMap K (CoverFunctionField N m t) t
  let p := genericOpenEulerPoint N m t hN hmPos hm hcop
  have htF : τ ≠ 0 := (map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht
  have hx0 : x ≠ 0 := by
    simpa only [p, x, genericOpenEulerPoint_x] using p.x_ne_zero
  have hy0 : y ≠ 0 := by
    simpa only [p, y, genericOpenEulerPoint_y] using p.y_ne_zero
  have h1x : 1 - x ≠ 0 := by
    simpa only [p, x, genericOpenEulerPoint_x] using p.one_sub_x_ne_zero
  have h1tx : 1 - τ * x ≠ 0 := by
    simpa only [p, τ, x, genericOpenEulerPoint_x] using p.one_sub_tx_ne_zero
  have hrconst (a : K) : r (algebraMap K (CoverFunctionField N m t) a) =
      algebraMap K (CoverFunctionField N m t) a :=
    genericReflectionFunctionFieldHom_const N m t hN hmPos hm hcop ht a
  have hrx : r x = reflectionX τ x :=
    genericReflectionFunctionFieldHom_x N m t hN hmPos hm hcop ht
  have hry : r y = reflectionY τ x y :=
    genericReflectionFunctionFieldHom_root N m t hN hmPos hm hcop ht
  have hrx2 : r (r x) = x := by
    rw [hrx, map_reflectionX, hrconst, hrx, reflectionX_reflectionX htF hx0]
  have hry2 : r (r y) = y := by
    rw [hry, map_reflectionY, hrconst, hrx, hry]
    exact reflectionY_reflectionY htF hx0 hy0 h1x h1tx
  apply IsFractionRing.ringHom_ext (A := CoverRing N m t)
  intro a
  have hcomp : (r.comp r).comp
      (algebraMap (CoverRing N m t) (CoverFunctionField N m t)) =
      algebraMap (CoverRing N m t) (CoverFunctionField N m t) := by
    apply AdjoinRoot.ringHom_ext
    · apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
      apply Polynomial.ringHom_ext
      · intro c
        change r (r (algebraMap K (CoverFunctionField N m t) c)) =
          algebraMap K (CoverFunctionField N m t) c
        rw [hrconst, hrconst]
      · simpa only [RingHom.comp_apply, x, coverFunctionFieldX,
          IsScalarTower.algebraMap_apply K[X] (CoverRing N m t)
            (CoverFunctionField N m t),
          IsScalarTower.algebraMap_apply K[X] (BaseRing t)
            (CoverRing N m t), AdjoinRoot.algebraMap_eq] using hrx2
    · simpa only [RingHom.comp_apply, y, coverFunctionFieldRoot,
        coverRoot] using hry2
  exact congrArg (fun f : CoverRing N m t →+* CoverFunctionField N m t => f a) hcomp

/-- The explicit reflection is an involutive automorphism of the Euler
function field. -/
def genericReflectionFunctionFieldEquiv (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    CoverFunctionField N m t ≃+* CoverFunctionField N m t := by
  letI : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let r := genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht
  have hinv : ∀ a : CoverFunctionField N m t, r (r a) = a := by
    intro a
    have h := congrArg
      (fun f : CoverFunctionField N m t →+* CoverFunctionField N m t => f a)
      (genericReflectionFunctionFieldHom_involutive N m t hN hmPos hm hcop ht)
    simpa only [r, RingHom.comp_apply, RingHom.id_apply] using h
  exact
    { toFun := r
      invFun := r
      left_inv := hinv
      right_inv := hinv
      map_mul' := r.map_mul
      map_add' := r.map_add }

/-- The actual function-field reflection acts through its constructed ring homomorphism. -/
theorem genericReflectionFunctionFieldEquiv_apply (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) (a : CoverFunctionField N m t) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    (genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht) a =
      (genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht) a := by
  rfl

/-- The explicit Euler reflection is a nonidentity function-field
automorphism.  Its action on the transcendental base coordinate is inversion
in `t * x`, so a fixed base coordinate would satisfy a quadratic equation. -/
theorem genericReflectionFunctionFieldEquiv_ne_refl (N m : ℕ) (t : K)
    (hN : N ≠ 0) (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (ht : t ≠ 0) :
    letI := coverRing_isDomain N m t hN hmPos hm hcop
    genericReflectionFunctionFieldEquiv N m t hN hmPos hm hcop ht ≠
      RingEquiv.refl (CoverFunctionField N m t) := by
  let : IsDomain (CoverRing N m t) := coverRing_isDomain N m t hN hmPos hm hcop
  let x := coverFunctionFieldX N m t
  let τ := algebraMap K (CoverFunctionField N m t) t
  have hxtr : Transcendental K x :=
    coverFunctionFieldX_transcendental N m t hN hmPos hm hcop
  have htF : τ ≠ 0 := (map_ne_zero (algebraMap K (CoverFunctionField N m t))).mpr ht
  have hx0 : x ≠ 0 := by
    simpa only [x, genericOpenEulerPoint_x] using
      (genericOpenEulerPoint N m t hN hmPos hm hcop).x_ne_zero
  intro heq
  have hfix : x = reflectionX τ x := by
    have h := congrArg
      (fun e : CoverFunctionField N m t ≃+* CoverFunctionField N m t => e x) heq
    change (genericReflectionFunctionFieldHom N m t hN hmPos hm hcop ht) x = x at h
    rw [genericReflectionFunctionFieldHom_x] at h
    exact h.symm
  have hmul : x * (τ * x) = 1 := by
    calc
      x * (τ * x) = reflectionX τ x * (τ * x) :=
        congrArg (fun z => z * (τ * x)) hfix
      _ = 1 := by rw [reflectionX_eq]; exact inv_mul_cancel₀ (mul_ne_zero htF hx0)
  have hτ : τ * x ^ 2 = 1 := by calc
    τ * x ^ 2 = x * (τ * x) := by ring
    _ = 1 := hmul
  have hrel : x ^ 2 = τ⁻¹ := by calc
    x ^ 2 = τ⁻¹ * (τ * x ^ 2) := by field_simp
    _ = τ⁻¹ := by rw [hτ]; simp
  have hp : (X ^ 2 - C t⁻¹ : K[X]) ≠ 0 := by
    intro heq
    have hcoeff := congrArg (fun p : K[X] => p.coeff 2) heq
    simp at hcoeff
  have hp0 : aeval x (X ^ 2 - C t⁻¹ : K[X]) = 0 := by
    simp [hrel, τ]
  exact hxtr ⟨X ^ 2 - C t⁻¹, hp, hp0⟩

end HilbertModularity.Hypergeometric.EulerCover
