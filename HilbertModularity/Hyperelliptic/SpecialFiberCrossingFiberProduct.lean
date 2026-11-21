/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingStalk

/-! # The local crossing as two branches glued at one point

The translated equation `y(y - 2t) = 0` has a more intrinsic description:
its two branch rings are glued along the divisor `t = 0`. This description
applies to the actual finite-chart stalk through the preceding equivalence.
It does not by itself identify an adic completion or assert Scheme nodality.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

/-- Pairs of functions on two copies of `Spec S` with equal restriction to
the divisor `t = 0`. -/
def localNodePairs {S : Type*} [CommRing S] (t : S) : Subring (S × S) where
  carrier := {z | Ideal.Quotient.mk (Ideal.span {t}) z.1 =
    Ideal.Quotient.mk (Ideal.span {t}) z.2}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change Ideal.Quotient.mk (Ideal.span {t}) (a + b).1 =
      Ideal.Quotient.mk (Ideal.span {t}) (a + b).2
    change Ideal.Quotient.mk (Ideal.span {t}) a.1 =
      Ideal.Quotient.mk (Ideal.span {t}) a.2 at ha
    change Ideal.Quotient.mk (Ideal.span {t}) b.1 =
      Ideal.Quotient.mk (Ideal.span {t}) b.2 at hb
    simpa only [Prod.fst_add, Prod.snd_add, map_add] using
      congrArg₂ (· + ·) ha hb
  mul_mem' := by
    intro a b ha hb
    change Ideal.Quotient.mk (Ideal.span {t}) (a * b).1 =
      Ideal.Quotient.mk (Ideal.span {t}) (a * b).2
    change Ideal.Quotient.mk (Ideal.span {t}) a.1 =
      Ideal.Quotient.mk (Ideal.span {t}) a.2 at ha
    change Ideal.Quotient.mk (Ideal.span {t}) b.1 =
      Ideal.Quotient.mk (Ideal.span {t}) b.2 at hb
    simpa only [Prod.fst_mul, Prod.snd_mul, map_mul] using
      congrArg₂ (· * ·) ha hb
  neg_mem' := by
    intro a ha
    change Ideal.Quotient.mk (Ideal.span {t}) (-a).1 =
      Ideal.Quotient.mk (Ideal.span {t}) (-a).2
    change Ideal.Quotient.mk (Ideal.span {t}) a.1 =
      Ideal.Quotient.mk (Ideal.span {t}) a.2 at ha
    simpa only [Prod.fst_neg, Prod.snd_neg, map_neg] using congrArg Neg.neg ha

/-- A pair belongs to the local crossing ring precisely when its two values
agree modulo the branch parameter. -/
theorem mem_localNodePairs_iff_dvd {S : Type*} [CommRing S]
    (t : S) (z : S × S) : z ∈ localNodePairs t ↔ t ∣ z.1 - z.2 := by
  change Ideal.Quotient.mk (Ideal.span {t}) z.1 =
    Ideal.Quotient.mk (Ideal.span {t}) z.2 ↔ _
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

/-- The diagonal branch parameter is in the conductor of the crossing ring
inside the product of its two branch rings. -/
theorem localNodePairs_parameter_mul_mem {S : Type*} [CommRing S]
    (t : S) (z : S × S) : (t * z.1, t * z.2) ∈ localNodePairs t := by
  rw [mem_localNodePairs_iff_dvd]
  refine ⟨z.1 - z.2, ?_⟩
  ring

/-- The conductor in the product of the branch rings consists exactly of
the pairs whose two entries vanish on the crossing divisor. -/
theorem localNodePairs_mul_all_iff {S : Type*} [CommRing S]
    (t : S) (z : S × S) :
    (∀ w : S × S, z * w ∈ localNodePairs t) ↔ t ∣ z.1 ∧ t ∣ z.2 := by
  constructor
  · intro hz
    constructor
    · simpa only [Prod.fst_mul, Prod.snd_mul, mul_one, mul_zero, sub_zero] using
        (mem_localNodePairs_iff_dvd t _).mp (hz (1, 0))
    · have h := (mem_localNodePairs_iff_dvd t _).mp (hz (0, 1))
      simpa only [Prod.fst_mul, Prod.snd_mul, mul_zero, mul_one, zero_sub,
        dvd_neg] using h
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ w
    rw [mem_localNodePairs_iff_dvd]
    refine ⟨a * w.1 - b * w.2, ?_⟩
    change (z * w).1 - (z * w).2 = t * (a * w.1 - b * w.2)
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [ha, hb]
    ring

/-- The two branch idempotents generate the product of branch rings over the
crossing ring. This finite extension is the algebraic input for normalization. -/
theorem localNodePairs_finite_product {S : Type*} [CommRing S] (t : S) :
    Module.Finite (localNodePairs t) (S × S) := by
  let A := localNodePairs t
  let e₁ : S × S := (1, 0)
  let e₂ : S × S := (0, 1)
  let f : A × A →ₗ[A] S × S := {
    toFun a := algebraMap A (S × S) a.1 * e₁ +
      algebraMap A (S × S) a.2 * e₂
    map_add' a b := by
      simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul]
      abel
    map_smul' a b := by
      change (algebraMap A (S × S)) (a * b.1) * e₁ +
        (algebraMap A (S × S)) (a * b.2) * e₂ =
        (algebraMap A (S × S)) a *
          ((algebraMap A (S × S)) b.1 * e₁ +
            (algebraMap A (S × S)) b.2 * e₂)
      simp only [map_mul]
      ring }
  apply Module.Finite.of_surjective f
  intro z
  let a : A := ⟨(z.1, z.1), rfl⟩
  let b : A := ⟨(z.2, z.2), rfl⟩
  refine ⟨(a, b), ?_⟩
  change a.1 * e₁ + b.1 * e₂ = z
  rcases z with ⟨x, y⟩
  simp [a, b, e₁, e₂]

/-- Each function on either normalized branch is integral over the crossing
ring, since the full product is finite as a module over that ring. -/
theorem localNodePairs_integral_product {S : Type*} [CommRing S] (t : S) :
    Algebra.IsIntegral (localNodePairs t) (S × S) := by
  let := localNodePairs_finite_product t
  exact Algebra.IsIntegral.of_finite (localNodePairs t) (S × S)

/-- Restriction of `y(y - 2t) = 0` to its branches `y = 0` and `y = 2t`. -/
def localNodePairMap {S : Type*} [CommRing S] (t : S) :
    QuadraticAlgebra S 0 (2 * t) →+* S × S where
  toFun z := (z.re, z.re + 2 * t * z.im)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;>
    simp [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] ; ring
  map_mul' x y := by ext <;>
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] ; ring

theorem localNodePairMap_mem {S : Type*} [CommRing S] (t : S)
    (z : QuadraticAlgebra S 0 (2 * t)) :
    localNodePairMap t z ∈ localNodePairs t := by
  change Ideal.Quotient.mk (Ideal.span {t}) z.re =
    Ideal.Quotient.mk (Ideal.span {t}) (z.re + 2 * t * z.im)
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  refine ⟨-(2 * z.im), ?_⟩
  ring

/-- If `t` is a nonzero parameter and two is invertible, the node ring is
exactly the fibre product of its two branch rings over `S/(t)`. -/
def localNodeFiberProductEquiv {S : Type*} [CommRing S] [IsDomain S]
    (t half : S) (ht : t ≠ 0) (hhalf : half * 2 = 1) :
    QuadraticAlgebra S 0 (2 * t) ≃+* localNodePairs t := by
  let f : QuadraticAlgebra S 0 (2 * t) →+* localNodePairs t :=
    { toFun := fun z => ⟨localNodePairMap t z, localNodePairMap_mem t z⟩
      map_zero' := Subtype.ext (map_zero (localNodePairMap t))
      map_one' := Subtype.ext (map_one (localNodePairMap t))
      map_add' := fun x y => Subtype.ext (map_add (localNodePairMap t) x y)
      map_mul' := fun x y => Subtype.ext (map_mul (localNodePairMap t) x y) }
  apply RingEquiv.ofBijective f
  constructor
  · intro x y hxy
    have hp : x.re = y.re := congrArg Prod.fst (congrArg Subtype.val hxy)
    have hq : x.re + 2 * t * x.im = y.re + 2 * t * y.im :=
      congrArg Prod.snd (congrArg Subtype.val hxy)
    have htwo : (2 : S) ≠ 0 := by
      intro h
      simp [h] at hhalf
    have h2t : (2 : S) * t ≠ 0 := mul_ne_zero htwo ht
    have him : x.im = y.im := by
      have h : (2 * t) * (x.im - y.im) = 0 := by
        linear_combination hq - hp
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h2t)
    exact QuadraticAlgebra.ext hp him
  · intro z
    have hz : t ∣ z.1.2 - z.1.1 := by
      have h := z.property
      change Ideal.Quotient.mk (Ideal.span {t}) z.1.1 =
        Ideal.Quotient.mk (Ideal.span {t}) z.1.2 at h
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton] at h
      exact dvd_neg.mp (by simpa only [neg_sub] using h)
    obtain ⟨q, hq⟩ := hz
    let w : QuadraticAlgebra S 0 (2 * t) := ⟨z.1.1, half * q⟩
    refine ⟨w, Subtype.ext (Prod.ext rfl ?_)⟩
    change z.1.1 + 2 * t * (half * q) = z.1.2
    linear_combination -hq + t * q * hhalf

/-- The actual finite-chart crossing stalk is the two-branch fibre product
over its residue point. -/
def finiteCrossing_stalkFiberProductEquiv
    {k : Type*} [Field k] (P : k[X]) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0)
    (hsimple : (finiteComponentPolynomial P).derivative.eval x ≠ 0)
    (h2 : (2 : k) ≠ 0) :
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    QuadraticAlgebra S
      (algebraMap k[X] S (finiteBranchPolynomial P 0))
      (algebraMap k[X] S 0) ≃+*
      localNodePairs (algebraMap k[X] S (X - C x)) := by
  letI : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
  let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
  let t : S := algebraMap k[X] S (X - C x)
  let half : S := algebraMap k S ((2 : k)⁻¹)
  have ht : t ≠ 0 := by
    have hM : (RingHom.ker (evalRingHom x)).primeCompl ≤ nonZeroDivisors k[X] := by
      intro a ha
      change a ∉ RingHom.ker (evalRingHom x) at ha
      have h0 : a ≠ 0 := by
        intro h
        exact ha (h ▸ (Ideal.zero_mem (RingHom.ker (evalRingHom x))))
      rw [mem_nonZeroDivisors_iff]
      constructor
      · intro b hb
        exact (mul_eq_zero.mp hb).resolve_left h0
      · intro b hb
        exact (mul_eq_zero.mp hb).resolve_right h0
    have hinj : Function.Injective (algebraMap k[X] S) :=
      IsLocalization.injective S hM
    simpa only [t, map_sub, map_zero] using
      hinj.ne (sub_ne_zero.mpr (by simpa using Polynomial.X_ne_C x))
  have hhalf : half * 2 = 1 := by
    simpa only [half, ← map_ofNat (algebraMap k S) 2, ← map_mul, map_one] using
      congrArg (algebraMap k S) (inv_mul_cancel₀ h2)
  exact (finiteCrossing_stalkNodeEquiv P x hx hsimple).toRingEquiv.trans
    (localNodeFiberProductEquiv t half ht hhalf)

end HilbertModularity.Hyperelliptic
