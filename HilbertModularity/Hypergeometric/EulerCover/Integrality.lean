/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.BaseChange
public import HilbertModularity.Hypergeometric.EulerCover.ExponentChange

/-! # Integrality of the affine Euler cover

The affine Euler equation is Eisenstein at the coordinate `x`. Its root algebra
over the polynomial ring is a domain, and localization at the branch product
identifies it with the actual affine Euler cover. This is the geometric
integrality prerequisite in [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

variable {K : Type*} [Field K]

private theorem branchPolynomial_coeff_one (N : ℕ) (t : K) :
    (branchPolynomial N 1 t).coeff 1 = 1 := by
  have hg : branchPolynomial N 1 t =
      (X : K[X]) * ((1 - X) ^ (N - 1) * (1 - C t * X)) := by
    simp only [branchPolynomial, pow_one, mul_assoc]
  rw [hg, coeff_X_mul]
  simp [coeff_zero_eq_eval_zero]

private theorem prime_span_X : (Ideal.span {(X : K[X])}).IsPrime := by
  rw [Ideal.span_singleton_prime (Polynomial.X_ne_zero : (X : K[X]) ≠ 0)]
  exact Polynomial.irreducible_X.prime

private def eulerPolynomialOverX (N : ℕ) (t : K) : (K[X])[X] :=
  X ^ N - C (branchPolynomial N 1 t)

private theorem eulerPolynomialOverX_monic (N : ℕ) (t : K) (hN : N ≠ 0) :
    (eulerPolynomialOverX N t).Monic := by
  exact monic_X_pow_sub_C _ hN

private theorem branchPolynomial_dvd_X (N : ℕ) (t : K) :
    (X : K[X]) ∣ branchPolynomial N 1 t := by
  refine ⟨(1 - X) ^ (N - 1) * (1 - C t * X), ?_⟩
  simp only [branchPolynomial, pow_one, mul_assoc]

private theorem eulerPolynomialOverX_eisenstein (N : ℕ) (t : K) (hN : N ≠ 0) :
    (eulerPolynomialOverX N t).IsEisensteinAt (Ideal.span {(X : K[X])}) := by
  have hdeg : (eulerPolynomialOverX N t).natDegree = N := natDegree_X_pow_sub_C
  have hc0 : (eulerPolynomialOverX N t).coeff 0 = -branchPolynomial N 1 t := by
    simp [eulerPolynomialOverX, coeff_X_pow, Ne.symm hN]
  refine ⟨?_, ?_, ?_⟩
  · have hh := (eulerPolynomialOverX_monic N t hN).leadingCoeff
    rw [hh, Ideal.mem_span_singleton]
    simp [X_dvd_iff]
  · intro n hn
    rw [hdeg] at hn
    by_cases hn0 : n = 0
    · subst n
      rw [Ideal.mem_span_singleton]
      rw [hc0]
      exact dvd_neg.mpr (branchPolynomial_dvd_X N t)
    · have hnN : n ≠ N := by omega
      have hc : (eulerPolynomialOverX N t).coeff n = 0 := by
        simp [eulerPolynomialOverX, coeff_X_pow, coeff_C, hn0, hnN]
      simp [hc]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    have hdvdg : (X : K[X]) ^ 2 ∣ branchPolynomial N 1 t := by
      simpa only [hc0, dvd_neg] using hdvd
    have hcoeff := (X_pow_dvd_iff.mp hdvdg) 1 (by norm_num)
    have hg := branchPolynomial_coeff_one N t
    rw [hg] at hcoeff
    exact one_ne_zero hcoeff

private theorem eulerPolynomialOverX_irreducible (N : ℕ) (t : K) (hN : N ≠ 0) :
    Irreducible (eulerPolynomialOverX N t) := by
  exact (eulerPolynomialOverX_eisenstein N t hN).irreducible prime_span_X
    (eulerPolynomialOverX_monic N t hN).isPrimitive
    (by rw [show (eulerPolynomialOverX N t).natDegree = N from natDegree_X_pow_sub_C]; omega)

private theorem eulerRootRing_isDomain (N : ℕ) (t : K) (hN : N ≠ 0) :
    IsDomain (AdjoinRoot (eulerPolynomialOverX N t)) := by
  let hprime : (Ideal.span {eulerPolynomialOverX N t}).IsPrime :=
    (Ideal.span_singleton_prime (eulerPolynomialOverX_monic N t hN).ne_zero).mpr
      (eulerPolynomialOverX_irreducible N t hN).prime
  have := hprime
  change IsDomain ((K[X])[X] ⧸ Ideal.span {eulerPolynomialOverX N t})
  infer_instance

private abbrev EulerRawRing (N : ℕ) (t : K) :=
  AdjoinRoot (eulerPolynomialOverX N t)

private def rawToCover (N : ℕ) (t : K) :
    EulerRawRing N t →+* CoverRing N 1 t :=
  AdjoinRoot.lift (algebraMap K[X] (CoverRing N 1 t)) (coverRoot N 1 t) (by
    simp only [eulerPolynomialOverX, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [coverRoot_pow]
    simp [radicand, IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N 1 t)])

private def rawBranchProduct (N : ℕ) (t : K) : EulerRawRing N t :=
  algebraMap K[X] (EulerRawRing N t) (branchProduct t)

private abbrev EulerRawOpen (N : ℕ) (t : K) :=
  Localization.Away (rawBranchProduct N t)

private def baseToRawOpen (N : ℕ) (t : K) :
    BaseRing t →+* EulerRawOpen N t :=
  Localization.awayLift
    ((algebraMap (EulerRawRing N t) (EulerRawOpen N t)).comp
      (algebraMap K[X] (EulerRawRing N t)))
    (branchProduct t) (by
      change IsUnit (algebraMap (EulerRawRing N t) (EulerRawOpen N t)
        (rawBranchProduct N t))
      exact IsLocalization.Away.algebraMap_isUnit (rawBranchProduct N t))

private theorem rawToCover_branchProduct_isUnit (N : ℕ) (t : K) :
    IsUnit (rawToCover N t (rawBranchProduct N t)) := by
  have hu : IsUnit (algebraMap K[X] (BaseRing t) (branchProduct t)) :=
    IsLocalization.Away.algebraMap_isUnit (branchProduct t)
  have hu' := hu.map (algebraMap (BaseRing t) (CoverRing N 1 t))
  simpa [rawToCover, rawBranchProduct, AdjoinRoot.lift_of,
    IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N 1 t)] using hu'

private def rawOpenToCover (N : ℕ) (t : K) :
    EulerRawOpen N t →+* CoverRing N 1 t :=
  Localization.awayLift (rawToCover N t) (rawBranchProduct N t)
    (rawToCover_branchProduct_isUnit N t)

private theorem baseToRawOpen_radicand (N : ℕ) (t : K) :
    baseToRawOpen N t (radicand N 1 t) =
      algebraMap (EulerRawRing N t) (EulerRawOpen N t)
        (algebraMap K[X] (EulerRawRing N t) (branchPolynomial N 1 t)) := by
  unfold radicand baseToRawOpen
  rw [IsLocalization.Away.lift_eq]
  rfl

private theorem rawRoot_pow (N : ℕ) (t : K) :
    (AdjoinRoot.root (eulerPolynomialOverX N t)) ^ N =
      algebraMap K[X] (EulerRawRing N t) (branchPolynomial N 1 t) := by
  exact AdjoinRoot.root_X_pow_sub_C_pow N (branchPolynomial N 1 t)

private def coverToRawOpen (N : ℕ) (t : K) :
    CoverRing N 1 t →+* EulerRawOpen N t :=
  AdjoinRoot.lift (baseToRawOpen N t)
    (algebraMap (EulerRawRing N t) (EulerRawOpen N t)
      (AdjoinRoot.root (eulerPolynomialOverX N t))) (by
      simp only [coverPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [← map_pow, rawRoot_pow, baseToRawOpen_radicand]
      simp)

private theorem rawOpenToCover_baseToRawOpen (N : ℕ) (t : K)
    (a : BaseRing t) :
    rawOpenToCover N t (baseToRawOpen N t a) =
      algebraMap (BaseRing t) (CoverRing N 1 t) a := by
  have h : (rawOpenToCover N t).comp (baseToRawOpen N t) =
      algebraMap (BaseRing t) (CoverRing N 1 t) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (branchProduct t))
    apply RingHom.ext
    intro p
    simp [baseToRawOpen, rawOpenToCover, rawToCover,
      IsLocalization.Away.lift_eq, AdjoinRoot.lift_of,
      IsScalarTower.algebraMap_apply K[X] (BaseRing t) (CoverRing N 1 t)]
  exact congrArg (fun f : BaseRing t →+* CoverRing N 1 t => f a) h

private theorem rawOpenToCover_coverToRawOpen (N : ℕ) (t : K) :
    (rawOpenToCover N t).comp (coverToRawOpen N t) =
      RingHom.id (CoverRing N 1 t) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change rawOpenToCover N t
        (coverToRawOpen N t (AdjoinRoot.of (coverPolynomial N 1 t) a)) = _
    simpa only [coverToRawOpen, AdjoinRoot.lift_of, RingHom.comp_apply,
      RingHom.id_apply, AdjoinRoot.algebraMap_eq] using
      rawOpenToCover_baseToRawOpen N t a
  · change rawOpenToCover N t (coverToRawOpen N t (coverRoot N 1 t)) = coverRoot N 1 t
    simp [coverToRawOpen, rawOpenToCover, rawToCover, coverRoot,
      AdjoinRoot.lift_root, IsLocalization.Away.lift_eq]

private theorem coverToRawOpen_rawOpenToCover (N : ℕ) (t : K) :
    (coverToRawOpen N t).comp (rawOpenToCover N t) =
      RingHom.id (EulerRawOpen N t) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (rawBranchProduct N t))
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro p
    change coverToRawOpen N t (rawOpenToCover N t
      (algebraMap (EulerRawRing N t) (EulerRawOpen N t)
        (AdjoinRoot.of (eulerPolynomialOverX N t) p))) = _
    rw [show rawOpenToCover N t
        (algebraMap (EulerRawRing N t) (EulerRawOpen N t)
          (AdjoinRoot.of (eulerPolynomialOverX N t) p)) =
          algebraMap K[X] (CoverRing N 1 t) p from by
            simp [rawOpenToCover, rawToCover, IsLocalization.Away.lift_eq,
              AdjoinRoot.lift_of]]
    change coverToRawOpen N t
      (algebraMap (BaseRing t) (CoverRing N 1 t)
        (algebraMap K[X] (BaseRing t) p)) = _
    simp [coverToRawOpen, baseToRawOpen, IsLocalization.Away.lift_eq,
      AdjoinRoot.lift_of, RingHom.comp_apply]
  · change coverToRawOpen N t (rawOpenToCover N t
      (algebraMap (EulerRawRing N t) (EulerRawOpen N t)
        (AdjoinRoot.root (eulerPolynomialOverX N t)))) = _
    simp [rawOpenToCover, rawToCover, coverToRawOpen, coverRoot,
      IsLocalization.Away.lift_eq, AdjoinRoot.lift_root]

private def rawOpenEquivCover (N : ℕ) (t : K) :
    EulerRawOpen N t ≃+* CoverRing N 1 t where
  toFun := rawOpenToCover N t
  invFun := coverToRawOpen N t
  left_inv a := by
    have h := congrArg (fun f : EulerRawOpen N t →+* EulerRawOpen N t => f a)
      (coverToRawOpen_rawOpenToCover N t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  right_inv a := by
    have h := congrArg (fun f : CoverRing N 1 t →+* CoverRing N 1 t => f a)
      (rawOpenToCover_coverToRawOpen N t)
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  map_mul' := map_mul (rawOpenToCover N t)
  map_add' := map_add (rawOpenToCover N t)

private theorem coverToRawOpen_injective (N : ℕ) (t : K) :
    Function.Injective (coverToRawOpen N t) := by
  intro a b h
  have hh := congrArg (rawOpenToCover N t) h
  simpa only [← RingHom.comp_apply, rawOpenToCover_coverToRawOpen,
    RingHom.id_apply] using hh

private theorem branchProduct_ne_zero (t : K) : branchProduct t ≠ 0 := by
  have hc : (branchProduct t).coeff 1 = 1 := by
    rw [branchProduct, mul_assoc, coeff_X_mul]
    simp [coeff_zero_eq_eval_zero]
  intro h
  rw [h] at hc
  have hzero : (1 : K) = 0 := by simpa using hc.symm
  exact one_ne_zero hzero

private theorem rawBranchProduct_ne_zero (N : ℕ) (t : K) (hN : N ≠ 0) :
    rawBranchProduct N t ≠ 0 := by
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hdegree : 0 < (eulerPolynomialOverX N t).degree := by
    rw [eulerPolynomialOverX, degree_X_pow_sub_C hpos]
    exact_mod_cast hpos
  have : FaithfulSMul K[X] (EulerRawRing N t) :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos
      (eulerPolynomialOverX_monic N t hN) hdegree
  intro h
  apply branchProduct_ne_zero t
  exact (FaithfulSMul.algebraMap_injective K[X] (EulerRawRing N t))
    (by simpa only [rawBranchProduct, map_zero] using h)

private theorem isDomain_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] (f : A →+* B) (hf : Function.Injective f) : IsDomain A := by
  have hz : NoZeroDivisors A := by
    constructor
    intro a b hab
    have hh : f a * f b = 0 := by simp [← map_mul, hab]
    rcases mul_eq_zero.mp hh with ha | hb
    · exact Or.inl (hf (by simpa only [map_zero] using ha))
    · exact Or.inr (hf (by simpa only [map_zero] using hb))
  have : NoZeroDivisors A := hz
  have hone : (1 : A) ≠ 0 := by
    intro h
    have hh : (1 : B) = 0 := by simpa using congrArg f h
    exact one_ne_zero hh
  have : Nontrivial A := nontrivial_of_ne 1 0 hone
  exact IsDomain.mk

/-- The actual Euler cover with exponent one is a domain over any coefficient field. -/
theorem coverRing_isDomain_one (N : ℕ) (t : K) (hN : N ≠ 0) :
    IsDomain (CoverRing N 1 t) := by
  have := eulerRootRing_isDomain N t hN
  have : IsDomain (EulerRawOpen N t) :=
    Localization.Away.isDomain (rawBranchProduct_ne_zero N t hN)
  exact isDomain_of_injective (coverToRawOpen N t) (coverToRawOpen_injective N t)

/-- The actual affine Euler cover is a domain for every coprime positive exponent.
The assertion also holds at degenerate parameter values; the manuscript uses
the specializations away from zero and one. -/
theorem coverRing_isDomain (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N) :
    IsDomain (CoverRing N m t) := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨e, _, _⟩ := exists_exponentChangeEquiv_of_coprime t N m hmPos hm hcop
  have : IsDomain (CoverRing N 1 t) := coverRing_isDomain_one N t hN
  exact isDomain_of_injective e.toRingHom e.injective

/-- Every coefficient-field extension of the actual affine Euler cover is a
domain, through the canonical scalar-extension equivalence. -/
theorem coverRing_scalarExtension_isDomain (N m : ℕ) (t : K) (hN : N ≠ 0)
    (hmPos : 1 ≤ m) (hm : m < N) (hcop : m.Coprime N)
    (E : Type*) [Field E] [Algebra K E] :
    IsDomain (E ⊗[K] (CoverRing N m t)) := by
  have : IsDomain (CoverRing N m (algebraMap K E t)) :=
    coverRing_isDomain N m (algebraMap K E t) hN hmPos hm hcop
  exact isDomain_of_injective
    (coverBaseChangeEquiv (R := K) (S := E) N m t).toRingHom
    (coverBaseChangeEquiv (R := K) (S := E) N m t).injective

end HilbertModularity.Hypergeometric.EulerCover
