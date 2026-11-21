/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PlusCurveJacobian
public import HilbertModularity.Hyperelliptic.Scaling
public import HilbertModularity.Hyperelliptic.Projective
public import HilbertModularity.Geometry.SmoothProperCurveExtension

/-! # The plus curve in the scaled coordinate chart

The manuscript's change of coordinates identifies the affine charts of the
plus curve and its scaled double cover. This is the algebraic comparison needed
before extending the map to their proper completions. -/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hyperelliptic

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- A nonconstant affine change of variable preserves separability. -/
private theorem separable_comp_affine {f : K[X]} (hf : f.Separable)
    {a b : K} (ha : a ≠ 0) :
    (f.comp (C a * X + C b)).Separable := by
  let q : K[X] := C a * X + C b
  have hder : (f.comp q).derivative = C a * f.derivative.comp q := by
    rw [derivative_comp]
    simp [q]
  obtain ⟨u, v, huv⟩ := hf
  refine ⟨u.comp q, C a⁻¹ * v.comp q, ?_⟩
  have hcomp := congrArg (fun g : K[X] => g.comp q) huv
  simp only [add_comp, mul_comp, one_comp] at hcomp
  rw [hder]
  have hunit : (C a⁻¹ : K[X]) * C a = 1 := by
    rw [← C_mul, inv_mul_cancel₀ ha, map_one]
  calc
    u.comp q * f.comp q + (C a⁻¹ * v.comp q) * (C a * f.derivative.comp q) =
        u.comp q * f.comp q + v.comp q * f.derivative.comp q := by
          rw [mul_assoc (C a⁻¹), mul_left_comm (v.comp q) (C a), ← mul_assoc, hunit,
            one_mul]
    _ = 1 := hcomp

/-- The branch polynomial of the plus curve becomes the branch polynomial of
the scaled model after `x = ϖu - 2` and `y₀ = ϖ^((p+1)/2)w`.
The factor is `ϖ^(p+1)`, since the printed scaled parameter is `t/ϖ^p`.
See [DarmonRigid, proof of Proposition 1.16] and [TripathiGoswami,
Proposition 4.7 and Appendix A]. -/
theorem plusPolynomial_eval_scaled {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (u t : K) :
    (plusPolynomial p t).eval (realCyclotomicParameter ζ * u - 2) =
      realCyclotomicParameter ζ ^ (p + 1) *
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p)).eval u := by
  rw [plusPolynomial_eq_cyclotomic hp hp2 hζ]
  have hcycl := cyclotomicChebyshevPolynomial_add_two hp hp2 hζ
  have hscale := negTracePolynomial_eval_scaled ζ (hζ.ne_zero hp.ne_zero) p u
  have hbranch : cyclotomicChebyshevPolynomial ζ p + 2 - C (4 * t) =
      (X + 2) * negTracePolynomial ζ p ^ 2 - C (4 * t) := by rw [hcycl]
  rw [hbranch]
  simp only [eval_mul, eval_add, eval_sub, eval_X, eval_C, eval_ofNat,
    eval_pow, finiteBranchPolynomial]
  rw [hscale]
  obtain ⟨d, rfl⟩ := hp.odd_of_ne_two hp2
  rw [show (2 * d + 1 - 1) / 2 = d by omega]
  field_simp
  ring

/-- The coordinate change is an identity of polynomials, so it can be
evaluated in any `K`-algebra, including the quadratic chart coordinate ring. -/
theorem plusPolynomial_comp_scaled {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    (plusPolynomial p t).comp (C (realCyclotomicParameter ζ) * X - C 2) =
      C (realCyclotomicParameter ζ ^ (p + 1)) *
        finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p) := by
  apply Polynomial.funext
  intro u
  simpa only [eval_comp, eval_sub, eval_mul, eval_C, eval_X] using
    plusPolynomial_eval_scaled hp hp2 hζ hϖ u t

/-- The scaled branch roots lie in the real cyclotomic coefficient field. -/
def realScaledRootPolynomial (p : ℕ) [Fact p.Prime] :
    (realCyclotomicField p)[X] :=
  ∏ j ∈ Finset.Icc 1 ((p - 1) / 2), (X - C (realScaledRoot p j))

theorem map_realScaledRootPolynomial (p : ℕ) [Fact p.Prime] :
    (realScaledRootPolynomial p).map (realCyclotomicField p).val.toRingHom =
      scaledRootPolynomial (zeta p) p := by
  simp only [realScaledRootPolynomial, scaledRootPolynomial, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  exact coe_realScaledRoot p j

/-- The branch polynomial used for the integral local scaled model becomes
the branch polynomial of the geometric comparison after passage to its
fraction field. Thus the comparison concerns the same generic curve as the
local special-fibre calculation. -/
theorem map_localScaledRootPolynomial_eq_realScaled (p : ℕ) [Fact p.Prime]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p))) :
    (localScaledRootPolynomial p P).map
      (algebraMap (P.valuationSubringAtPrime (realCyclotomicField p))
        (realCyclotomicField p)) = realScaledRootPolynomial p := by
  rw [map_localScaledRootPolynomial]
  simp only [realScaledRootPolynomial, realScaledRoot]

/-- The real scaling parameter is nonzero in the coefficient field. -/
theorem realCyclotomicScale_ne_zero (p : ℕ) [Fact p.Prime] :
    (2 - tau p 1 : realCyclotomicField p) ≠ 0 := by
  intro h
  have hh := congrArg (fun a : realCyclotomicField p => (a : Qbar)) h
  have hz := (zeta_isPrimitiveRoot p).ne_zero (NeZero.ne p)
  have heq : (2 - tau p 1 : Qbar) = realCyclotomicParameter (zeta p) := by
    rw [realCyclotomicParameter_eq _ hz]
    simp [rootTrace]
  have : realCyclotomicParameter (zeta p) = 0 := by
    rw [← heq]
    change ((2 - tau p 1 : realCyclotomicField p) : Qbar) = 0
    exact hh
  exact (realCyclotomicParameter_zeta_ne_zero p) this

/-- The printed scaled branch identity descends from `Qbar` to the real
cyclotomic field, which is the base field of the selected plus Jacobian. -/
theorem plusPolynomial_comp_realScaled (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (t : realCyclotomicField p) :
    (plusPolynomial p t).comp (C (2 - tau p 1) * X - C 2) =
      C ((2 - tau p 1) ^ (p + 1)) *
        finiteBranchPolynomial (realScaledRootPolynomial p)
          (t / (2 - tau p 1) ^ p) := by
  let ι : realCyclotomicField p →+* Qbar :=
    (realCyclotomicField p).val.toRingHom
  apply Polynomial.map_injective ι ι.injective
  have hz := zeta_isPrimitiveRoot p
  have hϖ := realCyclotomicParameter_zeta_ne_zero p
  have htwo : ι (2 : realCyclotomicField p) = (2 : Qbar) :=
    map_ofNat ι 2
  have hfour : ι (4 : realCyclotomicField p) = (4 : Qbar) :=
    map_ofNat ι 4
  have h := plusPolynomial_comp_scaled (K := Qbar)
    (Fact.out : p.Prime) (by omega) hz hϖ (ι t)
  have hscale : ι (2 - tau p 1) = realCyclotomicParameter (zeta p) := by
    rw [realCyclotomicParameter_eq _ (hz.ne_zero (NeZero.ne p))]
    rw [map_sub, htwo]
    simp [ι, rootTrace, coe_tau]
  have hplus : (plusPolynomial p t).map ι = plusPolynomial p (ι t) := by
    simp only [plusPolynomial, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat,
      Polynomial.map_C, Polynomial.Chebyshev.map_C, map_mul,
      map_sub, map_ofNat]
  have hparameter : ι (t / (2 - tau p 1) ^ p) =
      ι t / realCyclotomicParameter (zeta p) ^ p := by
    simp only [div_eq_mul_inv, map_mul, map_inv₀, map_pow, hscale]
  have hbranch :
      (finiteBranchPolynomial (realScaledRootPolynomial p)
        (t / (2 - tau p 1) ^ p)).map ι =
      finiteBranchPolynomial (scaledRootPolynomial (zeta p) p)
        (ι t / realCyclotomicParameter (zeta p) ^ p) := by
    simp only [finiteBranchPolynomial, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [map_realScaledRootPolynomial]
    rw [map_mul, hfour, hparameter]
  have hsub : (C (2 - tau p 1) * X - C 2 :
      (realCyclotomicField p)[X]).map ι =
      C (realCyclotomicParameter (zeta p)) * X - C 2 := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, hscale, htwo]
  simpa only [Polynomial.map_comp, hplus, hbranch, hsub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    map_pow, hscale] using h

/-- Away from the two singular parameters, the scaled finite branch equation
has simple roots over the real cyclotomic coefficient field. -/
theorem realScaledFiniteBranch_separable (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (t : realCyclotomicField p)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (finiteBranchPolynomial (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p)).Separable := by
  let a : realCyclotomicField p := 2 - tau p 1
  have ha : a ≠ 0 := realCyclotomicScale_ne_zero p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hplus : (plusPolynomial p t).Separable :=
    plusPolynomial_separable p
      ((Fact.out : p.Prime).odd_of_ne_two (by omega))
      (by norm_num) (Nat.cast_ne_zero.mpr hp0) t ht0 ht1
  have hcomp : ((plusPolynomial p t).comp (C a * X - C 2)).Separable := by
    simpa only [sub_eq_add_neg, map_neg] using
      (separable_comp_affine hplus (b := (-2 : realCyclotomicField p)) ha)
  have hpoly := plusPolynomial_comp_realScaled p hp5 t
  change (plusPolynomial p t).comp (C a * X - C 2) =
    C (a ^ (p + 1)) * finiteBranchPolynomial (realScaledRootPolynomial p)
      (t / a ^ p) at hpoly
  rw [hpoly] at hcomp
  exact hcomp.of_mul_right

omit [CharZero K] in
/-- For a monic root polynomial, the reciprocal branch equation is the
reverse of the finite branch equation. -/
theorem infinityBranchPolynomial_eq_reverse {P : K[X]} (hP : P.Monic) (t : K) :
    infinityBranchPolynomial P t = (finiteBranchPolynomial P t).reverse := by
  have hdegree : (X * P ^ 2).natDegree = 2 * P.natDegree + 1 := by
    rw [Polynomial.Monic.natDegree_mul monic_X (hP.pow 2)]
    simp [hP.natDegree_pow]
    omega
  have hX : (X : K[X]).reverse = 1 := by
    simp [Polynomial.reverse, Polynomial.reflect]
  have hfactor : finiteBranchPolynomial P t =
      X * (X * P ^ 2 + C (-(4 * t))) := by
    simp only [finiteBranchPolynomial, map_neg]
    ring
  rw [hfactor, reverse_mul_of_domain, hX, one_mul, reverse_add_C,
    reverse_mul_of_domain, hX, one_mul]
  have hpow : (P ^ 2).reverse = P.reverse ^ 2 := by
    simpa only [pow_two] using reverse_mul_of_domain P P
  rw [hpow, hdegree]
  simp only [infinityBranchPolynomial, map_neg, map_mul]
  ring

/-- The real scaled root polynomial is monic. -/
theorem realScaledRootPolynomial_monic (p : ℕ) [Fact p.Prime] :
    (realScaledRootPolynomial p).Monic := by
  exact monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _

/-- The reciprocal branch equation is separable on the same nonsingular
generic fibre as the finite branch equation. -/
theorem realScaledInfinityBranch_separable (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (t : realCyclotomicField p)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (infinityBranchPolynomial (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p)).Separable := by
  rw [infinityBranchPolynomial_eq_reverse (realScaledRootPolynomial_monic p)]
  exact (realScaledFiniteBranch_separable p hp5 t ht0 ht1).reverse

/-- The polynomial identity holds in every coefficient algebra. -/
theorem plusPolynomial_aeval_scaled {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K)
    {B : Type*} [CommRing B] [Algebra K B] (u : B) :
    aeval (algebraMap K B (realCyclotomicParameter ζ) * u - 2)
      (plusPolynomial p t) =
      (algebraMap K B (realCyclotomicParameter ζ)) ^ (p + 1) *
        aeval u (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p)) := by
  have h := congrArg (fun q : K[X] => aeval u q)
    (plusPolynomial_comp_scaled hp hp2 hζ hϖ t)
  simpa [aeval_comp, map_ofNat] using h

/-- The substitution on the finite affine charts is a map of coordinate
algebras, and therefore a morphism of affine schemes. -/
def scaledChartToPlusChartHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t) →ₐ[K]
      AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p)) := by
  let F := finiteBranchPolynomial (scaledRootPolynomial ζ p)
    (t / realCyclotomicParameter ζ ^ p)
  let B := AlgebraicGeometry.DoubleCover.ChartRing F
  let u : B := algebraMap K[X] B X
  let w : B := QuadraticAlgebra.omega
  have hw : w ^ 2 = aeval u F := by
    have h := AlgebraicGeometry.DoubleCover.chartGenerator_sq F
    change w ^ 2 = algebraMap K[X] B F at h
    have hX : (Algebra.algHom K K[X] B) X = u :=
      Algebra.algHom_apply K K[X] B X
    have hF : (Algebra.algHom K K[X] B) F = algebraMap K[X] B F :=
      Algebra.algHom_apply K K[X] B F
    have heval : aeval u F = algebraMap K[X] B F := by
      calc
        aeval u F = aeval ((Algebra.algHom K K[X] B) X) F := by rw [hX]
        _ = (Algebra.algHom K K[X] B) (aeval (X : K[X]) F) :=
          Polynomial.aeval_algHom_apply _ _ _
        _ = algebraMap K[X] B F := by
          rw [Polynomial.aeval_X_left, AlgHom.id_apply]
          exact hF
    rw [heval]
    exact h
  have hexp : 2 * ((p + 1) / 2) = p + 1 := by
    obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
    omega
  refine AlgebraicGeometry.Hyperelliptic.eval (plusPolynomial p t)
    (algebraMap K B (realCyclotomicParameter ζ) * u - 2)
    ((algebraMap K B (realCyclotomicParameter ζ)) ^ ((p + 1) / 2) * w) ?_
  rw [plusPolynomial_aeval_scaled hp hp2 hζ hϖ t u, ← hw]
  rw [mul_pow, ← pow_mul, show ((p + 1) / 2) * 2 = p + 1 by omega]

/-- The reverse substitution uses the inverse of the cyclotomic parameter
inside the coefficient field. -/
def plusChartToScaledChartHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p)) →ₐ[K]
      AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t) := by
  let F := finiteBranchPolynomial (scaledRootPolynomial ζ p)
    (t / realCyclotomicParameter ζ ^ p)
  let B := AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)
  let a : B := algebraMap K B (realCyclotomicParameter ζ)
  let ai : B := algebraMap K B (realCyclotomicParameter ζ)⁻¹
  let x : B := algebraMap K[X] B X
  let y : B := QuadraticAlgebra.omega
  let u : B := ai * (x + 2)
  let w : B := ai ^ ((p + 1) / 2) * y
  have hai : a * ai = 1 := by
    dsimp [a, ai]
    rw [← map_mul, mul_inv_cancel₀ hϖ, map_one]
  have hx : a * u - 2 = x := by
    dsimp [u]
    rw [← mul_assoc, hai]
    ring
  have hy : y ^ 2 = aeval x (plusPolynomial p t) := by
    have h := AlgebraicGeometry.DoubleCover.chartGenerator_sq (plusPolynomial p t)
    change y ^ 2 = algebraMap K[X] B (plusPolynomial p t) at h
    have hX : (Algebra.algHom K K[X] B) X = x :=
      Algebra.algHom_apply K K[X] B X
    have hF : (Algebra.algHom K K[X] B) (plusPolynomial p t) =
        algebraMap K[X] B (plusPolynomial p t) :=
      Algebra.algHom_apply K K[X] B (plusPolynomial p t)
    have heval : aeval x (plusPolynomial p t) =
        algebraMap K[X] B (plusPolynomial p t) := by
      calc
        aeval x (plusPolynomial p t) =
            aeval ((Algebra.algHom K K[X] B) X) (plusPolynomial p t) := by rw [hX]
        _ = (Algebra.algHom K K[X] B)
            (aeval (X : K[X]) (plusPolynomial p t)) :=
          Polynomial.aeval_algHom_apply _ _ _
        _ = algebraMap K[X] B (plusPolynomial p t) := by
          rw [Polynomial.aeval_X_left, AlgHom.id_apply]
          exact hF
    rw [heval]
    exact h
  have hycoord : a ^ ((p + 1) / 2) * w = y := by
    dsimp [w]
    rw [← mul_assoc, ← mul_pow, hai]
    simp
  have hexp : ((p + 1) / 2) * 2 = p + 1 := by
    obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
    omega
  have heq : a ^ (p + 1) * w ^ 2 = a ^ (p + 1) * aeval u F := by
    have h := hy
    rw [← hx, plusPolynomial_aeval_scaled hp hp2 hζ hϖ t u] at h
    change y ^ 2 = a ^ (p + 1) * aeval u F at h
    rw [← hycoord, mul_pow, ← pow_mul, hexp] at h
    exact h
  have haiPow : ai ^ (p + 1) * a ^ (p + 1) = 1 := by
    rw [← mul_pow, mul_comm ai a, hai]
    simp
  have hw : w ^ 2 = aeval u F := by
    have h := congrArg (fun z : B => ai ^ (p + 1) * z) heq
    simpa only [← mul_assoc, haiPow, one_mul] using h
  exact AlgebraicGeometry.Hyperelliptic.eval F u w hw

theorem scaledChartToPlusChartHom_coordinate {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    scaledChartToPlusChartHom hp hp2 hζ hϖ t
      (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)) X) =
        algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing
          (finiteBranchPolynomial (scaledRootPolynomial ζ p)
            (t / realCyclotomicParameter ζ ^ p))) (realCyclotomicParameter ζ) *
          algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing
            (finiteBranchPolynomial (scaledRootPolynomial ζ p)
              (t / realCyclotomicParameter ζ ^ p))) X - 2 := by
  simp [scaledChartToPlusChartHom]

theorem scaledChartToPlusChartHom_generator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    scaledChartToPlusChartHom hp hp2 hζ hϖ t
      (QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing
        (plusPolynomial p t)) =
      (algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p)))
          (realCyclotomicParameter ζ)) ^ ((p + 1) / 2) * QuadraticAlgebra.omega := by
  simp [scaledChartToPlusChartHom]

theorem plusChartToScaledChartHom_coordinate {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    plusChartToScaledChartHom hp hp2 hζ hϖ t
      (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p))) X) =
        algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing
          (plusPolynomial p t)) (realCyclotomicParameter ζ)⁻¹ *
          (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing
            (plusPolynomial p t)) X + 2) := by
  simp [plusChartToScaledChartHom]

theorem plusChartToScaledChartHom_generator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    plusChartToScaledChartHom hp hp2 hζ hϖ t
      (QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p))) =
      (algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing
        (plusPolynomial p t)) (realCyclotomicParameter ζ)⁻¹) ^ ((p + 1) / 2) *
        QuadraticAlgebra.omega := by
  simp [plusChartToScaledChartHom]

/-- Applying the scaled substitution and then its reverse fixes the original
affine plus chart. -/
theorem plusChartHom_leftInverse {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    (plusChartToScaledChartHom hp hp2 hζ hϖ t).comp
      (scaledChartToPlusChartHom hp hp2 hζ hϖ t) =
      AlgHom.id K (AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)) := by
  let B := AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)
  let a : B := algebraMap K B (realCyclotomicParameter ζ)
  let ai : B := algebraMap K B (realCyclotomicParameter ζ)⁻¹
  have hai : a * ai = 1 := by
    dsimp [a, ai]
    rw [← map_mul, mul_inv_cancel₀ hϖ, map_one]
  apply AlgebraicGeometry.Hyperelliptic.algHom_ext (plusPolynomial p t)
  · simp only [AlgHom.comp_apply, scaledChartToPlusChartHom_coordinate,
      map_sub, map_mul, map_ofNat, AlgHom.commutes,
      plusChartToScaledChartHom_coordinate, AlgHom.id_apply]
    change a * (ai * (algebraMap K[X] B X + 2)) - 2 = algebraMap K[X] B X
    rw [← mul_assoc, hai]
    ring
  · simp only [AlgHom.comp_apply, scaledChartToPlusChartHom_generator,
      map_mul, map_pow, AlgHom.commutes,
      plusChartToScaledChartHom_generator, AlgHom.id_apply]
    change a ^ ((p + 1) / 2) * (ai ^ ((p + 1) / 2) *
      (QuadraticAlgebra.omega : B)) = QuadraticAlgebra.omega
    rw [← mul_assoc, ← mul_pow, hai]
    simp

/-- The reverse substitution also fixes the scaled affine chart. -/
theorem plusChartHom_rightInverse {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    (scaledChartToPlusChartHom hp hp2 hζ hϖ t).comp
      (plusChartToScaledChartHom hp hp2 hζ hϖ t) =
      AlgHom.id K (AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p))) := by
  let F := finiteBranchPolynomial (scaledRootPolynomial ζ p)
    (t / realCyclotomicParameter ζ ^ p)
  let B := AlgebraicGeometry.DoubleCover.ChartRing F
  let a : B := algebraMap K B (realCyclotomicParameter ζ)
  let ai : B := algebraMap K B (realCyclotomicParameter ζ)⁻¹
  have hai : ai * a = 1 := by
    dsimp [a, ai]
    rw [← map_mul, inv_mul_cancel₀ hϖ, map_one]
  apply AlgebraicGeometry.Hyperelliptic.algHom_ext F
  · simp only [F, AlgHom.comp_apply, plusChartToScaledChartHom_coordinate,
      map_mul, map_add, map_ofNat, AlgHom.commutes,
      scaledChartToPlusChartHom_coordinate, AlgHom.id_apply]
    change ai * (a * algebraMap K[X] B X - 2 + 2) = algebraMap K[X] B X
    rw [sub_add_cancel, ← mul_assoc, hai]
    simp
  · simp only [F, AlgHom.comp_apply, plusChartToScaledChartHom_generator,
      map_mul, map_pow, AlgHom.commutes,
      scaledChartToPlusChartHom_generator, AlgHom.id_apply]
    change ai ^ ((p + 1) / 2) * (a ^ ((p + 1) / 2) *
      (QuadraticAlgebra.omega : B)) = QuadraticAlgebra.omega
    rw [← mul_assoc, ← mul_pow, hai]
    simp

/-- The two finite affine charts are isomorphic over the coefficient field.
The maps are the exact coordinate change used in the scaled model. -/
def plusScaledChartAlgEquiv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t) ≃ₐ[K]
      AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p)) :=
  AlgEquiv.ofAlgHom
    (scaledChartToPlusChartHom hp hp2 hζ hϖ t)
    (plusChartToScaledChartHom hp hp2 hζ hϖ t)
    (plusChartHom_rightInverse hp hp2 hζ hϖ t)
    (plusChartHom_leftInverse hp hp2 hζ hϖ t)

/-- The algebraic coordinate change gives an isomorphism of the actual finite
affine schemes, over the coefficient field. -/
def scaledAffineChartIso {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial (scaledRootPolynomial ζ p)
        (t / realCyclotomicParameter ζ ^ p)))) ≅
    Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
      (plusPolynomial p t))) :=
  Scheme.Spec.mapIso (plusScaledChartAlgEquiv hp hp2 hζ hϖ t).toCommRingCatIso.op

/-- The invertible coordinate substitution identifies the two affine branch
equations, with no restriction on the scaled parameter beyond `ϖ ≠ 0`. -/
theorem plusEquation_scaled_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (u w t : K) :
    (realCyclotomicParameter ζ ^ ((p + 1) / 2) * w) ^ 2 =
      (plusPolynomial p t).eval (realCyclotomicParameter ζ * u - 2) ↔
    w ^ 2 = (finiteBranchPolynomial (scaledRootPolynomial ζ p)
      (t / realCyclotomicParameter ζ ^ p)).eval u := by
  rw [plusPolynomial_eval_scaled hp hp2 hζ hϖ]
  have hexp : 2 * ((p + 1) / 2) = p + 1 := by
    obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
    omega
  rw [mul_pow, ← pow_mul, show ((p + 1) / 2) * 2 = p + 1 by omega]
  constructor
  · exact mul_left_cancel₀ (pow_ne_zero _ hϖ)
  · intro h
    rw [h]

/-- The finite affine charts are isomorphic as sets of solutions through the
manuscript's invertible coordinate change. The corresponding isomorphism of
proper curves requires extension across the points at infinity. -/
def scaledAffineSolutionsEquiv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    AlgebraicGeometry.Hyperelliptic.AffineSolutions
      (finiteBranchPolynomial (scaledRootPolynomial ζ p)
        (t / realCyclotomicParameter ζ ^ p)) ≃
    AlgebraicGeometry.Hyperelliptic.AffineSolutions (plusPolynomial p t) where
  toFun q :=
    ⟨(realCyclotomicParameter ζ * q.val.1 - 2,
      realCyclotomicParameter ζ ^ ((p + 1) / 2) * q.val.2),
      (plusEquation_scaled_iff hp hp2 hζ hϖ q.val.1 q.val.2 t).mpr q.property⟩
  invFun q :=
    ⟨((q.val.1 + 2) / realCyclotomicParameter ζ,
      q.val.2 / realCyclotomicParameter ζ ^ ((p + 1) / 2)), by
      apply (plusEquation_scaled_iff hp hp2 hζ hϖ _ _ t).mp
      have hx : realCyclotomicParameter ζ *
          ((q.val.1 + 2) / realCyclotomicParameter ζ) - 2 = q.val.1 := by
        field_simp
        ring
      have hy : realCyclotomicParameter ζ ^ ((p + 1) / 2) *
          (q.val.2 / realCyclotomicParameter ζ ^ ((p + 1) / 2)) = q.val.2 := by
        field_simp
      rw [hx, hy]
      exact q.property⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · dsimp
      field_simp
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · dsimp
      field_simp

/-- The scaled origin is the distinguished rational branch point. -/
def scaledBranchSolution {p : ℕ} {ζ : K} (t : K) :
    AlgebraicGeometry.Hyperelliptic.AffineSolutions
      (finiteBranchPolynomial (scaledRootPolynomial ζ p) t) :=
  ⟨⟨0, 0⟩, by simp [finiteBranchPolynomial]⟩

/-- The chosen branch point is carried by the proved affine coordinate
change, with no choice of a point at infinity. -/
theorem scaledBranchSolution_maps_to_plus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    scaledAffineSolutionsEquiv hp hp2 hζ hϖ t
      (scaledBranchSolution (ζ := ζ)
        (t / realCyclotomicParameter ζ ^ p)) =
      plusBranchSolution p t := by
  apply Subtype.ext
  rw [plusBranchSolution_val]
  change (realCyclotomicParameter ζ * 0 - 2,
    realCyclotomicParameter ζ ^ ((p + 1) / 2) * 0) = (-2, 0)
  simp

/-- The proper scaled double cover, regarded as a curve over its coefficient
field. This is the generic fibre of the scaled model, without any assertion
about the integral special fibre. -/
def scaledModelToSpec (P : K[X]) (t : K) :
    scaledDoubleCover P t ⟶ Spec (CommRingCat.of K) :=
  scaledDoubleCoverProjection P t ≫ ProjectiveLine.toSpec K

omit [CharZero K] in
/-- The scaled generic curve's structure map in its defining two-chart form. -/
theorem scaledModelToSpec_eq (P : K[X]) (t : K) :
    scaledModelToSpec P t =
      AlgebraicGeometry.DoubleCover.toProjectiveLine
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫ ProjectiveLine.toSpec K := by
  unfold scaledModelToSpec
  exact congrArg (fun f => f ≫ ProjectiveLine.toSpec K)
    (scaledDoubleCoverProjection_eq P t)

instance scaledModelToSpec_isProper (P : K[X]) (t : K) :
    IsProper (scaledModelToSpec P t) :=
  AlgebraicGeometry.DoubleCover.toSpec_isProper
    (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
    (P.natDegree + 1) (branch_transition P t)

/-- The finite scaled equation is an actual open subscheme of its proper
completion. -/
def scaledAffineInclusion (P : K[X]) (t : K) :
    Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial P t))) ⟶ scaledDoubleCover P t :=
  AlgebraicGeometry.DoubleCover.finiteChart
    (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
    (P.natDegree + 1) (branch_transition P t)

instance scaledAffineInclusion_isOpenImmersion (P : K[X]) (t : K) :
    IsOpenImmersion (scaledAffineInclusion P t) :=
  AlgebraicGeometry.DoubleCover.finiteChart_isOpenImmersion
    (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
    (P.natDegree + 1) (branch_transition P t)

omit [CharZero K] in
/-- The proven affine comparison is between dense opens of the two proper
curves. A global isomorphism still needs extension across infinity. -/
theorem scaledAffineInclusion_denseRange (P : K[X]) (t : K) :
    DenseRange (scaledAffineInclusion P t) :=
  AlgebraicGeometry.DoubleCover.finiteChart_denseRange
    (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
    (P.natDegree + 1) (branch_transition P t)

omit [CharZero K] in
/-- The affine coordinate change respects the structure maps to the
coefficient field. This is the base compatibility required for a comparison
of proper curves. -/
theorem plusAffineInclusion_toSpec (p : ℕ) (hp : Odd p) (t : K) :
    plusAffineInclusion p hp t ≫ plusCurveToSpec p hp t =
      Spec.map (CommRingCat.ofHom (algebraMap K
        (AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)))) := by
  change AlgebraicGeometry.DoubleCover.finiteChart
      (plusPolynomial p t) (plusPolynomial p t).reverse ((p + 1) / 2)
      (AlgebraicGeometry.Hyperelliptic.reverse_transition _ _
        (plusPolynomial_evenDegree p hp t)) ≫
      (AlgebraicGeometry.DoubleCover.toProjectiveLine
        (plusPolynomial p t) (plusPolynomial p t).reverse ((p + 1) / 2)
        (AlgebraicGeometry.Hyperelliptic.reverse_transition _ _
          (plusPolynomial_evenDegree p hp t)) ≫ ProjectiveLine.toSpec K) = _
  rw [← Category.assoc, AlgebraicGeometry.DoubleCover.finiteChart_toProjectiveLine,
    AlgebraicGeometry.DoubleCover.finiteProjection_toSpec]

omit [CharZero K] in
/-- The finite chart of the scaled model has its canonical coefficient-field map. -/
theorem scaledAffineInclusion_toSpec (P : K[X]) (t : K) :
    scaledAffineInclusion P t ≫ scaledModelToSpec P t =
      Spec.map (CommRingCat.ofHom (algebraMap K
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)))) := by
  change AlgebraicGeometry.DoubleCover.finiteChart
      (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
      (P.natDegree + 1) (branch_transition P t) ≫
      (AlgebraicGeometry.DoubleCover.toProjectiveLine
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫ ProjectiveLine.toSpec K) = _
  rw [← Category.assoc, AlgebraicGeometry.DoubleCover.finiteChart_toProjectiveLine,
    AlgebraicGeometry.DoubleCover.finiteProjection_toSpec]

/-- Separability of the finite branch equation makes both charts of the
proper scaled curve smooth over the coefficient field. Monicity identifies
the reciprocal equation with the reverse polynomial. -/
theorem scaledModelToSpec_smooth_of_separable (P : K[X]) (hP : P.Monic)
    (t : K) (hF : (finiteBranchPolynomial P t).Separable) :
    Smooth (scaledModelToSpec P t) := by
  let : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (AlgebraicGeometry.DoubleCover.openCover
      (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
      (P.natDegree + 1) (branch_transition P t))
  intro b
  cases b
  · change Smooth (AlgebraicGeometry.DoubleCover.finiteChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫
      (AlgebraicGeometry.DoubleCover.toProjectiveLine
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫
          ProjectiveLine.toSpec K))
    rw [← Category.assoc, AlgebraicGeometry.DoubleCover.finiteChart_toProjectiveLine,
      AlgebraicGeometry.DoubleCover.finiteProjection_toSpec]
    exact AlgebraicGeometry.Hyperelliptic.smooth_chart_toSpec _ hF (by norm_num)
  · change Smooth (AlgebraicGeometry.DoubleCover.infinityChart
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫
      (AlgebraicGeometry.DoubleCover.toProjectiveLine
        (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
        (P.natDegree + 1) (branch_transition P t) ≫
          ProjectiveLine.toSpec K))
    rw [← Category.assoc, AlgebraicGeometry.DoubleCover.infinityChart_toProjectiveLine,
      AlgebraicGeometry.DoubleCover.infinityProjection_toSpec]
    have hG : (infinityBranchPolynomial P t).Separable := by
      rw [infinityBranchPolynomial_eq_reverse hP]
      exact hF.reverse
    exact AlgebraicGeometry.Hyperelliptic.smooth_chart_toSpec _ hG (by norm_num)

theorem scaledAffineChartIso_over {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K) :
    (scaledAffineChartIso hp hp2 hζ hϖ t).hom ≫
      plusAffineInclusion p (hp.odd_of_ne_two hp2) t ≫
        plusCurveToSpec p (hp.odd_of_ne_two hp2) t =
    scaledAffineInclusion (scaledRootPolynomial ζ p)
        (t / realCyclotomicParameter ζ ^ p) ≫
      scaledModelToSpec (scaledRootPolynomial ζ p)
        (t / realCyclotomicParameter ζ ^ p) := by
  rw [plusAffineInclusion_toSpec, scaledAffineInclusion_toSpec]
  change Spec.map (CommRingCat.ofHom
      (plusScaledChartAlgEquiv hp hp2 hζ hϖ t).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K
        (AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)))) = _
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (plusScaledChartAlgEquiv hp hp2 hζ hϖ t).commutes a

/-- The proved affine coordinate change extends to an isomorphism of the
proper curves when the scaled completion has the expected integral smooth
curve structure. These geometric hypotheses are explicit because the scaled
model is also used over valuation rings where its total space need not be
regular. The extension step is the standard smooth proper curve theorem in
`SmoothProperCurveExtension`. -/
theorem exists_scaledModelIso_plusCurve {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    [IsIntegral (scaledDoubleCover (scaledRootPolynomial ζ p)
      (t / realCyclotomicParameter ζ ^ p))]
    [SmoothOfRelativeDimension 1
      (scaledModelToSpec (scaledRootPolynomial ζ p)
        (t / realCyclotomicParameter ζ ^ p))]
    [IsIntegral (plusCurve p (hp.odd_of_ne_two hp2) t)] :
    ∃ e : scaledDoubleCover (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p) ≅
        plusCurve p (hp.odd_of_ne_two hp2) t,
      e.hom ≫ plusCurveToSpec p (hp.odd_of_ne_two hp2) t =
        scaledModelToSpec (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p) ∧
      scaledAffineInclusion (scaledRootPolynomial ζ p)
          (t / realCyclotomicParameter ζ ^ p) ≫ e.hom =
        (scaledAffineChartIso hp hp2 hζ hϖ t).hom ≫
          plusAffineInclusion p (hp.odd_of_ne_two hp2) t := by
  let : Smooth (plusCurveToSpec p (hp.odd_of_ne_two hp2) t) :=
    plusCurveToSpec_smooth p (hp.odd_of_ne_two hp2) t ht0 ht1
  have hj : IsOpenImmersion
      ((scaledAffineChartIso hp hp2 hζ hϖ t).hom ≫
        plusAffineInclusion p (hp.odd_of_ne_two hp2) t) := inferInstance
  exact Scheme.exists_iso_extending_dense_open_of_smooth_proper_curve
    (scaledModelToSpec (scaledRootPolynomial ζ p)
      (t / realCyclotomicParameter ζ ^ p))
    (plusCurveToSpec p (hp.odd_of_ne_two hp2) t)
    (scaledAffineInclusion (scaledRootPolynomial ζ p)
      (t / realCyclotomicParameter ζ ^ p))
    (scaledAffineInclusion_denseRange (scaledRootPolynomial ζ p)
      (t / realCyclotomicParameter ζ ^ p))
    ((scaledAffineChartIso hp hp2 hζ hϖ t).hom ≫
      plusAffineInclusion p (hp.odd_of_ne_two hp2) t)
    (by simpa only [Category.assoc] using
      scaledAffineChartIso_over hp hp2 hζ hϖ t)

omit [CharZero K] in
/-- The generator relation of a finite quadratic chart, expressed using
polynomial evaluation at its affine coordinate. -/
theorem chartGenerator_sq_aeval (F : K[X]) :
    (QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing F) ^ 2 =
      aeval (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing F) X) F := by
  let B := AlgebraicGeometry.DoubleCover.ChartRing F
  have h := AlgebraicGeometry.DoubleCover.chartGenerator_sq F
  change (QuadraticAlgebra.omega : B) ^ 2 = algebraMap K[X] B F at h
  let f : K[X] →ₐ[K] B := Algebra.algHom K K[X] B
  have hx : f X = algebraMap K[X] B X := Algebra.algHom_apply K K[X] B X
  have heval : aeval (algebraMap K[X] B X) F = algebraMap K[X] B F := by
    rw [← hx, Polynomial.aeval_algHom_apply]
    rw [Polynomial.aeval_X_left, AlgHom.id_apply]
    exact Algebra.algHom_apply K K[X] B F
  exact h.trans heval.symm

/-- An affine change `x = a*u-b`, `y = d*w` between double-cover equations.
The polynomial identity records exactly the required compatibility. -/
def chartRescaleForward (F G : K[X]) (a b d : K)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    AlgebraicGeometry.DoubleCover.ChartRing F →ₐ[K]
      AlgebraicGeometry.DoubleCover.ChartRing G := by
  let B := AlgebraicGeometry.DoubleCover.ChartRing G
  let u : B := algebraMap K[X] B X
  let w : B := QuadraticAlgebra.omega
  refine AlgebraicGeometry.Hyperelliptic.eval F
    (algebraMap K B a * u - algebraMap K B b) (algebraMap K B d * w) ?_
  have h := congrArg (fun P : K[X] => aeval u P) hpoly
  have heval : aeval (algebraMap K B a * u - algebraMap K B b) F =
      algebraMap K B (d ^ 2) * aeval u G := by
    simpa [aeval_comp] using h
  rw [heval, ← chartGenerator_sq_aeval G]
  rw [mul_pow, ← map_pow]

/-- Reverse affine substitution in the coefficient field. -/
def chartRescaleBackward (F G : K[X]) (a b d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    AlgebraicGeometry.DoubleCover.ChartRing G →ₐ[K]
      AlgebraicGeometry.DoubleCover.ChartRing F := by
  let B := AlgebraicGeometry.DoubleCover.ChartRing F
  let aa : B := algebraMap K B a
  let bb : B := algebraMap K B b
  let dd : B := algebraMap K B d
  let ai : B := algebraMap K B a⁻¹
  let di : B := algebraMap K B d⁻¹
  let x : B := algebraMap K[X] B X
  let y : B := QuadraticAlgebra.omega
  let u : B := ai * (x + bb)
  let w : B := di * y
  have hai : aa * ai = 1 := by
    dsimp [aa, ai]
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have hdi : dd * di = 1 := by
    dsimp [dd, di]
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  have hx : aa * u - bb = x := by
    dsimp [u]
    rw [← mul_assoc, hai]
    ring
  have hy : dd * w = y := by
    dsimp [w]
    rw [← mul_assoc, hdi]
    simp
  have heval := congrArg (fun P : K[X] => aeval u P) hpoly
  have hF : aeval (aa * u - bb) F = dd ^ 2 * aeval u G := by
    simpa [aa, bb, dd, aeval_comp, ← map_pow] using heval
  have hG : w ^ 2 = aeval u G := by
    rw [hx, ← chartGenerator_sq_aeval F] at hF
    change y ^ 2 = dd ^ 2 * aeval u G at hF
    rw [← hy, mul_pow] at hF
    have hdiPow : di ^ 2 * dd ^ 2 = 1 := by
      rw [← mul_pow, mul_comm di dd]
      change (dd * di) ^ 2 = 1
      simp [hdi]
    have hh := congrArg (fun z : B => di ^ 2 * z) hF
    simpa only [← mul_assoc, hdiPow, one_mul] using hh
  exact AlgebraicGeometry.Hyperelliptic.eval G u w hG

omit [CharZero K] in
theorem chartRescaleForward_coordinate (F G : K[X]) (a b d : K)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    chartRescaleForward F G a b d hpoly
      (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing F) X) =
      algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing G) a *
        algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing G) X -
        algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing G) b := by
  simp [chartRescaleForward]

omit [CharZero K] in
theorem chartRescaleForward_generator (F G : K[X]) (a b d : K)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    chartRescaleForward F G a b d hpoly
      (QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing F) =
      algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing G) d *
        QuadraticAlgebra.omega := by
  simp [chartRescaleForward]

omit [CharZero K] in
theorem chartRescaleBackward_coordinate (F G : K[X]) (a b d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    chartRescaleBackward F G a b d ha hd hpoly
      (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing G) X) =
      algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing F) a⁻¹ *
        (algebraMap K[X] (AlgebraicGeometry.DoubleCover.ChartRing F) X +
          algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing F) b) := by
  simp [chartRescaleBackward]

omit [CharZero K] in
theorem chartRescaleBackward_generator (F G : K[X]) (a b d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    chartRescaleBackward F G a b d ha hd hpoly
      (QuadraticAlgebra.omega : AlgebraicGeometry.DoubleCover.ChartRing G) =
      algebraMap K (AlgebraicGeometry.DoubleCover.ChartRing F) d⁻¹ *
        QuadraticAlgebra.omega := by
  simp [chartRescaleBackward]

omit [CharZero K] in
theorem chartRescale_leftInverse (F G : K[X]) (a b d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    (chartRescaleBackward F G a b d ha hd hpoly).comp
      (chartRescaleForward F G a b d hpoly) =
      AlgHom.id K (AlgebraicGeometry.DoubleCover.ChartRing F) := by
  let B := AlgebraicGeometry.DoubleCover.ChartRing F
  let aa : B := algebraMap K B a
  let ai : B := algebraMap K B a⁻¹
  let dd : B := algebraMap K B d
  let di : B := algebraMap K B d⁻¹
  have hai : aa * ai = 1 := by
    dsimp [aa, ai]
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have hdi : dd * di = 1 := by
    dsimp [dd, di]
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  apply AlgebraicGeometry.Hyperelliptic.algHom_ext F
  · simp only [AlgHom.comp_apply, chartRescaleForward_coordinate, map_sub,
      map_mul, AlgHom.commutes, chartRescaleBackward_coordinate, AlgHom.id_apply]
    change aa * (ai * (algebraMap K[X] B X + algebraMap K B b)) -
      algebraMap K B b = algebraMap K[X] B X
    rw [← mul_assoc, hai]
    ring
  · simp only [AlgHom.comp_apply, chartRescaleForward_generator, map_mul,
      AlgHom.commutes, chartRescaleBackward_generator, AlgHom.id_apply]
    change dd * (di * (QuadraticAlgebra.omega : B)) = QuadraticAlgebra.omega
    rw [← mul_assoc, hdi]
    simp

omit [CharZero K] in
theorem chartRescale_rightInverse (F G : K[X]) (a b d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    (chartRescaleForward F G a b d hpoly).comp
      (chartRescaleBackward F G a b d ha hd hpoly) =
      AlgHom.id K (AlgebraicGeometry.DoubleCover.ChartRing G) := by
  let B := AlgebraicGeometry.DoubleCover.ChartRing G
  let aa : B := algebraMap K B a
  let ai : B := algebraMap K B a⁻¹
  let dd : B := algebraMap K B d
  let di : B := algebraMap K B d⁻¹
  have hai : ai * aa = 1 := by
    dsimp [aa, ai]
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hdi : di * dd = 1 := by
    dsimp [dd, di]
    rw [← map_mul, inv_mul_cancel₀ hd, map_one]
  apply AlgebraicGeometry.Hyperelliptic.algHom_ext G
  · simp only [AlgHom.comp_apply, chartRescaleBackward_coordinate, map_mul,
      map_add, AlgHom.commutes, chartRescaleForward_coordinate, AlgHom.id_apply]
    change ai * (aa * algebraMap K[X] B X - algebraMap K B b +
      algebraMap K B b) = algebraMap K[X] B X
    rw [sub_add_cancel, ← mul_assoc, hai]
    simp
  · simp only [AlgHom.comp_apply, chartRescaleBackward_generator, map_mul,
      AlgHom.commutes, chartRescaleForward_generator, AlgHom.id_apply]
    change di * (dd * (QuadraticAlgebra.omega : B)) = QuadraticAlgebra.omega
    rw [← mul_assoc, hdi]
    simp

/-- The algebraic coordinate substitution is an equivalence of finite affine
double-cover charts whenever its scale factors are units. -/
def chartRescaleAlgEquiv (F G : K[X]) (a b d : K)
    (ha : a ≠ 0) (hd : d ≠ 0)
    (hpoly : F.comp (C a * X - C b) = C (d ^ 2) * G) :
    AlgebraicGeometry.DoubleCover.ChartRing F ≃ₐ[K]
      AlgebraicGeometry.DoubleCover.ChartRing G :=
  AlgEquiv.ofAlgHom
    (chartRescaleForward F G a b d hpoly)
    (chartRescaleBackward F G a b d ha hd hpoly)
    (chartRescale_rightInverse F G a b d ha hd hpoly)
    (chartRescale_leftInverse F G a b d ha hd hpoly)

/-- The finite affine chart of the printed scaled model is isomorphic over
`K_p` to the finite chart of the actual plus curve. The scale and every
coefficient belong to the real cyclotomic field. -/
def realScaledChartAlgEquiv (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (t : realCyclotomicField p) :
    AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t) ≃ₐ[realCyclotomicField p]
      AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (realScaledRootPolynomial p)
          (t / (2 - tau p 1) ^ p)) := by
  let a : realCyclotomicField p := 2 - tau p 1
  let d : realCyclotomicField p := a ^ ((p + 1) / 2)
  have ha : a ≠ 0 := realCyclotomicScale_ne_zero p
  have hd : d ≠ 0 := pow_ne_zero _ ha
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpow : d ^ 2 = a ^ (p + 1) := by
    dsimp [d]
    rw [← pow_mul]
    congr 1
    obtain ⟨k, hk⟩ := hodd
    omega
  have hpoly : (plusPolynomial p t).comp (C a * X - C 2) =
      C (d ^ 2) * finiteBranchPolynomial (realScaledRootPolynomial p)
        (t / a ^ p) := by
    rw [hpow]
    exact plusPolynomial_comp_realScaled p hp5 t
  exact chartRescaleAlgEquiv (plusPolynomial p t)
    (finiteBranchPolynomial (realScaledRootPolynomial p) (t / a ^ p))
    a 2 d ha hd hpoly

/-- The same real-field affine equivalence, contravariantly on schemes. -/
def realScaledAffineChartIso (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (t : realCyclotomicField p) :
    Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
      (finiteBranchPolynomial (realScaledRootPolynomial p)
        (t / (2 - tau p 1) ^ p)))) ≅
    Spec (CommRingCat.of (AlgebraicGeometry.DoubleCover.ChartRing
      (plusPolynomial p t))) :=
  Scheme.Spec.mapIso (realScaledChartAlgEquiv p hp5 t).toCommRingCatIso.op

/-- The real-field chart isomorphism preserves the structure morphism to
`Spec K_p`, as required to compare the proper completions and Jacobians. -/
theorem realScaledAffineChartIso_over (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (t : realCyclotomicField p) :
    (realScaledAffineChartIso p hp5 t).hom ≫
      plusAffineInclusion p ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t ≫
        plusCurveToSpec p ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t =
    scaledAffineInclusion (realScaledRootPolynomial p)
        (t / (2 - tau p 1) ^ p) ≫
      scaledModelToSpec (realScaledRootPolynomial p)
        (t / (2 - tau p 1) ^ p) := by
  rw [plusAffineInclusion_toSpec, scaledAffineInclusion_toSpec]
  change Spec.map (CommRingCat.ofHom
      (realScaledChartAlgEquiv p hp5 t).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (realCyclotomicField p)
        (AlgebraicGeometry.DoubleCover.ChartRing (plusPolynomial p t)))) = _
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (realScaledChartAlgEquiv p hp5 t).commutes z

/-- The finite chart of the printed scaled generic curve is smooth at every
nonsingular parameter. This uses the actual affine coordinate isomorphism,
so it does not assert smoothness of the reciprocal chart or of an integral
model over a valuation ring. -/
theorem realScaledFiniteChart_smooth (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (t : realCyclotomicField p)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Smooth (scaledAffineInclusion (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p) ≫
        scaledModelToSpec (realScaledRootPolynomial p)
          (t / (2 - tau p 1) ^ p)) := by
  rw [← realScaledAffineChartIso_over p hp5 t]
  let : Smooth (plusCurveToSpec p
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t) :=
    plusCurveToSpec_smooth p
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t ht0 ht1
  infer_instance

/-- The entire proper scaled generic curve is smooth over the real cyclotomic
field at every nonsingular parameter. Separability controls both the finite
and reciprocal charts; this says nothing about regularity of an integral model
over a valuation ring. -/
theorem realScaledModelToSpec_smooth (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (t : realCyclotomicField p)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Smooth (scaledModelToSpec (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p)) :=
  scaledModelToSpec_smooth_of_separable
    (realScaledRootPolynomial p) (realScaledRootPolynomial_monic p)
    (t / (2 - tau p 1) ^ p)
    (realScaledFiniteBranch_separable p hp5 t ht0 ht1)

/-- The affine change of coordinates over `K_p` extends across infinity for
the smooth proper generic fibres. The hypotheses concern the generic fibres;
they do not assert regularity of an integral model over a valuation ring.
This is the comparison needed to apply the Jacobian property of the selected
plus family to the printed scaled curve. -/
theorem exists_realScaledModelIso_plusCurve (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (t : realCyclotomicField p)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    [IsIntegral (scaledDoubleCover (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p))]
    [SmoothOfRelativeDimension 1
      (scaledModelToSpec (realScaledRootPolynomial p)
        (t / (2 - tau p 1) ^ p))]
    [IsIntegral (plusCurve p ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t)] :
    ∃ e : scaledDoubleCover (realScaledRootPolynomial p)
          (t / (2 - tau p 1) ^ p) ≅
        plusCurve p ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t,
      e.hom ≫ plusCurveToSpec p
          ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t =
        scaledModelToSpec (realScaledRootPolynomial p)
          (t / (2 - tau p 1) ^ p) ∧
      scaledAffineInclusion (realScaledRootPolynomial p)
          (t / (2 - tau p 1) ^ p) ≫ e.hom =
        (realScaledAffineChartIso p hp5 t).hom ≫
          plusAffineInclusion p
            ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t := by
  let : Smooth (plusCurveToSpec p
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t) :=
    plusCurveToSpec_smooth p
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t ht0 ht1
  have hj : IsOpenImmersion
      ((realScaledAffineChartIso p hp5 t).hom ≫
        plusAffineInclusion p
          ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t) := inferInstance
  exact Scheme.exists_iso_extending_dense_open_of_smooth_proper_curve
    (scaledModelToSpec (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p))
    (plusCurveToSpec p
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t)
    (scaledAffineInclusion (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p))
    (scaledAffineInclusion_denseRange (realScaledRootPolynomial p)
      (t / (2 - tau p 1) ^ p))
    ((realScaledAffineChartIso p hp5 t).hom ≫
      plusAffineInclusion p
        ((Fact.out : p.Prime).odd_of_ne_two (by omega)) t)
    (by simpa only [Category.assoc] using
      realScaledAffineChartIso_over p hp5 t)

end HilbertModularity.Hyperelliptic
