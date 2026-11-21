/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.CyclotomicPolynomial
public import HilbertModularity.NumberTheory.RealCyclotomicUnits

/-! # Changes of coordinates and cusp scaling -/

@[expose] public section

namespace HilbertModularity.Hyperelliptic

open Polynomial Finset HilbertModularity.Cyclotomic

section

variable {K : Type*} [Field K]

/-- [TripathiGoswami], Proof of Proposition 4.7: with `y₀ = 2y + (x+2) g₀(x)`, the plus curve
`y₀² = (x + 2)(f(x) + 2 - 4t)` becomes `y² + (x+2) g₀(x) y + t(x+2) = 0`. -/
theorem plus_curve_transform [CharZero K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (x y t : K) :
    (2 * y + (x + 2) * (negTracePolynomial ζ p).eval x) ^ 2 = (x + 2) * ((cyclotomicChebyshevPolynomial ζ p).eval x + 2 - 4 * t) ↔
      y ^ 2 + (x + 2) * (negTracePolynomial ζ p).eval x * y + t * (x + 2) = 0 := by
  have h := congrArg (eval x) (cyclotomicChebyshevPolynomial_add_two hp hp2 hζ)
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  constructor
  · intro H
    linear_combination (1 / 4 : K) * H + (1 / 4 : K) * (x + 2) * h
  · intro H
    linear_combination 4 * H - (x + 2) * h

/-- `P(u) = ∏_{j=1}^{d} (u - r_j)` (Lemma 4.6). -/
noncomputable def scaledRootPolynomial (ζ : K) (p : ℕ) : K[X] :=
  ∏ j ∈ Icc 1 ((p - 1) / 2), (X - C (cyclotomicUnitRatio ζ j))

/-- The scaled polynomial in its quotient-root presentation. -/
theorem scaledRootPolynomial_eq_prod_div (ζ : K) (hζ : ζ ≠ 0) (hϖ : realCyclotomicParameter ζ ≠ 0) (p : ℕ) :
    scaledRootPolynomial ζ p =
      ∏ j ∈ Icc 1 ((p - 1) / 2), (X - C ((2 - rootTrace ζ j) / realCyclotomicParameter ζ)) := by
  simp only [scaledRootPolynomial, cyclotomicUnitRatio_eq_div ζ hζ hϖ]

/-- [TripathiGoswami], Proof of Proposition 4.7: `g₀(ϖu - 2) = ϖ^d P(u)`. -/
theorem negTracePolynomial_eval_scaled (ζ : K) (hζ : ζ ≠ 0) (p : ℕ) (u : K) :
    (negTracePolynomial ζ p).eval (realCyclotomicParameter ζ * u - 2) = realCyclotomicParameter ζ ^ ((p - 1) / 2) * (scaledRootPolynomial ζ p).eval u := by
  unfold negTracePolynomial scaledRootPolynomial
  rw [eval_prod, eval_prod]
  have hc : realCyclotomicParameter ζ ^ ((p - 1) / 2) = ∏ _j ∈ Icc 1 ((p - 1) / 2), realCyclotomicParameter ζ := by
    rw [prod_const, Nat.card_Icc]
    simp
  rw [hc, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  simp only [eval_add, eval_sub, eval_X, eval_C]
  linear_combination cyclotomicUnitRatio_mul_realCyclotomicParameter ζ hζ j

/-- [TripathiGoswami], Proof of Proposition 4.7, equation (4.7): the substitution `x = ϖu - 2`,
`y = ϖ^{d+1} v` turns `y² + (x+2) g₀(x) y + t(x+2)` into
`ϖ^{2d+2} (v² + u P(u) v + t̃ u)` with `t̃ = t / ϖ^{2d+1} = t / ϖ^p`. -/
theorem scaled_equation {p : ℕ} (hp : Odd p) (ζ : K) (hζ : ζ ≠ 0) (hϖ : realCyclotomicParameter ζ ≠ 0)
    (u v t : K) :
    let x := realCyclotomicParameter ζ * u - 2
    let y := realCyclotomicParameter ζ ^ ((p - 1) / 2 + 1) * v
    y ^ 2 + (x + 2) * (negTracePolynomial ζ p).eval x * y + t * (x + 2) =
      realCyclotomicParameter ζ ^ (p + 1) *
        (v ^ 2 + u * (scaledRootPolynomial ζ p).eval u * v + t / realCyclotomicParameter ζ ^ p * u) := by
  intro x y
  simp only [x, y]
  rw [negTracePolynomial_eval_scaled ζ hζ p u]
  obtain ⟨k, rfl⟩ := hp
  rw [show (2 * k + 1 - 1) / 2 = k by omega]
  field_simp
  ring

/-- The nonzero change of coordinates identifies the original equation with
the scaled affine equation, whose parameter is exactly `t / ϖ^p`. -/
theorem scaled_equation_iff {p : ℕ} (hp : Odd p) (ζ : K) (hζ : ζ ≠ 0)
    (hϖ : realCyclotomicParameter ζ ≠ 0) (u v t : K) :
    let x := realCyclotomicParameter ζ * u - 2
    let y := realCyclotomicParameter ζ ^ ((p - 1) / 2 + 1) * v
    y ^ 2 + (x + 2) * (negTracePolynomial ζ p).eval x * y + t * (x + 2) = 0 ↔
      v ^ 2 + u * (scaledRootPolynomial ζ p).eval u * v + t / realCyclotomicParameter ζ ^ p * u = 0 := by
  dsimp only
  rw [scaled_equation hp ζ hζ hϖ]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hϖ))


end

section LocalRoots

open scoped NumberField

variable (p : ℕ) [Fact p.Prime]
  (P : IsDedekindDomain.HeightOneSpectrum (𝓞 (realCyclotomicField p)))

/-- The scaled polynomial with coefficients in the real local ring.
Its roots are the integral quotients of cyclotomic trace differences. -/
noncomputable def localScaledRootPolynomial :
    (P.valuationSubringAtPrime (realCyclotomicField p))[X] :=
  ∏ j ∈ Icc 1 ((p - 1) / 2), (X - C (localScaledRoot p P j))

/-- Passing to the fraction field gives the quotient-root presentation. -/
theorem map_localScaledRootPolynomial :
    (localScaledRootPolynomial p P).map
        (algebraMap (P.valuationSubringAtPrime (realCyclotomicField p))
          (realCyclotomicField p)) =
      ∏ j ∈ Icc 1 ((p - 1) / 2), (X - C ((2 - tau p j) / (2 - tau p 1))) := by
  simp [localScaledRootPolynomial, Polynomial.map_prod, coe_localScaledRoot]

/-- The local polynomial and the field polynomial agree in the fixed algebraic closure. -/
theorem map_localScaledRootPolynomial_eq_scaledRootPolynomial :
    (localScaledRootPolynomial p P).map
        ((realCyclotomicField p).val.toRingHom.comp
          (algebraMap (P.valuationSubringAtPrime (realCyclotomicField p))
            (realCyclotomicField p))) =
      scaledRootPolynomial (zeta p) p := by
  simp only [localScaledRootPolynomial, scaledRootPolynomial, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]
  apply prod_congr rfl
  intro j _
  congr 2
  change (realScaledRoot p j : Qbar) = cyclotomicUnitRatio (zeta p) j
  exact coe_realScaledRoot p j

/-- The local scaled polynomial is monic. -/
theorem localScaledRootPolynomial_monic : (localScaledRootPolynomial p P).Monic := by
  exact monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _

end LocalRoots

/-- [TripathiGoswami], Proof of Lemma 4.6: since `p` is odd, `w = 2v + uP(u)` turns `v² + uP(u)v + Tu = 0`
into `w² = u²P(u)² - 4Tu`. -/
theorem w_substitution {K : Type*} [Field K] [CharZero K] (u v Pu T : K) :
    v ^ 2 + u * Pu * v + T * u = 0 ↔ (2 * v + u * Pu) ^ 2 = u ^ 2 * Pu ^ 2 - 4 * T * u := by
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination (1 / 4 : K) * h


/-- [TripathiGoswami], Lemma 4.6: the dual graph (two vertices, `d + 1` edges) has first Betti number `d`. -/
theorem dual_graph_rank (d : ℕ) : (d + 1 : ℤ) - 2 + 1 = d := by ring

end HilbertModularity.Hyperelliptic
