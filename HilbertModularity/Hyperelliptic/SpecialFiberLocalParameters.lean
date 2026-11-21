/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberResidue
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Local parameters at crossings of the square-branch fibre

At a simple root of the branch polynomial, its quotient by the linear factor
is coprime to that factor. Thus the quotient is invertible in the local ring
at the root, and the branch polynomial itself is a local parameter. This is
the algebraic input for the standard transverse-node criterion; it does not
identify a completed local ring or assert Scheme nodality.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- A polynomial nonzero at `x` is coprime to the linear factor at `x`. -/
theorem X_sub_C_isCoprime_of_eval_ne_zero (Q : k[X]) (x : k)
    (hq : Q.eval x ≠ 0) : IsCoprime (X - C x) Q := by
  let R := (Q - C (Q.eval x)) /ₘ (X - C x)
  have hroot : (Q - C (Q.eval x)).eval x = 0 := by simp
  have hfactor : Q - C (Q.eval x) = (X - C x) * R :=
    branch_factor_at_root (Q - C (Q.eval x)) x hroot
  refine ⟨-C ((Q.eval x)⁻¹) * R, C ((Q.eval x)⁻¹), ?_⟩
  have hc : C ((Q.eval x)⁻¹) * C (Q.eval x) = (1 : k[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  calc
    (-C ((Q.eval x)⁻¹) * R) * (X - C x) +
        C ((Q.eval x)⁻¹) * Q =
      C ((Q.eval x)⁻¹) * (Q - (X - C x) * R) := by ring
    _ = C ((Q.eval x)⁻¹) * C (Q.eval x) := by rw [← hfactor]; ring
    _ = 1 := hc

/-- The quotient in the simple-root factorization is coprime to the local
coordinate. -/
theorem branch_quotient_isCoprime (H : k[X]) (x : k)
    (hx : H.derivative.eval x ≠ 0) :
    IsCoprime (X - C x) (H /ₘ (X - C x)) :=
  X_sub_C_isCoprime_of_eval_ne_zero _ x
    (branch_quotient_eval_ne_zero H x hx)

theorem evaluationKernel_isPrime (x : k) :
    (RingHom.ker (evalRingHom x)).IsPrime := by
  exact RingHom.ker_isPrime _

/-- Every crossing of the actual cyclotomic finite chart has a coprime
unit factor in its local parameter decomposition. -/
theorem reducedLocalFiniteComponent_localParameter
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0) :
    IsCoprime (X - C x)
      ((finiteComponentPolynomial
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p))) /ₘ (X - C x)) :=
  branch_quotient_isCoprime _ x (reducedLocalFiniteComponent_simple_roots p hx)

/-- At a simple zero, the branch polynomial is the standard coordinate times
a unit in any localization at the evaluation prime. -/
theorem branch_localParameter_factor
    (H : k[X]) (x : k) (hx : H.eval x = 0)
    (hsimple : H.derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    ∃ u : Sˣ, algebraMap k[X] S H =
      algebraMap k[X] S (X - C x) * u := by
  have hunit : IsUnit (algebraMap k[X] S (H /ₘ (X - C x))) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff S
      (RingHom.ker (evalRingHom x)) _).2
    change H /ₘ (X - C x) ∉ RingHom.ker (evalRingHom x)
    simpa [evalRingHom] using
      branch_quotient_eval_ne_zero H x hsimple
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u, ?_⟩
  rw [branch_factor_at_root H x hx, map_mul, hu]

/-- A simple-root branch polynomial and the standard coordinate cut out the
same divisor in the coefficient local ring. -/
theorem branch_localParameter_span_eq
    (H : k[X]) (x : k) (hx : H.eval x = 0)
    (hsimple : H.derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    Ideal.span {algebraMap k[X] S H} =
      Ideal.span {algebraMap k[X] S (X - C x)} := by
  obtain ⟨u, hu⟩ := branch_localParameter_factor H x hx hsimple S
  ext a
  simp only [Ideal.mem_span_singleton]
  rw [hu]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨u * b, by rw [hb]; ring⟩
  · rintro ⟨b, hb⟩
    exact ⟨(u⁻¹ : Sˣ) * b, by rw [hb]; simp [mul_assoc]⟩

/-- The simple-root derivative is invertible at the evaluation prime. -/
theorem branch_derivative_isUnit_atPrime
    (H : k[X]) (x : k) (hsimple : H.derivative.eval x ≠ 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    IsUnit (algebraMap k[X] S H.derivative) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff S
    (RingHom.ker (evalRingHom x)) _).2
  change H.derivative ∉ RingHom.ker (evalRingHom x)
  simpa [evalRingHom] using hsimple

/-- At every actual finite crossing, the reduced branch section is a local
coordinate times a unit. This is the local algebra needed to apply a node
criterion to the scaled model. -/
theorem reducedLocalFiniteComponent_localParameter_factor
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0)
    (S : Type*) [CommRing S]
    [Algebra (ZMod p)[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    ∃ u : Sˣ,
      algebraMap (ZMod p)[X] S
        (finiteComponentPolynomial
          ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
            (Cyclotomic.realLocalReduction p))) =
      algebraMap (ZMod p)[X] S (X - C x) * u :=
  branch_localParameter_factor _ x hx
    (reducedLocalFiniteComponent_simple_roots p hx) S

/-- The actual reduced crossing branch parameter generates the maximal
parameter ideal of the coefficient local ring. -/
theorem reducedLocalFiniteComponent_localParameter_span_eq
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0)
    (S : Type*) [CommRing S]
    [Algebra (ZMod p)[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    Ideal.span {algebraMap (ZMod p)[X] S
      (finiteComponentPolynomial
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)))} =
      Ideal.span {algebraMap (ZMod p)[X] S (X - C x)} :=
  branch_localParameter_span_eq _ x hx
    (reducedLocalFiniteComponent_simple_roots p hx) S

/-- At an actual cyclotomic crossing, the derivative needed for an étale
change of coordinate is a unit in the coefficient local ring. -/
theorem reducedLocalFiniteComponent_derivative_isUnit_atPrime
    (p : ℕ) [Fact p.Prime] {x : ZMod p}
    (hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0)
    (S : Type*) [CommRing S]
    [Algebra (ZMod p)[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    IsUnit (algebraMap (ZMod p)[X] S
      (finiteComponentPolynomial
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p))).derivative) :=
  branch_derivative_isUnit_atPrime _ x
    (reducedLocalFiniteComponent_simple_roots p hx) S

end HilbertModularity.Hyperelliptic
