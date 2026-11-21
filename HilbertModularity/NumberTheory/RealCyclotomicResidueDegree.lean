/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.RealCyclotomicQuadratic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-! # Residue degrees over the real cyclotomic field

The residue degree in [TripathiGoswamiRevised, Theorem `thm:intro-main`]
is one or two: the ramification–inertia sum is the degree of the actual
quadratic extension. This also covers primes above the conductor.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] realFieldAlgebra

/-- Every finite prime of the full cyclotomic field has residue degree one
or two over the real cyclotomic field, at an odd prime conductor. -/
theorem inertiaDeg_real_cyclotomic_eq_one_or_two (hp : p ≠ 2)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField p))) :
    P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField p)) = 1 ∨
      P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField p)) = 2 := by
  classical
  let R := 𝓞 (realCyclotomicField p)
  let S := 𝓞 (cyclotomicField p)
  change P.asIdeal.inertiaDeg R = 1 ∨ P.asIdeal.inertiaDeg R = 2
  let q := P.asIdeal.under R
  let : Fintype (q.primesOver S) := Fintype.ofFinite _
  let Q : q.primesOver S := ⟨P.asIdeal, inferInstance, inferInstance⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank q S
  have hle : P.asIdeal.ramificationIdx R * P.asIdeal.inertiaDeg R ≤
      Module.finrank R S := by
    rw [← hsum]
    exact Finset.single_le_sum
      (f := fun Q : q.primesOver S => Q.1.ramificationIdx R * Q.1.inertiaDeg R)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)
  have hrank : Module.finrank R S = 2 := by
    rw [← IsFractionRing.finrank_eq R (realCyclotomicField p) S (cyclotomicField p)]
    exact finrank_real_cyclotomic p hp
  have he := P.asIdeal.ramificationIdx_pos R
  have hf := P.asIdeal.inertiaDeg_pos R
  have hbound := (Nat.le_mul_of_pos_left (P.asIdeal.inertiaDeg R) he).trans hle
  rw [hrank] at hbound
  omega

end HilbertModularity.Cyclotomic
