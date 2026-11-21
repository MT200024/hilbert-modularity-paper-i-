/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersectionRing

/-! # The square-branch chart as a gluing ring

The two signed components of the special fibre agree along the branch
divisor. Their coordinate rings form a fibre product over its quotient ring.
This is a ring-level description of the whole affine chart, rather than only
of its scheme-theoretic intersection.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Pairs of component functions with the same restriction to the branch
divisor. -/
def congruentComponentPairs (H : k[X]) : Subring (k[X] × k[X]) where
  carrier := {z | componentIntersectionQuotient H z.1 =
    componentIntersectionQuotient H z.2}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change componentIntersectionQuotient H a.1 = componentIntersectionQuotient H a.2 at ha
    change componentIntersectionQuotient H b.1 = componentIntersectionQuotient H b.2 at hb
    change componentIntersectionQuotient H (a + b).1 =
      componentIntersectionQuotient H (a + b).2
    simpa only [Prod.fst_add, Prod.snd_add, map_add] using
      congrArg₂ (· + ·) ha hb
  mul_mem' := by
    intro a b ha hb
    change componentIntersectionQuotient H a.1 = componentIntersectionQuotient H a.2 at ha
    change componentIntersectionQuotient H b.1 = componentIntersectionQuotient H b.2 at hb
    change componentIntersectionQuotient H (a * b).1 =
      componentIntersectionQuotient H (a * b).2
    simpa only [Prod.fst_mul, Prod.snd_mul, map_mul] using
      congrArg₂ (· * ·) ha hb
  neg_mem' := by
    intro a ha
    change componentIntersectionQuotient H a.1 = componentIntersectionQuotient H a.2 at ha
    change componentIntersectionQuotient H (-a).1 = componentIntersectionQuotient H (-a).2
    simpa only [Prod.fst_neg, Prod.snd_neg, map_neg] using congrArg Neg.neg ha

/-- The chart with equation `w² = H²` is the fibre product of its two
polynomial component rings over `k[X]/(H)`. -/
def squareBranchFiberProductEquiv (H : k[X]) (hH : H ≠ 0) (h2 : (2 : k) ≠ 0) :
    SquareBranchRing H ≃+* congruentComponentPairs H := by
  let f : SquareBranchRing H →+* congruentComponentPairs H :=
    { toFun := fun z => ⟨componentPair H z, by
        change componentIntersectionQuotient H (componentPair H z).1 =
          componentIntersectionQuotient H (componentPair H z).2
        rw [← sub_eq_zero, ← map_sub, componentIntersectionQuotient_apply,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
        exact componentPair_difference_dvd H z⟩
      map_zero' := Subtype.ext (map_zero (componentPair H))
      map_one' := Subtype.ext (map_one (componentPair H))
      map_add' := fun x y => Subtype.ext (map_add (componentPair H) x y)
      map_mul' := fun x y => Subtype.ext (map_mul (componentPair H) x y) }
  apply RingEquiv.ofBijective f
  constructor
  · intro x y h
    apply componentPair_injective H hH h2
    exact congrArg Subtype.val h
  · intro z
    have hz : H ∣ z.1.1 - z.1.2 := by
      have h := z.property
      change componentIntersectionQuotient H z.1.1 =
        componentIntersectionQuotient H z.1.2 at h
      rw [← sub_eq_zero, ← map_sub, componentIntersectionQuotient_apply,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
      exact h
    obtain ⟨x, hx⟩ := (mem_range_componentPair_iff H h2 z.1.1 z.1.2).mpr hz
    exact ⟨x, Subtype.ext hx⟩

/-- The actual finite chart at parameter zero is the gluing of its two
signed component charts along the branch divisor. -/
def finiteSpecialFiberChartPushoutEquiv (P : k[X]) (hP : P.Monic)
    (h2 : (2 : k) ≠ 0) :
    AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0) ≃+*
      congruentComponentPairs (finiteComponentPolynomial P) := by
  rw [finiteBranchPolynomial_zero]
  apply squareBranchFiberProductEquiv
  · rw [finiteComponentPolynomial_eq]
    exact mul_ne_zero X_ne_zero hP.ne_zero
  · exact h2

end HilbertModularity.Hyperelliptic
