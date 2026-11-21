/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersectionPullback
public import HilbertModularity.Hyperelliptic.SpecialFiberResidue
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # Splitting the finite crossing scheme

The affine intersection of the signed components is the quotient by the
branch polynomial. Distinct split roots make that quotient a product of
copies of the residue field. This is a certificate for reduced rational
intersection points, separate from a completed-local-ring node criterion.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Evaluation at distinct roots splits the coordinate algebra of their
reduced finite subscheme. -/
def quotientSpanProdXSubCEquiv (S : Finset k) :
    (k[X] ⧸ Ideal.span {∏ x ∈ S, (X - C x)}) ≃+* (S → k) := by
  classical
  have hcop : Pairwise (fun x y : S => IsCoprime (X - C (x : k)) (X - C (y : k))) :=
    fun x y hxy => Polynomial.pairwise_coprime_X_sub_C
      (fun a b hab => hab) (fun h => hxy (Subtype.ext h))
  have hinf : Ideal.span ({∏ x ∈ S, (X - C x)} : Set k[X]) =
      ⨅ x : S, Ideal.span {X - C (x : k)} := by
    rw [Ideal.iInf_span_singleton hcop, ← Finset.prod_coe_sort S]
  refine (Ideal.quotEquivOfEq hinf).trans ?_
  refine (Ideal.quotientInfRingEquivPiQuotient _ fun x y hxy => ?_).trans ?_
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hxy)
  · exact RingEquiv.piCongrRight fun x =>
      (Polynomial.quotientSpanXSubCAlgEquiv (x : k)).toRingEquiv

/-- The actual finite-chart intersection quotient splits into one copy of the
field for the origin and one for each distinct listed root. -/
def finiteComponentIntersectionEquiv [DecidableEq k] (P : k[X]) (S : Finset k)
    (hP : P = ∏ x ∈ S, (X - C x)) (hzero : 0 ∉ S) :
    componentIntersectionRing (finiteComponentPolynomial P) ≃+*
      (↥(insert (0 : k) S) → k) := by
  rw [finiteComponentPolynomial_eq, hP]
  have hprod : X * ∏ x ∈ S, (X - C x) =
      ∏ x ∈ insert (0 : k) S, (X - C x) := by
    rw [Finset.prod_insert hzero]
    simp
  rw [hprod]
  exact quotientSpanProdXSubCEquiv (insert 0 S)

/-- The cyclotomic residue intersection has exactly the expected product of
rational residue fields. -/
def reducedLocalFiniteComponentIntersectionEquiv (p : ℕ) [Fact p.Prime] :
    componentIntersectionRing (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))) ≃+*
      (↥(insert (0 : ZMod p) (residueRootSet p)) → ZMod p) :=
  finiteComponentIntersectionEquiv _ (residueRootSet p)
    (localScaledRootPolynomial_reduction_split p)
    (zero_not_mem_residueRootSet p)

/-- The scheme-theoretic finite intersection in the actual cyclotomic fibre is
reduced: its coordinate ring is the product of its rational residue fields. -/
theorem reducedLocalFiniteComponentIntersection_isReduced (p : ℕ) [Fact p.Prime] :
    IsReduced (componentIntersectionRing (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)))) := by
  let e := reducedLocalFiniteComponentIntersectionEquiv p
  constructor
  intro x hx
  apply e.injective
  have hn : IsNilpotent (e x) := hx.map e.toRingHom
  simpa using (IsReduced.eq_zero _ hn)

end HilbertModularity.Hyperelliptic
