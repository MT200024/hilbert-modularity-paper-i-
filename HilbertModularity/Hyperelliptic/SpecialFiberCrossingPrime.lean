/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberNodeEquation
public import HilbertModularity.Hyperelliptic.SpecialFiberIntersection

/-! # The prime of a finite crossing in the actual special-fibre chart

Evaluation on either signed component at a branch zero gives the same
field-valued point of the finite quadratic chart. Its kernel is prime and
contracts to the evaluation prime of the base line. This identifies the
point at which the local node presentation must be applied.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Evaluation at a point on the positive sheet of the actual finite chart. -/
def finiteCrossingEvaluation (P : k[X]) (x : k) :
    AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0) →ₐ[k] k :=
  (Polynomial.aeval x).comp (finitePositiveComponent P)

@[simp] theorem finiteCrossingEvaluation_base (P q : k[X]) (x : k) :
    finiteCrossingEvaluation P x
      (algebraMap k[X]
        (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)) q) =
      q.eval x := by
  simp [finiteCrossingEvaluation]

/-- At a branch zero, evaluation on the two signed sheets agrees. -/
theorem finiteCrossingEvaluation_negative (P : k[X]) (h2 : (2 : k) ≠ 0) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0) :
    finiteCrossingEvaluation P x =
      (Polynomial.aeval x).comp (finiteNegativeComponent P) := by
  exact (finiteComponent_eval_eq_iff P h2 x).mpr hx

/-- The actual finite crossing defines a prime ideal of the chart ring. -/
theorem finiteCrossingPrime_isPrime (P : k[X]) (x : k) :
    (RingHom.ker (finiteCrossingEvaluation P x).toRingHom).IsPrime := by
  exact RingHom.ker_isPrime _

/-- Evaluation is onto the residue field, so this is a closed rational point
of the actual finite chart. -/
theorem finiteCrossingPrime_isMaximal (P : k[X]) (x : k) :
    (RingHom.ker (finiteCrossingEvaluation P x).toRingHom).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro a
  refine ⟨algebraMap k
    (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)) a, ?_⟩
  simp [finiteCrossingEvaluation]

/-- The finite crossing lies over the expected evaluation prime of the base. -/
theorem finiteCrossingPrime_comap (P : k[X]) (x : k) :
    Ideal.comap
        (algebraMap k[X]
          (AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)))
        (RingHom.ker (finiteCrossingEvaluation P x).toRingHom) =
      RingHom.ker (evalRingHom x) := by
  ext q
  simp [Ideal.mem_comap, RingHom.mem_ker, finiteCrossingEvaluation_base,
    evalRingHom]

/-- At a branch zero, the crossing prime consists exactly of sections whose
scalar coefficient vanishes at the base point. This identifies the prime in
the quadratic chart, rather than merely its contraction to the base line. -/
theorem mem_finiteCrossingPrime_iff (P : k[X]) (x : k)
    (hx : (finiteComponentPolynomial P).eval x = 0)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)) :
    z ∈ RingHom.ker (finiteCrossingEvaluation P x).toRingHom ↔ z.re.eval x = 0 := by
  rw [RingHom.mem_ker]
  have hh : x * P.eval x = 0 := by
    simpa [finiteComponentPolynomial_eq] using hx
  simp [finiteCrossingEvaluation, finitePositiveComponent_apply, hh]

end HilbertModularity.Hyperelliptic
