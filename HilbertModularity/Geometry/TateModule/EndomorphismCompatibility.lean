/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Endomorphism
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace

/-! # Auxiliary-prime compatibility for algebraic endomorphisms

The input here concerns an actual endomorphism of an abelian variety. Applying
it to a good reduction still requires the specialization comparison; it does
not assert compatibility for an arbitrary Galois element or a labelled factor.
-/

public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

/-- The characteristic polynomial and trace of a rational algebraic endomorphism
are independent of the auxiliary prime.

[MilneAV, Chapter I, Theorem 10.9, pp. 46–47; Remark 10.11, p. 47;
Proposition 10.20, pp. 50–52]. Properness, smoothness and geometric connectedness
make the commutative group scheme an abelian variety. Remark 10.11 extends the
endomorphism polynomial to `End⁰(A)` by clearing denominators; the rational
endomorphism here is `c * f`. Proposition 10.20 identifies its polynomial and
trace with those of the covariant rational Tate map for every prime different
from the ground-field characteristic. The prime exclusion is `(p : K) ≠ 0`.
The polynomial is `det(X - f)`, and the statement is independent of the chosen
finite basis. No Frobenius specialization, RM projector or manuscript comparison
is included in this named literature admission. -/
theorem exists_rationalTateEndomorphism_polynomial
    (K : Type u) [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ A) [IsMonHom f] (c : ℚ) :
    ∃ (P : Polynomial ℚ) (t : ℚ),
      ∀ (p : ℕ) (hp : p.Prime) (_ : (p : K) ≠ 0),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (n : ℕ) (b : Module.Basis (Fin n) ℚ_[p] (rationalTate K A p)),
          (LinearMap.toMatrix b b ((algebraMap ℚ ℚ_[p] c) • rationalTateMap K p f)).charpoly =
              P.map (algebraMap ℚ ℚ_[p]) ∧
            (LinearMap.toMatrix b b ((algebraMap ℚ ℚ_[p] c) • rationalTateMap K p f)).trace =
              algebraMap ℚ ℚ_[p] t := by
  sorry

/-- The common rational trace in the basis-free form used by the projector
calculation. Finite dimensionality is supplied by the geometric realization. -/
theorem exists_rationalTateEndomorphism_trace
    (K : Type u) [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ A) [IsMonHom f] (c : ℚ) :
    ∃ t : ℚ, ∀ (p : ℕ) (hp : p.Prime) (_ : (p : K) ≠ 0),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K A p)),
        LinearMap.trace ℚ_[p] (rationalTate K A p)
          ((algebraMap ℚ ℚ_[p] c) • rationalTateMap K p f) = algebraMap ℚ ℚ_[p] t := by
  obtain ⟨P, t, h⟩ := exists_rationalTateEndomorphism_polynomial K A f c
  refine ⟨t, ?_⟩
  intro p hp hchar
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite
  let := hfinite
  have ht := (h p hp hchar _ (Module.finBasis ℚ_[p] (rationalTate K A p))).2
  rwa [← LinearMap.trace_eq_matrix_trace] at ht

/-- The same rational trace works after coefficient extension and a supplied
specialization isomorphism. The hypothesis identifies actual operators, rather
than assuming equality of their traces; this is the form needed for the
full-space traces preceding the labelled projector calculation. -/
theorem exists_rationalTateEndomorphism_trace_of_conjugacy
    (K : Type u) [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ A) [IsMonHom f] (c : ℚ) :
    ∃ t : ℚ, ∀ (p : ℕ) (hp : p.Prime) (_ : (p : K) ≠ 0),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (_ : FiniteDimensional ℚ_[p] (rationalTate K A p))
        (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
        [IsScalarTower ℚ ℚ_[p] L]
        (V : Type*) [AddCommGroup V] [Module L V]
        (e : (L ⊗[ℚ_[p]] rationalTate K A p) ≃ₗ[L] V)
        (T : Module.End L V),
        T = e.conj (((algebraMap ℚ ℚ_[p] c) • rationalTateMap K p f).baseChange L) →
        LinearMap.trace L V T = algebraMap ℚ L t := by
  obtain ⟨t, ht⟩ := exists_rationalTateEndomorphism_trace K A f c
  refine ⟨t, ?_⟩
  intro p hp hchar
  let : Fact p.Prime := ⟨hp⟩
  intro hfinite L _ _ _ _ V _ _ e T hT
  let := hfinite
  rw [hT, LinearMap.trace_conj', LinearMap.trace_baseChange, ht p hp hchar hfinite,
    ← IsScalarTower.algebraMap_apply]

end AlgebraicGeometry.GroupScheme
