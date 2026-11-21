/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Hyperelliptic

/-! # Geometric curve properties of a reciprocal double cover

The two quadratic charts of a squarefree double cover glue to a smooth
integral curve over a field. This is the standard projective hyperelliptic
construction, applied to the actual glued scheme rather than to an abstract
curve with the same function field.
-/

public section

open CategoryTheory Polynomial LaurentPolynomial

namespace AlgebraicGeometry.DoubleCover

/-- The standard two-chart construction of a smooth integral hyperelliptic
curve from a nonconstant separable branch equation. The transition identity
identifies `g` with the reciprocal branch equation of `f`, with `n` fixing the
homogenizing degree. Separability of `f` gives distinct finite branch points;
separability of `g` checks the reciprocal chart, including infinity. Positive
degree and separability also exclude a square branch equation, giving an
integral generic curve. These are the two charts in [src_poonen_curves,
§2.8.1, printed pp. 36–37]; uniqueness of the smooth projective model is in
§2.1.2, printed p. 23. This input makes no assertion about regularity or
stability of a model over a valuation ring. -/
theorem integral_and_smoothOfRelativeDimension_one
    {K : Type*} [Field K] (f g : K[X]) (n : ℕ)
    (h : invert (toLaurent g) = T (-(n : ℤ)) ^ 2 * toLaurent f)
    (hf : f.Separable) (hg : g.Separable)
    (hdeg : 0 < f.natDegree) (h2 : (2 : K) ≠ 0) :
    IsIntegral (scheme f g n h) ∧
      SmoothOfRelativeDimension 1
        (toProjectiveLine f g n h ≫ ProjectiveLine.toSpec K) := by
  sorry

end AlgebraicGeometry.DoubleCover
