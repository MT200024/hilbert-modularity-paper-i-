/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersectionCardinality
public import HilbertModularity.Hyperelliptic.SpecialFiberBaseChange

/-! # Geometric intersections of the actual special fibre

A field extension preserves the distinct split branch parameters.  Thus the
two projective sheets of the base-changed scaled cover have the same number of
intersection points, including after passage to an algebraic closure.
-/

public noncomputable section

open AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k K : Type*} [Field k] [Field K] [DecidableEq K]

/-- The split branch polynomial remains split with the same distinct roots
after any field extension. -/
theorem splitPolynomial_map (f : k →+* K) (P : k[X]) (S : Finset k)
    (hsplit : P = ∏ x ∈ S, (X - C x)) :
    P.map f = ∏ y ∈ S.image f, (X - C y) := by
  classical
  rw [hsplit, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [Finset.prod_image]
  intro x _ y _ hxy
  exact f.injective hxy

/-- Zero is outside the image of a nonzero set of split branch parameters. -/
theorem zero_not_mem_image (f : k →+* K) (S : Finset k)
    (hzero : (0 : k) ∉ S) : (0 : K) ∉ S.image f := by
  intro h
  obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp h
  have hx0 : x = 0 := f.injective (by simpa using hfx)
  exact hzero (hx0 ▸ hx)

/-- The actual two projective components of the base-changed special fibre
meet in precisely the images of the original split branch points. -/
theorem geometricComponent_intersection_eq_points (f : k →+* K)
    (P : k[X]) (S : Finset k) (hP : P.Monic) (h2 : (2 : K) ≠ 0)
    (hsplit : P = ∏ x ∈ S, (X - C x)) :
    Set.range ⇑(positiveGlobalComponent (P.map f)) ∩
        Set.range ⇑(negativeGlobalComponent (P.map f)) =
      ↑(globalComponentIntersectionPoints (P.map f) (S.image f)) := by
  classical
  exact globalComponent_intersection_eq_points (P.map f) (S.image f)
    (hP.map f) h2 (splitPolynomial_map f P S hsplit)

/-- The geometric intersection count is unchanged by a field extension. -/
theorem geometricComponent_intersections_card (f : k →+* K)
    (P : k[X]) (S : Finset k) (hzero : (0 : k) ∉ S) :
    (globalComponentIntersectionPoints (P.map f) (S.image f)).card =
      S.card + 1 := by
  classical
  rw [globalComponentIntersectionPoints_card]
  simp [zero_not_mem_image f S hzero,
    Finset.card_image_iff.mpr (fun _ _ _ _ h => f.injective h)]

end HilbertModularity.Hyperelliptic
