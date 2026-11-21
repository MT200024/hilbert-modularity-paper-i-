/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersection
public import HilbertModularity.Hyperelliptic.SpecialFiberResidue

/-! # Rational crossings of the scaled cyclotomic special fibre

The signed projective components coincide at the residue roots of the branch
polynomial and at the additional zero root. The count here concerns these
actual rational points of the glued cover. Scheme-theoretic nodality remains
separate from this pointwise certificate.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The positive sheet identifies each affine branch parameter with a point of
 the actual scaled double cover. -/
def globalCrossingPoint (P : k[X]) (x : k) :
    Spec (CommRingCat.of k) ⟶ scaledDoubleCover P 0 :=
  (affinePoint x ≫ ProjectiveLine.chartMap k 0 1 (by decide)) ≫
    positiveGlobalComponent P

/-- On points, the rational crossing morphism factors through the positive
finite chart map. -/
theorem globalCrossingPoint_apply_finite (P : k[X]) (x : k)
    (q : Spec (CommRingCat.of k)) :
    globalCrossingPoint P x q = finitePositiveMap P (affinePoint x q) := by
  simp only [globalCrossingPoint, Category.assoc, Scheme.Hom.comp_apply,
    chartMap_comp_positiveGlobalComponent_finite]

/-- Different affine parameters yield different points of the global sheet. -/
theorem globalCrossingPoint_injective (P : k[X]) :
    Function.Injective (globalCrossingPoint P) := by
  intro x y h
  have hp := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ scaledDoubleCover P 0 =>
      φ ≫ scaledDoubleCoverProjection P 0) h
  have hc : affinePoint x ≫ ProjectiveLine.chartMap k 0 1 (by decide) =
      affinePoint y ≫ ProjectiveLine.chartMap k 0 1 (by decide) := by
    simpa only [globalCrossingPoint, Category.assoc,
      positiveGlobalComponent_projection, Category.comp_id] using hp
  have hm : Mono (ProjectiveLine.chartMap k 0 1 (by decide)) := IsOpenImmersion.mono _
  exact affinePoint_injective ((cancel_mono _).mp hc)

variable (p : ℕ) [Fact p.Prime]

/-- In the actual residue fibre the two projective sheets coincide at exactly
 the origin and the distinct nonzero cyclotomic roots on the finite chart. -/
theorem reducedLocal_globalCrossing_iff (h2 : (2 : ZMod p) ≠ 0) (x : ZMod p) :
    (affinePoint x ≫ ProjectiveLine.chartMap (ZMod p) 0 1 (by decide)) ≫
        positiveGlobalComponent
          ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
            (Cyclotomic.realLocalReduction p)) =
      (affinePoint x ≫ ProjectiveLine.chartMap (ZMod p) 0 1 (by decide)) ≫
        negativeGlobalComponent
          ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
            (Cyclotomic.realLocalReduction p)) ↔
      x = 0 ∨ x ∈ residueRootSet p := by
  rw [globalComponent_affinePoint_eq_iff _ h2 x,
    finiteComponentPolynomial_eq_split _ _ (localScaledRootPolynomial_reduction_split p),
    splitFiniteBranchPolynomial_root_iff]

/-- The finite set of rational intersections in the actual special fibre. -/
def reducedLocalRationalCrossings :
    Finset (Spec (CommRingCat.of (ZMod p)) ⟶
      scaledDoubleCover
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)) 0) := by
  classical
  exact (insert 0 (residueRootSet p)).image (globalCrossingPoint
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)))

/-- There are exactly `(p-1)/2+1` distinct rational crossings on the finite chart. -/
theorem reducedLocalRationalCrossings_card (hp : 3 ≤ p) :
    (reducedLocalRationalCrossings p).card = (p - 1) / 2 + 1 := by
  classical
  unfold reducedLocalRationalCrossings
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ h => globalCrossingPoint_injective _ h)]
  exact reducedLocalFiniteComponent_crossing_count p hp

end HilbertModularity.Hyperelliptic
