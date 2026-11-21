/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberGlobalIntersection

/-! # Cardinality of the actual projective component intersection -/

public noncomputable section

open AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The finite set of intersection points on the actual glued special fibre. -/
def globalComponentIntersectionPoints [DecidableEq k] (P : k[X]) (S : Finset k) :
    Finset (scaledDoubleCover P 0) := by
  classical
  exact (insert 0 S).image (fun x => finitePositiveMap P (finiteRootPoint x))

/-- Distinct affine branch parameters give distinct points on the actual projective cover. -/
theorem finiteRootImage_injective (P : k[X]) :
    Function.Injective (fun x : k => finitePositiveMap P (finiteRootPoint x)) := by
  intro x y hxy
  have hbase : ProjectiveLine.chartMap k 0 1 (by decide) (finiteRootPoint x) =
      ProjectiveLine.chartMap k 0 1 (by decide) (finiteRootPoint y) := by
    have h := congrArg (scaledDoubleCoverProjection P 0) hxy
    simpa only [← Scheme.Hom.comp_apply, finitePositiveMap_projection] using h
  have hroot : finiteRootPoint x = finiteRootPoint y :=
    (ProjectiveLine.chartMap k 0 1 (by decide)).isOpenEmbedding.injective hbase
  have hmem : X - C x ∈ (finiteRootPoint y).asIdeal := by
    rw [← hroot]
    exact (mem_finiteRootPoint_asIdeal_iff x _).2 (by simp)
  have heval := (mem_finiteRootPoint_asIdeal_iff y _).1 hmem
  have hyx : y = x := by
    apply sub_eq_zero.mp
    simpa only [eval_sub, eval_X, eval_C] using heval
  exact hyx.symm

/-- The intersection of the signed projective component images consists
exactly of the listed points, including the extra point above zero. -/
theorem globalComponent_intersection_eq_points [DecidableEq k]
    (P : k[X]) (S : Finset k) (hP : P.Monic) (h2 : (2 : k) ≠ 0)
    (hsplit : P = ∏ x ∈ S, (X - C x)) :
    Set.range ⇑(positiveGlobalComponent P) ∩
        Set.range ⇑(negativeGlobalComponent P) =
      ↑(globalComponentIntersectionPoints P S) := by
  classical
  rw [globalComponent_ranges_inter_eq_splitCrossings P S hP h2 hsplit]
  ext z
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, globalComponentIntersectionPoints,
    Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- The number of actual projective intersection points is the number of
distinct finite branch parameters. -/
theorem globalComponentIntersectionPoints_card [DecidableEq k]
    (P : k[X]) (S : Finset k) :
    (globalComponentIntersectionPoints P S).card = (insert 0 S).card := by
  classical
  unfold globalComponentIntersectionPoints
  exact Finset.card_image_iff.mpr (fun _ _ _ _ h => finiteRootImage_injective P h)

/-- The two projective components of the cyclotomic residue fibre meet at
exactly `d + 1` points, where `d = (p - 1) / 2`. -/
theorem reducedLocal_globalComponentIntersectionPoints_card
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (globalComponentIntersectionPoints
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)) (residueRootSet p)).card =
      (p - 1) / 2 + 1 := by
  rw [globalComponentIntersectionPoints_card]
  exact reducedLocalFiniteComponent_crossing_count p hp

end HilbertModularity.Hyperelliptic
