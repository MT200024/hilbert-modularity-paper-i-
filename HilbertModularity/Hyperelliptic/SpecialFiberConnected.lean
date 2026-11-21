/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberComponentTopology

/-! # Connectedness of the square-branch special fibre -/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- The two signed projective components meet at the rational point over zero. -/
theorem globalComponent_ranges_inter_nonempty (P : k[X])
    (h2 : (2 : k) ≠ 0) :
    (Set.range ⇑(positiveGlobalComponent P) ∩
      Set.range ⇑(negativeGlobalComponent P)).Nonempty := by
  let q : Spec (CommRingCat.of k) := ⟨⊥, inferInstance⟩
  let y := (affinePoint (0 : k) ≫ ProjectiveLine.chartMap k 0 1 (by decide)) q
  have hmeet : positiveGlobalComponent P y = negativeGlobalComponent P y := by
    have h := (globalComponent_affinePoint_eq_iff P h2 0).mpr (by
      simp [finiteComponentPolynomial_eq])
    exact congrArg (fun f : Spec (CommRingCat.of k) ⟶ scaledDoubleCover P 0 => f q) h
  exact ⟨positiveGlobalComponent P y, ⟨y, rfl⟩, ⟨y, hmeet.symm⟩⟩

/-- The actual square-branch special fibre is connected because its two
irreducible projective components meet at the rational point over zero. -/
theorem scaledDoubleCover_zero_isConnected (P : k[X])
    (hP : P.Monic) (h2 : (2 : k) ≠ 0) :
    _root_.IsConnected (Set.univ : Set (scaledDoubleCover P 0)) := by
  have hpos : _root_.IsConnected (Set.range ⇑(positiveGlobalComponent P)) :=
    (positiveGlobalComponent_range_irreducible P).isConnected
  have hneg : _root_.IsConnected (Set.range ⇑(negativeGlobalComponent P)) :=
    (negativeGlobalComponent_range_irreducible P).isConnected
  have h := hpos.union (globalComponent_ranges_inter_nonempty P h2) hneg
  rwa [globalComponent_ranges_cover P hP h2] at h

end HilbertModularity.Hyperelliptic
