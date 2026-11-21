/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveFrobenius

/-! # The level-five examples over their original coefficient field

A specified coefficient embedding transports the concrete matrix calculation
and reflects equality of the finite comparison-character value.
See [TripathiGoswami, Example 7.1].
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace HilbertModularity.Examples

open Hyperelliptic

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩

private theorem charpolyRev_map {K : Type*} [CommRing K] (σ : K →+* ℂ)
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    (M.map σ).charpolyRev = M.charpolyRev.map σ := by
  unfold Matrix.charpolyRev
  change _ = (Polynomial.mapRingHom σ) _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite]

variable {K : Type*} [Field K] (σ : K →+* ℂ)

/-- The local polynomial at eleven is recovered in the original coefficient field. -/
theorem coefficient_local_polynomial_11
    (M N : Matrix (Fin 2) (Fin 2) K) (hM : M.det = 11) (hN : N.det = 11)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 11))) : ℂ) =
      11 + 1 - σ (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField11))) : ℂ) =
      11 ^ 2 + 1 - σ ((M ^ 2).trace + (N ^ 2).trace)) :
    (Matrix.fromBlocks M 0 0 N).charpolyRev =
      1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
  have hm : (M.map σ).det = 11 := by
    simpa only [RingHom.mapMatrix_apply, hM, map_ofNat] using (σ.map_det M).symm
  have hn : (N.map σ).det = 11 := by
    simpa only [RingHom.mapMatrix_apply, hN, map_ofNat] using (σ.map_det N).symm
  have h₁' := h₁
  have h₂' := h₂
  simp only [map_add, AddMonoidHom.map_trace, Matrix.map_pow] at h₁' h₂'
  have hp := frobenius_local_polynomial_11 (M.map σ) (N.map σ) hm hn h₁' h₂'
  apply Polynomial.map_injective σ σ.injective
  rw [← charpolyRev_map]
  simpa [Matrix.fromBlocks_map, Matrix.map_zero, map_ofNat] using hp

/-- The local polynomial at forty-one is recovered in the original coefficient field. -/
theorem coefficient_local_polynomial_41
    (M N : Matrix (Fin 2) (Fin 2) K) (hM : M.det = 41) (hN : N.det = 41)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 41))) : ℂ) =
      41 + 1 - σ (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField41))) : ℂ) =
      41 ^ 2 + 1 - σ ((M ^ 2).trace + (N ^ 2).trace)) :
    (Matrix.fromBlocks M 0 0 N).charpolyRev =
      1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
  have hm : (M.map σ).det = 41 := by
    simpa only [RingHom.mapMatrix_apply, hM, map_ofNat] using (σ.map_det M).symm
  have hn : (N.map σ).det = 41 := by
    simpa only [RingHom.mapMatrix_apply, hN, map_ofNat] using (σ.map_det N).symm
  have h₁' := h₁
  have h₂' := h₂
  simp only [map_add, AddMonoidHom.map_trace, Matrix.map_pow] at h₁' h₂'
  have hp := frobenius_local_polynomial_41 (M.map σ) (N.map σ) hm hn h₁' h₂'
  apply Polynomial.map_injective σ σ.injective
  rw [← charpolyRev_map]
  simpa [Matrix.fromBlocks_map, Matrix.map_zero, map_ofNat] using hp

/-- The fixed embedding selects the trace at 11 and reflects triviality of the actual
finite comparison character back to the original coefficient field. -/
theorem coefficient_comparison_character_11
    (M N : Matrix (Fin 2) (Fin 2) K) (hM : M.det = 11) (hN : N.det = 11)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 11))) : ℂ) =
      11 + 1 - σ (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField11))) : ℂ) =
      11 ^ 2 + 1 - σ ((M ^ 2).trace + (N ^ 2).trace))
    {G : Type*} [Group G] (ν : G →* Kˣ) (hν : (Set.range ν).Finite) (g : G)
    (A : MulChar (ZMod 11) ℂ) (hA : A 2 = fifthRoot)
    (θ : AddChar (ZMod 11) ℂ) (hθ : θ ≠ 1)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = σ (ν g : K) * σ M.trace) :
    σ M.trace = ((Real.sqrt 5 : ℂ) - 1) / 2 ∧ ν g = 1 := by
  have hm : (M.map σ).det = 11 := by
    simpa only [RingHom.mapMatrix_apply, hM, map_ofNat] using (σ.map_det M).symm
  have hn : (N.map σ).det = 11 := by
    simpa only [RingHom.mapMatrix_apply, hN, map_ofNat] using (σ.map_det N).symm
  have h₁' := h₁
  have h₂' := h₂
  simp only [map_add, AddMonoidHom.map_trace, Matrix.map_pow] at h₁' h₂'
  let νc : G →* ℂˣ := (Units.map (σ : K →* ℂ)).comp ν
  have hνc : (Set.range νc).Finite := by
    simpa only [νc, MonoidHom.coe_comp, Set.range_comp] using
      hν.image (Units.map (σ : K →* ℂ))
  have he' : Hypergeometric.rankTwoMcCarthySum θ A 125 = (νc g : ℂ) * (M.map σ).trace := by
    simpa [νc, AddMonoidHom.map_trace] using he
  have hp := frobenius_comparison_character_11 (M.map σ) (N.map σ) hm hn h₁' h₂'
    νc hνc g A hA θ hθ he'
  constructor
  · simpa only [AddMonoidHom.map_trace] using hp.1
  · apply Units.ext
    apply σ.injective
    simpa [νc] using congrArg (fun x : ℂˣ => (x : ℂ)) hp.2

/-- The fixed embedding selects the trace at 41 and reflects triviality of the actual
finite comparison character back to the original coefficient field. -/
theorem coefficient_comparison_character_41
    (M N : Matrix (Fin 2) (Fin 2) K) (hM : M.det = 41) (hN : N.det = 41)
    (h₁ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : ZMod 41))) : ℂ) =
      41 + 1 - σ (M.trace + N.trace))
    (h₂ : (Nat.card (Scheme.RationalPoint
      (plusCurveToSpec 5 (by decide) (125 : QuadraticField41))) : ℂ) =
      41 ^ 2 + 1 - σ ((M ^ 2).trace + (N ^ 2).trace))
    {G : Type*} [Group G] (ν : G →* Kˣ) (hν : (Set.range ν).Finite) (g : G)
    (A : MulChar (ZMod 41) ℂ) (hA : A 6 = fifthRoot)
    (θ : AddChar (ZMod 41) ℂ) (hθ : θ ≠ 1)
    (he : Hypergeometric.rankTwoMcCarthySum θ A 125 = σ (ν g : K) * σ M.trace) :
    σ M.trace = (-1 - 5 * (Real.sqrt 5 : ℂ)) / 2 ∧ ν g = 1 := by
  have hm : (M.map σ).det = 41 := by
    simpa only [RingHom.mapMatrix_apply, hM, map_ofNat] using (σ.map_det M).symm
  have hn : (N.map σ).det = 41 := by
    simpa only [RingHom.mapMatrix_apply, hN, map_ofNat] using (σ.map_det N).symm
  have h₁' := h₁
  have h₂' := h₂
  simp only [map_add, AddMonoidHom.map_trace, Matrix.map_pow] at h₁' h₂'
  let νc : G →* ℂˣ := (Units.map (σ : K →* ℂ)).comp ν
  have hνc : (Set.range νc).Finite := by
    simpa only [νc, MonoidHom.coe_comp, Set.range_comp] using
      hν.image (Units.map (σ : K →* ℂ))
  have he' : Hypergeometric.rankTwoMcCarthySum θ A 125 = (νc g : ℂ) * (M.map σ).trace := by
    simpa [νc, AddMonoidHom.map_trace] using he
  have hp := frobenius_comparison_character_41 (M.map σ) (N.map σ) hm hn h₁' h₂'
    νc hνc g A hA θ hθ he'
  constructor
  · simpa only [AddMonoidHom.map_trace] using hp.1
  · apply Units.ext
    apply σ.injective
    simpa [νc] using congrArg (fun x : ℂˣ => (x : ℂ)) hp.2

end HilbertModularity.Examples
