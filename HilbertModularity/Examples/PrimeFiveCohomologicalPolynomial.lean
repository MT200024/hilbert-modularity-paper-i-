/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteFieldGenusTwoFrobenius
public import HilbertModularity.Hyperelliptic.PrimeFiveQuadraticPoints
import Mathlib.Tactic.NormNum

/-! # The actual cohomological local polynomials at 11 and 41

The cited genus-two trace formula is applied to the completed level-five plus
curve. Its four point counts were proved by direct finite-field enumeration;
the numerical polynomials below are deductions from those counts.
-/

public noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace HilbertModularity.Examples

open Hyperelliptic

local instance primeFiveCohomologySevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance primeFiveCohomologyElevenPrime : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance primeFiveCohomologyFortyOnePrime : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The displayed level-five equation has degree six in every field. -/
theorem primeFivePolynomial_degree (K : Type*) [Field K] :
    (primeFivePolynomial K).natDegree = 2 * 3 := by
  simpa only [plusPolynomial_five] using
    (plusPolynomial_evenDegree 5 (by decide) (125 : K))

/-- The displayed level-five branch polynomial is monic. -/
theorem primeFivePolynomial_monic (K : Type*) [Field K] :
    (primeFivePolynomial K).Monic := by
  simpa only [plusPolynomial_five] using
    (plusPolynomial_isMonicOfDegree 5 (by decide) (125 : K)).monic

/-- The checked good-reduction hypotheses imply a separable branch polynomial. -/
theorem primeFivePolynomial_separable (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h0 : (125 : K) ≠ 0) (h1 : (125 : K) ≠ 1) :
    (primeFivePolynomial K).Separable := by
  simpa only [plusPolynomial_five] using
    (plusPolynomial_separable 5 (by decide) h2 h5 (125 : K) h0 h1)

/-- The actual geometric first cohomology of the completed level-five curve. -/
abbrev primeFiveGeometricH1 (K : Type*) [Field K] [Fintype K] :=
  AlgebraicGeometry.Hyperelliptic.genusTwoGeometricH1 K (primeFivePolynomial K)
    (primeFivePolynomial_degree K) 7

/-- Geometric Frobenius on the actual cohomology, with no Tate twist. -/
def primeFiveGeometricFrobeniusAction (K : Type*) [Field K] [Fintype K] :
    primeFiveGeometricH1 K →ₗ[ℚ_[7]] primeFiveGeometricH1 K :=
  AlgebraicGeometry.Hyperelliptic.genusTwoGeometricFrobeniusAction K
    (primeFivePolynomial K) (primeFivePolynomial_degree K) 7

/-- Equality of branch equations and half-degrees preserves the projective
rational-point count of their actual two-chart completions. -/
theorem rationalPointCount_congr {K : Type*} [Field K]
    {f g : K[X]} {n m : ℕ} (h : f = g) (hn : n = m)
    (hf : f.natDegree = 2 * n) (hg : g.natDegree = 2 * m) :
    Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec f n hf)) =
      Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec g m hg)) := by
  cases h
  cases hn
  rfl

/-- The manuscript's polynomial at eleven, on the chosen completed curve's
actual geometric first cohomology. [TripathiGoswami, Example 7.1]. -/
theorem primeFive_geometricFrobeniusPolynomial_11 :
    ∃ b : Module.Basis (Fin 4) ℚ_[7] (primeFiveGeometricH1 (ZMod 11)),
      (LinearMap.toMatrix b b (primeFiveGeometricFrobeniusAction (ZMod 11))).charpolyRev =
        1 + X + 21 * X ^ 2 + 11 * X ^ 3 + 121 * X ^ 4 := by
  let f := primeFivePolynomial (ZMod 11)
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree (ZMod 11)
  have hd₂ : (f.map (algebraMap (ZMod 11) QuadraticField11)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree QuadraticField11
  have h₁ : Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) =
      13 := by
    have heq : f = plusPolynomial 5 (125 : ZMod 11) :=
      (plusPolynomial_five (ZMod 11)).symm
    exact (rationalPointCount_congr heq (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : ZMod 11))).trans
      primeFive_count_11
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap (ZMod 11) QuadraticField11)) 3 hd₂)) = 163 := by
    have heq : f.map (algebraMap (ZMod 11) QuadraticField11) =
        plusPolynomial 5 (125 : QuadraticField11) := by
      simpa only [f, primeFivePolynomial_map] using
        (plusPolynomial_five QuadraticField11).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : QuadraticField11))).trans
      primeFive_count_121
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoGeometricFrobeniusPolynomial
    (ZMod 11) f hd 7 (primeFivePolynomial_monic (ZMod 11))
    (primeFivePolynomial_separable (ZMod 11) (by decide) (by decide)
      (by decide) (by decide)) (by decide) (by decide) hd₂
    (by simpa [ZMod.card] using quadraticField11_card)
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [primeFiveGeometricFrobeniusAction, primeFiveGeometricH1, f,
    ZMod.card] at hb ⊢
  exact hb

/-- The manuscript's polynomial at forty-one on the same completed equation
with its geometric cohomological Frobenius. [TripathiGoswami, Example 7.1]. -/
theorem primeFive_geometricFrobeniusPolynomial_41 :
    ∃ b : Module.Basis (Fin 4) ℚ_[7] (primeFiveGeometricH1 (ZMod 41)),
      (LinearMap.toMatrix b b (primeFiveGeometricFrobeniusAction (ZMod 41))).charpolyRev =
        1 + X + 51 * X ^ 2 + 41 * X ^ 3 + 1681 * X ^ 4 := by
  let f := primeFivePolynomial (ZMod 41)
  have hd : f.natDegree = 2 * 3 := primeFivePolynomial_degree (ZMod 41)
  have hd₂ : (f.map (algebraMap (ZMod 41) QuadraticField41)).natDegree = 2 * 3 := by
    simpa only [f, primeFivePolynomial_map] using primeFivePolynomial_degree QuadraticField41
  have h₁ : Nat.card (Scheme.RationalPoint (AlgebraicGeometry.Hyperelliptic.toSpec f 3 hd)) =
      43 := by
    have heq : f = plusPolynomial 5 (125 : ZMod 41) :=
      (plusPolynomial_five (ZMod 41)).symm
    exact (rationalPointCount_congr heq (by decide) hd
      (plusPolynomial_evenDegree 5 (by decide) (125 : ZMod 41))).trans
      primeFive_count_41
  have h₂ : Nat.card (Scheme.RationalPoint
      (AlgebraicGeometry.Hyperelliptic.toSpec
        (f.map (algebraMap (ZMod 41) QuadraticField41)) 3 hd₂)) = 1783 := by
    have heq : f.map (algebraMap (ZMod 41) QuadraticField41) =
        plusPolynomial 5 (125 : QuadraticField41) := by
      simpa only [f, primeFivePolynomial_map] using
        (plusPolynomial_five QuadraticField41).symm
    exact (rationalPointCount_congr heq (by decide) hd₂
      (plusPolynomial_evenDegree 5 (by decide) (125 : QuadraticField41))).trans
      primeFive_count_1681
  obtain ⟨b, hb⟩ := AlgebraicGeometry.Hyperelliptic.genusTwoGeometricFrobeniusPolynomial
    (ZMod 41) f hd 7 (primeFivePolynomial_monic (ZMod 41))
    (primeFivePolynomial_separable (ZMod 41) (by decide) (by decide)
      (by decide) (by decide)) (by decide) (by decide) hd₂
    (by simpa [ZMod.card] using quadraticField41_card)
  refine ⟨b, ?_⟩
  dsimp only at hb
  rw [h₁, h₂] at hb
  norm_num [primeFiveGeometricFrobeniusAction, primeFiveGeometricH1, f,
    ZMod.card] at hb ⊢
  exact hb

end HilbertModularity.Examples
