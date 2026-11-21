/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeDarmonTateComparison
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomology
public import Mathlib.RepresentationTheory.Character

/-! # The chosen Darmon dual factor on the same plus Jacobian

An equality of a dependent family together with its RM action preserves the
cohomological idempotent factor and its coefficient embedding. Applying this
to the selected Darmon/plus equality keeps the `m=1` label fixed.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

/-- A dependent equality of family and integral RM action preserves the
dual labelled factor, including the chosen coefficient embedding. -/
def fiberLabelledDualTateEquivOfFamilyEq
    (K : Type) [Field K] {S : Scheme}
    (x : Spec (CommRingCat.of K) ⟶ S)
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [Algebra ℚ_[ℓ] L] [Algebra ℚ L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : F →ₐ[ℚ] L)
    (D D' : Σ A : CommGrp (Over S), 𝓞 F →+* End A) (h : D = D') :
    (labelledDualTateFactor K (fiber K D.1 x).X ℓ F L hL
      (fiberPointsAction K (AlgebraicClosure K) D.1 x (𝓞 F) D.2)
      (fiberPointsAction_realized K (AlgebraicClosure K) D.1 x (𝓞 F) D.2) σ).Equiv
    (labelledDualTateFactor K (fiber K D'.1 x).X ℓ F L hL
      (fiberPointsAction K (AlgebraicClosure K) D'.1 x (𝓞 F) D'.2)
      (fiberPointsAction_realized K (AlgebraicClosure K) D'.1 x (𝓞 F) D'.2) σ) := by
  subst D'
  exact Representation.Equiv.refl _

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Examples

/-- Equivariant equality of two covariant Tate factors preserves the trace of
their cohomological duals at the same Galois element. -/
theorem dual_character_eq_of_equiv
    {L G V W : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    {ρ : Representation L G V} {τ : Representation L G W}
    (e : ρ.Equiv τ) (g : G) :
    ρ.dual.character g = τ.dual.character g := by
  have h := Representation.char_iso (HilbertModularity.representationDualEquiv e)
  exact congrArg (fun f : G → L => f g) h

end HilbertModularity.Examples
