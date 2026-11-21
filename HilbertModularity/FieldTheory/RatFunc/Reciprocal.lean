/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! # Reciprocal coordinates on the rational function field

The coordinate `X⁻¹` is again a transcendental generator. Its associated
field automorphism exchanges the finite zero coordinate and infinity.
-/

@[expose] public noncomputable section
namespace RatFunc
open _root_.IntermediateField
variable (K : Type*) [Field K]

/-- The reciprocal coordinate is transcendental over the constant field. -/
theorem transcendental_inv_X : Transcendental K ((X : RatFunc K)⁻¹) := by
  rw [Transcendental, IsAlgebraic.inv_iff]
  exact transcendental_X

/-- The reciprocal coordinate generates the entire rational function field. -/
theorem adjoin_inv_X : K⟮(X : RatFunc K)⁻¹⟯ = ⊤ := by
  apply top_unique
  rw [← adjoin_X (K := K), adjoin_simple_le_iff]
  simpa only [inv_inv] using
    (K⟮(X : RatFunc K)⁻¹⟯).inv_mem (mem_adjoin_simple_self K ((X : RatFunc K)⁻¹))

/-- The constant-field automorphism sending the coordinate to its reciprocal. -/
def reciprocalAlgEquiv : RatFunc K ≃ₐ[K] RatFunc K :=
  (algEquivOfTranscendental ((X : RatFunc K)⁻¹) (transcendental_inv_X K)).trans
    ((IntermediateField.equivOfEq (adjoin_inv_X K)).trans IntermediateField.topEquiv)

@[simp]
theorem reciprocalAlgEquiv_X : reciprocalAlgEquiv K X = (X : RatFunc K)⁻¹ := by
  change (algEquivOfTranscendental ((X : RatFunc K)⁻¹) (transcendental_inv_X K) X :
    RatFunc K) = _
  exact algEquivOfTranscendental_X _ _

/-- Constant-field algebra maps of rational functions are determined by the coordinate. -/
theorem algHom_ext_X {L : Type*} [Field L] [Algebra K L]
    {f g : RatFunc K →ₐ[K] L} (h : f X = g X) : f = g := by
  apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
  apply Polynomial.algHom_ext
  change f (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
    g (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
  simpa only [algebraMap_X] using h

/-- Inverting the coordinate twice fixes every rational function. -/
@[simp]
theorem reciprocalAlgEquiv_twice (f : RatFunc K) :
    reciprocalAlgEquiv K (reciprocalAlgEquiv K f) = f := by
  have h : (reciprocalAlgEquiv K).toAlgHom.comp (reciprocalAlgEquiv K).toAlgHom =
      AlgHom.id K (RatFunc K) := by
    apply algHom_ext_X K
    simp
  exact AlgHom.congr_fun h f

end RatFunc
