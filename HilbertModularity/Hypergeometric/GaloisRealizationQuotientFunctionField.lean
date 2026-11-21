/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotientFibreMap
public import HilbertModularity.Hypergeometric.GaloisRealizationInvariantFixedFieldOdd

/-! # The selected Euler quotient on function fields

The function-field map of a quotient morphism is taken from its map on
generic-point stalks.  This makes the function-field comparison refer to the
same selected morphism as the cohomological pullback.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback on generic-point local rings for a morphism that carries the
generic point to the generic point.  The underlying map is the stalk map of
the given morphism; no field embedding is selected independently. -/
def functionFieldMapOfGenericPoint {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (f.stalkMap (genericPoint X)).hom.comp
    (Y.presheaf.stalkSpecializes
      (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y)).hom

/-- The geometric conditions under which the function-field correspondence
for a smooth projective integral curve is used.  Smooth proper integral curves
over a field are projective; dimension one is retained explicitly. -/
def IsSmoothProperIntegralCurveOver {K : Type*} [Field K]
    (X : Scheme) (p : X ⟶ Spec (CommRingCat.of K)) : Prop :=
  IsProper p ∧ Smooth p ∧ topologicalKrullDim X = 1

/-- Canonical pullback on function fields is contravariantly functorial for
smooth projective integral curves.  The maps here are exactly the generic
stalk maps above, and the hypotheses retain the curve and dominant-map
conditions of [src_poonen_curves, §§2.1.1–2.1.2, p. 23].  This established
curve/function-field correspondence is a visible literature premise. -/
theorem functionFieldMapOfGenericPoint_comp_of_curves
    {K : Type*} [Field K] {X Y Z : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K))
    (pZ : Z ⟶ Spec (CommRingCat.of K))
    (hX : IsSmoothProperIntegralCurveOver X pX)
    (hY : IsSmoothProperIntegralCurveOver Y pY)
    (hZ : IsSmoothProperIntegralCurveOver Z pZ)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfK : f ≫ pY = pX) (hgK : g ≫ pZ = pY)
    (hf : f.base (genericPoint X) = genericPoint Y)
    (hg : g.base (genericPoint Y) = genericPoint Z)
    (hfg : (f ≫ g).base (genericPoint X) = genericPoint Z) :
    functionFieldMapOfGenericPoint (f ≫ g) hfg =
      (functionFieldMapOfGenericPoint f hf).comp
        (functionFieldMapOfGenericPoint g hg) := by
  sorry

/-- Invariance of a selected morphism gives fixedness of its *canonical*
function-field image.  No second field embedding is chosen. -/
theorem functionFieldMapOfGenericPoint_fixed_of_invariant
    {K : Type*} [Field K] {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y]
    (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K))
    (hX : IsSmoothProperIntegralCurveOver X pX)
    (hY : IsSmoothProperIntegralCurveOver Y pY)
    (s : X ⟶ X) (q : X ⟶ Y)
    (hsK : s ≫ pX = pX) (hqK : q ≫ pY = pX)
    (hs : s.base (genericPoint X) = genericPoint X)
    (hq : q.base (genericPoint X) = genericPoint Y)
    (hinv : s ≫ q = q) (u : Y.functionField) :
    functionFieldMapOfGenericPoint s hs
        (functionFieldMapOfGenericPoint q hq u) =
      functionFieldMapOfGenericPoint q hq u := by
  have hsq : (s ≫ q).base (genericPoint X) = genericPoint Y := by
    rw [hinv]
    exact hq
  have hcomp := functionFieldMapOfGenericPoint_comp_of_curves
    pX pX pY hX hX hY s q hsK hqK hs hq hsq
  have heq : functionFieldMapOfGenericPoint (s ≫ q) hsq =
      functionFieldMapOfGenericPoint q hq := by
    simp only [hinv]
  have h := congrArg (fun φ : Y.functionField →+* X.functionField => φ u)
    (hcomp.symm.trans heq)
  exact h

/-- If a curve model of the reflection fixed field factors through a selected
quotient map, then the *selected map's* generic-stalk image is exactly that
fixed field.  The factorization and model are geometric hypotheses; neither
is replaced by a new choice of quotient field embedding. -/
theorem functionFieldMapOfGenericPoint_range_eq_fixed_of_factor
    {K : Type*} [Field K] {X Y Z : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K))
    (pZ : Z ⟶ Spec (CommRingCat.of K))
    (hX : IsSmoothProperIntegralCurveOver X pX)
    (hY : IsSmoothProperIntegralCurveOver Y pY)
    (hZ : IsSmoothProperIntegralCurveOver Z pZ)
    (s : X ⟶ X) (q : X ⟶ Y) (r : X ⟶ Z)
    (hsK : s ≫ pX = pX) (hqK : q ≫ pY = pX)
    (hs : s.base (genericPoint X) = genericPoint X)
    (hq : q.base (genericPoint X) = genericPoint Y)
    (hr : r.base (genericPoint X) = genericPoint Z)
    (hinv : s ≫ q = q)
    (hmodel : Set.range (functionFieldMapOfGenericPoint r hr) =
      {v : X.functionField | functionFieldMapOfGenericPoint s hs v = v})
    (hfactor : ∃ g : Y ⟶ Z, q ≫ g = r ∧ g ≫ pZ = pY) :
    Set.range (functionFieldMapOfGenericPoint q hq) =
      {v : X.functionField | functionFieldMapOfGenericPoint s hs v = v} := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact functionFieldMapOfGenericPoint_fixed_of_invariant
      pX pY hX hY s q hsK hqK hs hq hinv u
  · intro hv
    rw [← hmodel] at hv
    obtain ⟨u, rfl⟩ := hv
    obtain ⟨g, hqg, hgK⟩ := hfactor
    have hqg_generic : (q ≫ g).base (genericPoint X) = genericPoint Z := by
      simpa only [hqg] using hr
    have hg : g.base (genericPoint Y) = genericPoint Z := by
      change g.base (q.base (genericPoint X)) = genericPoint Z at hqg_generic
      simpa only [hq] using hqg_generic
    have hcomp := functionFieldMapOfGenericPoint_comp_of_curves
      pX pY pZ hX hY hZ q g hqK hgK hq hg hqg_generic
    have heq : functionFieldMapOfGenericPoint (q ≫ g) hqg_generic =
        functionFieldMapOfGenericPoint r hr := by
      simp only [hqg]
    refine ⟨functionFieldMapOfGenericPoint g hg u, ?_⟩
    exact congrArg (fun φ : Z.functionField →+* X.functionField => φ u)
      (hcomp.symm.trans heq)

/-- The selected quotient's universal property supplies the factorization
used above.  Uniqueness also forces that factorization to respect the ground
field, so the same curve/function-field comparison applies. -/
theorem functionFieldMapOfGenericPoint_range_eq_fixed_of_universal
    {K : Type*} [Field K] {X Y Z : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (pX : X ⟶ Spec (CommRingCat.of K))
    (pY : Y ⟶ Spec (CommRingCat.of K))
    (pZ : Z ⟶ Spec (CommRingCat.of K))
    (hX : IsSmoothProperIntegralCurveOver X pX)
    (hY : IsSmoothProperIntegralCurveOver Y pY)
    (hZ : IsSmoothProperIntegralCurveOver Z pZ)
    (s : X ⟶ X) (q : X ⟶ Y) (r : X ⟶ Z)
    (hsK : s ≫ pX = pX) (hqK : q ≫ pY = pX)
    (hrK : r ≫ pZ = pX)
    (hs : s.base (genericPoint X) = genericPoint X)
    (hq : q.base (genericPoint X) = genericPoint Y)
    (hr : r.base (genericPoint X) = genericPoint Z)
    (hinv : s ≫ q = q) (hrInv : s ≫ r = r)
    (hmodel : Set.range (functionFieldMapOfGenericPoint r hr) =
      {v : X.functionField | functionFieldMapOfGenericPoint s hs v = v})
    (hquotient : ∀ (T : Scheme) (f : X ⟶ T), s ≫ f = f →
      ∃! g : Y ⟶ T, q ≫ g = f) :
    Set.range (functionFieldMapOfGenericPoint q hq) =
      {v : X.functionField | functionFieldMapOfGenericPoint s hs v = v} := by
  obtain ⟨g, hg, _⟩ := hquotient Z r hrInv
  obtain ⟨j, hj, hjunique⟩ := hquotient (Spec (CommRingCat.of K)) pX hsK
  have hgp : g ≫ pZ = pY := by
    have h1 : q ≫ (g ≫ pZ) = pX := by
      rw [← Category.assoc, hg, hrK]
    exact (hjunique (g ≫ pZ) h1).trans (hjunique pY hqK).symm
  exact functionFieldMapOfGenericPoint_range_eq_fixed_of_factor
    pX pY pZ hX hY hZ s q r hsK hqK hs hq hr hinv hmodel
      ⟨g, hg, hgp⟩

end AlgebraicGeometry.Scheme

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic
open AlgebraicGeometry CategoryTheory

/-- The generic-stalk pullback of the *specialized chosen Euler quotient* is
fixed by the same proper reflection used to construct that quotient.  The
displayed hypotheses are the as-yet separate geometric requirements for
using the smooth-curve function-field correspondence on these fibres. -/
theorem smoothProperEulerFibreToRealQuotient_functionField_fixed
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    [IsIntegral (smoothProperEulerFibre N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))]
    [IsIntegral (cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ)]
    (hC : Scheme.IsSmoothProperIntegralCurveOver
      (smoothProperEulerFibre N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ))
      (smoothProperEulerFibreStructureMap N m 𝒞
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ)))
    (hQ : Scheme.IsSmoothProperIntegralCurveOver
      (cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ)
      (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ))
    (hs : (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ)).hom.base
        (genericPoint _) = genericPoint _)
    (hq : (smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ).base
        (genericPoint _) = genericPoint _)
    (u : (cyclotomicRealEulerQuotientFibre N m 𝒞 𝒬 ξ).functionField) :
    Scheme.functionFieldMapOfGenericPoint
      (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution
        (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
        (one_sub_realEulerParameter_isUnit N ξ)).hom hs
      (Scheme.functionFieldMapOfGenericPoint
        (smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ) hq u) =
      Scheme.functionFieldMapOfGenericPoint
        (smoothProperEulerFibreToRealQuotient N m 𝒞 𝒬 ξ) hq u := by
  exact Scheme.functionFieldMapOfGenericPoint_fixed_of_invariant
    (smoothProperEulerFibreStructureMap N m 𝒞
      (realEulerParameter N ξ) (realEulerParameter_isUnit N ξ)
      (one_sub_realEulerParameter_isUnit N ξ))
    (cyclotomicRealEulerQuotientFibreStructureMap N m 𝒞 𝒬 ξ)
    hC hQ _ _
    (smoothProperEulerFibreAutomorphism_snd N m 𝒞 𝒬.involution ξ)
    (smoothProperEulerFibreToRealQuotient_overField N m 𝒞 𝒬 ξ)
    hs hq (smoothProperEulerFibreToRealQuotient_invariant N m 𝒞 𝒬 ξ) u

end HilbertModularity.Hypergeometric
