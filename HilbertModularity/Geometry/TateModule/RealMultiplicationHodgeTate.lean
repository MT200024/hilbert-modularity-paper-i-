/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.Geometry.TateModule.CoefficientDual
public import HilbertModularity.RepresentationTheory.LabelledCharacterAlgebraization
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Labelled Hodge–Tate comparison for real-multiplication abelian varieties

This is the standard geometric input for the cohomological RM factor in
[TripathiGoswamiRevised, Theorem `thm:RMgeneral`]. It concerns the actual
abelian variety, its endomorphism action and its contragredient Tate factor.
It does not assert an Euler comparison, determinant identity or modularity.
-/

public noncomputable section

open CategoryTheory NumberField IsDedekindDomain NumberField.LocalGalois
open scoped CategoryTheory.MonObj
attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace AlgebraicGeometry.GroupScheme

/-- [src_brinon_conrad, Theorem 2.2.3, p. 13; Example 2.4.13, pp. 24–25]
gives the functorial smooth-proper Hodge–Tate comparison. Its degree-one
application to this abelian variety is identified with the contragredient Tate
module by [MilneAV, I Theorem 12.1(a), p. 55]. Endomorphism functoriality and
finite coefficient extension retain the specified RM idempotent and every
embedding of the local base field.

The multiplicities use the standard complex-torus description
[MilneAV, I Proposition 2.1, pp. 10–11; Theorem 2.9, p. 14]. At each complex
embedding of the ground number field, complex conjugation exchanges the
holomorphic and antiholomorphic pieces and preserves each totally real RM
label. Their equal dimensions sum to the rank two of this labelled factor,
so both are one. Characteristic-zero comparison and base change transport
these dimensions to each local embedding. These comparison and labelled
linear-algebra consequences are included in this named literature input;
none of the cited passages is claimed to state this entire Lean signature
verbatim. The convention is cohomological weights `{0,1}`, cyclotomic weight
`-1`, with no Tate twist and no good-reduction hypothesis at `p`. -/
theorem labelledDualTate_hodgeTate_of_totallyReal
    (K : Type) [Field K] [NumberField K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom]
    (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [NumberField F] (hreal : NumberField.IsTotallyReal F)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A.X))
    (hφ : ∀ a, ∃ (f : A.X ⟶ A.X) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (σ : F →ₐ[ℚ] L)
    {V : Type} [AddCommGroup V] [Module L V] [Module ℚ_[p] V]
    [IsScalarTower ℚ_[p] L V] [FiniteDimensional L V] [FiniteDimensional ℚ_[p] V]
    [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V]
    [ContinuousSMul L V] [IsModuleTopology ℚ_[p] V] [IsModuleTopology L V]
    (ρ : Representation L (HilbertModularity.HilbertModularForms.AbsoluteGalois K) V)
    (e : ρ.Equiv (labelledDualTateFactor K A.X p F L hL φ hφ σ))
    (hdim : Module.finrank L V = 2) :
    (∀ (q : HeightOneSpectrum (𝓞 K))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion K))
        (Representation.restrictScalars ℚ_[p] (ρ.comp (localGaloisRestriction p K q))))) ∧
    (∀ (q : HeightOneSpectrum (𝓞 K))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion K →ₐ[ℚ_[p]] AlgebraicClosure L) (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion K))
        (ρ.comp (localGaloisRestriction p K q)) n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) := by
  sorry

end AlgebraicGeometry.GroupScheme
