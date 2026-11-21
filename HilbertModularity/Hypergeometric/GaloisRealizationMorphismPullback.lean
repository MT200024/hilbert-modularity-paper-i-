/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Cohomology.Functoriality

/-! # Pullback on degree-one cohomology for scheme morphisms

The existing cohomology API constructs pullback for scheme isomorphisms.
This named standard functoriality input extends it to morphisms, including
the specialized Euler quotient map.  It concerns the cohomology theory in
general and contains no Euler trace or representation comparison.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Contravariant pullback on the actual integral degree-one pro-étale
cohomology, compatible with the already constructed isomorphism pullback.
The identity and composition laws are the standard inverse-image
functoriality of [src_milne_lec, §8, Proposition 8.7], applied to the
pro-étale coefficient model [proetale2015, §4]. -/
structure EllAdicCohomologyMorphismPullback (ℓ : ℕ) [Fact ℓ.Prime] where
  map : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) →
    Y.EllAdicCohomology ℓ 1 →ₗ[ℤ_[ℓ]] X.EllAdicCohomology ℓ 1
  map_id : ∀ (X : Scheme.{u}), map (𝟙 X) = LinearMap.id
  map_comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = (map f).comp (map g)
  map_iso : ∀ {X Y : Scheme.{u}} (e : X ≅ Y),
    map e.hom = (ellAdicCohomologyLinearEquiv e ℓ 1).toLinearMap

/-- Standard morphism pullback for the actual pro-étale cohomology model.
The cited inverse-image and coefficient comparison are the only admitted
construction here; the input makes no assertion about the Euler quotient.
[src_milne_lec, §8, Proposition 8.7; proetale2015, §4] -/
theorem exists_ellAdicCohomologyMorphismPullback (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (EllAdicCohomologyMorphismPullback.{u} ℓ) := by
  sorry

/-- A fixed functorial choice of cohomological morphism pullback. -/
def ellAdicCohomologyMorphismPullback (ℓ : ℕ) [Fact ℓ.Prime] :
    EllAdicCohomologyMorphismPullback.{u} ℓ :=
  Classical.choice (exists_ellAdicCohomologyMorphismPullback ℓ)

end AlgebraicGeometry.Scheme
