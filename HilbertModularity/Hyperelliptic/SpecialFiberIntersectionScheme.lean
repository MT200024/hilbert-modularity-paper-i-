/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberIntersectionRing

/-! # Affine test schemes on the intersection of the signed components

The two maps to the square-branch affine cover agree on a test affine scheme
precisely when their base maps coincide and the branch polynomial vanishes.
This is the functor-of-points certificate for the scheme-theoretic
intersection, without a claim about the completed local rings of the nodes.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace HilbertModularity.Hyperelliptic

universe u
variable {k : Type u} [Field k]

/-- An affine test scheme mapped to the affine line by an algebra map. -/
def componentTestMap {A : Type u} [CommRing A] [Algebra k A]
    (f : k[X] →ₐ[k] A) :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k[X]) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

/-- The signed affine components have the expected intersection functor on
affine test schemes. -/
theorem componentTestMap_compositions_eq_iff {A : Type u} [CommRing A] [Algebra k A]
    (H : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    componentTestMap f ≫
        Spec.map (CommRingCat.ofHom (positiveComponent H).toRingHom) =
      componentTestMap g ≫
        Spec.map (CommRingCat.ofHom (negativeComponent H).toRingHom) ↔
      f = g ∧ f H = 0 := by
  have hspec :
      (componentTestMap f ≫
          Spec.map (CommRingCat.ofHom (positiveComponent H).toRingHom) =
        componentTestMap g ≫
          Spec.map (CommRingCat.ofHom (negativeComponent H).toRingHom)) ↔
        f.comp (positiveComponent H) = g.comp (negativeComponent H) := by
    simp only [componentTestMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Spec.map_inj]
    constructor
    · intro h
      apply AlgHom.coe_ringHom_injective
      exact congrArg (fun φ : CommRingCat.of (SquareBranchRing H) ⟶
        CommRingCat.of A => φ.hom) h
    · intro h
      exact congrArg (fun φ : SquareBranchRing H →ₐ[k] A =>
        CommRingCat.ofHom φ.toRingHom) h
  exact hspec.trans (component_compositions_eq_iff H h2 f g)

private theorem componentTestMap_compositions_eq_iff_comp
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (pos neg : B →ₐ[k] k[X]) (f g : k[X] →ₐ[k] A) :
    componentTestMap f ≫ Spec.map (CommRingCat.ofHom pos.toRingHom) =
      componentTestMap g ≫ Spec.map (CommRingCat.ofHom neg.toRingHom) ↔
      f.comp pos = g.comp neg := by
  simp only [componentTestMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Spec.map_inj]
  constructor
  · intro h
    apply AlgHom.coe_ringHom_injective
    exact congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of A => φ.hom) h
  · intro h
    exact congrArg (fun φ : B →ₐ[k] A =>
      CommRingCat.ofHom φ.toRingHom) h

/-- The actual finite-chart component intersection is represented on affine
test schemes by the quotient by `X * P`. -/
theorem finiteComponentTestMap_compositions_eq_iff_intersection_factor
    {A : Type u} [CommRing A] [Algebra k A]
    (P : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    componentTestMap f ≫
        Spec.map (CommRingCat.ofHom (finitePositiveComponent P).toRingHom) =
      componentTestMap g ≫
        Spec.map (CommRingCat.ofHom (finiteNegativeComponent P).toRingHom) ↔
      f = g ∧ ∃! q : componentIntersectionRing (finiteComponentPolynomial P) →ₐ[k] A,
        q.comp (componentIntersectionQuotient (finiteComponentPolynomial P)) = f := by
  exact (componentTestMap_compositions_eq_iff_comp
    (finitePositiveComponent P) (finiteNegativeComponent P) f g).trans
      (finiteComponent_compositions_eq_iff_intersection_factor P h2 f g)

/-- On the reciprocal chart the intersection is represented by the quotient
by `P.reverse`; its origin is absent for monic `P` by the existing disjointness
lemma. -/
theorem infinityComponentTestMap_compositions_eq_iff_intersection_factor
    {A : Type u} [CommRing A] [Algebra k A]
    (P : k[X]) (h2 : (2 : k) ≠ 0) (f g : k[X] →ₐ[k] A) :
    componentTestMap f ≫
        Spec.map (CommRingCat.ofHom (infinityPositiveComponent P).toRingHom) =
      componentTestMap g ≫
        Spec.map (CommRingCat.ofHom (infinityNegativeComponent P).toRingHom) ↔
      f = g ∧ ∃! q : componentIntersectionRing (infinityComponentPolynomial P) →ₐ[k] A,
        q.comp (componentIntersectionQuotient (infinityComponentPolynomial P)) = f := by
  exact (componentTestMap_compositions_eq_iff_comp
    (infinityPositiveComponent P) (infinityNegativeComponent P) f g).trans
      (infinityComponent_compositions_eq_iff_intersection_factor P h2 f g)

end HilbertModularity.Hyperelliptic
