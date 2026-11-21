/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.PullbackComposition

/-! # Pointed automorphisms of actual étale fundamental groups

A scheme automorphism fixing a rational point acts continuously on its actual
profinite fundamental group. The arithmetic loops from that point are fixed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K] {S : Scheme.{u}}
  (e : S ≅ S) (x : Spec (CommRingCat.of K) ⟶ S) (hx : x ≫ e.hom = x)

/-- A pointed scheme automorphism acts on the actual profinite fundamental group. -/
def etaleFundamentalGroupPointedAutomorphism :
    etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K x :=
  Eq.mp (congrArg (fun y : Spec (CommRingCat.of K) ⟶ S =>
    etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K y) hx)
      (etaleFundamentalGroupIsoEquiv e K x)

/-- A pointed scheme automorphism fixes the arithmetic loops from its rational base point. -/
theorem etaleFundamentalGroupPointedAutomorphism_galois
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    etaleFundamentalGroupPointedAutomorphism K e x hx
      (galoisToEtaleFundamentalGroup K x g) = galoisToEtaleFundamentalGroup K x g := by
  have transport (y : Spec (CommRingCat.of K) ⟶ S) (hy : y = x)
      (a : etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K y)
      (ha : a (galoisToEtaleFundamentalGroup K x g) = galoisToEtaleFundamentalGroup K y g) :
      (Eq.mp (congrArg (fun z : Spec (CommRingCat.of K) ⟶ S =>
        etaleFundamentalGroup K x ≃ₜ* etaleFundamentalGroup K z) hy) a)
          (galoisToEtaleFundamentalGroup K x g) =
          galoisToEtaleFundamentalGroup K x g := by
    subst y
    exact ha
  exact transport (x ≫ e.hom) hx (etaleFundamentalGroupIsoEquiv e K x)
    (etaleFundamentalGroupIsoEquiv_galois e K x g)

end AlgebraicGeometry.Scheme
