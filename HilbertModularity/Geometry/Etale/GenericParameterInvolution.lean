/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.CoordinateInvolution
public import HilbertModularity.Geometry.Etale.GeometricPointIso
public import HilbertModularity.Geometry.Etale.ArithmeticFieldEquiv
public import HilbertModularity.Geometry.Etale.PullbackComposition
public import HilbertModularity.Geometry.Etale.PathTransport
public import HilbertModularity.CategoryTheory.Conjugation

/-! # The complement automorphism at the generic parameter point

The actual rational-coordinate involution extends to the chosen geometric field.
Its spectrum map supplies a path between the generic fibre and its complement.
No path existence theorem or identification of cusp generators is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K]

/-- The extension of `t ↦ 1-t` to the geometric function field identifies the actual
complemented generic point with the original point. -/
def puncturedRationalPointComplementGeometricIso :
    Scheme.geometricPointOver (RatFunc K)
        (puncturedRationalPoint K ≫ (puncturedComplementIso K).hom) ≅
      Scheme.geometricPointOver (RatFunc K) (puncturedRationalPoint K) :=
  Over.isoMk (Scheme.Spec.mapIso
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure (RatFunc K))
      (AlgebraicClosure (RatFunc K)) (RatFunc.complementAlgEquiv K).toRingEquiv).toCommRingCatIso.op)
    (by
      rw [puncturedRationalPoint_complement]
      exact Scheme.geometricPointOver_fieldEquiv (RatFunc K) (RatFunc K)
        (RatFunc.complementAlgEquiv K).toRingEquiv (puncturedRationalPoint K))

/-- The actual generic finite étale fibre is isomorphic to the fibre at the complemented point. -/
def puncturedRationalPointComplementFiberIso :
    Scheme.finiteArithmeticFiberFunctor (RatFunc K) (puncturedRationalPoint K) ≅
      Scheme.finiteArithmeticFiberFunctor (RatFunc K)
        (puncturedRationalPoint K ≫ (puncturedComplementIso K).hom) :=
  Scheme.finiteEtaleFiberPointIso (AlgebraicClosure (RatFunc K)) (AlgebraicClosure (RatFunc K))
    _ _ (puncturedRationalPointComplementGeometricIso K).symm

/-- The chosen generic geometric point makes the actual complement map a continuous
fundamental-group automorphism, without asserting a formula for geometric cusp generators. -/
def genericComplementFundamentalAutomorphism :
    Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) ≃ₜ*
      Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) :=
  (Scheme.etaleFundamentalGroupIsoEquiv (puncturedComplementIso K)
    (RatFunc K) (puncturedRationalPoint K)).trans
    (Scheme.etaleFundamentalGroupPathEquiv (RatFunc K) (punctured K)
      (puncturedRationalPointComplementFiberIso K).symm)

/-- The generic complement first pulls back along the base automorphism and then
uses the chosen geometric-field path. -/
theorem genericComplementFundamentalAutomorphism_apply
    (g : Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)) :
    genericComplementFundamentalAutomorphism K g =
      Scheme.etaleFundamentalGroupPathEquiv (RatFunc K) (punctured K)
        (puncturedRationalPointComplementFiberIso K).symm
        (Scheme.etaleFundamentalGroupIsoEquiv (puncturedComplementIso K)
          (RatFunc K) (puncturedRationalPoint K) g) :=
  ContinuousMulEquiv.trans_apply
    (Scheme.etaleFundamentalGroupIsoEquiv (puncturedComplementIso K)
      (RatFunc K) (puncturedRationalPoint K))
    (Scheme.etaleFundamentalGroupPathEquiv (RatFunc K) (punctured K)
      (puncturedRationalPointComplementFiberIso K).symm) g

/-- The concrete generic fibre path intertwines arithmetic Galois actions by the
chosen algebraic-closure extension of the rational-coordinate involution. -/
theorem puncturedRationalPointComplementFiberIso_galois
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) :
    (puncturedRationalPointComplementFiberIso K).hom ≫
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc K)
          (puncturedRationalPoint K ≫ (puncturedComplementIso K).hom)
          (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
            (RatFunc.complementAlgEquiv K).toRingEquiv g)).hom =
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) g).hom ≫
        (puncturedRationalPointComplementFiberIso K).hom := by
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro v
  apply Over.OverMorphism.ext
  let σ := (RatFunc.complementAlgEquiv K).toRingEquiv
  let j := IsAlgClosure.equivOfEquiv (AlgebraicClosure (RatFunc K))
    (AlgebraicClosure (RatFunc K)) σ
  have hj : CommRingCat.ofHom j.toRingHom ≫
      CommRingCat.ofHom (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K) σ g).toRingHom =
        CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom j.toRingHom := by
    ext a
    exact AlgebraicClosure.galoisFieldEquiv_intertwines (RatFunc K) (RatFunc K) σ g a
  change Spec.map (CommRingCat.ofHom
      (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K) σ g).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom j.toRingHom) ≫ v.left) =
    Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ v.left)
  rw [← Category.assoc, ← Spec.map_comp, hj, Spec.map_comp, Category.assoc]

set_option maxHeartbeats 500000 in
/-- On the generic arithmetic subgroup, complement acts by the inverse closure-conjugation
map corresponding to `t ↦ 1-t`; no involutivity of the chosen closure lift is assumed. -/
theorem genericComplementFundamentalAutomorphism_galois
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) :
    genericComplementFundamentalAutomorphism K
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) g) =
      Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)
        ((AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
          (RatFunc.complementAlgEquiv K).toRingEquiv).symm g) := by
  let e := puncturedRationalPointComplementFiberIso K
  let φ := AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
    (RatFunc.complementAlgEquiv K).toRingEquiv
  let y := puncturedRationalPoint K ≫ (puncturedComplementIso K).hom
  have h₀ := puncturedRationalPointComplementFiberIso_galois K (φ.symm g)
  have h : e.hom ≫ (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) y g).hom =
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)
        (φ.symm g)).hom ≫ e.hom :=
    (congrArg (fun a => e.hom ≫ (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) y a).hom)
      (φ.apply_symm_apply g)).symm.trans h₀
  exact (genericComplementFundamentalAutomorphism_apply K _).trans
    ((congrArg (Scheme.etaleFundamentalGroupPathEquiv (RatFunc K) (punctured K) e.symm)
      (Scheme.etaleFundamentalGroupIsoEquiv_galois (puncturedComplementIso K)
        (RatFunc K) (puncturedRationalPoint K) g)).trans
      ((Scheme.etaleFundamentalGroupPathEquiv_apply (RatFunc K) (punctured K) e.symm _).trans
        (Iso.conjAut_symm_eq_of_intertwines e _ _ h)))

end AlgebraicGeometry.ProjectiveLine
