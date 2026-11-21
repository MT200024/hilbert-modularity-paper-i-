/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricField
public import HilbertModularity.Geometry.GroupScheme.TorsionPoints
public import HilbertModularity.Topology.TateModule.Equiv

/-! # Geometric field extension on torsion points -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme
universe u
variable (Ω Ω' : Type u) [Field Ω] [Field Ω'] [Algebra Ω Ω']
  {S : Scheme.{u}} (x : Spec (CommRingCat.of Ω) ⟶ S) (A : CommGrp (Over S))

/-- Geometric field extension is the actual precomposition map on group-scheme points. -/
def geometricPointsFieldMap : Additive (Over.mk x ⟶ A.X) →+
    Additive (Over.mk (Spec.algebraMap Ω Ω' ≫ x) ⟶ A.X) :=
  ((yonedaMonObj A.X).map (Over.homMk
    (U := Over.mk (Spec.algebraMap Ω Ω' ≫ x)) (V := Over.mk x)
    (Spec.algebraMap Ω Ω') rfl).op).hom.toAdditive

/-- The point-group map is induced by the specified extension of geometric fields. -/
@[simp]
theorem geometricPointsFieldMap_apply (v : Additive (Over.mk x ⟶ A.X)) :
    (geometricPointsFieldMap Ω Ω' x A v).toMul =
      Over.homMk (U := Over.mk (Spec.algebraMap Ω Ω' ≫ x)) (V := Over.mk x)
        (Spec.algebraMap Ω Ω') rfl ≫ v.toMul := rfl

/-- Field extension commutes with every morphism of the original group schemes. -/
theorem geometricPointsFieldMap_natural (B : CommGrp (Over S)) (f : A ⟶ B) :
    (geometricPointsFieldMap Ω Ω' x B).comp
        (IsMonHom.monoidHom f.hom.hom.hom (Over.mk x)).toAdditive =
      (IsMonHom.monoidHom f.hom.hom.hom
        (Over.mk (Spec.algebraMap Ω Ω' ≫ x))).toAdditive.comp
        (geometricPointsFieldMap Ω Ω' x A) := by
  apply AddMonoidHom.ext
  intro v
  exact (Category.assoc _ v.toMul f.hom.hom.hom).symm

variable [IsAlgClosed Ω]

attribute [local instance] torsionObjectEtale torsionObjectIsFinite

/-- Finite étale prime-power multiplication makes geometric field extension bijective on torsion. -/
theorem torsionMap_geometricPointsFieldMap_bijective (p : ℕ) [Fact p.Prime] (n : ℕ)
    [IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left] [Etale (p ^ n • 𝟙 A).hom.hom.hom.left] :
    Function.Bijective (TateModule.torsionMap p (geometricPointsFieldMap Ω Ω' x A) n) := by
  let q := Over.homMk (U := Over.mk (Spec.algebraMap Ω Ω' ≫ x)) (V := Over.mk x)
    (Spec.algebraMap Ω Ω') rfl
  let e := CommGrp.torsionPointAddEquiv A (p ^ n) (Over.mk x)
  let e' := CommGrp.torsionPointAddEquiv A (p ^ n)
    (Over.mk (Spec.algebraMap Ω Ω' ≫ x))
  have h := Scheme.finiteEtaleFiberFieldMap_bijective Ω Ω' x
    (Scheme.finiteEtaleGroupCover (CommGrp.torsionObject A (p ^ n)))
  change Function.Bijective (fun v : Over.mk x ⟶ (CommGrp.torsionObject A (p ^ n)).X =>
    q ≫ v) at h
  have hn (v : Additive (Over.mk x ⟶ (CommGrp.torsionObject A (p ^ n)).X)) :
      TateModule.torsionMap p (geometricPointsFieldMap Ω Ω' x A) n (e v) =
        e' (Additive.ofMul (q ≫ v.toMul)) := by
    apply Subtype.ext
    change q ≫ (v.toMul ≫ Grp.kernelInclusion (p ^ n • 𝟙 A).hom) =
      (q ≫ v.toMul) ≫ Grp.kernelInclusion (p ^ n • 𝟙 A).hom
    exact (Category.assoc _ _ _).symm
  have h' : Function.Bijective (fun v :
      Additive (Over.mk x ⟶ (CommGrp.torsionObject A (p ^ n)).X) =>
      Additive.ofMul (q ≫ v.toMul)) := h
  have hh := e'.bijective.comp (h'.comp e.symm.bijective)
  convert hh using 1
  funext v
  simpa only [Function.comp_apply, AddEquiv.apply_symm_apply] using hn (e.symm v)

variable (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Geometric field extension identifies the actual integral Tate modules through their torsion. -/
def geometricTateFieldEquiv :
    TateModule.integral p (Additive (Over.mk x ⟶ A.X)) ≃ₗ[ℤ_[p]]
      TateModule.integral p (Additive (Over.mk (Spec.algebraMap Ω Ω' ≫ x) ⟶ A.X)) :=
  TateModule.equivOfTorsion p
    (fun n => LinearEquiv.ofBijective
      (TateModule.torsionMap p (geometricPointsFieldMap Ω Ω' x A) n)
      (torsionMap_geometricPointsFieldMap_bijective Ω Ω' x A p n))
    (fun n v => (TateModule.torsionMap_transition p
      (geometricPointsFieldMap Ω Ω' x A) n v).symm)

/-- The integral equivalence is the original covariant Tate map on its forward direction. -/
@[simp]
theorem geometricTateFieldEquiv_toLinearMap :
    (geometricTateFieldEquiv Ω Ω' x A p).toLinearMap =
      TateModule.map p (geometricPointsFieldMap Ω Ω' x A) := rfl

/-- Scalar extension identifies the rational Tate modules after geometric field extension. -/
def geometricRationalTateFieldEquiv :
    TateModule.rational p (Additive (Over.mk x ⟶ A.X)) ≃ₗ[ℚ_[p]]
      TateModule.rational p (Additive (Over.mk (Spec.algebraMap Ω Ω' ≫ x) ⟶ A.X)) :=
  LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ (geometricTateFieldEquiv Ω Ω' x A p)

/-- The rational equivalence is the usual rational covariant Tate map. -/
@[simp]
theorem geometricRationalTateFieldEquiv_toLinearMap :
    (geometricRationalTateFieldEquiv Ω Ω' x A p).toLinearMap =
      TateModule.rationalMap p (geometricPointsFieldMap Ω Ω' x A) := rfl

/-- The integral field-extension equivalence intertwines every original group-scheme endomorphism. -/
theorem geometricTateFieldEquiv_endomorphism (f : End A) :
    (geometricTateFieldEquiv Ω Ω' x A p).toLinearMap.comp
        (TateModule.map p (CommGrp.pointsEndomorphismMap (Over.mk x) A f)) =
      (TateModule.map p (CommGrp.pointsEndomorphismMap
        (Over.mk (Spec.algebraMap Ω Ω' ≫ x)) A f)).comp
        (geometricTateFieldEquiv Ω Ω' x A p).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact (Category.assoc _ (v.val n).val.toMul f.hom.hom.hom).symm

/-- Every original endomorphism is also intertwined after rationalizing the Tate modules. -/
theorem geometricRationalTateFieldEquiv_endomorphism (f : End A) :
    (geometricRationalTateFieldEquiv Ω Ω' x A p).toLinearMap.comp
        (TateModule.rationalMap p (CommGrp.pointsEndomorphismMap (Over.mk x) A f)) =
      (TateModule.rationalMap p (CommGrp.pointsEndomorphismMap
        (Over.mk (Spec.algebraMap Ω Ω' ≫ x)) A f)).comp
        (geometricRationalTateFieldEquiv Ω Ω' x A p).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    change c ⊗ₜ ((geometricTateFieldEquiv Ω Ω' x A p)
        (TateModule.map p (CommGrp.pointsEndomorphismMap (Over.mk x) A f) v)) =
      c ⊗ₜ (TateModule.map p (CommGrp.pointsEndomorphismMap
        (Over.mk (Spec.algebraMap Ω Ω' ≫ x)) A f)
        (geometricTateFieldEquiv Ω Ω' x A p v))
    exact congrArg (fun w => c ⊗ₜ[ℤ_[p]] w)
      (LinearMap.congr_fun (geometricTateFieldEquiv_endomorphism Ω Ω' x A p f) v)
  | add z w hz hw => simp only [map_add, hz, hw]

end AlgebraicGeometry.GroupScheme
