/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.TateModule
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.FieldTheory.Galois.Profinite

/-! # Covariant Tate modules of commutative group schemes

Geometric points are morphisms from the spectrum of an algebraic closure in the
category of schemes over the ground field. Field automorphisms act by
precomposition on these morphisms and therefore covariantly on torsion points.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

namespace GroupScheme

universe u

variable (K : Type u) [Field K] (E : Type u) [Field E] [Algebra K E]

/-- The spectrum of an extension field, regarded as a scheme over `K`. -/
def fieldPoint : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E)))

/-- The `E`-valued points of a group scheme, written additively. -/
abbrev Points (A : Over (Spec (CommRingCat.of K))) :=
  Additive (fieldPoint K E ⟶ A)

variable (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

instance pointsAddCommGroup : AddCommGroup (Points K E A) := inferInstance

/-- An extension-field automorphism induces a morphism of spectra over `K`. -/
def fieldPointMap (g : E ≃ₐ[K] E) : fieldPoint K E ⟶ fieldPoint K E :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap K E))
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r)

@[simp]
theorem fieldPointMap_one : fieldPointMap K E 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (1 : E ≃ₐ[K] E).toRingHom) = 𝟙 _
  exact Spec.map_id _

/-- Contravariance of spectra gives the order needed for the left action on points. -/
theorem fieldPointMap_mul (g h : E ≃ₐ[K] E) :
    fieldPointMap K E (g * h) = fieldPointMap K E g ≫ fieldPointMap K E h := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The usual Galois action on geometric points, before passing to torsion. -/
instance pointsDistribMulAction : DistribMulAction (E ≃ₐ[K] E) (Points K E A) where
  smul g x := Additive.ofMul (fieldPointMap K E g ≫ x.toMul)
  one_smul x := by
    change fieldPointMap K E 1 ≫ x.toMul = x.toMul
    rw [fieldPointMap_one, Category.id_comp]
  mul_smul g h x := by
    change fieldPointMap K E (g * h) ≫ x.toMul =
      fieldPointMap K E g ≫ (fieldPointMap K E h ≫ x.toMul)
    rw [fieldPointMap_mul, Category.assoc]
  smul_zero g := by
    change fieldPointMap K E g ≫ (1 : fieldPoint K E ⟶ A) = 1
    exact MonObj.comp_one _
  smul_add g x y := by
    change fieldPointMap K E g ≫ (x.toMul * y.toMul) =
      (fieldPointMap K E g ≫ x.toMul) * (fieldPointMap K E g ≫ y.toMul)
    exact MonObj.comp_mul _ _ _

/-- Geometric points carry the discrete topology used in the torsion inverse limit. -/
instance pointsTopologicalSpace : TopologicalSpace (Points K E A) := ⊥

instance pointsDiscreteTopology : DiscreteTopology (Points K E A) := ⟨rfl⟩

omit [IsCommMonObj A] in
/-- On a geometric point the action is precomposition by the induced spectrum map. -/
@[simp]
theorem points_smul (g : E ≃ₐ[K] E) (x : Points K E A) :
    (g • x).toMul = fieldPointMap K E g ≫ x.toMul := rfl

omit [GrpObj A] [IsCommMonObj A] in
/-- A geometric point over an algebraic extension has closed image on a separated scheme. -/
theorem isClosed_point [Algebra.IsIntegral K E] [IsSeparated A.hom]
    (x : Points K E A) : IsClosed {x.toMul.left (IsLocalRing.closedPoint E)} := by
  let : Subsingleton (fieldPoint K E).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of E)))
  have hcomp : IsIntegralHom (x.toMul.left ≫ A.hom) := by
    rw [Over.w]
    change IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K E)))
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  have : IsIntegralHom x.toMul.left := IsIntegralHom.of_comp _ A.hom
  have h := x.toMul.left.isClosedMap.isClosed_range
  have hr : Set.range x.toMul.left = {x.toMul.left (IsLocalRing.closedPoint E)} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg x.toMul.left (Subsingleton.elim _ _)
    · intro hy
      exact ⟨IsLocalRing.closedPoint E, hy.symm⟩
  rwa [hr] at h

omit [GrpObj A] [IsCommMonObj A] in
/-- The residue field of a geometric point is finite over the base field. -/
theorem isFinite_point_residue [Algebra.IsIntegral K E] [IsSeparated A.hom]
    [LocallyOfFiniteType A.hom] (x : Points K E A) :
    IsFinite (A.left.fromSpecResidueField (x.toMul.left (IsLocalRing.closedPoint E)) ≫ A.hom) := by
  have hx := isClosed_point K E A x
  rw [isClosed_singleton_iff_isClosedImmersion] at hx
  rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
  infer_instance

omit [GrpObj A] [IsCommMonObj A] in
/-- A geometric point is fixed by the automorphisms fixing a finite intermediate field. -/
theorem exists_finite_fixing_field [Algebra.IsIntegral K E] [IsSeparated A.hom]
    [LocallyOfFiniteType A.hom] (x : Points K E A) :
    ∃ L : IntermediateField K E, FiniteDimensional K L ∧
      ∀ g ∈ L.fixingSubgroup, fieldPointMap K E g ≫ x.toMul = x.toMul := by
  let f : Spec (CommRingCat.of E) ⟶ A.left := x.toMul.left
  let t := f (IsLocalRing.closedPoint E)
  let F := A.left.residueField t
  let j : F ⟶ CommRingCat.of E :=
    A.left.descResidueField (Scheme.stalkClosedPointTo f)
  let k : CommRingCat.of K ⟶ F :=
    Spec.preimage (A.left.fromSpecResidueField t ≫ A.hom)
  have hj : k ≫ j = CommRingCat.ofHom (algebraMap K E) := by
    rw [← Spec.map_inj, Spec.map_comp]
    change Spec.map j ≫ Spec.map (Spec.preimage _) = _
    rw [Spec.map_preimage, ← Category.assoc]
    change (Spec.map (A.left.descResidueField (Scheme.stalkClosedPointTo f)) ≫
      A.left.fromSpecResidueField _) ≫ A.hom = _
    rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    exact x.toMul.w
  let : Algebra K F := k.hom.toAlgebra
  have hf : k.hom.Finite := by
    rw [← IsFinite.SpecMap_iff]
    change IsFinite (Spec.map (Spec.preimage _))
    rw [Spec.map_preimage]
    exact isFinite_point_residue K E A x
  let : FiniteDimensional K F := hf
  let φ : F →ₐ[K] E :=
    { __ := j.hom
      commutes' r := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of E => f r) hj }
  let L := φ.fieldRange
  let : FiniteDimensional K L := φ.toLinearMap.finiteDimensional_range
  refine ⟨L, inferInstance, ?_⟩
  intro g hg
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ f = f
  have hfactor : Spec.map j ≫ A.left.fromSpecResidueField t = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField E A.left f
  rw [← hfactor, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact (IntermediateField.mem_fixingSubgroup_iff L g).mp hg (φ a) ⟨a, rfl⟩

omit [IsCommMonObj A] in
/-- The stabilizer of a geometric point is open in the Krull topology. -/
theorem isOpen_point_stabilizer [Algebra.IsIntegral K E] [IsSeparated A.hom]
    [LocallyOfFiniteType A.hom] (x : Points K E A) :
    IsOpen (MulAction.stabilizer (E ≃ₐ[K] E) x : Set (E ≃ₐ[K] E)) := by
  obtain ⟨L, hL, hfix⟩ := exists_finite_fixing_field K E A x
  let := hL
  exact Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) hfix L.fixingSubgroup_isOpen

/-- The actual action on geometric points is continuous for their discrete topology. -/
instance pointsContinuousSMul [Algebra.IsIntegral K E] [IsSeparated A.hom]
    [LocallyOfFiniteType A.hom] : ContinuousSMul (E ≃ₐ[K] E) (Points K E A) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  exact isOpen_point_stabilizer K E A

variable (p : ℕ) [Fact p.Prime]

/-- The integral Tate module of the actual geometric points of the group scheme. -/
abbrev integralTate := TateModule.integral p (Points K (AlgebraicClosure K) A)

/-- The rational covariant Tate module of the group scheme. -/
abbrev rationalTate := TateModule.rational p (Points K (AlgebraicClosure K) A)

/-- The absolute Galois representation on the integral Tate module. -/
def integralTateRepresentation : Representation ℤ_[p]
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (integralTate K A p) :=
  TateModule.representation p _ _

/-- The absolute Galois action on the integral Tate module is jointly continuous. -/
theorem continuous_integralTateRepresentation [IsSeparated A.hom]
    [LocallyOfFiniteType A.hom] :
    Continuous (fun gx : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) × integralTate K A p =>
      integralTateRepresentation K A p gx.1 gx.2) :=
  TateModule.continuous_representation_apply p _ _

/-- The absolute Galois representation on the covariant rational Tate module. -/
def tateRepresentation : Representation ℚ_[p]
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (rationalTate K A p) :=
  TateModule.rationalRepresentation p _ _

/-- The covariant representation fixes `Q_p` and acts on the compatible torsion points. -/
@[simp]
theorem tateRepresentation_tmul (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (c : ℚ_[p]) (x : integralTate K A p) :
    tateRepresentation K A p g (c ⊗ₜ x) =
      c ⊗ₜ integralTateRepresentation K A p g x := rfl

/-- The rational covariant Tate action is jointly continuous in characteristic zero. -/
theorem continuous_tateRepresentation [CharZero K] [IsSeparated A.hom]
    [LocallyOfFiniteType A.hom] :
    Continuous (fun gx : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) × rationalTate K A p =>
      tateRepresentation K A p gx.1 gx.2) :=
  TateModule.continuous_rationalRepresentation_apply p _ _

end GroupScheme

end AlgebraicGeometry
