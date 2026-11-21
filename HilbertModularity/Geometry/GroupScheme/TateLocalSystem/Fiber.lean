/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Equiv
public import HilbertModularity.Geometry.GroupScheme.FiberPoints
public import HilbertModularity.Geometry.GroupScheme.TateMonodromy
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.Topology

/-! # Actual Tate representations of the pullback fibre -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Arithmetic specialization of actual integral Tate monodromy is the Tate representation of the pullback fibre. -/
def integralGeometricFiberTateEquiv :
    Representation.Equiv
      ((integralTateMonodromy K x A p).comp (Scheme.galoisToEtaleFundamentalGroup K x))
      (integralTateRepresentation K (fiber K A x).X p) :=
  .mk (TateModule.mapEquiv p (geometricFiberPointsAddEquiv K A x)) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    apply Subtype.ext
    have h₁ := congrArg (geometricFiberPointsMulEquiv K A x)
      (integralTateMonodromy_arithmetic_projection K x A p g v n)
    have h₂ := geometricFiberPointsAddEquiv_arithmetic K A x g (v.val n).val
    exact h₁.trans h₂)

/-- The integral arithmetic comparison is the ordinary Tate map of the point equivalence. -/
@[simp]
theorem integralGeometricFiberTateEquiv_toLinearEquiv :
    (integralGeometricFiberTateEquiv K A x p).toLinearEquiv =
      TateModule.mapEquiv p (geometricFiberPointsAddEquiv K A x) := rfl

/-- Rational arithmetic specialization agrees with the covariant rational Tate representation of the actual fibre. -/
def rationalGeometricFiberTateEquiv :
    Representation.Equiv
      ((rationalTateMonodromy K x A p).comp (Scheme.galoisToEtaleFundamentalGroup K x))
      (tateRepresentation K (fiber K A x).X p) :=
  .mk (TateModule.rationalMapEquiv p (geometricFiberPointsAddEquiv K A x))
    ((integralGeometricFiberTateEquiv K A x p).baseChange ℚ_[p]).isIntertwining'

/-- The rational arithmetic comparison is scalar extension of the point-induced Tate equivalence. -/
@[simp]
theorem rationalGeometricFiberTateEquiv_toLinearEquiv :
    (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv =
      TateModule.rationalMapEquiv p (geometricFiberPointsAddEquiv K A x) := rfl

/-- The rational fibre comparison fixes coefficients and extends the integral comparison. -/
@[simp]
theorem rationalGeometricFiberTateEquiv_tmul
    (c : ℚ_[p]) (v : TateModule.integral p
      (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalGeometricFiberTateEquiv K A x p (c ⊗ₜ v) =
      c ⊗ₜ integralGeometricFiberTateEquiv K A x p v := rfl

/-- The actual integral Tate family specializes to the Tate representation of its pullback fibre. -/
def integralTateLocalSystem_arithmeticEquiv :
    Representation.Equiv
      (Scheme.arithmeticFiberRepresentation K S (integralTateLocalSystem K A p) x)
      (integralTateRepresentation K (fiber K A x).X p) := by
  let e := integralGeometricFiberTateEquiv K A x p
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  have h₁ := congrArg e (integralTateLocalSystem_loop K A p x
    (Scheme.galoisToEtaleFundamentalGroup K x g) v)
  have h₂ := LinearMap.congr_fun (e.isIntertwining' g) v
  exact h₁.trans h₂

variable [Surjective (p • 𝟙 A).hom.hom.hom.left]

set_option maxHeartbeats 400000 in
/-- The single continuous Tate local system specializes to the ordinary covariant Tate representation of its actual fibre. -/
def tateEtaleLocalSystem_arithmeticEquiv :
    Representation.Equiv
      ((tateEtaleLocalSystem K A p).arithmeticRepresentation x)
      (tateRepresentation K (fiber K A x).X p) := by
  let e := rationalGeometricFiberTateEquiv K A x p
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  have h₁ := congrArg e (rationalTateLocalSystem_loop K A p x
    (Scheme.galoisToEtaleFundamentalGroup K x g) v)
  have h₂ := LinearMap.congr_fun (e.isIntertwining' g) v
  exact h₁.trans h₂


end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A B : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 B).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 B).hom.hom.hom.left]

/-- The arithmetic Tate comparison respects maps of the original families, including their coefficient endomorphisms. -/
theorem integralGeometricFiberTateEquiv_natural (f : A ⟶ B) :
    (integralGeometricFiberTateEquiv K B x p).toLinearEquiv.toLinearMap.comp
        (TateModule.map p
          (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive) =
      (integralTateMap K p ((Over.pullback x).mapCommGrp.map f).hom.hom.hom).comp
        (integralGeometricFiberTateEquiv K A x p).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact geometricFiberPointsAddEquiv_map K A B x f (v.val n).val




set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational fibre comparison preserves the maps induced by the same original family morphism. -/
theorem rationalGeometricFiberTateEquiv_natural (f : A ⟶ B) :
    (rationalGeometricFiberTateEquiv K B x p).toLinearEquiv.toLinearMap.comp
        (TateModule.rationalMap p
          (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive) =
      (rationalTateMap K p (A := (fiber K A x).X) (B := (fiber K B x).X)
        ((Over.pullback x).mapCommGrp.map f).hom.hom.hom).comp
        (rationalGeometricFiberTateEquiv K A x p).toLinearEquiv.toLinearMap := by
  let f₀ : TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) →ₗ[ℚ_[p]]
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ B.X)) :=
    TateModule.rationalMap p
      (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive
  let g₀ : rationalTate K (fiber K A x).X p →ₗ[ℚ_[p]] rationalTate K (fiber K B x).X p :=
    rationalTateMap K p (A := (fiber K A x).X) (B := (fiber K B x).X)
      ((Over.pullback x).mapCommGrp.map f).hom.hom.hom
  have hB := congrArg (fun e :
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ B.X)) ≃ₗ[ℚ_[p]]
        rationalTate K (fiber K B x).X p => e.toLinearMap.comp f₀)
    (rationalGeometricFiberTateEquiv_toLinearEquiv K B x p)
  have hA := congrArg (fun e :
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) ≃ₗ[ℚ_[p]]
        rationalTate K (fiber K A x).X p => g₀.comp e.toLinearMap)
    (rationalGeometricFiberTateEquiv_toLinearEquiv K A x p)
  have h := TateModule.rationalMapEquiv_natural p
    (A' := Points K (AlgebraicClosure K) (fiber K A x).X)
    (B' := Points K (AlgebraicClosure K) (fiber K B x).X)
    (geometricFiberPointsAddEquiv K A x) (geometricFiberPointsAddEquiv K B x)
    (IsMonHom.monoidHom f.hom.hom.hom (Scheme.geometricPointOver K x)).toAdditive
    (pointsMap K (AlgebraicClosure K) (A := (fiber K A x).X) (B := (fiber K B x).X)
      ((Over.pullback x).mapCommGrp.map f).hom.hom.hom)
    (geometricFiberPointsAddEquiv_map K A B x f)
  exact hB.trans (h.trans hA.symm)

end AlgebraicGeometry.GroupScheme
