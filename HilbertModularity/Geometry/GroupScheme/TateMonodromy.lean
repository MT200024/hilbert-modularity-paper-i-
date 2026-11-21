/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TorsionMonodromy
public import HilbertModularity.Geometry.GroupScheme.TorsionTransitionComparison
public import HilbertModularity.RepresentationTheory.TorsionRepresentation
public import HilbertModularity.RepresentationTheory.TateModule.ScalarExtension

/-! # Geometric monodromy on the ordinary Tate module -/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.GroupScheme
universe u
attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory
variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S)) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- Actual monodromy commutes with the native Tate transition, by naturality on torsion covers. -/
theorem finiteTorsionMonodromy_transition (σ : Scheme.etaleFundamentalGroup K x) (n : ℕ)
    (v : TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) (n + 1)) :
    TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n
        ((finiteTorsionMonodromy K x A (p ^ (n + 1)) σ).toAdd v) =
      (finiteTorsionMonodromy K x A (p ^ n) σ).toAdd
        (TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n v) := by
  let e := finiteTorsionFiberPointsEquiv K x A (p ^ n)
  let e' := finiteTorsionFiberPointsEquiv K x A (p ^ (n + 1))
  obtain ⟨w, rfl⟩ := e'.surjective v
  rw [finiteTorsionMonodromy_apply, finiteTorsionMonodromy_apply]
  change TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n
      (e' (Additive.ofMul (σ • (e'.symm (e' w)).toMul))) =
    e (Additive.ofMul (σ • (e.symm
      (TateModule.transition p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n (e' w))).toMul))
  rw [AddEquiv.symm_apply_apply]
  rw [← finiteTorsionFiberPointsEquiv_transition K x A p n w]
  rw [AddEquiv.symm_apply_apply]
  rw [← finiteTorsionFiberPointsEquiv_transition K x A p n (Additive.ofMul (σ • w.toMul))]
  have h := congrArg (fun f => f w.toMul)
    ((Scheme.finiteGroupFiberPathIso K σ).hom.naturality (finiteEtaleTorsionTransition A p n))
  exact congrArg (fun z => e (Additive.ofMul z)) h.symm

/-- The native `p`-power torsion action is linear for the canonical `p`-adic coefficients. -/
def torsionMonodromyRepresentation (n : ℕ) : Representation ℤ_[p]
    (Scheme.etaleFundamentalGroup K x)
    (TateModule.Torsion p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n) :=
  TateModule.torsionRepresentationOfAddAut p n (finiteTorsionMonodromy K x A (p ^ n))

/-- The actual finite étale torsion tower acts on the ordinary integral Tate module. -/
def integralTateMonodromy : Representation ℤ_[p] (Scheme.etaleFundamentalGroup K x)
    (TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
  TateModule.representationOfTorsion p (Scheme.etaleFundamentalGroup K x)
    (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    (torsionMonodromyRepresentation K x A p) (finiteTorsionMonodromy_transition K x A p)

/-- Each coordinate of geometric Tate monodromy is the actual finite étale monodromy action. -/
@[simp]
theorem integralTateMonodromy_projection (σ : Scheme.etaleFundamentalGroup K x)
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) (n : ℕ) :
    TateModule.projection p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n
        (integralTateMonodromy K x A p σ v) =
      (finiteTorsionMonodromy K x A (p ^ n) σ).toAdd
        (TateModule.projection p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n v) := rfl

/-- Arithmetic restriction of the geometric Tate action is the original action on each torsion point. -/
theorem integralTateMonodromy_arithmetic_projection
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) (n : ℕ) :
    (TateModule.projection p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n
      (integralTateMonodromy K x A p (Scheme.galoisToEtaleFundamentalGroup K x g) v)).val.toMul =
    Scheme.arithmeticFiberPointMap K x g ≫
      (TateModule.projection p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) n v).val.toMul := by
  rw [integralTateMonodromy_projection]
  exact finiteTorsionMonodromy_arithmetic K x A (p ^ n) g _

/-- The covariant rational Tate monodromy of the actual finite étale torsion tower. -/
def rationalTateMonodromy : Representation ℚ_[p] (Scheme.etaleFundamentalGroup K x)
    (TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :=
  (integralTateMonodromy K x A p).baseChange ℚ_[p]

/-- Geometric monodromy fixes rational coefficients and acts on the integral Tate factor. -/
@[simp]
theorem rationalTateMonodromy_tmul (σ : Scheme.etaleFundamentalGroup K x)
    (c : ℚ_[p]) (v : TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X))) :
    rationalTateMonodromy K x A p σ (c ⊗ₜ v) =
      c ⊗ₜ integralTateMonodromy K x A p σ v := rfl

variable [TopologicalSpace (Additive (Scheme.geometricPointOver K x ⟶ A.X))]
  [DiscreteTopology (Additive (Scheme.geometricPointOver K x ⟶ A.X))]

/-- The geometric action on the ordinary integral Tate module is jointly continuous. -/
theorem continuous_integralTateMonodromy :
    Continuous (fun gv : Scheme.etaleFundamentalGroup K x ×
      TateModule.integral p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) =>
        integralTateMonodromy K x A p gv.1 gv.2) :=
  TateModule.continuous_representationOfTorsion p (Scheme.etaleFundamentalGroup K x)
    (Additive (Scheme.geometricPointOver K x ⟶ A.X))
    (torsionMonodromyRepresentation K x A p) (finiteTorsionMonodromy_transition K x A p)
    (fun n => continuous_finiteTorsionMonodromy K x A (p ^ n))

/-- The actual rational geometric Tate action is jointly continuous. -/
theorem continuous_rationalTateMonodromy :
    Continuous (fun gv : Scheme.etaleFundamentalGroup K x ×
      TateModule.rational p (Additive (Scheme.geometricPointOver K x ⟶ A.X)) =>
        rationalTateMonodromy K x A p gv.1 gv.2) :=
  TateModule.continuous_baseChange p (integralTateMonodromy K x A p)
    (continuous_integralTateMonodromy K x A p)

end AlgebraicGeometry.GroupScheme
