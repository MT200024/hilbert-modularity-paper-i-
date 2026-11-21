/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition
public import HilbertModularity.Geometry.TateModule.FiniteGeneration
public import HilbertModularity.Topology.TateModule.FiniteFree
public import Mathlib.Topology.Algebra.Algebra

/-! # Continuous labelled geometric Tate factors

The actual scalar-extended Tate action has continuous orbits for a compatible
coefficient topology. Its labelled idempotent summands inherit continuity, and
the actual labelled decomposition is a linear homeomorphism. These supply the
topological coefficient-label realization in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K] (A : Over (Spec (CommRingCat.of K)))
  [GrpObj A] [IsCommMonObj A] [IsSeparated A.hom] [LocallyOfFiniteType A.hom]
  (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]
  (L : Type*) [Field L] [Algebra ℚ_[p] L]
  [TopologicalSpace L] [ContinuousSMul ℚ_[p] L]
  [TopologicalSpace (L ⊗[ℚ_[p]] rationalTate K A p)]
  [IsModuleTopology L (L ⊗[ℚ_[p]] rationalTate K A p)]

/-- Scalar extension of the actual geometric Tate representation preserves continuous orbit maps. -/
theorem continuous_tensorTateRepresentation (v : L ⊗[ℚ_[p]] rationalTate K A p) :
    Continuous (fun g => ((tateRepresentation K A p).baseChange L) g v) := by
  let : ContinuousAdd (L ⊗[ℚ_[p]] rationalTate K A p) :=
    IsModuleTopology.toContinuousAdd L _
  let : ContinuousSMul ℚ_[p] (L ⊗[ℚ_[p]] rationalTate K A p) := ⟨by
    have h := ((continuous_algebraMap ℚ_[p] L).comp
      (continuous_fst : Continuous (fun z : ℚ_[p] × (L ⊗[ℚ_[p]] rationalTate K A p) => z.1))).smul continuous_snd
    change Continuous (fun z : ℚ_[p] × (L ⊗[ℚ_[p]] rationalTate K A p) =>
      algebraMap ℚ_[p] L z.1 • z.2) at h
    apply h.congr
    intro z
    exact IsScalarTower.algebraMap_smul L z.1 z.2⟩
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    apply (hx.add hy).congr
    intro g
    exact (map_add (((tateRepresentation K A p).baseChange L) g) x y).symm
  | tmul a x =>
    exact (IsModuleTopology.continuous_of_linearMap
      (TensorProduct.mk ℚ_[p] L (rationalTate K A p) a)).comp
        (TateModule.continuous_rationalRepresentation p _ (Points K (AlgebraicClosure K) A) x)

variable (F : Type*) [Field F] [NumberField F] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    φ a = pointsMap K (AlgebraicClosure K) f)

/-- The actual labelled geometric Tate summands have continuous Galois orbit maps. -/
theorem continuous_labelledTateRepresentation (σ : F →ₐ[ℚ] L)
    (v : labelledTateSummand K A p F L hL φ σ) :
    Continuous (fun g => (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g v) :=
  (continuous_tensorTateRepresentation K A p L v.val).subtype_mk _

/-- The actual labelled Tate decomposition respects the coefficient-module topologies. -/
def labelledTateDecompositionContinuousEquiv :
    (L ⊗[ℚ_[p]] rationalTate K A p) ≃L[L]
      ((σ : F →ₐ[ℚ] L) → labelledTateSummand K A p F L hL φ σ) := by
  classical
  let : ContinuousAdd (L ⊗[ℚ_[p]] rationalTate K A p) :=
    IsModuleTopology.toContinuousAdd L _
  refine { labelledTateDecomposition K A p F L hL φ with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_pi
    intro σ
    exact (IsModuleTopology.continuous_of_linearMap
      (labelledTateProjection K A p F L hL φ σ)).subtype_mk _
  · change Continuous (fun v : (σ : F →ₐ[ℚ] L) → labelledTateSummand K A p F L hL φ σ =>
      ∑ σ, (v σ : L ⊗[ℚ_[p]] rationalTate K A p))
    exact continuous_finsetSum _ fun σ _ => continuous_subtype_val.comp (continuous_apply σ)

end AlgebraicGeometry.GroupScheme
