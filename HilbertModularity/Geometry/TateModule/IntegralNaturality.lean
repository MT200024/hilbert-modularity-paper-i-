/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.IntegralLattice
public import HilbertModularity.RepresentationTheory.IntegralNaturality

/-! # Naturality of the constructed integral Tate lattices

An actual coefficient-compatible geometric morphism preserves the ambient and
labelled integral image lattices, hence induces maps on their residual Galois
representations. These are the integral naturality maps needed by
[TripathiGoswami]; existence of a chosen specialization morphism is separate.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L]
  (R : Type*) [CommRing R] [Algebra ℤ_[p] R] [Algebra R L]
  [IsScalarTower ℤ_[p] R L]


variable {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  (f : A ⟶ B) [IsMonHom f]

/-- A geometric morphism preserves the ambient lattice constructed from integral Tate modules. -/
theorem rationalTateMap_mem_integralTateLattice
    {x : L ⊗[ℚ_[p]] rationalTate K A p}
    (hx : x ∈ (integralTateLattice K A p L R).toSubmodule) :
    (rationalTateMap K p f).baseChange L x ∈ (integralTateLattice K B p L R).toSubmodule :=
  Representation.map_mem_iteratedIntegralBaseChangeLattice ℤ_[p] R L
    (integralTateRepresentation K A p) ℚ_[p] (integralTateIntertwiningMap K p f) hx

variable (F : Type*) [Field F] [NumberField F] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (ψ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) B))
  (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    φ a = pointsMap K (AlgebraicClosure K) f)
  (hψ : ∀ a, ∃ (f : B ⟶ B) (_ : IsMonHom f),
    ψ a = pointsMap K (AlgebraicClosure K) f)
  (h : ∀ (a : 𝓞 F) (x : Points K (AlgebraicClosure K) A),
    pointsMap K (AlgebraicClosure K) f (φ a x) = ψ a (pointsMap K (AlgebraicClosure K) f x))

/-- A coefficient-compatible geometric morphism preserves the constructed labelled integral lattice. -/
theorem labelledTateMap_mem_integralTateLattice (σ : F →ₐ[ℚ] L)
    {x : labelledTateSummand K A p F L hL φ σ}
    (hx : x ∈ (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule) :
    labelledTateSummandMap K A p F L hL φ ψ f h σ x ∈
      (labelledIntegralTateLattice K B p L R F hL ψ hψ σ).toSubmodule := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨(rationalTateMap K p f).baseChange L v,
    rationalTateMap_mem_integralTateLattice K A p L R f hv, ?_⟩
  apply Subtype.ext
  exact (tensorTateAction_intertwines K A p F φ ψ f h L
    (Algebra.TensorProduct.embeddingIdempotent ℚ F L hL σ) v).symm

/-- The geometric map restricts to an actual intertwiner of the labelled integral lattices. -/
def labelledIntegralTateIntertwiner (σ : F →ₐ[ℚ] L) :
    (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toRepresentation.IntertwiningMap
      (labelledIntegralTateLattice K B p L R F hL ψ hψ σ).toRepresentation where
  toLinearMap :=
    ((((labelledTateIntertwiningMap K A p F L hL φ hφ ψ f h hψ σ).restrictScalars R).toLinearMap.comp
      (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule.subtype).codRestrict _
        (fun v => labelledTateMap_mem_integralTateLattice K A p L R f F hL φ ψ hφ hψ h σ v.property))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun l => l v.val)
      ((labelledTateIntertwiningMap K A p F L hL φ hφ ψ f h hψ σ).isIntertwining' g)

/-- The integral map is the restriction of the actual labelled geometric Tate map. -/
@[simp]
theorem labelledIntegralTateIntertwiner_apply (σ : F →ₐ[ℚ] L)
    (v : (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule) :
    (labelledIntegralTateIntertwiner K A p L R f F hL φ ψ hφ hψ h σ v).val =
        labelledTateSummandMap K A p F L hL φ ψ f h σ v.val := rfl

/-- Reduction of the actual integral map gives an intertwiner of the constructed residual factors. -/
def labelledResidualTateIntertwiner (k : Type*) [CommRing k] [Algebra R k]
    (σ : F →ₐ[ℚ] L) :
    ((labelledIntegralTateLattice K A p L R F hL φ hφ σ).toRepresentation.baseChange k).IntertwiningMap
      ((labelledIntegralTateLattice K B p L R F hL ψ hψ σ).toRepresentation.baseChange k) :=
  (labelledIntegralTateIntertwiner K A p L R f F hL φ ψ hφ hψ h σ).baseChange k


end AlgebraicGeometry.GroupScheme
