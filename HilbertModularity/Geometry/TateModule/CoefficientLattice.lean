/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition
public import HilbertModularity.RepresentationTheory.CoefficientLattice

/-! # Integral lattices in labelled geometric Tate factors

Project the actual ambient stable lattice through the geometric coefficient
idempotent. Its image is stable and spans the labelled Tate factor, even when
the idempotent does not preserve the original lattice. This is the integral
labelled-constituent construction used in
[TripathiGoswami, coefficient labels and determinant rigidity].
-/

@[expose] public noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    φ a = pointsMap K (AlgebraicClosure K) f)

/-- Project the actual geometric Tate representation onto its labelled factor. -/
def labelledTateProjectionIntertwiner (σ : F →ₐ[ℚ] L) :
    ((tateRepresentation K A p).baseChange L).IntertwiningMap
      (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation where
  toLinearMap := (labelledTateProjection K A p F L hL φ σ).rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun
      (tensorTateAction_commute K A p F L φ hφ g (embeddingIdempotent ℚ F L hL σ)) v

/-- The geometric labelled projection is onto its labelled factor. -/
theorem labelledTateProjectionIntertwiner_surjective (σ : F →ₐ[ℚ] L) :
    Function.Surjective (labelledTateProjectionIntertwiner K A p F L hL φ hφ σ) := by
  rintro ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

variable (R : Type*) [CommRing R] [Algebra R L]
  (S : Subrepresentation (((tateRepresentation K A p).baseChange L).restrictScalars R))

/-- The actual integral labelled Tate lattice obtained by projecting the ambient stable lattice. -/
def labelledTateLattice (σ : F →ₐ[ℚ] L) :
    Subrepresentation
      ((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation.restrictScalars R) :=
  ((labelledTateProjectionIntertwiner K A p F L hL φ hφ σ).restrictScalars R).mapSubrepresentation S

/-- An ambient full stable Tate lattice gives a full stable lattice in every labelled factor. -/
instance labelledTateLattice_isLattice [Submodule.IsLattice L S.toSubmodule] (σ : F →ₐ[ℚ] L) :
    Submodule.IsLattice L (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule := by
  change Submodule.IsLattice L
    (S.toSubmodule.map ((labelledTateProjection K A p F L hL φ σ).rangeRestrict.restrictScalars R))
  refine Submodule.IsLattice.map_of_surjective (R := R) (K := L)
    S.toSubmodule (labelledTateProjection K A p F L hL φ σ).rangeRestrict ?_
  rintro ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R L]
  [Submodule.IsLattice L S.toSubmodule]

/-- The integral labelled Tate lattice has the rank of its characteristic-zero labelled factor. -/
theorem labelledTateLattice_finrank (σ : F →ₐ[ℚ] L) :
    Module.finrank R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule =
      Module.finrank L (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule :=
  congrArg Cardinal.toNat (Submodule.IsLattice.rank' (R := R)
    (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule) L
    (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule)

/-- A finite integral basis in an actual labelled Tate lattice over a PID. -/
def labelledTateLatticeBasis (σ : F →ₐ[ℚ] L) :
    Module.Basis
      (Fin (Module.finrank R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule))
      R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule :=
  let : Module.Free R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule :=
    Submodule.IsLattice.free (K := L)
      (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
      (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule
  let : Module.Finite R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule :=
    Submodule.IsLattice.finite L
      (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
      (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule
  Module.finBasis R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule

/-- The residual labelled Tate lattice has the dimension of its characteristic-zero labelled factor. -/
theorem labelledTateLattice_reduction_finrank (k : Type*) [Field k] [Algebra R k]
    (σ : F →ₐ[ℚ] L) :
    Module.finrank k (k ⊗[R] (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule) =
      Module.finrank L (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule := by
  let : Module.Free R (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule :=
    Submodule.IsLattice.free (K := L)
      (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
      (labelledTateLattice K A p F L hL φ hφ R S σ).toSubmodule
  rw [Module.finrank_baseChange, labelledTateLattice_finrank]

end AlgebraicGeometry.GroupScheme
