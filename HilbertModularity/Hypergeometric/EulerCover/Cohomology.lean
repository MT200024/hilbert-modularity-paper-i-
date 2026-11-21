/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.DeckTransformations
public import HilbertModularity.Geometry.Etale.Cohomology.Automorphisms
public import HilbertModularity.Geometry.Etale.Cohomology.DeckAction
public import HilbertModularity.RepresentationTheory.CharacterProjector
public import HilbertModularity.NumberTheory.Cyclotomic

/-! # Affine Euler-cover cohomology and deck characters

This module uses the actual pro-étale cohomology of the affine Euler cover and
the actual deck transformations. It is groundwork for the cohomological
normalization of [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Limits
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable {R : Type u} [CommRing R] (N : ℕ) [NeZero N] (m : ℕ) (t : R)
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- Deck automorphisms act on the actual integral pro-étale cohomology by pullback. -/
def deckCohomologyRepresentation (n : ℕ) :
    Representation ℤ_[ℓ] (rootsOfUnity N R)
      ((affineScheme N m t).EllAdicCohomology ℓ n) :=
  ((affineScheme N m t).ellAdicCohomologyAutRepresentation ℓ n).comp
    ((MonoidHom.op ((Over.forget _).mapAut (Over.mk (structureMap N m t)))).comp
      (deckActionOver N m t))

/-- The integral action is pullback by the original affine deck isomorphism. -/
theorem deckCohomologyRepresentation_apply (n : ℕ) (ξ : rootsOfUnity N R)
    (x : (affineScheme N m t).EllAdicCohomology ℓ n) :
    deckCohomologyRepresentation N m t ℓ n ξ x =
      AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
        (deckTransformation N m t ξ) ℓ n x := rfl

/-- Rationalization extends the actual deck pullback action on integral cohomology. -/
def rationalDeckCohomologyRepresentation (n : ℕ) :
    Representation ℚ_[ℓ] (rootsOfUnity N R)
      ((affineScheme N m t).RationalEllAdicCohomology ℓ n) :=
  Representation.baseChange ℚ_[ℓ] (deckCohomologyRepresentation N m t ℓ n)

variable {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]

/-- The coefficient embedding itself defines the primitive deck character;
the exponent `m` is not applied to this character. -/
def coefficientDeckCharacter (ι : R →+* L) : rootsOfUnity N R →* Lˣ :=
  (Units.map ι).comp (rootsOfUnity N R).subtype

omit [NeZero N] in
/-- This character evaluates the chosen coefficient embedding on the deck root. -/
@[simp] theorem coefficientDeckCharacter_apply (ι : R →+* L) (ξ : rootsOfUnity N R) :
    (coefficientDeckCharacter N ι ξ : L) = ι ((ξ : Rˣ) : R) := rfl

/-- The actual affine Euler cohomology with coefficients extended to `L`. -/
abbrev CoefficientCohomology (n : ℕ) : Type _ :=
  L ⊗[ℚ_[ℓ]] (affineScheme N m t).RationalEllAdicCohomology ℓ n

/-- The actual deck action after extending rational p-adic coefficients to `L`. -/
def coefficientDeckCohomologyRepresentation (n : ℕ) :
    Representation L (rootsOfUnity N R) (CoefficientCohomology N m t ℓ (L := L) n) :=
  Representation.baseChange L (rationalDeckCohomologyRepresentation N m t ℓ n)

/-- On pure tensors, the `L`-action is the actual deck pullback on the integral factor. -/
theorem coefficientDeckCohomologyRepresentation_tmul (n : ℕ)
    (ξ : rootsOfUnity N R) (a : L) (b : ℚ_[ℓ])
    (x : (affineScheme N m t).EllAdicCohomology ℓ n) :
    coefficientDeckCohomologyRepresentation N m t ℓ (L := L) n ξ
      (a ⊗ₜ[ℚ_[ℓ]] (b ⊗ₜ[ℤ_[ℓ]] x)) =
        a ⊗ₜ[ℚ_[ℓ]]
          (b ⊗ₜ[ℤ_[ℓ]]
            AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
              (deckTransformation N m t ξ) ℓ n x) := by
  rfl

variable [IsDomain R] [Fintype (rootsOfUnity N R)] [CharZero L]
  [FiniteDimensional ℚ_[ℓ] L]

/-- The chosen primitive root gives exactly `N` distinct deck transformations. -/
theorem card_deckGroup {ζ : R} (hζ : IsPrimitiveRoot ζ N) :
    Fintype.card (rootsOfUnity N R) = N := by
  classical
  simpa only [Nat.card_eq_fintype_card] using hζ.card_rootsOfUnity

/-- The fixed primitive-character average on actual affine Euler cohomology. -/
def fixedPrimitiveProjector (ι : R →+* L) (n : ℕ) :
    CoefficientCohomology N m t ℓ (L := L) n →ₗ[L]
      CoefficientCohomology N m t ℓ (L := L) n := by
  classical
  exact Representation.characterProjector (coefficientDeckCharacter N ι)
    (coefficientDeckCohomologyRepresentation N m t ℓ (L := L) n)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The projector is the explicit average with `1/N` and the unmodified character. -/
theorem fixedPrimitiveProjector_formula {ζ : R} (hζ : IsPrimitiveRoot ζ N)
    (ι : R →+* L) (n : ℕ) :
    fixedPrimitiveProjector N m t ℓ ι n =
      ((N : L)⁻¹) •
        ∑ ξ : rootsOfUnity N R,
          ((coefficientDeckCharacter N ι ξ : L)⁻¹) •
            coefficientDeckCohomologyRepresentation N m t ℓ (L := L) n ξ := by
  classical
  unfold fixedPrimitiveProjector Representation.characterProjector
  rw [card_deckGroup N hζ]

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- The fixed average is idempotent once the chosen root has exact order `N`. -/
theorem fixedPrimitiveProjector_idempotent {ζ : R} (hζ : IsPrimitiveRoot ζ N)
    (ι : R →+* L) (n : ℕ) :
    (fixedPrimitiveProjector N m t ℓ ι n).comp
        (fixedPrimitiveProjector N m t ℓ ι n) =
      fixedPrimitiveProjector N m t ℓ ι n := by
  unfold fixedPrimitiveProjector
  apply Representation.characterProjector_idempotent
  rw [card_deckGroup N hζ]
  exact Nat.cast_ne_zero.mpr (NeZero.ne N)

omit [IsDomain R] [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The image transforms by the embedded primitive deck character. -/
theorem fixedPrimitiveProjector_eigen (ι : R →+* L) (n : ℕ)
    (ξ : rootsOfUnity N R) (v : CoefficientCohomology N m t ℓ (L := L) n) :
    coefficientDeckCohomologyRepresentation N m t ℓ (L := L) n ξ
        (fixedPrimitiveProjector N m t ℓ ι n v) =
      ι ((ξ : Rˣ) : R) • fixedPrimitiveProjector N m t ℓ ι n v := by
  classical
  exact Representation.characterProjector_eigen
    (coefficientDeckCharacter N ι)
    (coefficientDeckCohomologyRepresentation N m t ℓ (L := L) n) ξ v

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- The projector image is exactly the fixed primitive-character eigenspace. -/
theorem mem_fixedPrimitiveProjector_range_iff {ζ : R} (hζ : IsPrimitiveRoot ζ N)
    (ι : R →+* L) (n : ℕ) (v : CoefficientCohomology N m t ℓ (L := L) n) :
    v ∈ (fixedPrimitiveProjector N m t ℓ ι n).range ↔
      ∀ ξ : rootsOfUnity N R,
        coefficientDeckCohomologyRepresentation N m t ℓ (L := L) n ξ v =
          ι ((ξ : Rˣ) : R) • v := by
  constructor
  · rintro ⟨w, rfl⟩ ξ
    exact fixedPrimitiveProjector_eigen N m t ℓ ι n ξ w
  · intro hv
    refine ⟨v, ?_⟩
    unfold fixedPrimitiveProjector
    apply Representation.characterProjector_eq_self_of_eigen
    · rw [card_deckGroup N hζ]
      exact Nat.cast_ne_zero.mpr (NeZero.ne N)
    · intro ξ
      simpa only [coefficientDeckCharacter_apply] using hv ξ

variable (L)

/-- The actual cyclotomic Euler cover with a chosen finite p-adic coefficient
field and an embedding of the cyclotomic field. -/
def cyclotomicFixedPrimitiveProjector (m : ℕ)
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) (n : ℕ) :
    CoefficientCohomology N m t ℓ (L := L) n →ₗ[L]
      CoefficientCohomology N m t ℓ (L := L) n := by
  classical
  letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact fixedPrimitiveProjector N m t ℓ ι n

/-- In the cyclotomic field, the actual chosen root proves that the deck group
has exactly `N` elements. -/
theorem card_cyclotomicDeckGroup :
    Nat.card (rootsOfUnity N (Cyclotomic.cyclotomicField N)) = N :=
  (Cyclotomic.root_isPrimitiveRoot N).card_rootsOfUnity

end HilbertModularity.Hypergeometric.EulerCover

namespace HilbertModularity.Hypergeometric.EulerCover

universe v
variable {K : Type v} [Field K] (N : ℕ) [NeZero N] (m : ℕ) (t : K)
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual affine Euler cover after extension to an algebraic closure. -/
abbrev geometricAffineScheme : Scheme :=
  pullback (GroupScheme.fieldPoint K (AlgebraicClosure K)).hom
    (structureMap N m t)

/-- A deck transformation on the actual geometric affine Euler cover. -/
def geometricDeckIso (ξ : rootsOfUnity N K) :
    geometricAffineScheme N m t ≅ geometricAffineScheme N m t :=
  AlgebraicGeometry.Scheme.baseChangedIso (structureMap N m t)
    (GroupScheme.fieldPoint K (AlgebraicClosure K)).hom
    (deckTransformation N m t ξ) (deckTransformation_structureMap N m t ξ)

/-- The original deck group acts on the actual geometric affine cover.
The opposite group records the contravariance of cohomological pullback. -/
def geometricDeckAction :
    rootsOfUnity N K →* (Aut (geometricAffineScheme N m t))ᵐᵒᵖ where
  toFun ξ := MulOpposite.op (geometricDeckIso N m t ξ)
  map_one' := by
    apply MulOpposite.unop_injective
    change geometricDeckIso N m t 1 = Iso.refl _
    apply Iso.ext
    apply pullback.hom_ext
    · simp [geometricDeckIso]
    · have h : (deckTransformation N m t 1).hom = 𝟙 _ := by
        rw [deckTransformation_hom, map_one]
        exact Spec.map_id _
      simp only [geometricDeckIso, AlgebraicGeometry.Scheme.baseChangedIso_snd,
        h, Category.comp_id, Iso.refl_hom, Category.id_comp]
  map_mul' ξ η := by
    apply MulOpposite.unop_injective
    change geometricDeckIso N m t (ξ * η) =
      geometricDeckIso N m t ξ ≪≫ geometricDeckIso N m t η
    apply Iso.ext
    apply pullback.hom_ext
    · simp [geometricDeckIso]
    · simp only [geometricDeckIso, AlgebraicGeometry.Scheme.baseChangedIso_snd]
      have h : (deckTransformation N m t (ξ * η)).hom =
          (deckTransformation N m t ξ).hom ≫
            (deckTransformation N m t η).hom := by
        rw [deckTransformation_hom, deckTransformation_hom, deckTransformation_hom]
        erw [← Spec.map_comp]
        congr 1
        exact congrArg (fun φ : CoverRing N m t ≃ₐ[BaseRing t] CoverRing N m t =>
          CommRingCat.ofHom φ.toRingHom) ((deckAlgebraAction N m t).map_mul ξ η)
      simp only [Iso.trans_hom]
      rw [Category.assoc, AlgebraicGeometry.Scheme.baseChangedIso_snd]
      rw [← Category.assoc, AlgebraicGeometry.Scheme.baseChangedIso_snd]
      rw [h, ← Category.assoc]

/-- The field automorphism on the same actual geometric affine cover. -/
def geometricGaloisIso (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    geometricAffineScheme N m t ≅ geometricAffineScheme N m t :=
  (AlgebraicGeometry.Scheme.fieldBaseChangeGaloisAut K (AlgebraicClosure K)
    (structureMap N m t) σ).unop

/-- On the geometric affine Euler cover, pullback by an actual deck
transformation commutes with the algebraic Galois pullback over the field
containing the chosen roots of unity. -/
theorem geometricDeckCohomology_comm_galois
    (ξ : rootsOfUnity N K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (n : ℕ)
    (x : (geometricAffineScheme N m t).EllAdicCohomology ℓ n) :
    AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
        (geometricDeckIso N m t ξ) ℓ n
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
          (geometricGaloisIso N m t σ) ℓ n x) =
      AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
        (geometricGaloisIso N m t σ) ℓ n
        (AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv
          (geometricDeckIso N m t ξ) ℓ n x) := by
  exact AlgebraicGeometry.Scheme.ellAdicCohomologyEquiv_baseChangedIso_comm_galois
    K (AlgebraicClosure K) (structureMap N m t)
    (deckTransformation N m t ξ)
    (deckTransformation_structureMap N m t ξ) σ ℓ n x

/-- The actual geometric deck action on integral affine cohomology. -/
def geometricDeckCohomologyRepresentation (n : ℕ) :
    Representation ℤ_[ℓ] (rootsOfUnity N K)
      ((geometricAffineScheme N m t).EllAdicCohomology ℓ n) :=
  ((geometricAffineScheme N m t).ellAdicCohomologyAutRepresentation ℓ n).comp
    (geometricDeckAction N m t)

/-- The actual algebraic Galois action on the same integral affine cohomology. -/
def geometricGaloisCohomologyRepresentation (n : ℕ) :
    Representation ℤ_[ℓ] (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((geometricAffineScheme N m t).EllAdicCohomology ℓ n) :=
  AlgebraicGeometry.Scheme.ellAdicCohomologyGaloisRepresentation K
    (structureMap N m t) ℓ n

/-- The deck and algebraic Galois actions commute on actual integral affine cohomology. -/
theorem geometricDeckGalois_comm (ξ : rootsOfUnity N K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (n : ℕ) :
    (geometricDeckCohomologyRepresentation N m t ℓ n ξ).comp
        (geometricGaloisCohomologyRepresentation N m t ℓ n σ) =
      (geometricGaloisCohomologyRepresentation N m t ℓ n σ).comp
        (geometricDeckCohomologyRepresentation N m t ℓ n ξ) := by
  ext x
  exact geometricDeckCohomology_comm_galois N m t ℓ ξ σ n x

variable {L : Type*} [Field L] [Algebra ℚ_[ℓ] L]

/-- Actual geometric affine cohomology after extending coefficients to `L`. -/
abbrev GeometricCoefficientCohomology (n : ℕ) : Type _ :=
  L ⊗[ℚ_[ℓ]] (geometricAffineScheme N m t).RationalEllAdicCohomology ℓ n

/-- The geometric deck action with coefficients in `L`. -/
def geometricCoefficientDeckRepresentation (n : ℕ) :
    Representation L (rootsOfUnity N K)
      (GeometricCoefficientCohomology N m t ℓ (L := L) n) :=
  Representation.baseChange L
    (Representation.baseChange ℚ_[ℓ]
      (geometricDeckCohomologyRepresentation N m t ℓ n))

/-- The algebraic Galois action on geometric affine cohomology with coefficients in `L`. -/
def geometricCoefficientGaloisRepresentation (n : ℕ) :
    Representation L (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (GeometricCoefficientCohomology N m t ℓ (L := L) n) :=
  Representation.baseChange L
    (Representation.baseChange ℚ_[ℓ]
      (geometricGaloisCohomologyRepresentation N m t ℓ n))

/-- Deck and Galois commute after both coefficient extensions. -/
theorem geometricCoefficientDeckGalois_comm (ξ : rootsOfUnity N K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (n : ℕ) :
    (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n ξ).comp
        (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ) =
      (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ).comp
        (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n ξ) := by
  have h := geometricDeckGalois_comm N m t ℓ ξ σ n
  have hq := congrArg (fun f => LinearMap.baseChange ℚ_[ℓ] f) h
  have hL := congrArg (fun f => LinearMap.baseChange L f) hq
  change (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricDeckCohomologyRepresentation N m t ℓ n ξ))).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (geometricGaloisCohomologyRepresentation N m t ℓ n σ))) =
    (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricGaloisCohomologyRepresentation N m t ℓ n σ))).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (geometricDeckCohomologyRepresentation N m t ℓ n ξ)))
  simpa only [LinearMap.baseChange_comp] using hL

variable [Fintype (rootsOfUnity N K)] [CharZero L] [FiniteDimensional ℚ_[ℓ] L]

/-- The fixed primitive-character average on actual geometric affine cohomology. -/
def geometricFixedPrimitiveProjector (ι : K →+* L) (n : ℕ) :
    GeometricCoefficientCohomology N m t ℓ (L := L) n →ₗ[L]
      GeometricCoefficientCohomology N m t ℓ (L := L) n :=
  Representation.characterProjector (coefficientDeckCharacter N ι)
    (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The geometric projector is the manuscript's explicit `1/N` average of
actual base-changed deck pullbacks. -/
theorem geometricFixedPrimitiveProjector_formula {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) (ι : K →+* L) (n : ℕ) :
    geometricFixedPrimitiveProjector N m t ℓ ι n =
      ((N : L)⁻¹) • ∑ ξ : rootsOfUnity N K,
        ((coefficientDeckCharacter N ι ξ : L)⁻¹) •
          geometricCoefficientDeckRepresentation N m t ℓ (L := L) n ξ := by
  classical
  unfold geometricFixedPrimitiveProjector Representation.characterProjector
  rw [card_deckGroup N hζ]

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The image of the geometric projector has the fixed, unpowered deck character. -/
theorem geometricFixedPrimitiveProjector_eigen (ι : K →+* L) (n : ℕ)
    (ξ : rootsOfUnity N K)
    (v : GeometricCoefficientCohomology N m t ℓ (L := L) n) :
    geometricCoefficientDeckRepresentation N m t ℓ (L := L) n ξ
        (geometricFixedPrimitiveProjector N m t ℓ ι n v) =
      ι ((ξ : Kˣ) : K) • geometricFixedPrimitiveProjector N m t ℓ ι n v := by
  exact Representation.characterProjector_eigen
    (coefficientDeckCharacter N ι)
    (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n) ξ v

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- The geometric fixed-character average is idempotent for a primitive root. -/
theorem geometricFixedPrimitiveProjector_idempotent {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) (ι : K →+* L) (n : ℕ) :
    (geometricFixedPrimitiveProjector N m t ℓ ι n).comp
        (geometricFixedPrimitiveProjector N m t ℓ ι n) =
      geometricFixedPrimitiveProjector N m t ℓ ι n := by
  unfold geometricFixedPrimitiveProjector
  apply Representation.characterProjector_idempotent
  rw [card_deckGroup N hζ]
  exact Nat.cast_ne_zero.mpr (NeZero.ne N)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- Algebraic Galois commutes with the fixed geometric projector over a field
containing the chosen deck roots. -/
theorem geometricFixedPrimitiveProjector_comm_galois (ι : K →+* L) (n : ℕ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (geometricFixedPrimitiveProjector N m t ℓ ι n).comp
        (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ) =
      (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ).comp
        (geometricFixedPrimitiveProjector N m t ℓ ι n) := by
  classical
  exact Representation.characterProjector_comm
    (coefficientDeckCharacter N ι)
    (geometricCoefficientDeckRepresentation N m t ℓ (L := L) n)
    (geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ)
    (fun ξ => geometricCoefficientDeckGalois_comm N m t ℓ (L := L) ξ σ n)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The image of the actual geometric primitive-character projector is stable
under algebraic Galois over the field containing the deck roots. -/
theorem geometricFixedPrimitiveProjector_galois_mem_range
    (ι : K →+* L) (n : ℕ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    {v : GeometricCoefficientCohomology N m t ℓ (L := L) n}
    (hv : v ∈ (geometricFixedPrimitiveProjector N m t ℓ ι n).range) :
    geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ v ∈
      (geometricFixedPrimitiveProjector N m t ℓ ι n).range := by
  rcases hv with ⟨w, rfl⟩
  refine ⟨geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ w, ?_⟩
  exact congrArg (fun f : _ →ₗ[L] _ => f w)
    (geometricFixedPrimitiveProjector_comm_galois N m t ℓ ι n σ)

variable (L)

/-- The actual affine geometric Euler cover over the cyclotomic field, with
the fixed primitive projector on its `L`-coefficient cohomology. -/
def cyclotomicGeometricFixedPrimitiveProjector (m : ℕ)
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) (n : ℕ) :
    GeometricCoefficientCohomology N m t ℓ (L := L) n →ₗ[L]
      GeometricCoefficientCohomology N m t ℓ (L := L) n := by
  classical
  letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
  exact geometricFixedPrimitiveProjector N m t ℓ ι n

omit [FiniteDimensional ℚ_[ℓ] L] in
/-- The fixed projector on cyclotomic geometric affine cohomology is idempotent. -/
theorem cyclotomicGeometricFixedPrimitiveProjector_idempotent (m : ℕ)
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) (n : ℕ) :
    (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n).comp
        (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n) =
      cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n := by
  classical
  exact
    (letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
     geometricFixedPrimitiveProjector_idempotent N m t ℓ
       (Cyclotomic.root_isPrimitiveRoot N) ι n)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- Every vector in the cyclotomic projector image has the chosen primitive
deck eigencharacter, with no second power of `m`. -/
theorem cyclotomicGeometricFixedPrimitiveProjector_eigen (m : ℕ)
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) (n : ℕ)
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    (v : GeometricCoefficientCohomology N m t ℓ (L := L) n) :
    geometricCoefficientDeckRepresentation N m t ℓ (L := L) n ξ
        (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n v) =
      ι ((ξ : (Cyclotomic.cyclotomicField N)ˣ) : Cyclotomic.cyclotomicField N) •
        cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n v := by
  classical
  exact
    (letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
     geometricFixedPrimitiveProjector_eigen N m t ℓ ι n ξ v)

omit [CharZero L] [FiniteDimensional ℚ_[ℓ] L] in
/-- The cyclotomic geometric projector is stable under the actual algebraic
Galois action over the field containing its deck roots. -/
theorem cyclotomicGeometricFixedPrimitiveProjector_galois_mem_range (m : ℕ)
    (t : Cyclotomic.cyclotomicField N)
    (ι : Cyclotomic.cyclotomicField N →+* L) (n : ℕ)
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[
      Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    {v : GeometricCoefficientCohomology N m t ℓ (L := L) n}
    (hv : v ∈ (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n).range) :
    geometricCoefficientGaloisRepresentation N m t ℓ (L := L) n σ v ∈
      (cyclotomicGeometricFixedPrimitiveProjector N ℓ L m t ι n).range := by
  classical
  exact
    (letI : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) := Fintype.ofFinite _
     geometricFixedPrimitiveProjector_galois_mem_range N m t ℓ ι n σ hv)

end HilbertModularity.Hypergeometric.EulerCover
