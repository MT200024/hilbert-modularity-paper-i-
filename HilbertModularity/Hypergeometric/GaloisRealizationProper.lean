/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationFamily
public import HilbertModularity.Hypergeometric.EulerCover.Cohomology
public import Mathlib.RepresentationTheory.Subrepresentation

/-! # The fixed deck character on proper Euler cohomology

The deck transformations of the chosen smooth proper Euler family act on its
actual geometric fibres. Their degree-one cohomology carries the same fixed
character projector as the affine Euler chart of
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N]
  (𝒞 : SmoothProperEulerFamily N m)
  (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))

local instance : Fintype (rootsOfUnity N (Cyclotomic.cyclotomicField N)) :=
  Fintype.ofFinite _

/-- Base change of a specialized proper Euler deck transformation to the
algebraic closure of its cyclotomic ground field. -/
def geometricProperEulerDeckIso
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    geometricSmoothProperEulerFibre N m 𝒞 t ht h1t ≅
      geometricSmoothProperEulerFibre N m 𝒞 t ht h1t :=
  Scheme.baseChangedIso (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t)
    (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
      (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
    (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ξ).unop
    (smoothProperEulerFibreDeckAction_structureMap N m 𝒞 t ht h1t ξ)

/-- The geometric deck map has identity first projection on the selected fibre. -/
theorem geometricProperEulerDeckIso_fst
    (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    (geometricProperEulerDeckIso N m 𝒞 t ht h1t ζ).hom ≫
        pullback.fst
          (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
            (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
          (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) =
      pullback.fst _ _ :=
  Scheme.baseChangedIso_fst _ _ _ _

/-- The second projection of the geometric deck map is the selected
specialized proper-fibre deck transformation. -/
theorem geometricProperEulerDeckIso_snd
    (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    (geometricProperEulerDeckIso N m 𝒞 t ht h1t ζ).hom ≫
        pullback.snd
          (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
            (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
          (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) =
      pullback.snd _ _ ≫
        (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ).unop.hom :=
  Scheme.baseChangedIso_snd _ _ _ _

/-- The proper geometric fibre has the specialized deck-group action.
The opposite group accounts for contravariance on cohomology. -/
def geometricProperEulerDeckAction :
    rootsOfUnity N (Cyclotomic.cyclotomicField N) →*
      (Aut (geometricSmoothProperEulerFibre N m 𝒞 t ht h1t))ᵐᵒᵖ where
  toFun ξ := MulOpposite.op (geometricProperEulerDeckIso N m 𝒞 t ht h1t ξ)
  map_one' := by
    apply MulOpposite.unop_injective
    change geometricProperEulerDeckIso N m 𝒞 t ht h1t 1 = Iso.refl _
    apply Iso.ext
    apply pullback.hom_ext
    · exact Scheme.baseChangedIso_fst _ _ _ _
    · have h : (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t 1).unop.hom =
          𝟙 _ := by
        have hIso := congrArg MulOpposite.unop
          ((smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t).map_one)
        exact congrArg Iso.hom hIso
      simp only [Iso.refl_hom, Category.id_comp]
      calc
        _ = pullback.snd _ _ ≫
            (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t 1).unop.hom :=
          Scheme.baseChangedIso_snd _ _ _ _
        _ = _ := by rw [h, Category.comp_id]
  map_mul' ξ η := by
    have hfst (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
        (geometricProperEulerDeckIso N m 𝒞 t ht h1t ζ).hom ≫
            pullback.fst
              (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
                (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
              (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) =
          pullback.fst
            (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
              (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
            (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) :=
      Scheme.baseChangedIso_fst _ _ _ _
    have hsnd (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
        (geometricProperEulerDeckIso N m 𝒞 t ht h1t ζ).hom ≫
            pullback.snd
              (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
                (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
              (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) =
          pullback.snd
            (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
              (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
            (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ≫
              (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ).unop.hom :=
      Scheme.baseChangedIso_snd _ _ _ _
    apply MulOpposite.unop_injective
    change geometricProperEulerDeckIso N m 𝒞 t ht h1t (ξ * η) =
      geometricProperEulerDeckIso N m 𝒞 t ht h1t ξ ≪≫
        geometricProperEulerDeckIso N m 𝒞 t ht h1t η
    apply Iso.ext
    apply pullback.hom_ext
    · change (geometricProperEulerDeckIso N m 𝒞 t ht h1t (ξ * η)).hom ≫
          pullback.fst
            (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
              (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
            (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) =
        (geometricProperEulerDeckIso N m 𝒞 t ht h1t ξ ≪≫
          geometricProperEulerDeckIso N m 𝒞 t ht h1t η).hom ≫
            pullback.fst
              (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
                (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
              (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t)
      rw [Iso.trans_hom, Category.assoc, hfst η, hfst ξ, hfst (ξ * η)]
    ·
      have hIso : (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t (ξ * η)).unop =
          (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t η).unop *
            (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ξ).unop := by
        simpa only [MulOpposite.unop_mul] using congrArg MulOpposite.unop
          ((smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t).map_mul ξ η)
      have h : (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t (ξ * η)).unop.hom =
          (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ξ).unop.hom ≫
            (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t η).unop.hom := by
        exact congrArg Iso.hom hIso
      rw [Iso.trans_hom, Category.assoc, hsnd η, ← Category.assoc, hsnd ξ,
        hsnd (ξ * η), h, Category.assoc]

/-- The actual deck pullback action on integral cohomology of the proper
geometric Euler fibre. -/
def geometricProperEulerDeckCohomologyRepresentation (ℓ n : ℕ) [Fact ℓ.Prime] :
    Representation ℤ_[ℓ]
      (rootsOfUnity N (Cyclotomic.cyclotomicField N))
      ((geometricSmoothProperEulerFibre N m 𝒞 t ht h1t).EllAdicCohomology ℓ n) :=
  ((geometricSmoothProperEulerFibre N m 𝒞 t ht h1t).ellAdicCohomologyAutRepresentation
      ℓ n).comp (geometricProperEulerDeckAction N m 𝒞 t ht h1t)

/-- A proper Euler deck pullback commutes with arithmetic Galois over the
field containing the deck roots of unity. -/
theorem geometricProperEulerDeckCohomology_comm_galois
    (ℓ n : ℕ) [Fact ℓ.Prime]
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    (x : (geometricSmoothProperEulerFibre N m 𝒞 t ht h1t).EllAdicCohomology ℓ n) :
    Scheme.ellAdicCohomologyEquiv (geometricProperEulerDeckIso N m 𝒞 t ht h1t ξ)
        ℓ n (Scheme.ellAdicCohomologyEquiv
          (Scheme.fieldBaseChangeGaloisAut (Cyclotomic.cyclotomicField N)
            (AlgebraicClosure (Cyclotomic.cyclotomicField N))
            (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) σ).unop ℓ n x) =
      Scheme.ellAdicCohomologyEquiv
        (Scheme.fieldBaseChangeGaloisAut (Cyclotomic.cyclotomicField N)
          (AlgebraicClosure (Cyclotomic.cyclotomicField N))
          (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) σ).unop ℓ n
        (Scheme.ellAdicCohomologyEquiv
          (geometricProperEulerDeckIso N m 𝒞 t ht h1t ξ) ℓ n x) := by
  exact Scheme.ellAdicCohomologyEquiv_baseChangedIso_comm_galois
    (Cyclotomic.cyclotomicField N)
    (AlgebraicClosure (Cyclotomic.cyclotomicField N))
    (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t)
    (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ξ).unop
    (smoothProperEulerFibreDeckAction_structureMap N m 𝒞 t ht h1t ξ)
    σ ℓ n x

/-- The fixed deck action after extending the actual proper cohomology to a
coefficient field. -/
def geometricProperEulerCoefficientDeckRepresentation
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    Representation L (rootsOfUnity N (Cyclotomic.cyclotomicField N))
      (GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L) :=
  Representation.baseChange L
    (Representation.baseChange ℚ_[ℓ]
      (geometricProperEulerDeckCohomologyRepresentation N m 𝒞 t ht h1t ℓ 1))

/-- The coefficient deck operator is pullback by the same geometric deck
automorphism of the selected proper fibre. -/
theorem geometricProperEulerCoefficientDeckRepresentation_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ζ =
      (Representation.baseChange L (Representation.baseChange ℚ_[ℓ]
        ((geometricSmoothProperEulerFibre N m 𝒞 t ht h1t).ellAdicCohomologyAutRepresentation
          ℓ 1)))
        (MulOpposite.op (geometricProperEulerDeckIso N m 𝒞 t ht h1t ζ)) :=
  (rfl)

/-- The character on the exponent-`m` proper curve is always the fixed
`χ₀(ζ)=ι(ζ)`; there is no second exponent on the character. -/
def geometricProperEulerFixedPrimitiveProjector
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L →ₗ[L]
      GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L := by
  classical
  exact Representation.characterProjector (EulerCover.coefficientDeckCharacter N ι)
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L)

/-- The proper projector is the literal fixed-character average. -/
theorem geometricProperEulerFixedPrimitiveProjector_formula
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι =
      ((N : L)⁻¹) • ∑ ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N),
        ((EulerCover.coefficientDeckCharacter N ι ξ : L)⁻¹) •
          geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ := by
  classical
  unfold geometricProperEulerFixedPrimitiveProjector Representation.characterProjector
  rw [EulerCover.card_deckGroup N (Cyclotomic.root_isPrimitiveRoot N)]

/-- A vector in the proper projector image has the unpowered deck character. -/
theorem geometricProperEulerFixedPrimitiveProjector_eigen
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    (v : GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L) :
    geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ
        (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι v) =
      ι ((ξ : (Cyclotomic.cyclotomicField N)ˣ) : Cyclotomic.cyclotomicField N) •
        geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι v := by
  classical
  exact Representation.characterProjector_eigen
    (EulerCover.coefficientDeckCharacter N ι)
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L) ξ v

/-- The fixed primitive proper projector is idempotent in characteristic zero. -/
theorem geometricProperEulerFixedPrimitiveProjector_idempotent
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] [CharZero L]
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι).comp
        (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι) =
      geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι := by
  classical
  unfold geometricProperEulerFixedPrimitiveProjector
  apply Representation.characterProjector_idempotent
  rw [EulerCover.card_deckGroup N (Cyclotomic.root_isPrimitiveRoot N)]
  exact Nat.cast_ne_zero.mpr (NeZero.ne N)

/-- The fixed-character projector commutes with every deck operator of the
abelian cyclic cover. -/
theorem geometricProperEulerFixedPrimitiveProjector_comm_deck
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι).comp
        (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ) =
      (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ).comp
        (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι) := by
  classical
  exact Representation.characterProjector_comm
    (EulerCover.coefficientDeckCharacter N ι)
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L)
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ)
    (by
      intro η
      change
        (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L) η *
          (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L) ξ =
        (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L) ξ *
          (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L) η
      rw [← map_mul, ← map_mul, mul_comm])

/-- The two actions on integral cohomology commute because every proper deck
transformation is defined over the cyclotomic ground field. -/
theorem geometricProperEulerDeckGalois_comm
    (ℓ n : ℕ) [Fact ℓ.Prime]
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N)) :
    (geometricProperEulerDeckCohomologyRepresentation N m 𝒞 t ht h1t ℓ n ξ).comp
        (Scheme.ellAdicCohomologyGaloisRepresentation
          (Cyclotomic.cyclotomicField N)
          (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ℓ n σ) =
      (Scheme.ellAdicCohomologyGaloisRepresentation
        (Cyclotomic.cyclotomicField N)
        (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ℓ n σ).comp
        (geometricProperEulerDeckCohomologyRepresentation N m 𝒞 t ht h1t ℓ n ξ) := by
  ext x
  exact geometricProperEulerDeckCohomology_comm_galois N m 𝒞 t ht h1t ℓ n ξ σ x

/-- Deck and arithmetic Galois commute after both coefficient extensions. -/
theorem geometricProperEulerCoefficientDeckGalois_comm
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N)) :
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ).comp
        (geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ) =
      (geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ).comp
        (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L ξ) := by
  have h := geometricProperEulerDeckGalois_comm N m 𝒞 t ht h1t ℓ 1 ξ σ
  have hq := congrArg (fun f => LinearMap.baseChange ℚ_[ℓ] f) h
  have hL := congrArg (fun f => LinearMap.baseChange L f) hq
  simp only [geometricProperEulerGaloisRepresentation_eq]
  change (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (geometricProperEulerDeckCohomologyRepresentation N m 𝒞 t ht h1t ℓ 1 ξ))).comp
      (LinearMap.baseChange L
        (LinearMap.baseChange ℚ_[ℓ]
          (Scheme.ellAdicCohomologyGaloisRepresentation
            (Cyclotomic.cyclotomicField N)
            (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ℓ 1 σ))) =
    (LinearMap.baseChange L
      (LinearMap.baseChange ℚ_[ℓ]
        (Scheme.ellAdicCohomologyGaloisRepresentation
          (Cyclotomic.cyclotomicField N)
          (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ℓ 1 σ))).comp
        (LinearMap.baseChange L
          (LinearMap.baseChange ℚ_[ℓ]
            (geometricProperEulerDeckCohomologyRepresentation N m 𝒞 t ht h1t ℓ 1 ξ)))
  simpa only [LinearMap.baseChange_comp] using hL

/-- The fixed proper projector commutes with arithmetic Galois over the
cyclotomic field. -/
theorem geometricProperEulerFixedPrimitiveProjector_comm_galois
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N)) :
    (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι).comp
        (geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ) =
      (geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ).comp
        (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι) := by
  classical
  exact Representation.characterProjector_comm
    (EulerCover.coefficientDeckCharacter N ι)
    (geometricProperEulerCoefficientDeckRepresentation N m 𝒞 t ht h1t ℓ L)
    (geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ)
    (fun ξ => geometricProperEulerCoefficientDeckGalois_comm
      N m 𝒞 t ht h1t ℓ L ξ σ)

/-- The proper primitive character component is stable under the actual
cyclotomic-field Galois action. -/
theorem geometricProperEulerFixedPrimitiveProjector_galois_mem_range
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    {v : GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L}
    (hv : v ∈ (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι).range) :
    geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ v ∈
      (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι).range := by
  rcases hv with ⟨w, rfl⟩
  refine ⟨geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ w, ?_⟩
  exact congrArg (fun f : _ →ₗ[L] _ => f w)
    (geometricProperEulerFixedPrimitiveProjector_comm_galois
      N m 𝒞 t ht h1t ℓ L ι σ)

/-- The fixed-character summand of the actual proper geometric Euler fibre
as a subrepresentation of its arithmetic Galois action over `F_N`. -/
def properPrimitiveGaloisSubrepresentation
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    Subrepresentation
      (geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L) where
  toSubmodule :=
    (geometricProperEulerFixedPrimitiveProjector N m 𝒞 t ht h1t ℓ L ι).range
  apply_mem_toSubmodule σ := by
    intro v hv
    exact geometricProperEulerFixedPrimitiveProjector_galois_mem_range
      N m 𝒞 t ht h1t ℓ L ι σ hv

/-- Arithmetic Galois restricted to the proper primitive summand. -/
def properPrimitiveGaloisRepresentation
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L) :
    Representation L
      (AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
        AlgebraicClosure (Cyclotomic.cyclotomicField N))
      (properPrimitiveGaloisSubrepresentation N m 𝒞 t ht h1t ℓ L ι).toSubmodule :=
  (properPrimitiveGaloisSubrepresentation N m 𝒞 t ht h1t ℓ L ι).toRepresentation

/-- Restricting the proper Euler Galois action does not change its underlying
cohomology class. -/
theorem properPrimitiveGaloisRepresentation_val
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (ι : Cyclotomic.cyclotomicField N →+* L)
    (g : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N))
    (v : (properPrimitiveGaloisSubrepresentation N m 𝒞 t ht h1t ℓ L ι).toSubmodule) :
    ((properPrimitiveGaloisRepresentation N m 𝒞 t ht h1t ℓ L ι g v) :
      GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L) =
      geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L g v.1 :=
  (rfl)

end HilbertModularity.Hypergeometric
