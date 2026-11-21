/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.SchemeSpecialization
public import HilbertModularity.Geometry.Etale.Cohomology.Galois
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.NumberTheory.Cyclotomic

/-! # The smooth proper Euler family

The affine exponent-`m` Euler family already has an actual scheme and parameter
map.  A smooth proper completion is a separate geometric construction.  The
chosen completion below is over the entire punctured parameter line, so its
fibres come from one family, as required by
[TripathiGoswamiRevised, Definition 2.3].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

namespace HilbertModularity.Hypergeometric

universe u

/-- Coefficient extension on the affine ring of the punctured parameter line. -/
def puncturedCoordinateMap {K F : Type u} [Field K] [Field F]
    (σ : K →+* F) :
    ProjectiveLine.puncturedCoordinateRing K →+*
      ProjectiveLine.puncturedCoordinateRing F :=
  Localization.awayLift
    ((algebraMap F[X] (ProjectiveLine.puncturedCoordinateRing F)).comp
      (Polynomial.mapRingHom σ))
    ((X : K[X]) * (X - 1)) (by
      have h : ((X : K[X]) * (X - 1)).map σ =
          (X : F[X]) * (X - 1) := by simp
      change IsUnit ((algebraMap F[X] (ProjectiveLine.puncturedCoordinateRing F))
        (((X : K[X]) * (X - 1)).map σ))
      rw [h]
      exact IsLocalization.Away.algebraMap_isUnit ((X : F[X]) * (X - 1)))

/-- The parameter coordinate is unchanged by coefficient extension. -/
@[simp] theorem puncturedCoordinateMap_algebraMap {K F : Type u}
    [Field K] [Field F] (σ : K →+* F) (f : K[X]) :
    puncturedCoordinateMap σ
        (algebraMap K[X] (ProjectiveLine.puncturedCoordinateRing K) f) =
      algebraMap F[X] (ProjectiveLine.puncturedCoordinateRing F) (f.map σ) := by
  simp [puncturedCoordinateMap, Localization.awayLift, IsLocalization.Away.lift_eq]

/-- Coefficient change fixes the parameter coordinate of the Euler family. -/
@[simp] theorem puncturedCoordinateMap_familyParameter {K F : Type u}
    [Field K] [Field F] (σ : K →+* F) :
    puncturedCoordinateMap σ (EulerCover.familyParameter K) =
      EulerCover.familyParameter F := by
  simpa only [EulerCover.familyParameter, Polynomial.map_X] using
    puncturedCoordinateMap_algebraMap σ (X : K[X])

/-- Coefficient change on the *actual* affine Euler family. Its coordinate
ring map is `EulerCover.coverRingMap` applied to the parameter-ring map;
in particular it sends the original Euler root `y` to the original `y`,
with no deck rotation. -/
def affineFamilyCoefficientMap {K F : Type u} [Field K] [Field F]
    (σ : K →+* F) (N m : ℕ) :
    EulerCover.affineFamily F N m ⟶ EulerCover.affineFamily K N m := by
  simpa only [EulerCover.affineFamily, puncturedCoordinateMap_familyParameter] using
    (EulerCover.affineSchemeBaseChange (puncturedCoordinateMap σ) N m
      (EulerCover.familyParameter K))

/-- The ring map defining coefficient change sends the original Euler
covering coordinate to the original covering coordinate. -/
theorem affineFamilyCoefficientMap_root {K F : Type u} [Field K] [Field F]
    (σ : K →+* F) (N m : ℕ) :
    HEq (EulerCover.coverRingMap (puncturedCoordinateMap σ) N m
        (EulerCover.familyParameter K)
        (EulerCover.coverRoot N m (EulerCover.familyParameter K)))
      (EulerCover.coverRoot N m (EulerCover.familyParameter F)) := by
  rw [EulerCover.coverRingMap_root]
  rw [puncturedCoordinateMap_familyParameter]

/-- The same ring map also preserves the original branch coordinate `x`.
Together with `affineFamilyCoefficientMap_root`, this rules out a hidden
deck rotation in the affine coefficient-change map. -/
theorem affineFamilyCoefficientMap_x {K F : Type u} [Field K] [Field F]
    (σ : K →+* F) (N m : ℕ) :
    HEq (EulerCover.coverRingMap (puncturedCoordinateMap σ) N m
        (EulerCover.familyParameter K)
        (algebraMap (EulerCover.BaseRing (EulerCover.familyParameter K))
          (EulerCover.CoverRing N m (EulerCover.familyParameter K))
          (algebraMap (ProjectiveLine.puncturedCoordinateRing K)[X]
            (EulerCover.BaseRing (EulerCover.familyParameter K)) X)))
      (algebraMap (EulerCover.BaseRing (EulerCover.familyParameter F))
        (EulerCover.CoverRing N m (EulerCover.familyParameter F))
        (algebraMap (ProjectiveLine.puncturedCoordinateRing F)[X]
          (EulerCover.BaseRing (EulerCover.familyParameter F)) X)) := by
  rw [EulerCover.coverRingMap_algebraMap]
  rw [EulerCover.baseRingMap_algebraMap]
  simp only [Polynomial.map_X]
  rw [puncturedCoordinateMap_familyParameter]

/-- The parameter-preserving map from the punctured line over `F` to that
over `K`. It is the actual scalar-change map for the real Euler model. -/
def puncturedCoefficientMap {K F : Type u} [Field K] [Field F]
    (σ : K →+* F) :
    ProjectiveLine.punctured F ⟶ ProjectiveLine.punctured K :=
  (ProjectiveLine.puncturedAffineIso F).hom ≫
    Spec.map (CommRingCat.ofHom (puncturedCoordinateMap σ)) ≫
      (ProjectiveLine.puncturedAffineIso K).inv

/-- The real cyclotomic field's actual inclusion in the coefficient field
of the deck action. Defined here so the family can record its real form. -/
@[expose] def realEulerCoefficientInclusion (N : ℕ) [NeZero N] :
    Cyclotomic.realCyclotomicField N →+*
      Cyclotomic.cyclotomicField N :=
  IntermediateField.inclusion (Cyclotomic.realCyclotomicField_le N)

/-- A smooth proper model of the *actual* exponent-`m` Euler family over the
cyclotomic parameter line.  The displayed open immersion identifies its
dense affine chart with `EulerCover.affineFamily`; it is geometric data, not
a representation with prescribed Frobenius values. -/
structure SmoothProperEulerFamily (N m : ℕ) [NeZero N] where
  curve : Scheme
  projection : curve ⟶ ProjectiveLine.punctured (Cyclotomic.cyclotomicField N)
  isProper : IsProper projection
  isSmooth : Smooth projection
  affineInclusion :
    EulerCover.affineFamily (Cyclotomic.cyclotomicField N) N m ⟶ curve
  affineInclusion_isOpenImmersion : IsOpenImmersion affineInclusion
  affineInclusion_denseRange : DenseRange affineInclusion
  affineInclusion_overBase :
    affineInclusion ≫ projection =
      EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m
  pair_affineOpen : ∀ x y : curve, ∃ U : curve.Opens,
    IsAffineOpen U ∧ x ∈ U ∧ y ∈ U
  realCurve : Scheme
  realProjection : realCurve ⟶
    ProjectiveLine.punctured (Cyclotomic.realCyclotomicField N)
  realIsProper : IsProper realProjection
  realIsSmooth : Smooth realProjection
  realRelDimOne : SmoothOfRelativeDimension 1 realProjection
  realPair_affineOpen : ∀ x y : realCurve, ∃ U : realCurve.Opens,
    IsAffineOpen U ∧ x ∈ U ∧ y ∈ U
  realAffineInclusion :
    EulerCover.affineFamily (Cyclotomic.realCyclotomicField N) N m ⟶ realCurve
  realAffineInclusion_isOpenImmersion : IsOpenImmersion realAffineInclusion
  realAffineInclusion_denseRange : DenseRange realAffineInclusion
  realAffineInclusion_overBase :
    realAffineInclusion ≫ realProjection =
      EulerCover.familyStructureMap (Cyclotomic.realCyclotomicField N) N m
  realBaseChangeIso : curve ≅
    pullback realProjection (puncturedCoefficientMap
      (realEulerCoefficientInclusion N))
  realBaseChangeIso_overBase :
    realBaseChangeIso.hom ≫ pullback.snd _ _ = projection
  realBaseChangeIso_affineInclusion :
    affineInclusion ≫ realBaseChangeIso.hom ≫ pullback.fst _ _ =
      affineFamilyCoefficientMap (realEulerCoefficientInclusion N) N m ≫
        realAffineInclusion
  deckAction :
    rootsOfUnity N (Cyclotomic.cyclotomicField N) →*
      (Aut (Over.mk projection))ᵐᵒᵖ
  affineInclusion_deck : ∀ ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N),
    (EulerCover.familyDeckOverIso (Cyclotomic.cyclotomicField N) N m
      (rootsOfUnity.mapHom N
        (algebraMap (Cyclotomic.cyclotomicField N)
          (ProjectiveLine.puncturedCoordinateRing (Cyclotomic.cyclotomicField N))) ξ)).hom.left ≫
        affineInclusion =
      affineInclusion ≫ (deckAction ξ).unop.hom.left

/-- For a chart-coherent selected family, the concrete Euler coefficient
map also respects the parameter projection. This follows from the two
commuting squares in the record; no separate map is chosen. -/
theorem SmoothProperEulerFamily.affineFamilyCoefficientMap_overBase
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m) :
    affineFamilyCoefficientMap (realEulerCoefficientInclusion N) N m ≫
        EulerCover.familyStructureMap (Cyclotomic.realCyclotomicField N) N m =
      EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m ≫
        puncturedCoefficientMap (realEulerCoefficientInclusion N) := by
  let σ := realEulerCoefficientInclusion N
  let p := puncturedCoefficientMap σ
  let a := affineFamilyCoefficientMap σ N m
  let e := 𝒞.realBaseChangeIso.hom
  have hchart : 𝒞.affineInclusion ≫ e ≫
      pullback.fst 𝒞.realProjection p = a ≫ 𝒞.realAffineInclusion :=
    𝒞.realBaseChangeIso_affineInclusion
  have hbase : 𝒞.affineInclusion ≫ e ≫
      pullback.snd 𝒞.realProjection p =
        EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m := by
    calc
      _ = 𝒞.affineInclusion ≫ 𝒞.projection := by
        dsimp only [e, p]
        rw [𝒞.realBaseChangeIso_overBase]
      _ = _ := 𝒞.affineInclusion_overBase
  change a ≫ EulerCover.familyStructureMap (Cyclotomic.realCyclotomicField N) N m =
    EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m ≫ p
  calc
    a ≫ EulerCover.familyStructureMap (Cyclotomic.realCyclotomicField N) N m =
        (a ≫ 𝒞.realAffineInclusion) ≫ 𝒞.realProjection := by
          simp only [Category.assoc, 𝒞.realAffineInclusion_overBase]
    _ = (𝒞.affineInclusion ≫ e ≫ pullback.fst 𝒞.realProjection p) ≫
          𝒞.realProjection := by rw [hchart]
    _ = (𝒞.affineInclusion ≫ e ≫ pullback.snd 𝒞.realProjection p) ≫ p := by
          simp only [Category.assoc]
          rw [pullback.condition]
    _ = EulerCover.familyStructureMap (Cyclotomic.cyclotomicField N) N m ≫ p := by
          rw [hbase]

/-- The tame cyclic-cover construction of [EsnaultViehweg, §3, (3.5)–(3.13)
and Lemma 3.15(b)], applied to the Euler equation of [GPRV, Definition 8.2].
On the relative projective line take `L = O(2)` and the section with divisor
`m[0] + (N-m)[1] + m[1/t] + (N-m)[∞]`. Its four sections are disjoint on the
punctured parameter line. The normalized cyclic algebra in (3.7)–(3.10) is
finite over that projective line and has the deck action of (3.9).

The source is written over algebraically closed fields. Its explicit algebra
and multiplication are defined over the cyclotomic ground field. The relative
smoothness assertion uses its local equation (3.13)(c), `z^N = u^a x`, with
`x` a relative parameter and `u` a unit, and the étale branch complement.
The same finite map to the relative projective line gives an affine open
containing each pair of points of the cover, recorded as `pair_affineOpen`.
This is the orbit-in-affine hypothesis of [SGA1, Exposé V, Proposition 1.8]
for any later involution; it does not choose or assert that involution.
The Euler equation is defined over the real field before adjoining `ζ_N`.
The construction over that field gives `realCurve` and its actual
branch-open Euler immersion. Its parameter-preserving cyclotomic
base-change isomorphism agrees on that same affine chart with
`affineFamilyCoefficientMap`, which is induced by the coefficientwise Euler
algebra map preserving both `x` and `y`. This excludes a deck-rotated
identification. The deck action
requires the cyclotomic extension, but the curve itself does not. Its
relative dimension one and pair-affine properties are recorded on the
real form as well as on the cyclotomic form.
This relative application and ground-field descent are included in the named
literature input; Lemma 3.15(b) alone is a statement of absolute nonsingularity.
No Frobenius, cohomological comparison or arithmetic descent is assumed here. -/
theorem exists_smoothProperEulerFamily_of_coprime (N m : ℕ) [NeZero N]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : Nat.Coprime N m) :
    Nonempty (SmoothProperEulerFamily N m) := by
  sorry

/-- The prime-level specialization of the tame cyclic-cover input.
Coprimality of the branch multiplicities follows from the exponent range. -/
theorem exists_smoothProperEulerFamily (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    Nonempty (SmoothProperEulerFamily N m) := by
  apply exists_smoothProperEulerFamily_of_coprime N m (le_trans (by decide) h5) hm hmN
  exact hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)

/-- One generic smooth proper Euler family, chosen once before specializing
the parameter or the coefficient place. -/
def chosenSmoothProperEulerFamily (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N) :
    SmoothProperEulerFamily N m :=
  Classical.choice (exists_smoothProperEulerFamily N m hN h5 hm hmN)

end HilbertModularity.Hypergeometric

namespace HilbertModularity.Hypergeometric

open CategoryTheory.Limits

variable (N m : ℕ) [NeZero N]

/-- The actual fibre of a chosen smooth proper Euler family over a point of
the punctured cyclotomic parameter line. -/
@[expose] def smoothProperEulerFibre (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    Scheme :=
  pullback 𝒞.projection
    (EulerCover.puncturedParameterPoint
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t)

/-- Its structural map to the cyclotomic ground field. -/
@[expose] def smoothProperEulerFibreStructureMap (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    smoothProperEulerFibre N m 𝒞 t ht h1t ⟶
      Spec (CommRingCat.of (Cyclotomic.cyclotomicField N)) :=
  pullback.snd _ _

/-- Properness of every fibre follows from the proper family projection by
base change. -/
theorem smoothProperEulerFibre_isProper (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    IsProper (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) := by
  let : IsProper 𝒞.projection := 𝒞.isProper
  change IsProper (pullback.snd 𝒞.projection
    (EulerCover.puncturedParameterPoint
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t))
  infer_instance

/-- Smoothness of every fibre follows from the smooth family projection by
base change. -/
theorem smoothProperEulerFibre_isSmooth (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    Smooth (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) := by
  let : Smooth 𝒞.projection := 𝒞.isSmooth
  change Smooth (pullback.snd 𝒞.projection
    (EulerCover.puncturedParameterPoint
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t))
  infer_instance

/-- The family deck action after specialization, retaining its map over the
ground field. -/
def smoothProperEulerFibreDeckActionOver (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    rootsOfUnity N (Cyclotomic.cyclotomicField N) →*
      (Aut (Over.mk (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t)))ᵐᵒᵖ :=
  (MonoidHom.op
    ((Over.pullback (EulerCover.puncturedParameterPoint
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t)).mapAut
        (Over.mk 𝒞.projection))).comp 𝒞.deckAction

/-- The actual family deck action specialized to a parameter fibre.  The
opposite group records the variance of the later cohomological pullback. -/
def smoothProperEulerFibreDeckAction (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    rootsOfUnity N (Cyclotomic.cyclotomicField N) →*
      (Aut (smoothProperEulerFibre N m 𝒞 t ht h1t))ᵐᵒᵖ :=
  (MonoidHom.op
    ((Over.pullback (EulerCover.puncturedParameterPoint
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t) ⋙
      Over.forget (Spec (CommRingCat.of (Cyclotomic.cyclotomicField N)))).mapAut
        (Over.mk 𝒞.projection))).comp 𝒞.deckAction

/-- The selected fibre deck transformation projects to its family action. -/
theorem smoothProperEulerFibreDeckAction_fst (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ξ).unop.hom ≫
      pullback.fst 𝒞.projection
        (EulerCover.puncturedParameterPoint
          (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t) =
    pullback.fst 𝒞.projection
      (EulerCover.puncturedParameterPoint
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N) t ht h1t) ≫
      (𝒞.deckAction ξ).unop.hom.left := by
  change ((Over.pullback (EulerCover.puncturedParameterPoint
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
      t ht h1t)).map (𝒞.deckAction ξ).unop.hom).left ≫
        pullback.fst 𝒞.projection _ =
      pullback.fst 𝒞.projection _ ≫ (𝒞.deckAction ξ).unop.hom.left
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

/-- Every specialized deck transformation is a map over the cyclotomic
ground field. -/
theorem smoothProperEulerFibreDeckAction_structureMap
    (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ξ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ξ).unop.hom ≫
        smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t =
      smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t := by
  exact (smoothProperEulerFibreDeckActionOver N m 𝒞 t ht h1t ξ).unop.hom.w

/-- The geometric proper Euler fibre is the actual base change of that fibre
to the algebraic closure of the cyclotomic ground field. -/
abbrev geometricSmoothProperEulerFibre (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t)) :
    Scheme :=
  pullback
    (GroupScheme.fieldPoint (Cyclotomic.cyclotomicField N)
      (AlgebraicClosure (Cyclotomic.cyclotomicField N))).hom
    (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t)

/-- Degree-one cohomology of the actual geometric proper Euler fibre after
extension to a chosen coefficient field. -/
abbrev GeometricProperEulerCohomology (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] : Type _ :=
  L ⊗[ℚ_[ℓ]]
    (geometricSmoothProperEulerFibre N m 𝒞 t ht h1t).RationalEllAdicCohomology ℓ 1

/-- The algebraic Galois action on the actual proper geometric fibre. -/
def geometricProperEulerGaloisRepresentation (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L] :
    Representation L
      (AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
        AlgebraicClosure (Cyclotomic.cyclotomicField N))
      (GeometricProperEulerCohomology N m 𝒞 t ht h1t ℓ L) :=
  Representation.baseChange L
    (Representation.baseChange ℚ_[ℓ]
      (AlgebraicGeometry.Scheme.ellAdicCohomologyGaloisRepresentation
        (Cyclotomic.cyclotomicField N)
        (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ℓ 1))

/-- The coefficient-field Galois action is obtained by two scalar extensions
of the integral pullback action. -/
theorem geometricProperEulerGaloisRepresentation_eq
    (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t) (h1t : IsUnit (1 - t))
    (ℓ : ℕ) [Fact ℓ.Prime] (L : Type*) [Field L] [Algebra ℚ_[ℓ] L]
    (σ : AlgebraicClosure (Cyclotomic.cyclotomicField N) ≃ₐ[Cyclotomic.cyclotomicField N]
      AlgebraicClosure (Cyclotomic.cyclotomicField N)) :
    geometricProperEulerGaloisRepresentation N m 𝒞 t ht h1t ℓ L σ =
      LinearMap.baseChange L (LinearMap.baseChange ℚ_[ℓ]
        (AlgebraicGeometry.Scheme.ellAdicCohomologyGaloisRepresentation
          (Cyclotomic.cyclotomicField N)
          (smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t) ℓ 1 σ)) :=
  (rfl)

end HilbertModularity.Hypergeometric
