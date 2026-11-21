/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationChartDeckRelation
public import HilbertModularity.Hypergeometric.GaloisRealizationQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Deck action on the selected proper Euler fibre

The deck action on the proper fibre is specialized from the chosen family.
These lemmas compare it with the explicit affine deck transformation, retaining
the same cyclotomic root label used in [GPRV, equation (76)].
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace HilbertModularity.Hypergeometric

variable (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t))

/-- Specializing a constant root of unity through the parameter ring retains
its original cyclotomic label. -/
theorem constantDeckRoot_specialization
    (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    rootsOfUnity.mapHom N
      (EulerCover.parameterEval (Cyclotomic.cyclotomicField N) t ht h1t)
      (rootsOfUnity.mapHom N
        (algebraMap (Cyclotomic.cyclotomicField N)
          (ProjectiveLine.puncturedCoordinateRing
            (Cyclotomic.cyclotomicField N))) ζ) = ζ := by
  apply Subtype.ext
  apply Units.ext
  have h := EulerCover.parameterEval_coeff
    (Cyclotomic.cyclotomicField N) t ht h1t
      (((ζ : (Cyclotomic.cyclotomicField N)ˣ) : Cyclotomic.cyclotomicField N))
  rw [← Polynomial.algebraMap_eq] at h
  rw [← IsScalarTower.algebraMap_apply] at h
  simpa [rootsOfUnity.coe_mapHom] using h

/-- On the actual specialized affine chart, the proper-fibre deck action is
the explicit scaling of the Euler root coordinate by the same `ζ`. -/
theorem smoothProperEulerFibreChartInclusion_deck
    (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N)) :
    (EulerCover.deckTransformation N m t ζ).hom ≫
      smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t =
    smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t ≫
      (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ).unop.hom := by
  let a : EulerCover.affineScheme N m t ⟶
      EulerCover.affineFamily (Cyclotomic.cyclotomicField N) N m :=
    EulerCover.affineFamilySpecialization
    (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
    N m t ht h1t
  let i : EulerCover.affineFamily (Cyclotomic.cyclotomicField N) N m ⟶
      𝒞.curve := 𝒞.affineInclusion
  let j : EulerCover.affineScheme N m t ⟶
      smoothProperEulerFibre N m 𝒞 t ht h1t :=
    smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t
  let d : EulerCover.affineScheme N m t ⟶
      EulerCover.affineScheme N m t :=
    (EulerCover.deckTransformation N m t ζ).hom
  let D : smoothProperEulerFibre N m 𝒞 t ht h1t ⟶
      smoothProperEulerFibre N m 𝒞 t ht h1t :=
    (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ).unop.hom
  let p : smoothProperEulerFibre N m 𝒞 t ht h1t ⟶ 𝒞.curve :=
    smoothProperEulerFibreToCurve N m 𝒞 t ht h1t
  let s : smoothProperEulerFibre N m 𝒞 t ht h1t ⟶
      Spec (CommRingCat.of (Cyclotomic.cyclotomicField N)) :=
    smoothProperEulerFibreStructureMap N m 𝒞 t ht h1t
  let z := rootsOfUnity.mapHom N
    (algebraMap (Cyclotomic.cyclotomicField N)
      (ProjectiveLine.puncturedCoordinateRing (Cyclotomic.cyclotomicField N))) ζ
  have hspec : a ≫ (EulerCover.deckTransformation N m
      (EulerCover.familyParameter (Cyclotomic.cyclotomicField N)) z).hom =
      d ≫ a := by
    simpa only [a, d, z, constantDeckRoot_specialization N t ht h1t ζ]
      using EulerCover.affineFamilySpecialization_deck
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t z
  have hfamily :
      (EulerCover.deckTransformation N m
        (EulerCover.familyParameter (Cyclotomic.cyclotomicField N)) z).hom ≫ i =
      i ≫ (𝒞.deckAction ζ).unop.hom.left :=
    𝒞.affineInclusion_deck ζ
  have hj : j ≫ p = a ≫ i :=
    smoothProperEulerFibreChartInclusion_fst N m 𝒞 t ht h1t
  have hD : D ≫ p = p ≫ (𝒞.deckAction ζ).unop.hom.left :=
    smoothProperEulerFibreDeckAction_fst N m 𝒞 t ht h1t ζ
  have hjs : j ≫ s = EulerCover.structureMap N m t :=
    smoothProperEulerFibreChartInclusion_snd N m 𝒞 t ht h1t
  have hDs : D ≫ s = s :=
    smoothProperEulerFibreDeckAction_structureMap N m 𝒞 t ht h1t ζ
  apply pullback.hom_ext
  · change (d ≫ j) ≫ p = (j ≫ D) ≫ p
    calc
      (d ≫ j) ≫ p = d ≫ (j ≫ p) := Category.assoc _ _ _
      _ = d ≫ (a ≫ i) := by rw [hj]
      _ = (a ≫ (EulerCover.deckTransformation N m
          (EulerCover.familyParameter (Cyclotomic.cyclotomicField N)) z).hom) ≫ i := by
            exact (Category.assoc d a i).symm.trans
              (congrArg (fun f => f ≫ i) hspec.symm)
      _ = (a ≫ i) ≫ (𝒞.deckAction ζ).unop.hom.left := by
            exact (Category.assoc a _ i).trans
              ((congrArg (fun f => a ≫ f) hfamily).trans
                (Category.assoc a i _).symm)
      _ = (j ≫ p) ≫ (𝒞.deckAction ζ).unop.hom.left := by rw [hj]
      _ = j ≫ (D ≫ p) := by rw [hD, ← Category.assoc]
      _ = (j ≫ D) ≫ p := (Category.assoc _ _ _).symm
  · change (d ≫ j) ≫ s = (j ≫ D) ≫ s
    calc
      (d ≫ j) ≫ s = d ≫ (j ≫ s) := Category.assoc _ _ _
      _ = d ≫ EulerCover.structureMap N m t := by rw [hjs]
      _ = EulerCover.structureMap N m t :=
        EulerCover.deckTransformation_structureMap N m t ζ
      _ = j ≫ s := hjs.symm
      _ = j ≫ (D ≫ s) := by rw [hDs]
      _ = (j ≫ D) ≫ s := (Category.assoc _ _ _).symm

/-- The reflection conjugates the actual deck action on the same selected
proper fibre.  Density and reducedness are stated explicitly: neither follows
from density of the chart in the total family alone. -/
theorem smoothProperEulerFibreReflection_deck
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (hmPos : 1 ≤ m) (hmN : m < N) (hcop : m.Coprime N)
    (ζ : rootsOfUnity N (Cyclotomic.cyclotomicField N))
    [IsReduced (smoothProperEulerFibre N m 𝒞 t ht h1t)]
    [(smoothProperEulerFibre N m 𝒞 t ht h1t).IsSeparated]
    [IsDominant (smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t)] :
    (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom ≫
        (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ).unop.hom =
      (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ⁻¹).unop.hom ≫
        (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom := by
  let j := smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t
  let r := (EulerCover.reflectionChartSchemeIso N m t (NeZero.ne N)
    hmPos hmN hcop ht.ne_zero).hom
  let d := (EulerCover.deckTransformation N m t ζ).hom
  let di := (EulerCover.deckTransformation N m t ζ⁻¹).hom
  let S := (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom
  let D := (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ).unop.hom
  let Di := (smoothProperEulerFibreDeckAction N m 𝒞 t ht h1t ζ⁻¹).unop.hom
  have hr : r ≫ j = j ≫ S := 𝒬.involution_affineChart t ht h1t hmPos hmN hcop
  have hd : d ≫ j = j ≫ D :=
    smoothProperEulerFibreChartInclusion_deck N m 𝒞 t ht h1t ζ
  have hdi : di ≫ j = j ≫ Di :=
    smoothProperEulerFibreChartInclusion_deck N m 𝒞 t ht h1t ζ⁻¹
  have hrd : r ≫ d = di ≫ r :=
    EulerCover.reflectionChartSchemeIso_comp_deck N m t hmPos hmN hcop ht.ne_zero ζ
  apply ext_of_isDominant j
  change j ≫ (S ≫ D) = j ≫ (Di ≫ S)
  calc
    j ≫ (S ≫ D) = (r ≫ j) ≫ D := by rw [hr]; simp only [Category.assoc]
    _ = r ≫ (d ≫ j) := by rw [hd]; simp only [Category.assoc]
    _ = (di ≫ r) ≫ j := by rw [← Category.assoc, hrd, Category.assoc]
    _ = di ≫ (j ≫ S) := by rw [Category.assoc, hr]
    _ = j ≫ (Di ≫ S) := by rw [← Category.assoc, hdi, Category.assoc]

end HilbertModularity.Hypergeometric
