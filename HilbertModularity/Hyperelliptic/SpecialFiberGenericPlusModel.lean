/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberStableGeometry
public import HilbertModularity.Geometry.GroupScheme.PrimePlusScaledJacobian
public import HilbertModularity.NumberTheory.RealCyclotomicPrime

/-! # The generic fibre of the local scaled plus model

The local projective double cover used for the nodal special fibre has the
selected scaled plus curve as its generic fibre. This is an equality of the
actual two-chart model after coefficient change, and therefore the pointed
Jacobian already constructed for the plus family belongs to this same model.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

/-- Transport the pointed Jacobian property across an isomorphism of the
source curve over the same field, retaining the identical abelian variety. -/
def PointedCurveJacobian.transportIso {K : Type*} [Field K]
    {C D : Over (Spec (CommRingCat.of K))}
    {b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ D}
    {J : CommGrp (Over (Spec (CommRingCat.of K)))}
    (hJ : PointedCurveJacobian K D b J) (e : C ≅ D) :
    PointedCurveJacobian K C (b ≫ e.inv) J where
  targetProper := hJ.targetProper
  targetSmooth := hJ.targetSmooth
  targetGeometricallyConnected := hJ.targetGeometricallyConnected
  abelJacobi := e.hom ≫ hJ.abelJacobi
  normalized := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hJ.normalized
  universal := by
    intro A hproper hsmooth hconn f hnorm
    have hnorm' : b ≫ (e.inv ≫ f) =
        (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) := by
      simpa only [Category.assoc] using hnorm
    obtain ⟨h, hh, hu⟩ := hJ.universal A hproper hsmooth hconn
      (e.inv ≫ f) hnorm'
    refine ⟨h, ?_, ?_⟩
    · calc
        (e.hom ≫ hJ.abelJacobi) ≫ h.hom.hom.hom =
            e.hom ≫ (hJ.abelJacobi ≫ h.hom.hom.hom) := Category.assoc _ _ _
        _ = e.hom ≫ (e.inv ≫ f) := by rw [hh]
        _ = f := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    · intro h' hh'
      apply hu
      calc
        hJ.abelJacobi ≫ h'.hom.hom.hom =
            e.inv ≫ ((e.hom ≫ hJ.abelJacobi) ≫ h'.hom.hom.hom) := by
              simp only [Category.assoc, ← Category.assoc e.inv e.hom,
                e.inv_hom_id, Category.id_comp]
        _ = e.inv ≫ f := by rw [hh']

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hyperelliptic

private theorem geometricallyConnected_comp_iso
    {X Y S : Scheme} (e : X ≅ Y) (f : Y ⟶ S)
    (hc : GeometricallyConnected f) :
    GeometricallyConnected (e.hom ≫ f) := by
  have h := CategoryTheory.MorphismProperty.RespectsIso.precomp
    (geometrically (fun x => ConnectedSpace ↥x)) e.hom f
    hc.geometrically_connectedSpace
  exact ⟨h⟩

private theorem scaledBranch_natDegree_pos_of_nonzero
    {K : Type*} [Field K] (P : K[X]) (t : K) (ht : t ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    0 < (finiteBranchPolynomial P t).natDegree := by
  have h4 : (4 : K) ≠ 0 := by
      convert mul_ne_zero h2 h2 using 1; ring
  have hc : (finiteBranchPolynomial P t).coeff 1 = -(4 * t) := by
    simp [finiteBranchPolynomial,
      Polynomial.coeff_sub,
      Polynomial.coeff_X_pow_mul']
  have hne : (finiteBranchPolynomial P t).coeff 1 ≠ 0 := by
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero h4 ht)
  exact lt_of_lt_of_le (by omega : 0 < 1)
    (Polynomial.le_natDegree_of_ne_zero hne)

/-- A field element of positive local order is an element of the canonical
valuation subring used by the scaled stable model. -/
def realLocalScaledParameter (p : ℕ) [Fact p.Prime]
    (a : realCyclotomicField p)
    (ha : (realPrimeAboveConductor p).valuation (realCyclotomicField p) a < 1) :
    (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p) :=
  ⟨a, by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact (((realPrimeAboveConductor p).valuation
      (realCyclotomicField p)).mem_valuationSubring_iff a).2 (le_of_lt ha)⟩

@[simp] theorem realLocalScaledParameter_algebraMap (p : ℕ) [Fact p.Prime]
    (a : realCyclotomicField p)
    (ha : (realPrimeAboveConductor p).valuation (realCyclotomicField p) a < 1) :
    algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)) (realCyclotomicField p)
      (realLocalScaledParameter p a ha) = a := (rfl)

/-- Nonvanishing survives the inclusion into the local valuation ring. -/
theorem realLocalScaledParameter_ne_zero (p : ℕ) [Fact p.Prime]
    (a : realCyclotomicField p)
    (ha : (realPrimeAboveConductor p).valuation (realCyclotomicField p) a < 1)
    (ha0 : a ≠ 0) : realLocalScaledParameter p a ha ≠ 0 := by
  intro h
  have hfield := congrArg (algebraMap
    ((realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)) (realCyclotomicField p)) h
  exact ha0 (by simpa only [realLocalScaledParameter_algebraMap, map_zero] using hfield)

private theorem mem_maximalIdeal_of_eq_valuationSubring
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring K)
    (hA : A = v.valuationSubring) (x : A) (hx : v (x : K) < 1) :
    x ∈ IsLocalRing.maximalIdeal A := by
  cases hA
  exact (v.mem_maximalIdeal_iff).2 hx

/-- The constructed parameter lies in the maximal ideal of the actual
Dedekind localization. This states the manuscript's local hypothesis
directly, before identifying the residue field with `ZMod p`. -/
theorem realLocalScaledParameter_mem_maximalIdeal (p : ℕ) [Fact p.Prime]
    (a : realCyclotomicField p)
    (ha : (realPrimeAboveConductor p).valuation (realCyclotomicField p) a < 1) :
    realLocalScaledParameter p a ha ∈
      IsLocalRing.maximalIdeal
        ((realPrimeAboveConductor p).valuationSubringAtPrime
          (realCyclotomicField p)) := by
  let P := realPrimeAboveConductor p
  let v := P.valuation (realCyclotomicField p)
  apply mem_maximalIdeal_of_eq_valuationSubring v _
    P.valuationSubringAtPrime_eq_valuationSubring
  simpa only [realLocalScaledParameter] using ha

/-- Strictly positive local order places the scaled parameter in the maximal
ideal, so its actual cyclotomic residue is zero. -/
theorem realLocalScaledParameter_residue_zero (p : ℕ) [Fact p.Prime]
    (a : realCyclotomicField p)
    (ha : (realPrimeAboveConductor p).valuation (realCyclotomicField p) a < 1) :
    realLocalReduction p (realLocalScaledParameter p a ha) = 0 := by
  have hmax : realLocalScaledParameter p a ha ∈
      IsLocalRing.maximalIdeal
        ((realPrimeAboveConductor p).valuationSubringAtPrime
          (realCyclotomicField p)) :=
    realLocalScaledParameter_mem_maximalIdeal p a ha
  have hres := (IsLocalRing.residue_eq_zero_iff
    (realLocalScaledParameter p a ha)).2 hmax
  unfold Cyclotomic.realLocalReduction
    IsDedekindDomain.HeightOneSpectrum.localResidue
  change (realCyclotomicResidueEquiv p).toRingHom
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal
      (realPrimeAboveConductor p).asIdeal
      ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p))).symm.toRingHom
        ((IsLocalRing.residue _) (realLocalScaledParameter p a ha))) = 0
  rw [hres]
  change (realCyclotomicResidueEquiv p)
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal
    (realPrimeAboveConductor p).asIdeal
    ((realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))).symm 0) = 0
  rw [RingEquiv.map_zero, RingEquiv.map_zero]

/-- The coefficient-changed local polynomial is exactly the real scaled
polynomial used by the selected plus-Jacobian comparison. -/
theorem realLocalScaledDoubleCover_genericCurve_eq (p : ℕ) [Fact p.Prime]
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)) :
    let R := (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
    let f := algebraMap R (realCyclotomicField p)
    scaledDoubleCover (P.map f) (f T) =
      scaledDoubleCover (realScaledRootPolynomial p) (f T) := by
  dsimp only
  rw [map_localScaledRootPolynomial_eq_realScaled]

/-- The real-field polynomial used by the selected plus Jacobian has the
same degree `d=(p-1)/2` as the integral polynomial of the stable model. -/
theorem realScaledRootPolynomial_natDegree_eq (p : ℕ) [Fact p.Prime] :
    (realScaledRootPolynomial p).natDegree = (p - 1) / 2 := by
  rw [← map_localScaledRootPolynomial_eq_realScaled p
    (realPrimeAboveConductor p)]
  rw [monic_natDegree_map _ _
    (localScaledRootPolynomial_monic p (realPrimeAboveConductor p))]
  exact localCyclotomicScaledRootPolynomial_natDegree p

/-- The identity of generic curves also respects their structure morphisms
to the cyclotomic coefficient field. -/
def realLocalScaledDoubleCover_genericIso (p : ℕ) [Fact p.Prime]
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)) :
    let R := (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
    let f := algebraMap R (realCyclotomicField p)
    Over.mk (scaledDoubleCoverToSpec (P.map f) (f T)) ≅
      Over.mk (scaledModelToSpec (realScaledRootPolynomial p) (f T)) := by
  dsimp only
  rw [map_localScaledRootPolynomial_eq_realScaled]
  simp only [scaledDoubleCoverToSpec, scaledDoubleCoverProjection_eq,
    scaledModelToSpec_eq]
  exact Iso.refl _

/-- Base change from the canonical local coefficient ring to the real
cyclotomic field identifies the *same* proper flat scaled double cover with
the scaled generic model used in the plus-Jacobian comparison. -/
theorem realLocalScaledDoubleCover_genericFibre_isPullback (p : ℕ) [Fact p.Prime]
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)) :
    let R := (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
    let f := algebraMap R (realCyclotomicField p)
    IsPullback
      (scaledDoubleCoverMap f P T
        (monic_natDegree_map f P (localScaledRootPolynomial_monic p _)))
      (scaledDoubleCoverToSpec (P.map f) (f T))
      (scaledDoubleCoverToSpec P T)
      (Spec.map (CommRingCat.ofHom f)) := by
  let R := (realPrimeAboveConductor p).valuationSubringAtPrime
    (realCyclotomicField p)
  let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
  let f := algebraMap R (realCyclotomicField p)
  have hP : P.Monic := localScaledRootPolynomial_monic p _
  have h := scaledDoubleCoverMap_toSpec_isPullback (S := realCyclotomicField p)
    P T (monic_natDegree_map f P hP)
  exact h

/-- At a nonsingular plus-family parameter, the generic fibre of this
local integral model is smooth. The equality of field parameters is a
concrete coefficient identity; no generic smoothness of the integral total
space is inferred. -/
theorem realLocalScaledDoubleCover_genericSmooth (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hT : (algebraMap
      ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) (realCyclotomicField p)) T =
      ξ.val / (2 - tau p 1) ^ p) :
    let R := (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
    let f := algebraMap R (realCyclotomicField p)
    Smooth (scaledDoubleCoverToSpec (P.map f) (f T)) := by
  dsimp only
  rw [map_localScaledRootPolynomial_eq_realScaled, hT]
  simpa only [scaledDoubleCoverToSpec, scaledDoubleCoverProjection_eq,
    scaledModelToSpec_eq] using
      (realScaledModelToSpec_smooth p hp ξ.val ξ.property.1 ξ.property.2)

/-- The selected smooth proper scaled curve is geometrically connected.
Its comparison is an isomorphism over the coefficient field with the plus
curve whose selected pointed-Jacobian property records geometric
connectedness. This transports that property along the actual curve iso.
The smooth proper curve input is [src_poonen_curves, §§2.1.2 and 2.8.1,
printed pp. 23 and 36–37]; the selected Jacobian property is the cited
Darmon plus-family input in `primePlusRationalFiberJacobian`. -/
theorem realScaledModelToSpec_geometricallyConnected (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    GeometricallyConnected (scaledModelToSpec (realScaledRootPolynomial p)
      (ξ.val / (2 - tau p 1) ^ p)) := by
  let t : realCyclotomicField p := ξ.val / (2 - tau p 1) ^ p
  have ht : t ≠ 0 := div_ne_zero ξ.property.1
    (pow_ne_zero _ (realCyclotomicScale_ne_zero p))
  have h2 : (2 : realCyclotomicField p) ≠ 0 := by norm_num
  have hscaled := AlgebraicGeometry.DoubleCover.integral_and_smoothOfRelativeDimension_one
    (finiteBranchPolynomial (realScaledRootPolynomial p) t)
    (infinityBranchPolynomial (realScaledRootPolynomial p) t)
    ((realScaledRootPolynomial p).natDegree + 1)
    (branch_transition (realScaledRootPolynomial p) t)
    (realScaledFiniteBranch_separable p hp ξ.val ξ.property.1 ξ.property.2)
    (realScaledInfinityBranch_separable p hp ξ.val ξ.property.1 ξ.property.2)
    (scaledBranch_natDegree_pos_of_nonzero (realScaledRootPolynomial p) t ht h2) h2
  let : IsIntegral (scaledDoubleCover (realScaledRootPolynomial p) t) :=
    hscaled.1
  let : SmoothOfRelativeDimension 1
      (scaledModelToSpec (realScaledRootPolynomial p) t) := by
    rw [scaledModelToSpec_eq]
    exact hscaled.2
  have hplus := AlgebraicGeometry.DoubleCover.integral_and_smoothOfRelativeDimension_one
    (plusPolynomial p ξ.val) (plusPolynomial p ξ.val).reverse
    ((p + 1) / 2)
    (AlgebraicGeometry.Hyperelliptic.reverse_transition _ _
      (plusPolynomial_evenDegree p (Hypergeometric.primePlusData p hp).p_odd ξ.val))
    (plusPolynomial_separable p (Hypergeometric.primePlusData p hp).p_odd h2
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      ξ.val ξ.property.1 ξ.property.2)
    (plusPolynomial_separable p (Hypergeometric.primePlusData p hp).p_odd h2
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      ξ.val ξ.property.1 ξ.property.2).reverse
    (by rw [plusPolynomial_evenDegree p (Hypergeometric.primePlusData p hp).p_odd ξ.val]
        omega) h2
  let : IsIntegral (plusCurve p (Hypergeometric.primePlusData p hp).p_odd ξ.val) :=
    hplus.1
  obtain ⟨e, he, _⟩ := exists_realScaledModelIso_plusCurve p hp ξ.val
    ξ.property.1 ξ.property.2
  have hc : GeometricallyConnected
      (plusCurveToSpec p (Hypergeometric.primePlusData p hp).p_odd ξ.val) :=
    (Hypergeometric.primePlusRationalFiberJacobian p hp ξ).curveGeometricallyConnected
  rw [← he]
  exact geometricallyConnected_comp_iso e _ hc

/-- Geometric connectedness belongs to the generic fibre of the exact
local scaled cover after field base change. -/
theorem realLocalScaledDoubleCover_genericGeometricallyConnected
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hT : (algebraMap
      ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) (realCyclotomicField p)) T =
      ξ.val / (2 - tau p 1) ^ p) :
    let R := (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
    let f := algebraMap R (realCyclotomicField p)
    GeometricallyConnected (scaledDoubleCoverToSpec (P.map f) (f T)) := by
  dsimp only
  rw [map_localScaledRootPolynomial_eq_realScaled, hT]
  simpa only [scaledDoubleCoverToSpec, scaledDoubleCoverProjection_eq,
    scaledModelToSpec_eq] using
      (realScaledModelToSpec_geometricallyConnected p hp ξ)

/-- The generic fibre of the local scaled model has the pointed Jacobian of
the **same selected plus family**. The equality of scaled field parameters
connects the integral model parameter to the existing plus-fibre comparison;
the target abelian variety and its integral RM action are not replaced. -/
def realLocalScaledDoubleCover_genericJacobian (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (T : (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hT : (algebraMap
      ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) (realCyclotomicField p)) T =
      ξ.val / (2 - tau p 1) ^ p) :
    let R := (realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (realPrimeAboveConductor p)
    let f := algebraMap R (realCyclotomicField p)
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledDoubleCoverToSpec (P.map f) (f T)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledDoubleCoverToSpec (P.map f) (f T))) b
        (GroupScheme.fiber (realCyclotomicField p)
          (Hypergeometric.primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  dsimp only
  rw [hT]
  let e : Over.mk (scaledDoubleCoverToSpec
      ((localScaledRootPolynomial p (realPrimeAboveConductor p)).map
        (algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
          (realCyclotomicField p)) (realCyclotomicField p)))
      (ξ.val / (2 - tau p 1) ^ p)) ≅
      Over.mk (scaledModelToSpec (realScaledRootPolynomial p)
        (ξ.val / (2 - tau p 1) ^ p)) := by
    have e₀ := realLocalScaledDoubleCover_genericIso p T
    dsimp only at e₀
    rw [hT] at e₀
    exact e₀
  obtain ⟨b, hb⟩ := Hypergeometric.primePlusRealScaledFiberJacobian p hp ξ
  exact ⟨b ≫ e.inv, hb.transportIso e⟩

/-- The selected pointed Jacobian has relative dimension `d=(p-1)/2`.
For the smooth geometrically connected generic curve, this is the genus
index in the classical Jacobian–genus comparison; the underlying relative
dimension statement is already available from the selected plus family. -/
theorem primePlusSelectedJacobian_relativeDimension (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    SmoothOfRelativeDimension ((p - 1) / 2)
      (GroupScheme.fiber (realCyclotomicField p)
        (Hypergeometric.primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).X.hom := by
  rw [← finrank_realCyclotomicField p (by omega)]
  infer_instance

/-- Concrete same-model data supplied to the Raynaud/Picard step. The
generic curve is smooth and geometrically connected and has the selected
plus Jacobian; its proper flat local model has the checked split nodal
special-fibre geometry. No regularity of the integral total space is claimed.
-/
structure PrimePlusScaledStableModelData (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) where
  T : (realPrimeAboveConductor p).valuationSubringAtPrime
    (realCyclotomicField p)
  field_parameter :
    (algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p)) (realCyclotomicField p)) T =
        ξ.val / (2 - tau p 1) ^ p
  nonzero : T ≠ 0
  maximal : T ∈ IsLocalRing.maximalIdeal
    ((realPrimeAboveConductor p).valuationSubringAtPrime
      (realCyclotomicField p))
  residue_zero : realLocalReduction p T = 0
  special_geometry : CyclotomicStableGeometry.{0, 0, 0, 0, 0, 0} p T
  generic_smooth :
    Smooth (scaledDoubleCoverToSpec
      ((localScaledRootPolynomial p (realPrimeAboveConductor p)).map
        (algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
          (realCyclotomicField p)) (realCyclotomicField p)))
      ((algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) (realCyclotomicField p)) T))
  generic_geometricallyConnected :
    GeometricallyConnected (scaledDoubleCoverToSpec
      ((localScaledRootPolynomial p (realPrimeAboveConductor p)).map
        (algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
          (realCyclotomicField p)) (realCyclotomicField p)))
      ((algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) (realCyclotomicField p)) T))
  pointed_jacobian :
    Σ b : Over.mk (𝟙 (Spec (CommRingCat.of (realCyclotomicField p)))) ⟶
        Over.mk (scaledDoubleCoverToSpec
          ((localScaledRootPolynomial p (realPrimeAboveConductor p)).map
            (algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
              (realCyclotomicField p)) (realCyclotomicField p)))
          ((algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
            (realCyclotomicField p)) (realCyclotomicField p)) T)),
      GroupScheme.PointedCurveJacobian (realCyclotomicField p)
        (Over.mk (scaledDoubleCoverToSpec
          ((localScaledRootPolynomial p (realPrimeAboveConductor p)).map
            (algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
              (realCyclotomicField p)) (realCyclotomicField p)))
          ((algebraMap ((realPrimeAboveConductor p).valuationSubringAtPrime
            (realCyclotomicField p)) (realCyclotomicField p)) T))) b
        (GroupScheme.fiber (realCyclotomicField p)
          (Hypergeometric.primePlusFamily p hp)
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ))
  jacobian_relative_dimension :
    SmoothOfRelativeDimension ((p - 1) / 2)
      (GroupScheme.fiber (realCyclotomicField p)
        (Hypergeometric.primePlusFamily p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).X.hom

/-- A scaled field parameter of positive local order constructs the actual
proper flat model and identifies its generic Jacobian with the selected plus
fibre. This deductive step uses no extra hypothesis about the integral total
space. -/
def PrimePlusScaledStableModelData.of_positiveValuation (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hval : (realPrimeAboveConductor p).valuation (realCyclotomicField p)
      (ξ.val / (2 - tau p 1) ^ p) < 1) :
    PrimePlusScaledStableModelData p hp ξ := by
  let a : realCyclotomicField p := ξ.val / (2 - tau p 1) ^ p
  let T := realLocalScaledParameter p a hval
  have ha0 : a ≠ 0 := div_ne_zero ξ.property.1
    (pow_ne_zero _ (realCyclotomicScale_ne_zero p))
  have hTne : T ≠ 0 := realLocalScaledParameter_ne_zero p a hval ha0
  have hTmax : T ∈ IsLocalRing.maximalIdeal
      ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) :=
    realLocalScaledParameter_mem_maximalIdeal p a hval
  have hTzero : realLocalReduction p T = 0 :=
    realLocalScaledParameter_residue_zero p a hval
  have hTfield : (algebraMap
      ((realPrimeAboveConductor p).valuationSubringAtPrime
        (realCyclotomicField p)) (realCyclotomicField p)) T = a :=
    realLocalScaledParameter_algebraMap p a hval
  exact ⟨T, hTfield, hTne, hTmax, hTzero,
    cyclotomicStableGeometry_of_five_le p hp T hTne hTzero,
    realLocalScaledDoubleCover_genericSmooth p hp T ξ hTfield,
    realLocalScaledDoubleCover_genericGeometricallyConnected p hp T ξ hTfield,
    realLocalScaledDoubleCover_genericJacobian p hp T ξ hTfield,
    primePlusSelectedJacobian_relativeDimension p hp ξ⟩

end HilbertModularity.Hyperelliptic
