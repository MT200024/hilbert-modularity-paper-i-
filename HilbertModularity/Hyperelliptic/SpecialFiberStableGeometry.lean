/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberProper
public import HilbertModularity.Hyperelliptic.SpecialFiberGluedFibre
public import HilbertModularity.Hyperelliptic.SpecialFiberConnected
public import HilbertModularity.Hyperelliptic.SpecialFiberReduced
public import HilbertModularity.Hyperelliptic.SpecialFiberComponentTopology
public import HilbertModularity.Hyperelliptic.SpecialFiberNormalizationMap
public import HilbertModularity.Hyperelliptic.SpecialFiberGeometricIntersections
public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingDecomposition
public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingStalk
public import HilbertModularity.Hyperelliptic.SpecialFiberAwaySmooth
public import HilbertModularity.Hyperelliptic.SpecialFiberPrimeStrata
public import HilbertModularity.Hyperelliptic.SpecialFiberEtaleCoordinate
public import HilbertModularity.Hyperelliptic.SpecialFiberFamilyNodeApplication

/-! # Stable reduction geometry of the scaled cyclotomic cover

This file collects properties of the **same** projective scaled double cover.
Its special fibre has two embedded projective lines and a reduced intersection
scheme, and each crossing has the explicit split-node local algebra. The
relative coordinates retain the different smoothing thicknesses at zero and
at nonzero branch points. The interpretation as a nodal stable curve uses the
standard criteria of [src_stacks_nodal_stable_criteria], Lemmas 53.19.7 (Tag 0C4D) and
53.20.1 (Tag 0C59), and Definition 109.22.2 (Tag 0E75).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open scoped NumberField

namespace HilbertModularity.Hyperelliptic

/-- The exact degree of the scaled root polynomial is the genus index
`d = (p-1)/2` appearing in the projective branch section. -/
theorem localCyclotomicScaledRootPolynomial_natDegree (p : ℕ) [Fact p.Prime] :
    (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).natDegree = (p - 1) / 2 := by
  rw [localScaledRootPolynomial, Polynomial.natDegree_prod]
  · simp
  · intro j hj
    exact (monic_X_sub_C _).ne_zero

private theorem two_ne_zero_of_fieldHom {k K : Type*} [Field k] [Field K]
    (f : k →+* K) (h2 : (2 : k) ≠ 0) : (2 : K) ≠ 0 := by
  have hmap : f (2 : k) ≠ f 0 := f.injective.ne h2
  simpa only [map_ofNat, map_zero] using hmap

/-- At the manuscript's prime levels, two is invertible in the residue
field; this does not need an additional reduction hypothesis. -/
theorem two_ne_zero_in_residueField (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  change ¬ (((2 : ℕ) : ZMod p) = 0)
  rw [ZMod.natCast_eq_zero_iff]
  intro hdiv
  have hle := Nat.le_of_dvd (by omega : 0 < 2) hdiv
  omega

/-- The concrete hypotheses for the split, stable special fibre of the
projective cyclotomic double cover. The local-node field gives the actual
stalk presentation, not merely a count of points. -/
structure CyclotomicStableGeometry (p : ℕ) [Fact p.Prime]
    (T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)) : Prop where
  parameter_nonzero : T ≠ 0
  parameter_residue_zero : Cyclotomic.realLocalReduction p T = 0
  proper : IsProper (scaledDoubleCoverToSpec
    (localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)) T)
  flat : Flat (scaledDoubleCoverToSpec
    (localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)) T)
  special_fibre_reduced : IsReduced (scaledDoubleCover
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)) 0)
  special_fibre_connected : _root_.IsConnected (Set.univ : Set (scaledDoubleCover
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)) 0))
  geometric_reduced : ∀ {K : Type*} [Field K] (f : ZMod p →+* K),
    IsReduced (scaledDoubleCover
      (((localScaledRootPolynomial p
        (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)).map f) 0)
  geometric_connected : ∀ {K : Type*} [Field K] (f : ZMod p →+* K),
    _root_.IsConnected (Set.univ : Set (scaledDoubleCover
      (((localScaledRootPolynomial p
        (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)).map f) 0))
  components : irreducibleComponents (scaledDoubleCover
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)) 0) =
      {Set.range ⇑(positiveGlobalComponent
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p))),
       Set.range ⇑(negativeGlobalComponent
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)))}
  geometric_components : ∀ {K : Type*} [Field K] (f : ZMod p →+* K),
    let Q := ((localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)).map f
    irreducibleComponents (scaledDoubleCover Q 0) =
      {Set.range ⇑(positiveGlobalComponent Q),
       Set.range ⇑(negativeGlobalComponent Q)}
  component_map_finite : IsFinite (specialFiberComponentCoproductMap
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)))
  component_map_surjective : Surjective (specialFiberComponentCoproductMap
    ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)))
  intersection :
    Set.range ⇑(positiveGlobalComponent
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))) ∩
    Set.range ⇑(negativeGlobalComponent
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))) =
      ↑(globalComponentIntersectionPoints
        ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)) (residueRootSet p))
  node_count :
    (globalComponentIntersectionPoints
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)) (residueRootSet p)).card =
      (p - 1) / 2 + 1
  branch_degree :
    (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).natDegree = (p - 1) / 2
  geometric_intersection_count : ∀ {K : Type*} [Field K] [DecidableEq K]
    (f : ZMod p →+* K),
    (globalComponentIntersectionPoints
      (((localScaledRootPolynomial p
          (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)).map f)
      ((residueRootSet p).image f)).card = (p - 1) / 2 + 1
  geometric_intersection : ∀ {K : Type*} [Field K] [DecidableEq K]
    (f : ZMod p →+* K),
    let Q := ((localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)).map f
    Set.range ⇑(positiveGlobalComponent Q) ∩
      Set.range ⇑(negativeGlobalComponent Q) =
        ↑(globalComponentIntersectionPoints Q ((residueRootSet p).image f))
  geometric_crossings_simple : ∀ {K : Type*} [Field K] [DecidableEq K]
    (f : ZMod p →+* K) (x : K),
    let Q := ((localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)).map f
    (finiteComponentPolynomial Q).eval x = 0 →
      (finiteComponentPolynomial Q).derivative.eval x ≠ 0
  at_least_three_nodes : 3 ≤ (p - 1) / 2 + 1
  crossing_scheme_reduced : IsReduced (componentIntersectionRing
    (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))))
  finite_chart_smooth_away :
    let Q := (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)
    let A := Localization.Away (finiteComponentPolynomial Q)
    Algebra.Smooth (ZMod p)
      (QuadraticAlgebra A
        (algebraMap (ZMod p)[X] A (finiteBranchPolynomial Q 0)) 0)
  infinity_chart_smooth_away :
    let Q := (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)
    let A := Localization.Away (infinityComponentPolynomial Q)
    Algebra.Smooth (ZMod p)
      (QuadraticAlgebra A
        (algebraMap (ZMod p)[X] A (infinityBranchPolynomial Q 0)) 0)
  every_crossing_simple : ∀ x : ZMod p,
    (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0 →
    (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).derivative.eval x ≠ 0
  crossing_stalk_node : ∀ (x : ZMod p)
    (_hx : (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0),
    letI : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    Nonempty (QuadraticAlgebra S
      (algebraMap (ZMod p)[X] S
        (finiteBranchPolynomial
          ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
            (Cyclotomic.realLocalReduction p)) 0))
      (algebraMap (ZMod p)[X] S 0) ≃ₐ[S]
        QuadraticAlgebra S 0 (2 * algebraMap (ZMod p)[X] S (X - C x)))
  zero_family_coordinate :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let H : R[X] := X * P ^ 2
    letI : Algebra R[X] R[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt R[X]
      (residuePointPrime (Cyclotomic.realLocalReduction p) (0 : ZMod p))
  zero_branch_unit :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let 𝔭 := residuePointPrime (Cyclotomic.realLocalReduction p) (0 : ZMod p)
    letI : 𝔭.IsPrime := residuePointPrime_isPrime _ _
    IsUnit (algebraMap R[X] (Localization.AtPrime 𝔭) P)
  nonzero_family_coordinate : ∀ x : ZMod p,
    (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p))).eval x = 0 →
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    let H : R[X] := X * P
    letI : Algebra R[X] R[X] := (aeval H).toRingHom.toAlgebra
    Algebra.IsEtaleAt R[X]
      (residuePointPrime (Cyclotomic.realLocalReduction p) x)
  nonzero_base_unit : ∀ x ∈ residueRootSet p,
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let 𝔭 := residuePointPrime (Cyclotomic.realLocalReduction p) x
    letI : 𝔭.IsPrime := residuePointPrime_isPrime _ _
    IsUnit (algebraMap R[X] (Localization.AtPrime 𝔭) X)
  nonzero_family_smoothing :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    finiteFamilyNodeMinus P T * finiteFamilyNodePlus P T =
      algebraMap R[X] (QuadraticAlgebra R[X] (finiteBranchPolynomial P T) 0)
        (-(4 * C T * X))
  zero_family_smoothing :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    familyZeroNodeMinus P X (C T) * familyZeroNodePlus P X (C T) =
      algebraMap R[X]
        (QuadraticAlgebra R[X] ((X * P) ^ 2 - 4 * C T * X) 0)
        (-(4 * (C T) ^ 2))

/-- The actual scaled family satisfies the two-projective-line criterion for
stable reduction. `T ≠ 0` and its vanishing in the residue field are kept
separate. The latter expresses membership in the maximal ideal; smoothness
of the generic fibre is a separate hypothesis of the stable-model theorem. -/
theorem cyclotomicStableGeometry (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (h2 : (2 : ZMod p) ≠ 0)
    (T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p))
    (hTne : T ≠ 0) (hTzero : Cyclotomic.realLocalReduction p T = 0) :
    CyclotomicStableGeometry p T := by
  let P := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
  let Q := P.map (Cyclotomic.realLocalReduction p)
  have hP : P.Monic := localScaledRootPolynomial_monic p _
  have hQ : Q.Monic := hP.map (Cyclotomic.realLocalReduction p)
  have hsplit : Q = ∏ x ∈ residueRootSet p, (X - C x) :=
    localScaledRootPolynomial_reduction_split p
  constructor
  · exact hTne
  · exact hTzero
  · infer_instance
  · infer_instance
  · exact scaledDoubleCover_zero_isReduced Q hQ h2
  · exact scaledDoubleCover_zero_isConnected Q hQ h2
  · intro K _ f
    exact scaledDoubleCover_zero_isReduced (Q.map f) (hQ.map f)
      (two_ne_zero_of_fieldHom f h2)
  · intro K _ f
    exact scaledDoubleCover_zero_isConnected (Q.map f) (hQ.map f)
      (two_ne_zero_of_fieldHom f h2)
  · exact specialFiber_irreducibleComponents_eq_pair Q hQ h2
  · intro K _ f
    exact specialFiber_irreducibleComponents_eq_pair (Q.map f) (hQ.map f)
      (two_ne_zero_of_fieldHom f h2)
  · infer_instance
  · exact specialFiberComponentCoproductMap_isSurjective Q hQ h2
  · exact globalComponent_intersection_eq_points Q (residueRootSet p) hQ h2 hsplit
  · exact reducedLocal_globalComponentIntersectionPoints_card p (by omega)
  · exact localCyclotomicScaledRootPolynomial_natDegree p
  · intro K _ _ f
    rw [geometricComponent_intersections_card f Q (residueRootSet p)
      (zero_not_mem_residueRootSet p), residueRootSet_card p (by omega)]
  · intro K _ _ f
    exact geometricComponent_intersection_eq_points f Q (residueRootSet p)
      hQ (two_ne_zero_of_fieldHom f h2) hsplit
  · intro K _ _ f x
    dsimp only
    intro hx
    exact finiteComponentPolynomial_simple_roots (Q.map f)
      ((residueRootSet p).image f)
      (splitPolynomial_map f Q (residueRootSet p) hsplit)
      (zero_not_mem_image f (residueRootSet p)
        (zero_not_mem_residueRootSet p)) hx
  · omega
  · exact reducedLocalFiniteComponentIntersection_isReduced p
  · exact smooth_finiteSpecialFiberAway Q h2
  · exact smooth_infinitySpecialFiberAway Q h2
  · intro x hx
    exact reducedLocalFiniteComponent_simple_roots p hx
  · intro x hx
    exact ⟨reducedLocalFiniteCrossing_localNodeEquiv p hx _⟩
  · exact localZeroNodePolynomial_isEtaleCoordinateOnFamily p
  · exact localScaledRootPolynomial_isUnit_atZeroNode p
  · intro x hx
    exact localFiniteComponent_isEtaleCoordinateOnFamily p hx
  · intro x hx
    have hxn : x ≠ 0 := by
      intro h
      exact zero_not_mem_residueRootSet p (h ▸ hx)
    exact residuePointPrime_X_isUnit_of_ne_zero
      (Cyclotomic.realLocalReduction p) x hxn
  · exact finiteFamilyNodeMinus_mul_plus P T
  · exact finiteFamilyZeroNode_product P T

/-- The stable-reduction geometry has exactly the manuscript's prime and
parameter hypotheses: `p ≥ 5`, `T ≠ 0`, and vanishing of `T` in the residue
field. In particular the characteristic-two exclusion is deduced from `p ≥ 5`. -/
theorem cyclotomicStableGeometry_of_five_le (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p))
    (hTne : T ≠ 0) (hTzero : Cyclotomic.realLocalReduction p T = 0) :
    CyclotomicStableGeometry p T :=
  cyclotomicStableGeometry p hp (two_ne_zero_in_residueField p hp) T hTne hTzero

/-- Every prime of the actual finite special-fibre chart is either one of
the listed rational crossings or lies on its smooth away-from-branch open.
This is the pointwise exhaustion needed before applying the local node
criterion; it makes no regularity claim about the integral total space. -/
theorem cyclotomicFiniteSpecialFibre_prime_strata (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (q : Ideal (DoubleCover.ChartRing (finiteBranchPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)) 0)))
    (hq : q.IsPrime) :
    let Q := (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)
    (∃ x ∈ insert 0 (residueRootSet p),
      q = RingHom.ker (finiteCrossingEvaluation Q x).toRingHom) ∨
    (algebraMap (ZMod p)[X] _ (finiteComponentPolynomial Q) ∉ q ∧
      ((QuadraticAlgebra.omega -
          algebraMap (ZMod p)[X] _ (finiteComponentPolynomial Q)) ∈ q ↔
        (QuadraticAlgebra.omega +
          algebraMap (ZMod p)[X] _ (finiteComponentPolynomial Q)) ∉ q)) := by
  exact finiteSpecialFiber_prime_strata _ (residueRootSet p)
    (localScaledRootPolynomial_reduction_split p)
      (two_ne_zero_in_residueField p hp) q hq

/-- On the reciprocal chart, every prime above the infinity point lies
away from its branch polynomial, so the smooth-away theorem covers it. -/
theorem cyclotomicInfinitySpecialFibre_isAway (p : ℕ) [Fact p.Prime]
    (q : Ideal (DoubleCover.ChartRing (infinityBranchPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)) 0)))
    (hq : q.IsPrime)
    (hX : algebraMap (ZMod p)[X] _ X ∈ q) :
    let Q := (localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)
    algebraMap (ZMod p)[X] _ (infinityComponentPolynomial Q) ∉ q := by
  let P := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
  have hQ : (P.map (Cyclotomic.realLocalReduction p)).Monic :=
    (localScaledRootPolynomial_monic p _).map _
  exact infinitySpecialFiber_prime_over_zero_isAway _ hQ q hq hX

/-- Every crossing remains a split node after a field extension of the
residue field. The displayed algebra is the localization of the actual
quadratic chart at the crossing prime, by
`finiteCrossing_stalk_isLocalization_atPrime`. The standard interpretation
as an ordinary node is [Stacks Project, Tag 0C4D, Lemma 53.19.7]. -/
theorem CyclotomicStableGeometry.geometric_crossing_stalk_node
    {p : ℕ} [Fact p.Prime]
    {T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)}
    (_h : CyclotomicStableGeometry p T)
    {K : Type*} [Field K] [DecidableEq K] (f : ZMod p →+* K) (x : K)
    (hx : (finiteComponentPolynomial
      (((localScaledRootPolynomial p
        (Cyclotomic.realPrimeAboveConductor p)).map
          (Cyclotomic.realLocalReduction p)).map f)).eval x = 0) :
    let Q := ((localScaledRootPolynomial p
      (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)).map f
    letI : (RingHom.ker (evalRingHom x)).IsPrime := RingHom.ker_isPrime _
    let S := Localization.AtPrime (RingHom.ker (evalRingHom x))
    Nonempty (QuadraticAlgebra S
      (algebraMap K[X] S (finiteBranchPolynomial Q 0))
      (algebraMap K[X] S 0) ≃ₐ[S]
        QuadraticAlgebra S 0 (2 * algebraMap K[X] S (X - C x))) := by
  let Q := ((localScaledRootPolynomial p
    (Cyclotomic.realPrimeAboveConductor p)).map
      (Cyclotomic.realLocalReduction p)).map f
  have hsplit : Q = ∏ y ∈ (residueRootSet p).image f, (X - C y) :=
    splitPolynomial_map f _ (residueRootSet p)
      (localScaledRootPolynomial_reduction_split p)
  have hs : (finiteComponentPolynomial Q).derivative.eval x ≠ 0 :=
    finiteComponentPolynomial_simple_roots Q ((residueRootSet p).image f)
      hsplit (zero_not_mem_image f (residueRootSet p)
        (zero_not_mem_residueRootSet p)) hx
  exact ⟨finiteCrossing_stalkNodeEquiv Q x hx hs⟩

/-- The displayed square-branch curve is the **scheme-theoretic special
fibre of this same proper flat family**, not a separately chosen nodal curve.
The parameter hypothesis is precisely its vanishing in the residue field. -/
theorem cyclotomicStableGeometry_specialFibre_isPullback (p : ℕ) [Fact p.Prime]
    (T : (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p))
    (hTzero : Cyclotomic.realLocalReduction p T = 0) :
    let R := (Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
      (Cyclotomic.realCyclotomicField p)
    let P : R[X] := localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)
    letI : Algebra R (ZMod p) := (Cyclotomic.realLocalReduction p).toAlgebra
    IsPullback
      (scaledDoubleCoverSpecializationMap (algebraMap R (ZMod p)) P T
        hTzero (localScaledRootPolynomial_monic p _))
      (scaledDoubleCoverToSpec (P.map (Cyclotomic.realLocalReduction p)) 0)
      (scaledDoubleCoverToSpec P T)
      (Spec.map (CommRingCat.ofHom (Cyclotomic.realLocalReduction p))) := by
  let : Algebra
      ((Cyclotomic.realPrimeAboveConductor p).valuationSubringAtPrime
        (Cyclotomic.realCyclotomicField p)) (ZMod p) :=
    (Cyclotomic.realLocalReduction p).toAlgebra
  exact scaledDoubleCoverSpecialization_toSpec_isPullback
    (localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)) T
      hTzero (localScaledRootPolynomial_monic p _)

end HilbertModularity.Hyperelliptic
