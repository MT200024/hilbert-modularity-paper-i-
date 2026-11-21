/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusDeepCuspOrdinary
public import HilbertModularity.Hypergeometric.PrimeHypergeometricChecklist

/-! # The deep-cusp ordinary input for Skinner–Wiles

The local ordinary quotient comes from the same selected plus Jacobian as the
residual torsion and completed Tate determinant. A comparison with the global
representation and its chosen integral residual lattice is still explicit.
-/

public section
noncomputable section

open scoped NumberField Pointwise ValuativeRel TensorProduct
open ValuativeRel NumberField AlgebraicGeometry AlgebraicGeometry.GroupScheme
open IsDedekindDomain

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms
  IsNonarchimedeanLocalField

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower
  primePlusDecompositionRationalModule primePlusDecompositionScalarTower

local instance primePlusDeepCuspChecklistCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

local instance primePlusDeepCuspChecklistGalCompact
    (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- The remaining local comparisons for a chosen ordinary basis of the
selected plus Jacobian. The equivalence identifies the actual global action
with its local Tate action on the decomposition group, and the two residual
equalities use its specified integral lattice and character ordering. None of
these equalities follows from an abstract ordinary quotient. See
[TripathiGoswamiRevised, Proposition `SW-checklist`] and
[SkinnerWiles, §4.5, Theorem A]. -/
structure PrimePlusSkinnerWilesLocalComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] where
  decompositionMap : primeDecompositionGroup Q →*
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)
  continuous_decompositionMap : Continuous decompositionMap
  localEquiv : (Fin 2 → RealPrimePowerCompletion p 0) ≃ₗ[RealPrimePowerCompletion p 0]
    (Fin 2 → RealPrimePowerCompletion p 0)
  representation_intertwines : ∀ (g : primeDecompositionGroup Q)
      (v : Fin 2 → RealPrimePowerCompletion p 0),
    localEquiv (ρ (g : AbsoluteGalois (realCyclotomicField p)) v) =
      d.coordinateRepresentation p hp ξ (decompositionMap g) (localEquiv v)
  upper_residual_eq : ∀ g : primeDecompositionGroup Q,
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
      (integerCharacter (RealPrimePowerCompletion p 0)
        d.upperCharacter d.upper_continuous)) (decompositionMap g) =
      D.chi₁ (g : AbsoluteGalois (realCyclotomicField p))
  lower_residual_eq : ∀ g : primeDecompositionGroup Q,
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
      (Representation.determinantCharacter d.lattice.toRepresentation))
        (decompositionMap g) =
      D.chi₂ (g : AbsoluteGalois (realCyclotomicField p))
  inertia_map : ∀ g : primeDecompositionGroup Q,
    (g : AbsoluteGalois (realCyclotomicField p)) ∈
      Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
    decompositionMap g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)

/-- The selected ordinary basis and its explicit arithmetic comparison give
the local lifting-theorem hypothesis. The upper-triangular form and finite
normalized inertia are deduced from the selected Jacobian's quotient. -/
noncomputable def PrimePlusSkinnerWilesLocalComparison.ordinaryAt
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (C : PrimePlusSkinnerWilesLocalComparison p hp ξ m hm d ρ D Q) :
    SkinnerWilesOrdinaryAt p ρ D Q :=
  d.skinnerWilesOrdinaryAt_of_equiv p hp ξ m hm ρ D Q C.decompositionMap
    C.continuous_decompositionMap C.localEquiv C.representation_intertwines
    C.upper_residual_eq C.lower_residual_eq C.inertia_map

/-- A chosen weight-zero quotient of the selected plus Jacobian supplies its
normalized ordinary basis. Its existence is the explicit `DO` hypothesis in
[TripathiGoswamiRevised, Definition `DO`]; no geometric existence is
asserted here. -/
noncomputable def primePlusNormalizedOrdinaryData_of_ordinaryQuotient
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    PrimePlusNormalizedOrdinaryData p hp ξ m hm :=
  Classical.choice (W.exists_normalizedOrdinaryData p hp ξ m hm)

/-- The manuscript's `DO` hypothesis on the actual selected RM Tate factor
gives the local Skinner–Wiles condition once the decomposition action and
residual characters are compared on the chosen integral lattice. See
[TripathiGoswamiRevised, Lemma `primeordinary`] and
[SkinnerWiles, §4.5, Theorem A]. -/
noncomputable def skinnerWilesOrdinaryAt_of_primePlusOrdinaryQuotient
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (C : PrimePlusSkinnerWilesLocalComparison p hp ξ m hm
      (primePlusNormalizedOrdinaryData_of_ordinaryQuotient p hp ξ m hm W)
      ρ D Q) :
    SkinnerWilesOrdinaryAt p ρ D Q :=
  C.ordinaryAt p hp ξ m hm
    (primePlusNormalizedOrdinaryData_of_ordinaryQuotient p hp ξ m hm W)
    ρ D Q

/-- At either rational cubic deep cusp, the graph-period and complementary
involution inputs produce the *same selected Jacobian's* normalized ordinary
basis. Its global/local and residual-lattice comparisons then imply the local
Skinner–Wiles condition. This is the local deduction in
[TripathiGoswami, Proposition `prime-deep-DO` and Theorem `prime`]. -/
noncomputable def skinnerWilesOrdinaryAt_of_primePlusDeepCusp
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (e : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp (darmonRationalParameter p ξ)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (C : PrimePlusSkinnerWilesLocalComparison p hp
      (darmonRationalParameter p ξ) m hm
      (primePlusNormalizedOrdinaryData_of_deep_cusp p hp ξ
        hξ hA hB hAB hgraph χ hχ horder e hdeep m hm) ρ D Q) :
    SkinnerWilesOrdinaryAt p ρ D Q :=
  C.ordinaryAt p hp (darmonRationalParameter p ξ) m hm
    (primePlusNormalizedOrdinaryData_of_deep_cusp p hp ξ
      hξ hA hB hAB hgraph χ hχ horder e hdeep m hm) ρ D Q

/-- At a rational cubic deep cusp, the selected plus Jacobian supplies every
local ordinary input in the weight-two Skinner–Wiles checklist. The comparison
at each prime uses the same chosen integral residual lattice as the global
representation. The graph-period and complementary-cusp data construct the
ordinary basis; the local comparison structure only identifies its arithmetic
action, residual characters, and inertia. See
[TripathiGoswamiRevised, Proposition `SW-checklist`] and
[SkinnerWiles, §4.5, Theorem A]. -/
noncomputable def skinnerWilesWeightTwoInput_of_primePlusDeepCusp
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hgraph : ∀ η : ProjectiveLine.Parameter ℚ,
      (realPrimeAboveConductor p).valuation (realCyclotomicField p)
        (((darmonRationalParameter p η).val : realCyclotomicField p) /
          (2 - tau p 1) ^ p) < 1 →
        Nonempty (PrimePlusGraphPeriodData p hp (darmonRationalParameter p η)))
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ) (hχ : Continuous χ)
    (horder : IsOfFinOrder χ)
    (eComplement : (((Representation.ofCharacter χ).tprod
      (primePlusDecompositionRepresentation p hp
        (ProjectiveLine.complementParameter (realCyclotomicField p)
          (darmonRationalParameter p ξ))).ρ).Equiv
      (primePlusDecompositionRepresentation p hp (darmonRationalParameter p ξ)).ρ))
    (hdeep : (p : ℤ) ^ 3 ∣ A ∨ (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    [NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p 0)]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (eTate : letI := primePlusIntegralTateModule p hp (darmonRationalParameter p ξ)
      ρ.Equiv ((primePlusIntegralTateRepresentation p hp
        (darmonRationalParameter p ξ)).baseChange (RealPrimePowerCompletion p 0)))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp (darmonRationalParameter p ξ)
      LinearMap.det ((primePlusIntegralTateRepresentation p hp
        (darmonRationalParameter p ξ)).baseChange (RealPrimePowerCompletion p 0) g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        (@algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) _ _
          (NormedAlgebra.toAlgebra)) (z : ℚ_[p]))
    (hreal : NumberField.IsTotallyReal (realCyclotomicField p))
    (hcontinuous : ∀ i j : Fin 2,
      Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        ρ g (Pi.single j 1) i))
    (hirred : (Representation.baseChange
      (AlgebraicClosure (RealPrimePowerCompletion p 0)) ρ).IsIrreducible)
    (ramified : Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))))
    (hramified : ramified.Finite)
    (hunramified : ∀ q, q ∉ ramified →
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        g ∈ Q.inertia (AbsoluteGalois (realCyclotomicField p)) → ρ g = 1)
    (D : SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]))
    (hres : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp (darmonRationalParameter p ξ)
      letI := (AdicCompletion.evalOneₐ
        (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
      (LinearMap.toMatrix (primePlusResidualTateBasis p hp (darmonRationalParameter p ξ))
        (primePlusResidualTateBasis p hp (darmonRationalParameter p ξ))
        ((primePlusIntegralTateRepresentation p hp (darmonRationalParameter p ξ)).baseChange
          (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) g)).map
            κ.toRingHom =
        (LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[RealPrimePowerCompletion p 0])))
    (hlocal : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      PrimePlusSkinnerWilesLocalComparison p hp
        (darmonRationalParameter p ξ) m hm
        (primePlusNormalizedOrdinaryData_of_deep_cusp p hp ξ
          hξ hA hB hAB hgraph χ hχ horder eComplement hdeep m hm) ρ D Q) :
    letI : Algebra ℚ_[p] (RealPrimePowerCompletion p 0) :=
      (inferInstance : NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
    SkinnerWilesWeightTwoInput p ρ (cyclotomicField p) := by
  letI : Algebra ℚ_[p] (RealPrimePowerCompletion p 0) :=
    (inferInstance : NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
  refine skinnerWilesWeightTwoInput_of_primePlusTateEquiv p hp
    (darmonRationalParameter p ξ) (RealPrimePowerCompletion p 0) ρ eTate
    hTateDet hcoeff hreal hcontinuous hirred ramified hramified hunramified
    D κ hres ?_
  intro P _ hpP Q _ _
  exact skinnerWilesOrdinaryAt_of_primePlusDeepCusp p hp ξ
    hξ hA hB hAB hgraph χ hχ horder eComplement hdeep m hm ρ D Q
    (hlocal P hpP Q)

/-- Under the manuscript's explicit `DO` hypothesis, the selected plus
Jacobian supplies the ordinary row of the complete weight-two Skinner–Wiles
checklist. The remaining same-lattice global, residual, and local comparisons
are kept visible. See [TripathiGoswamiRevised, Proposition `SW-checklist`]
and [SkinnerWiles, §4.5, Theorem A]. -/
noncomputable def skinnerWilesWeightTwoInput_of_primePlusOrdinaryQuotient
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm)
    [NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p 0)]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (eTate : letI := primePlusIntegralTateModule p hp ξ
      ρ.Equiv ((primePlusIntegralTateRepresentation p hp
        ξ).baseChange (RealPrimePowerCompletion p 0)))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp
        ξ).baseChange (RealPrimePowerCompletion p 0) g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        (@algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) _ _
          (NormedAlgebra.toAlgebra)) (z : ℚ_[p]))
    (hreal : NumberField.IsTotallyReal (realCyclotomicField p))
    (hcontinuous : ∀ i j : Fin 2,
      Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        ρ g (Pi.single j 1) i))
    (hirred : (Representation.baseChange
      (AlgebraicClosure (RealPrimePowerCompletion p 0)) ρ).IsIrreducible)
    (ramified : Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))))
    (hramified : ramified.Finite)
    (hunramified : ∀ q, q ∉ ramified →
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        g ∈ Q.inertia (AbsoluteGalois (realCyclotomicField p)) → ρ g = 1)
    (D : SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]))
    (hres : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      letI := (AdicCompletion.evalOneₐ
        (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
      (LinearMap.toMatrix (primePlusResidualTateBasis p hp ξ)
        (primePlusResidualTateBasis p hp ξ)
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) g)).map
            κ.toRingHom =
        (LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[RealPrimePowerCompletion p 0])))
    (hlocal : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      PrimePlusSkinnerWilesLocalComparison p hp
        ξ m hm
        (primePlusNormalizedOrdinaryData_of_ordinaryQuotient p hp ξ m hm W) ρ D Q) :
    letI : Algebra ℚ_[p] (RealPrimePowerCompletion p 0) :=
      (inferInstance : NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
    SkinnerWilesWeightTwoInput p ρ (cyclotomicField p) := by
  letI : Algebra ℚ_[p] (RealPrimePowerCompletion p 0) :=
    (inferInstance : NormedAlgebra ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
  refine skinnerWilesWeightTwoInput_of_primePlusTateEquiv p hp
    ξ (RealPrimePowerCompletion p 0) ρ eTate
    hTateDet hcoeff hreal hcontinuous hirred ramified hramified hunramified
    D κ hres ?_
  intro P _ hpP Q _ _
  exact skinnerWilesOrdinaryAt_of_primePlusOrdinaryQuotient p hp ξ m hm W
    ρ D Q (hlocal P hpP Q)

end HilbertModularity.Hypergeometric
