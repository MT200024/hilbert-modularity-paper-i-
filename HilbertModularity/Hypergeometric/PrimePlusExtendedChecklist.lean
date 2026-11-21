/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesInput
public import HilbertModularity.RepresentationTheory.CoefficientMap
public import HilbertModularity.NumberTheory.LocalFieldMorphisms
public import HilbertModularity.NumberTheory.CyclotomicLocalResidue
public import HilbertModularity.Hypergeometric.PrimePlusSelectedChecklist
public import HilbertModularity.NumberTheory.AdicCompletionIntegersComparison

/-! # Residual data under a genuine local coefficient extension

The cyclotomic coefficient completion is a finite extension of the native
real completion. It is not the fraction field of the real completed integer
ring. Residual characters and their ratio instead move through the actual
integer and residue maps of the field extension.
-/

public noncomputable section

open IsDedekindDomain
open scoped ValuativeRel

namespace Representation

variable {R S G : Type*} [CommRing R] [CommRing S] [Monoid G]

/-- Mapping a coordinate representation through a commutative ring map
maps its trace through the same map. -/
theorem trace_mapCoefficients_commRing (f : R →+* S)
    (ρ : Representation R G (Fin 2 → R)) (g : G) :
    LinearMap.trace S (Fin 2 → S) (ρ.mapCoefficients f g) =
      f (LinearMap.trace R (Fin 2 → R) (ρ g)) := by
  rw [LinearMap.trace_eq_matrix_trace S (Pi.basisFun S (Fin 2)),
    LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin 2))]
  change Matrix.trace (LinearMap.toMatrixAlgEquiv' (ρ.mapCoefficients f g)) =
    f (Matrix.trace (LinearMap.toMatrixAlgEquiv' (ρ g)))
  rw [toMatrix_mapCoefficients]
  exact (AddMonoidHom.map_trace f _).symm

/-- Mapping a coordinate representation through a commutative ring map
maps its determinant through the same map. -/
theorem det_mapCoefficients_commRing (f : R →+* S)
    (ρ : Representation R G (Fin 2 → R)) (g : G) :
    LinearMap.det (ρ.mapCoefficients f g) = f (LinearMap.det (ρ g)) := by
  rw [← LinearMap.det_toMatrix' (ρ.mapCoefficients f g),
    ← LinearMap.det_toMatrix' (ρ g)]
  change (LinearMap.toMatrixAlgEquiv' (ρ.mapCoefficients f g)).det =
    f ((LinearMap.toMatrixAlgEquiv' (ρ g)).det)
  rw [toMatrix_mapCoefficients]
  exact (f.map_det _).symm

end Representation

namespace HilbertModularity.Hypergeometric

open HilbertModularity.HilbertModularForms
open scoped NumberField

variable {F K L : Type*} [Field F] [NumberField F]
  [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]

/-- Integral and residue maps for an actual finite local coefficient
extension. The compatibility equations retain the chosen residue map,
including the uniformizer normalization needed by the residual characters. -/
structure LocalIntegerResidueComparison (f : K →+* L) where
  integerMap : 𝒪[K] →+* 𝒪[L]
  residueMap : (𝒪[K] ⧸ 𝓂[K]) →+* (𝒪[L] ⧸ 𝓂[L])
  coe_integerMap : ∀ a : 𝒪[K], (integerMap a : L) = f (a : K)
  residueMap_mk : ∀ a : 𝒪[K],
    residueMap (Ideal.Quotient.mk (𝓂[K]) a) =
      Ideal.Quotient.mk (𝓂[L]) (integerMap a)
  residue_injective : Function.Injective residueMap

/-- Transport an integral rank-two residual decomposition along the actual
field, integer-ring and residue maps. No identification of the larger field
with the fraction field of the smaller integer ring is used. -/
def SkinnerWilesResidualData.mapLocalCoefficients
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (f : K →+* L) (C : LocalIntegerResidueComparison f) :
    SkinnerWilesResidualData (ρ.mapCoefficients f) where
  integralAction := D.integralAction.mapCoefficients C.integerMap
  integral_spec := by
    intro g i j
    rw [Representation.mapCoefficients_apply_single,
      Representation.mapCoefficients_apply_single, C.coe_integerMap,
      D.integral_spec]
  chi₁ := (Units.map C.residueMap.toMonoidHom).comp D.chi₁
  chi₂ := (Units.map C.residueMap.toMonoidHom).comp D.chi₂
  residual_trace := by
    intro g
    rw [Representation.trace_mapCoefficients_commRing]
    calc
      Ideal.Quotient.mk (𝓂[L])
          (C.integerMap (LinearMap.trace (𝒪[K]) (Fin 2 → 𝒪[K])
            (D.integralAction g))) =
          C.residueMap (Ideal.Quotient.mk (𝓂[K])
            (LinearMap.trace (𝒪[K]) (Fin 2 → 𝒪[K])
              (D.integralAction g))) := (C.residueMap_mk _).symm
      _ = C.residueMap ((D.chi₁ g : 𝒪[K] ⧸ 𝓂[K]) +
          (D.chi₂ g : 𝒪[K] ⧸ 𝓂[K])) := by rw [D.residual_trace]
      _ = _ := by simp [map_add]
  residual_det := by
    intro g
    rw [Representation.det_mapCoefficients_commRing]
    calc
      Ideal.Quotient.mk (𝓂[L])
          (C.integerMap (LinearMap.det (D.integralAction g))) =
          C.residueMap (Ideal.Quotient.mk (𝓂[K])
            (LinearMap.det (D.integralAction g))) := (C.residueMap_mk _).symm
      _ = C.residueMap ((D.chi₁ g : 𝒪[K] ⧸ 𝓂[K]) *
          (D.chi₂ g : 𝒪[K] ⧸ 𝓂[K])) := by rw [D.residual_det]
      _ = _ := by simp [map_mul]

omit [NumberField F] in
/-- The upper residual character uses the specified residue-field map. -/
theorem SkinnerWilesResidualData.mapLocalCoefficients_chi₁
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (f : K →+* L) (C : LocalIntegerResidueComparison f) :
    (SkinnerWilesResidualData.mapLocalCoefficients D f C).chi₁ =
      (Units.map C.residueMap.toMonoidHom).comp D.chi₁ := (rfl)

omit [NumberField F] in
/-- The lower residual character uses the same specified residue-field map. -/
theorem SkinnerWilesResidualData.mapLocalCoefficients_chi₂
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (f : K →+* L) (C : LocalIntegerResidueComparison f) :
    (SkinnerWilesResidualData.mapLocalCoefficients D f C).chi₂ =
      (Units.map C.residueMap.toMonoidHom).comp D.chi₂ := (rfl)

omit [NumberField F] in
/-- The residual ratio is mapped through the same actual residue field map. -/
theorem SkinnerWilesResidualData.residualRatio_mapLocalCoefficients
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (f : K →+* L) (C : LocalIntegerResidueComparison f)
    (g : AbsoluteGalois F) :
    residualRatio (SkinnerWilesResidualData.mapLocalCoefficients D f C) g =
      Units.map C.residueMap.toMonoidHom (residualRatio D g) := by
  apply Units.ext
  rw [HilbertModularForms.residualRatio_apply,
    HilbertModularForms.residualRatio_apply]
  simp [SkinnerWilesResidualData.mapLocalCoefficients, map_mul, map_inv]

omit [NumberField F] in
/-- Transporting an integral model along equality of its field action does
not change the residual character ratio. -/
theorem SkinnerWilesResidualData.residualRatio_transportAction
    {ρ σ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ) (h : ρ = σ) :
    residualRatio (h ▸ D) = residualRatio D := by
  cases h
  rfl

/-- The induced map on residue units remains injective when the residue map
is injective. -/
theorem LocalIntegerResidueComparison.unitsMap_injective
    (f : K →+* L) (C : LocalIntegerResidueComparison f) :
    Function.Injective (Units.map C.residueMap.toMonoidHom) := by
  intro a b hab
  apply Units.ext
  apply C.residue_injective
  simpa using congrArg
    (fun u : (𝒪[L] ⧸ 𝓂[L])ˣ => (u : 𝒪[L] ⧸ 𝓂[L])) hab

/-- The same finite extension cuts out the residual ratio after a local
coefficient enlargement with injective residue map. -/
def SkinnerWilesRatioField.mapLocalCoefficients
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (M : Type*) [Field M] [NumberField M] [Algebra F M]
    (H : SkinnerWilesRatioField D M)
    (f : K →+* L) (C : LocalIntegerResidueComparison f) :
    SkinnerWilesRatioField (SkinnerWilesResidualData.mapLocalCoefficients D f C) M where
  embedding := H.embedding
  galois_over_rat := H.galois_over_rat
  abelian_over_rat := H.abelian_over_rat
  cuts_out_ratio := by
    intro g
    rw [SkinnerWilesResidualData.residualRatio_mapLocalCoefficients D f C g]
    have heq : Units.map C.residueMap.toMonoidHom (residualRatio D g) = 1 ↔
        residualRatio D g = 1 := by
      rw [← map_one (Units.map C.residueMap.toMonoidHom)]
      exact (C.unitsMap_injective f).eq_iff
    exact heq.trans (H.cuts_out_ratio g)

/-- Equality of two coordinate actions transports a residual ratio field
together with the residual datum from which its kernel is defined. -/
def SkinnerWilesRatioField.transportAction
    {ρ σ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (D : SkinnerWilesResidualData ρ)
    (M : Type*) [Field M] [NumberField M] [Algebra F M]
    (H : SkinnerWilesRatioField D M) (h : ρ = σ) :
    SkinnerWilesRatioField (h ▸ D) M := by
  cases h
  exact H

/-- Transport a completed Skinner–Wiles checklist to a genuine finite local
coefficient extension. The ordinary row at the new field is supplied for the
transported residual datum; it is a local geometric application, while all
global rows follow from the original checklist and the actual residue map.
The larger field need not be a fraction field of the original integer ring. -/
def SkinnerWilesWeightTwoInput.mapLocalCoefficients
    (p : ℕ) [Fact p.Prime]
    {K L : Type*} [NormedField K] [ValuativeRel K]
      [Algebra ℚ_[p] K] [ContinuousSMul ℚ_[p] K] [IsUniformAddGroup K]
      [IsNonarchimedeanLocalField K] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
      [NormedField L] [ValuativeRel L]
      [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L] [IsUniformAddGroup L]
      [IsNonarchimedeanLocalField L] [CharP (𝒪[L] ⧸ 𝓂[L]) p]
    {ρ : Representation K (AbsoluteGalois F) (Fin 2 → K)}
    (M : Type*) [Field M] [NumberField M] [Algebra F M]
    (H : SkinnerWilesWeightTwoInput p ρ M)
    (f : K →+* L) (hf : Continuous f)
    (hfp : ∀ x : ℚ_[p], f (algebraMap ℚ_[p] K x) =
      algebraMap ℚ_[p] L x)
    (C : LocalIntegerResidueComparison f)
    (habs : (Representation.baseChange (AlgebraicClosure L)
      (ρ.mapCoefficients f)).IsIrreducible)
    (hordinary : ∀ (P : Ideal (𝓞 F)) [P.IsMaximal],
      (p : 𝓞 F) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F)))
        [Q.IsMaximal] [Q.LiesOver P],
      SkinnerWilesOrdinaryAt p (ρ.mapCoefficients f)
        (HilbertModularity.Hypergeometric.SkinnerWilesResidualData.mapLocalCoefficients
          H.residual f C) Q) :
    SkinnerWilesWeightTwoInput p (ρ.mapCoefficients f) M where
  p_odd := H.p_odd
  totally_real := H.totally_real
  galois_over_rat := H.galois_over_rat
  abelian_over_rat := H.abelian_over_rat
  continuous := by
    intro i j
    exact Representation.continuous_mapCoefficients f hf ρ H.continuous i j
  absolutely_irreducible := habs
  ramified := H.ramified
  ramified_finite := H.ramified_finite
  unramified := by
    intro q hq P _ hP Q _ _ g hg
    exact Representation.mapCoefficients_eq_one f ρ g (H.unramified q hq P hP Q g hg)
  residual := HilbertModularity.Hypergeometric.SkinnerWilesResidualData.mapLocalCoefficients
    H.residual f C
  ratio_field := HilbertModularity.Hypergeometric.SkinnerWilesRatioField.mapLocalCoefficients
    H.residual M H.ratio_field f C
  ratio_odd := by
    intro c hc
    rw [SkinnerWilesResidualData.residualRatio_mapLocalCoefficients]
    have h := H.ratio_odd c hc
    change C.residueMap (residualRatio H.residual c : 𝒪[K] ⧸ 𝓂[K]) = -1
    rw [h, map_neg, map_one]
  local_ordinary := hordinary
  ratio_distinguished := by
    intro P _ hpP Q _ _
    obtain ⟨g, hg⟩ := H.ratio_distinguished P hpP Q
    refine ⟨g, ?_⟩
    rw [SkinnerWilesResidualData.residualRatio_mapLocalCoefficients]
    intro heq
    apply hg
    apply C.unitsMap_injective f
    simpa using heq
  finite_det_character := (Units.map f.toMonoidHom).comp H.finite_det_character
  finite_det_range := by
    simpa only [MonoidHom.coe_comp, Set.range_comp] using
      H.finite_det_range.image (Units.map f.toMonoidHom)
  determinant := by
    intro g
    rw [Representation.det_mapCoefficients_commRing, H.determinant, map_mul]
    simp only [Field.cyclotomicCharacterWithCoefficients_coe]
    rw [← hfp]
    rfl

end HilbertModularity.Hypergeometric

namespace HilbertModularity.Cyclotomic

open scoped NumberField

/-- The actual completion of the full cyclotomic coefficient field at its
unique prime above the conductor. -/
abbrev FullConductorCompletion (p : ℕ) [Fact p.Prime] :=
  (primeAboveConductor p).adicCompletion (cyclotomicField p)

/-- The inclusion of the real coefficient field extends to the chosen full
cyclotomic completion. Its source and target are the actual native local
fields, with no false fraction-field instance on the larger field. -/
def realToFullConductorCompletionMap (p : ℕ) [Fact p.Prime] :
    RealCompletion p →+* FullConductorCompletion p := by
  letI : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  haveI : (primeAboveConductor p).asIdeal.LiesOver
      (realPrimeAboveConductor p).asIdeal := by
    rw [Ideal.liesOver_iff]
    exact realPrimeAboveConductor_eq_comap p
  exact (realPrimeAboveConductor p).completionMap
    (K := realCyclotomicField p) (L := cyclotomicField p)
    (primeAboveConductor p)

/-- The coefficient extension map is continuous for the native local-field
topologies. -/
theorem continuous_realToFullConductorCompletionMap (p : ℕ) [Fact p.Prime] :
    Continuous (realToFullConductorCompletionMap p) := by
  let : Algebra (realCyclotomicField p) (cyclotomicField p) :=
    (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra
  have : (primeAboveConductor p).asIdeal.LiesOver
      (realPrimeAboveConductor p).asIdeal := by
    rw [Ideal.liesOver_iff]
    exact realPrimeAboveConductor_eq_comap p
  exact (realPrimeAboveConductor p).continuous_completionMap
    (K := realCyclotomicField p) (L := cyclotomicField p)
    (primeAboveConductor p)

/-- The inclusion of conductor completions preserves the canonical `ℚₚ`
coefficient map. Both continuous maps agree on dense rational scalars. -/
theorem realToFullConductorCompletionMap_padic
    (p : ℕ) [Fact p.Prime] (z : ℚ_[p]) :
    realToFullConductorCompletionMap p
      (NumberField.padicCompletionMap p (realCyclotomicField p)
        (realPrimeAboveConductor p) z) =
      NumberField.padicCompletionMap p (cyclotomicField p)
        (primeAboveConductor p) z := by
  have hfun : (fun x : ℚ_[p] => realToFullConductorCompletionMap p
        (NumberField.padicCompletionMap p (realCyclotomicField p)
          (realPrimeAboveConductor p) x)) =
      (fun x : ℚ_[p] => NumberField.padicCompletionMap p (cyclotomicField p)
        (primeAboveConductor p) x) := by
    apply Continuous.ext_on (s := Set.range (fun q : ℚ => (q : ℚ_[p])))
      (Padic.denseRange_ratCast p)
      ((continuous_realToFullConductorCompletionMap p).comp
        (NumberField.continuous_padicCompletionMap p
          (realCyclotomicField p) (realPrimeAboveConductor p)))
      (NumberField.continuous_padicCompletionMap p
        (cyclotomicField p) (primeAboveConductor p))
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    have hrat := map_ratCast
      ((realToFullConductorCompletionMap p).comp
        (NumberField.padicCompletionMap p (realCyclotomicField p)
          (realPrimeAboveConductor p))) q
    exact hrat.trans (map_ratCast
      (NumberField.padicCompletionMap p (cyclotomicField p)
        (primeAboveConductor p)) q).symm
  exact congrFun hfun z

/-- The continuous field map restricts to the actual integer rings of the
two coefficient completions. -/
def realToFullConductorIntegerMap (p : ℕ) [Fact p.Prime] :
    𝒪[RealCompletion p] →+* 𝒪[FullConductorCompletion p] := by
  letI : IsNonarchimedeanLocalField (RealCompletion p) :=
    NumberField.isNonarchimedeanLocalField_padicCompletion
      (realCyclotomicField p) (realPrimeAboveConductor p) p
  letI : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
    NumberField.isNonarchimedeanLocalField_padicCompletion
      (cyclotomicField p) (primeAboveConductor p) p
  exact IsNonarchimedeanLocalField.integerMap
    (realToFullConductorCompletionMap p)
    (continuous_realToFullConductorCompletionMap p)

/-- The integer map is local for this finite extension of complete discrete
valuation fields. [MilneANT, Theorem 7.38 and Corollary 7.42, printed
pp. 123–124] give the unique extending valuation and its ramification and
residue degrees. In particular the extension map sends the maximal ideal
into the maximal ideal and induces the residue-field embedding. This standard local-field input says
nothing about Tate actions or Skinner–Wiles hypotheses. -/
theorem realToFullConductorIntegerMap_isLocalHom
    (p : ℕ) [Fact p.Prime] :
    IsLocalHom (realToFullConductorIntegerMap p) := by
  sorry

/-- The induced map of the actual native residue fields. -/
def realToFullConductorResidueMap (p : ℕ) [Fact p.Prime] :
    𝓀[RealCompletion p] →+* 𝓀[FullConductorCompletion p] := by
  letI : IsLocalHom (realToFullConductorIntegerMap p) :=
    realToFullConductorIntegerMap_isLocalHom p
  exact IsLocalRing.ResidueField.map (realToFullConductorIntegerMap p)

/-- The full native coefficient extension carries compatible field, integer
and residue maps, with injectivity of the residue embedding. -/
def realToFullConductorIntegerResidueComparison
    (p : ℕ) [Fact p.Prime] :
    HilbertModularity.Hypergeometric.LocalIntegerResidueComparison
      (realToFullConductorCompletionMap p) where
  integerMap := realToFullConductorIntegerMap p
  residueMap := realToFullConductorResidueMap p
  coe_integerMap := by
    intro a
    let : IsNonarchimedeanLocalField (RealCompletion p) :=
      NumberField.isNonarchimedeanLocalField_padicCompletion
        (realCyclotomicField p) (realPrimeAboveConductor p) p
    let : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
      NumberField.isNonarchimedeanLocalField_padicCompletion
        (cyclotomicField p) (primeAboveConductor p) p
    exact IsNonarchimedeanLocalField.coe_integerMap
      (realToFullConductorCompletionMap p)
      (continuous_realToFullConductorCompletionMap p) a
  residueMap_mk := by
    intro a
    let : IsLocalHom (realToFullConductorIntegerMap p) :=
      realToFullConductorIntegerMap_isLocalHom p
    exact IsLocalRing.ResidueField.map_residue
      (realToFullConductorIntegerMap p) a
  residue_injective := by
    let : IsLocalHom (realToFullConductorIntegerMap p) :=
      realToFullConductorIntegerMap_isLocalHom p
    exact (IsLocalRing.ResidueField.map
      (realToFullConductorIntegerMap p)).injective

/-- The residue field of the full conductor completion has exactly `p`
elements, via the already computed global cyclotomic prime residue. -/
theorem card_fullConductorCompletionResidue
    (p : ℕ) [Fact p.Prime] :
    Nat.card 𝓀[FullConductorCompletion p] = p := by
  calc
    Nat.card 𝓀[FullConductorCompletion p] =
        Nat.card (𝓞 (cyclotomicField p) ⧸ (primeAboveConductor p).asIdeal) :=
      Nat.card_congr (NumberField.adicCompletionResidueEquiv
        (cyclotomicField p) (primeAboveConductor p)).symm.toEquiv
    _ = p := card_quotient_primeAboveConductor p

/-- The actual full and real conductor completions have the same prime
residue field. The induced embedding is therefore an isomorphism; its map
still records the specified integer and uniformizer normalization. -/
def realToFullConductorResidueEquiv
    (p : ℕ) [Fact p.Prime] :
    𝓀[RealCompletion p] ≃+* 𝓀[FullConductorCompletion p] := by
  letI : IsNonarchimedeanLocalField (FullConductorCompletion p) :=
    NumberField.isNonarchimedeanLocalField_padicCompletion
      (cyclotomicField p) (primeAboveConductor p) p
  have hcard : Nat.card 𝓀[RealCompletion p] =
      Nat.card 𝓀[FullConductorCompletion p] := by
    rw [Nat.card_congr (realCompletionResidueEquiv p).toEquiv,
      Nat.card_zmod, card_fullConductorCompletionResidue]
  exact RingEquiv.ofBijective (realToFullConductorResidueMap p)
    ((Nat.bijective_iff_injective_and_card
      (realToFullConductorResidueMap p)).2
        ⟨(realToFullConductorIntegerResidueComparison p).residue_injective,
          hcard⟩)

/-- The residue equivalence is induced by the chosen integral completion
map, so reduction of every actual integer commutes with the extension. -/
@[simp] theorem realToFullConductorResidueEquiv_mk
    (p : ℕ) [Fact p.Prime] (a : 𝒪[RealCompletion p]) :
    realToFullConductorResidueEquiv p
      (Ideal.Quotient.mk (𝓂[RealCompletion p]) a) =
      Ideal.Quotient.mk (𝓂[FullConductorCompletion p])
        (realToFullConductorIntegerMap p a) := by
  exact (realToFullConductorIntegerResidueComparison p).residueMap_mk a

/-- The canonical ring equivalence from the selected Tate coefficient
completion to the native real valuation integers. -/
def realPrimeGeneratorAdicIntegersEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) ≃+* 𝒪[RealCompletion p] :=
  (AdicCompletion.idealEqRingEquiv (span_realPrimeGenerator p (by omega))).trans
    (realPrimeAdicCompletionIntegersEquiv p)

/-- The selected adic integer equivalence preserves every global real integer. -/
theorem realPrimeGeneratorAdicIntegersEquiv_algebraMap
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (a : 𝓞 (realCyclotomicField p)) :
    realPrimeGeneratorAdicIntegersEquiv p hp
      (algebraMap (𝓞 (realCyclotomicField p))
        (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) a) =
      NumberField.adicCompletionIntegerMap (realCyclotomicField p)
        (realPrimeAboveConductor p) a := by
  simp only [realPrimeGeneratorAdicIntegersEquiv, RingEquiv.trans_apply,
    AdicCompletion.idealEqRingEquiv_algebraMap,
    realPrimeAdicCompletionIntegersEquiv_algebraMap]

/-- The cofinal Tate coefficient map has the canonical rational p-adic normalization. -/
theorem realPrimeGeneratorAdicIntegersEquiv_padic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (z : ℤ_[p]) :
    (realPrimeGeneratorAdicIntegersEquiv p hp
      (TateModule.coefficientPrimeRingEquiv p (𝓞 (realCyclotomicField p))
        (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
        (realPrimeRamification_pos p (by omega))
        (span_realPrimeGenerator_pow p (by omega))
        (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) :
      RealCompletion p) = algebraMap ℚ_[p] (RealCompletion p) (z : ℚ_[p]) := by
  convert coe_adicCompletionIntegersEquiv_padicInt p hp z using 1
  unfold realPrimeGeneratorAdicIntegersEquiv padicIntToRealPrimeAdicCompletion
    TateModule.coefficientPrimeRingEquiv
  rfl

/-- The canonical native integer specialization of the selected Tate
coefficient ring. The source ideal is the actual real conductor prime. -/
def realPrimeGeneratorAdicToNativeIntegers
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealCompletion p] :=
  (realPrimeGeneratorAdicIntegersEquiv p hp).toRingHom

/-- The same chosen Tate coefficient ring maps into the larger cyclotomic
completion through its actual integral field-extension map. -/
def realPrimeGeneratorAdicToFullIntegers
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[FullConductorCompletion p] :=
  (realToFullConductorIntegerMap p).comp
    (realPrimeGeneratorAdicToNativeIntegers p hp)

end HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms
  AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField

/-- The two coefficient specializations of the same selected integral Tate
basis agree after extending scalars through a compatible local field map.
This compares the actual global Galois actions, before any ordinary data. -/
theorem primePlusTateFieldCoordinateAction_mapLocalCoefficients
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E L : Type*} [Field E] [ValuativeRel E]
    [Field L] [ValuativeRel L]
    (βE : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (βL : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[L])
    (f : E →+* L)
    (hβ : ∀ a, f (βE a : E) = (βL a : L)) :
    primePlusTateFieldCoordinateAction p hp ξ βL =
      (primePlusTateFieldCoordinateAction p hp ξ βE).mapCoefficients f := by
  let := primePlusIntegralTateModule p hp ξ
  let : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E := ((𝒪[E]).subtype.comp βE).toAlgebra
  let : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) L := ((𝒪[L]).subtype.comp βL).toAlgebra
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrixAlgEquiv'.injective
  rw [Representation.toMatrix_mapCoefficients]
  have h := (toMatrix_coordinateAction_extension
    (primePlusIntegralTateBasis p hp ξ)
    (primePlusIntegralTateRepresentation p hp ξ g) f hβ).symm
  calc
    _ = LinearMap.toMatrixAlgEquiv'
        (((primePlusIntegralTateBasis p hp ξ).baseChange L).equivFun.conjRingEquiv
          ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g)) :=
          congrArg _ (primePlusTateFieldCoordinateAction_apply p hp ξ βL g)
    _ = (LinearMap.toMatrixAlgEquiv'
        (((primePlusIntegralTateBasis p hp ξ).baseChange E).equivFun.conjRingEquiv
          ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g))).map f := h
    _ = _ := by
      exact congrArg (fun M : Matrix (Fin 2) (Fin 2) E => M.map f)
        (congrArg LinearMap.toMatrixAlgEquiv'
          (primePlusTateFieldCoordinateAction_apply p hp ξ βE g)).symm

/-- The chosen integral Tate action transports along an actual local integer
and residue comparison. The field action uses the composed integer map, not a
spurious fraction-field structure on the larger completion. -/
theorem primePlusTateFieldCoordinateAction_mapLocalIntegerComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E L : Type*} [Field E] [ValuativeRel E]
    [Field L] [ValuativeRel L]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (f : E →+* L) (C : LocalIntegerResidueComparison f) :
    primePlusTateFieldCoordinateAction p hp ξ (C.integerMap.comp β) =
      (primePlusTateFieldCoordinateAction p hp ξ β).mapCoefficients f := by
  apply primePlusTateFieldCoordinateAction_mapLocalCoefficients p hp ξ
    β (C.integerMap.comp β) f
  intro a
  exact (C.coe_integerMap (β a)).symm

/-- At the conductor prime the full-field coordinate action of the actual
selected plus Jacobian is the scalar enlargement of its native real-field
coordinate action. Both use the same integral Tate basis and the canonical
maps of the two number-field completions. -/
theorem selectedPlusFullConductorAction_eq_mapNative
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p)) :
    primePlusTateFieldCoordinateAction p hp ξ
      (realPrimeGeneratorAdicToFullIntegers p hp) =
    (primePlusTateFieldCoordinateAction p hp ξ
      (realPrimeGeneratorAdicToNativeIntegers p hp)).mapCoefficients
        (realToFullConductorCompletionMap p) := by
  exact primePlusTateFieldCoordinateAction_mapLocalIntegerComparison
    p hp ξ (realPrimeGeneratorAdicToNativeIntegers p hp)
    (realToFullConductorCompletionMap p)
    (realToFullConductorIntegerResidueComparison p)

/-- Residual semisimplification data of the same selected plus Jacobian after
enlarging its native coefficient field. The two characters are mapped through
the induced residue embedding. -/
def SkinnerWilesResidualData.selectedPlusMapLocalCoefficients
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E L : Type*} [Field E] [ValuativeRel E]
    [Field L] [ValuativeRel L]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ β))
    (f : E →+* L) (C : LocalIntegerResidueComparison f) :
    SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ (C.integerMap.comp β)) :=
  (primePlusTateFieldCoordinateAction_mapLocalIntegerComparison p hp ξ β f C).symm ▸
    HilbertModularity.Hypergeometric.SkinnerWilesResidualData.mapLocalCoefficients D f C

/-- The selected plus Jacobian's actual full cyclotomic residual datum from
its native real-completion datum, using the canonical integer and residue
maps. Its Galois action is the same selected integral Tate basis. -/
def selectedPlusFullConductorResidualData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp))) :
    SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp)) :=
  (selectedPlusFullConductorAction_eq_mapNative p hp ξ).symm ▸
    HilbertModularity.Hypergeometric.SkinnerWilesResidualData.mapLocalCoefficients
      D (realToFullConductorCompletionMap p)
      (realToFullConductorIntegerResidueComparison p)

/-- The canonical named full residual datum is the actual transported
native datum, including its selected action equality. -/
theorem selectedPlusFullConductorResidualData_eq_mapLocalCoefficients
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp))) :
    selectedPlusFullConductorResidualData p hp ξ D =
      (selectedPlusFullConductorAction_eq_mapNative p hp ξ).symm ▸
        HilbertModularity.Hypergeometric.SkinnerWilesResidualData.mapLocalCoefficients D
          (realToFullConductorCompletionMap p)
          (realToFullConductorIntegerResidueComparison p) := (rfl)

/-- The actual cyclotomic ratio field remains the kernel field of the
selected plus Jacobian's residual character ratio after coefficient
extension. The underlying global field is unchanged. -/
def selectedPlusFullConductorRatioField
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)))
    (M : Type*) [Field M] [NumberField M]
      [Algebra (realCyclotomicField p) M]
    (H : SkinnerWilesRatioField D M) :
    SkinnerWilesRatioField
      (selectedPlusFullConductorResidualData p hp ξ D) M :=
  HilbertModularity.Hypergeometric.SkinnerWilesRatioField.transportAction
    (HilbertModularity.Hypergeometric.SkinnerWilesResidualData.mapLocalCoefficients
      D (realToFullConductorCompletionMap p)
        (realToFullConductorIntegerResidueComparison p)) M
    (HilbertModularity.Hypergeometric.SkinnerWilesRatioField.mapLocalCoefficients
      D M H (realToFullConductorCompletionMap p)
        (realToFullConductorIntegerResidueComparison p))
    (selectedPlusFullConductorAction_eq_mapNative p hp ξ).symm

/-- The actual full-conductor residual ratio is the residue embedding of
the native ratio, so the ratio kernel is unchanged. -/
theorem selectedPlusFullConductorResidualRatio
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp))) :
    residualRatio (selectedPlusFullConductorResidualData p hp ξ D) =
      (Units.map (realToFullConductorResidueMap p).toMonoidHom).comp
        (residualRatio D) := by
  unfold selectedPlusFullConductorResidualData
  rw [HilbertModularity.Hypergeometric.SkinnerWilesResidualData.residualRatio_transportAction]
  apply MonoidHom.ext
  intro g
  exact HilbertModularity.Hypergeometric.SkinnerWilesResidualData.residualRatio_mapLocalCoefficients
    D (realToFullConductorCompletionMap p)
      (realToFullConductorIntegerResidueComparison p) g

/-- The real-place oddness check passes to the selected full-conductor
residual ratio through the actual residue-field map. -/
theorem selectedPlusFullConductorResidualRatio_odd
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)))
    (c : AbsoluteGalois (realCyclotomicField p))
    (hodd : (residualRatio D c : 𝒪[RealCompletion p] ⧸ 𝓂[RealCompletion p]) = -1) :
    (residualRatio (selectedPlusFullConductorResidualData p hp ξ D) c :
      𝒪[FullConductorCompletion p] ⧸ 𝓂[FullConductorCompletion p]) = -1 := by
  rw [selectedPlusFullConductorResidualRatio]
  change (realToFullConductorIntegerResidueComparison p).residueMap
    (residualRatio D c : 𝒪[RealCompletion p] ⧸ 𝓂[RealCompletion p]) = -1
  rw [hodd, map_neg, map_one]

/-- A native nontrivial residual ratio value remains nontrivial after
coefficient enlargement; hence a distinguished decomposition group stays
distinguished at the same global prime. -/
theorem selectedPlusFullConductorResidualRatio_ne_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (D : SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToNativeIntegers p hp)))
    (g : AbsoluteGalois (realCyclotomicField p))
    (h : residualRatio D g ≠ 1) :
    residualRatio (selectedPlusFullConductorResidualData p hp ξ D) g ≠ 1 := by
  rw [selectedPlusFullConductorResidualRatio]
  intro heq
  apply h
  apply (realToFullConductorIntegerResidueComparison p).unitsMap_injective
    (realToFullConductorCompletionMap p)
  change Units.map
    (realToFullConductorIntegerResidueComparison p).residueMap.toMonoidHom
      (residualRatio D g) = 1 at heq
  simpa using heq

/-- Entrywise continuity of the same selected Jacobian action survives the
actual real-to-cyclotomic coefficient map. -/
theorem selectedPlusFullConductorAction_continuous_of_native
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hcontinuous : ∀ i j : Fin 2,
      Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        primePlusTateFieldCoordinateAction p hp ξ
          (realPrimeGeneratorAdicToNativeIntegers p hp) g (Pi.single j 1) i))
    (i j : Fin 2) :
    Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
      primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp) g (Pi.single j 1) i) := by
  rw [selectedPlusFullConductorAction_eq_mapNative p hp ξ]
  exact Representation.continuous_mapCoefficients
    (realToFullConductorCompletionMap p)
    (continuous_realToFullConductorCompletionMap p) _ hcontinuous i j

/-- Inertia-triviality of the same selected integral Tate action is
preserved when its coefficients enter the cyclotomic completion. -/
theorem selectedPlusFullConductorAction_eq_one_of_native
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (g : AbsoluteGalois (realCyclotomicField p))
    (h : primePlusTateFieldCoordinateAction p hp ξ
      (realPrimeGeneratorAdicToNativeIntegers p hp) g = 1) :
    primePlusTateFieldCoordinateAction p hp ξ
      (realPrimeGeneratorAdicToFullIntegers p hp) g = 1 := by
  rw [selectedPlusFullConductorAction_eq_mapNative p hp ξ]
  exact Representation.mapCoefficients_eq_one
    (realToFullConductorCompletionMap p) _ g h

/-- The exact native covariant Tate determinant remains the canonical
cyclotomic determinant at the full conductor completion. This uses the
proved `ℚₚ` coefficient compatibility, with no `NormedAlgebra` or false
fraction-field instance on the larger completion. -/
theorem selectedPlusFullConductorAction_det_of_native
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det
        (primePlusTateFieldCoordinateAction p hp ξ
          (realPrimeGeneratorAdicToNativeIntegers p hp) g) =
        NumberField.padicCompletionMap p (realCyclotomicField p)
          (realPrimeAboveConductor p)
          ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]))
    (g : AbsoluteGalois (realCyclotomicField p)) :
    LinearMap.det
      (primePlusTateFieldCoordinateAction p hp ξ
        (realPrimeGeneratorAdicToFullIntegers p hp) g) =
      NumberField.padicCompletionMap p (cyclotomicField p)
        (primeAboveConductor p)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]) := by
  rw [selectedPlusFullConductorAction_eq_mapNative p hp ξ,
    Representation.det_mapCoefficients_commRing, hdet,
    realToFullConductorCompletionMap_padic]

end HilbertModularity.Hypergeometric
