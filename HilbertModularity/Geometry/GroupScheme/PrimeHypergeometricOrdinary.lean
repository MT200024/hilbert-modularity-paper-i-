/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricRanks
public import HilbertModularity.Geometry.GroupScheme.HypergeometricOrdinary
public import HilbertModularity.Geometry.TwoComponentGraph
public import HilbertModularity.NumberTheory.RealCyclotomicPrime
public import HilbertModularity.NumberTheory.CyclotomicLocalField
public import HilbertModularity.NumberTheory.IntegralCharacter
public import HilbertModularity.RepresentationTheory.HodgeTateInertia
public import HilbertModularity.RepresentationTheory.HodgeTateComparison
public import HilbertModularity.RepresentationTheory.HodgeTateInjectivity

/-! # Local ordinary quotient of the selected prime plus Jacobian

This is the actual completed Tate representation of the same family whose
pointed fibres are plus-curve Jacobians. Its ordinary quotient is a separate
geometric obligation; the definitions and label independence below do not
assert that it exists.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry IsNonarchimedeanLocalField
open scoped ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local instance realPrimeCompletionIntegerQuotientCharP :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- A coefficient label on the selected plus Jacobian's actual local Tate
representation. At prime conductor the label is a unit modulo `p`. -/
@[expose] def primePlusDecompositionScalarConjugate (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :=
  Rep.localCoefficientConjugate p 0 m hm
    (primePlusDecompositionRepresentation p hp ξ)

/-- Each coefficient label preserves the selected fibre's completed RM rank. -/
theorem finrank_primePlusDecompositionScalarConjugate (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Module.finrank (RealPrimePowerCompletion p 0)
      (primePlusDecompositionScalarConjugate p hp ξ m hm) = 2 := by
  unfold primePlusDecompositionScalarConjugate
  exact (Rep.finrank_localCoefficientConjugate p 0 m hm
    (primePlusDecompositionRepresentation p hp ξ)).trans
      (finrank_primePlusDecompositionRepresentation p hp ξ)

/-- Rational scalars on the restricted Tate representation. -/
@[instance_reducible] def primePlusDecompositionRationalModule :
    Module ℚ_[p] (primePlusDecompositionRepresentation p hp ξ) :=
  Module.compHom _ (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0))

attribute [local instance] primePlusDecompositionRationalModule

/-- The original and completed coefficient actions form a scalar tower. -/
theorem primePlusDecompositionScalarTower :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (primePlusDecompositionRepresentation p hp ξ) where
  smul_assoc r a v := by
    change (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) r * a) • v =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) r • (a • v)
    exact mul_smul _ _ _

attribute [local instance] primePlusDecompositionScalarTower

/-- Rational scalars on a conjugated factor come from its completed RM field. -/
@[expose, instance_reducible] def primePlusConjugateRationalModule (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Module ℚ_[p] (primePlusDecompositionScalarConjugate p hp ξ m hm) :=
  Module.compHom _ (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0))

attribute [local instance] primePlusConjugateRationalModule

/-- The two coefficient actions on a labelled factor form a scalar tower. -/
theorem primePlusConjugateScalarTower (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (primePlusDecompositionScalarConjugate p hp ξ m hm) where
  smul_assoc r a v := by
    change (algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) r * a) • v =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p 0) r • (a • v)
    exact mul_smul _ _ _

attribute [local instance] primePlusConjugateScalarTower

/-- The same-fibre deep ordinary condition, expressed as a concrete rank-one
weight-zero quotient of its completed covariant Tate representation. -/
@[expose] def PrimePlusOrdinaryQuotient (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :=
  HodgeTate.WeightZeroQuotient p (realPrimePowerLocalPeriodAction p 0)
    (realPrimePowerLocalPeriodAction_fixes p 0)
    (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ

/-- The period-lattice quotient in the Raynaud sequence has coefficient rank
one once its rational rank is the degree of the local RM field. This is the
dimension calculation in [TripathiGoswamiRevised, proof of Proposition
`prime-deep-DO`]; the existence of the sequence is a separate geometric input. -/
theorem finrank_primePlusPeriodQuotient_eq_one
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hperiod : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        Module.finrank ℚ_[p] (RealPrimePowerCompletion p 0)) :
    Module.finrank (RealPrimePowerCompletion p 0)
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) = 1 := by
  let V := primePlusDecompositionRepresentation p hp ξ
  let E := RealPrimePowerCompletion p 0
  have hV : Module.finrank E V = 2 :=
    finrank_primePlusDecompositionRepresentation p hp ξ
  let : Module.Finite E V := by
    exact Module.finite_of_finrank_eq_succ (by simpa using hV)
  let : Module.Finite E (V ⧸ S.toSubmodule) := inferInstance
  let : Module.Finite ℚ_[p] E := inferInstance
  let : IsScalarTower ℚ_[p] E (V ⧸ S.toSubmodule) := inferInstance
  let : Module.Finite ℚ_[p] V := Module.Finite.trans E V
  let : Module.Finite ℚ_[p] (V ⧸ S.toSubmodule) :=
    Module.Finite.quotient ℚ_[p] S.toSubmodule
  have hdeg : 0 < Module.finrank ℚ_[p] E := Module.finrank_pos
  have htower := Module.finrank_mul_finrank ℚ_[p] E (V ⧸ S.toSubmodule)
  rw [hperiod] at htower
  have hrank : Module.finrank ℚ_[p] E *
      Module.finrank E (V ⧸ S.toSubmodule) =
      Module.finrank ℚ_[p] E * 1 := by simpa using htower
  exact Nat.eq_of_mul_eq_mul_left hdeg hrank

/-- A period quotient of rational dimension `(p - 1) / 2` has rank one
 over the unique completed prime-level RM field. This is the dimension step
 in [TripathiGoswamiRevised, proof of Proposition `prime-deep-DO`]. -/
theorem finrank_primePlusPeriodQuotient_of_rank
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hperiod : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        (p - 1) / 2) :
    Module.finrank (RealPrimePowerCompletion p 0)
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) = 1 := by
  have hlocal : Module.finrank ℚ_[p] (RealPrimePowerCompletion p 0) =
      (p - 1) / 2 := by
    rw [← (realPrimePowerCompletionTensorEquiv p 0).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange]
    have hz : zeta (p ^ (0 + 1)) = zeta p := by
      congr 1
      simp
    have hfield : realCyclotomicField (p ^ (0 + 1)) = realCyclotomicField p := by
      unfold realCyclotomicField
      rw [hz]
    rw [hfield, finrank_realCyclotomicField p (by omega)]
  exact finrank_primePlusPeriodQuotient_eq_one p hp ξ S (hperiod.trans hlocal.symm)

/-- The numerical part of the Raynaud--Picard argument for the *selected*
plus Jacobian: a comparison of its period quotient with the homology of the
actual two-component, `d + 1`-node dual graph makes the quotient rank one over
the completed RM field. The geometric and Galois-compatible comparison is a
separate input; a bare vector-space equivalence does not prove weight zero. -/
theorem finrank_primePlusPeriodQuotient_of_graph
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hgraph : ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) ≃ₗ[ℚ_[p]]
      (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology) :
    Module.finrank (RealPrimePowerCompletion p 0)
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) = 1 := by
  have hgraphRank : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        (p - 1) / 2 := by
    rw [hgraph.finrank_eq, (Graph.twoComponentHomologyEquiv ℚ_[p] ((p - 1) / 2)).finrank_eq]
    exact Module.finrank_fin_fun ℚ_[p]
  exact finrank_primePlusPeriodQuotient_of_rank p hp ξ S hgraphRank

/-- The manuscript's numerical graph calculation gives an ordinary quotient of
the *same* selected Jacobian once the period quotient has the stated
Hodge--Tate comparison and weights. The equivariant Picard/period comparison
and the Hodge--Tate statements are explicit hypotheses here, not consequences
of a nodal special fibre alone. This applies to every coprime coefficient
label by scalar conjugation. -/
theorem nonempty_primePlusOrdinaryQuotient_of_graph
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hgraph : ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) ≃ₗ[ℚ_[p]]
      (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology)
    (hcomparison : Function.Bijective (HodgeTate.comparison p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])))
    (hweights : ∀ q : ℤ, q ≠ 0 → HodgeTate.weightSpace p
      (realPrimePowerLocalPeriodAction p 0)
      (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p 0 m hm
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateRationalModule p hp ξ m hm
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (Rep.localCoefficientConjugate p 0 m hm
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateScalarTower p hp ξ m hm
  have hbase : Nonempty (HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (primePlusDecompositionRepresentation p hp ξ).ρ) :=
    ⟨⟨S, finrank_primePlusPeriodQuotient_of_graph p hp ξ S hgraph,
      hcomparison, hweights⟩⟩
  exact (HodgeTate.nonempty_weightZeroQuotient_localCoefficientConjugate_iff p
    (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
    0 m hm (primePlusDecompositionRepresentation p hp ξ)).mp hbase

/-- For the same selected plus Jacobian, a Galois-stable period quotient whose
dimension matches the graph and whose fixed periods span gives the ordinary
quotient at every coefficient label. Injectivity is required of the actual
`Cp` comparison map; the graph isomorphism is only a linear equivalence and
does not establish either period assertion. The conversion
from fixed periods to the Hodge--Tate conditions uses
[src_brinon_conrad, Remark 2.3.2] through the comparison-map API. -/
theorem nonempty_primePlusOrdinaryQuotient_of_graph_fixedPeriods
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hgraph : ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) ≃ₗ[ℚ_[p]]
      (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology)
    (hinj : Function.Injective (HodgeTate.comparison p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])))
    (hperiods : HodgeTate.zeroWeightSpan
      (ι := realPrimePowerLocalPeriodAction p 0)
      (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) = ⊤)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  obtain ⟨hcomparison, hweights⟩ :=
    (HodgeTate.zeroWeightSpan_eq_top_iff_comparison_bijective_and_weights_zero p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) hinj).mp hperiods
  exact nonempty_primePlusOrdinaryQuotient_of_graph p hp ξ S hgraph
    hcomparison hweights m hm

/-- A representation with trivial rational Galois action has enough actual
fixed `Cp` periods: pure tensors `1 ⊗ v` are fixed and span the tensor.
This is the representation-theoretic step after a split graph comparison. -/
private theorem zeroWeightSpan_trivialRepresentation
    {G W : Type*} [Group G] [AddCommGroup W] [Module ℚ_[p] W]
    (ι : G →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :
    HodgeTate.zeroWeightSpan (ι := ι) (Representation.trivial ℚ_[p] G W) = ⊤ := by
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
      have hv : (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] v ∈
          HodgeTate.weightSpace p ι (Representation.trivial ℚ_[p] G W) 0 := by
        rw [HodgeTate.mem_weightSpace]
        intro g
        simp [HodgeTate.periodRepresentation_tmul]
      have hs : (1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] v ∈
          HodgeTate.zeroWeightSpan (ι := ι)
            (Representation.trivial ℚ_[p] G W) :=
        Submodule.subset_span hv
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (HodgeTate.zeroWeightSpan (ι := ι)
        (Representation.trivial ℚ_[p] G W)).smul_mem c hs
  | add x y hx hy =>
      exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)

/-- Construct the particular weight-zero quotient carried by a fixed period
map. Its kernel is the supplied stable toric subrepresentation, so subsequent
character arguments can use the genuine Raynaud quotient action. -/
theorem exists_primePlusBaseOrdinaryQuotient_of_trivialPeriodAction
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hperiod : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        (p - 1) / 2)
    (htrivial : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule),
      (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule g v = v) :
    ∃ W : HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0)
      (primePlusDecompositionRepresentation p hp ξ).ρ,
      W.kernel = S := by
  let E := RealPrimePowerCompletion p 0
  let V := primePlusDecompositionRepresentation p hp ξ
  let Q := V ⧸ S.toSubmodule
  let ρQ := (V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]
  have hVfinite : Module.Finite E V :=
    Module.finite_of_finrank_eq_succ (by
      simpa only [Nat.reduceAdd] using finrank_primePlusDecompositionRepresentation p hp ξ)
  let : Module.Finite E V := hVfinite
  let : Module.Finite ℚ_[p] E := inferInstance
  let : Module.Finite ℚ_[p] V := Module.Finite.trans E V
  let : Module.Finite ℚ_[p] Q := Module.Finite.quotient ℚ_[p] S.toSubmodule
  let : TopologicalSpace Q := moduleTopology ℚ_[p] Q
  let : IsModuleTopology ℚ_[p] Q := ⟨rfl⟩
  have haction (g : Gal(PadicAlgCl p/E)) (v : Q) : ρQ g v = v :=
    htrivial g v
  have hcontinuous : Continuous (fun y : Gal(PadicAlgCl p/E) × Q => ρQ y.1 y.2) := by
    simpa only [haction] using (continuous_snd :
      Continuous (fun y : Gal(PadicAlgCl p/E) × Q => y.2))
  have hinj : Function.Injective (HodgeTate.comparison p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) := by
    exact HodgeTate.comparison_injective p E ρQ hcontinuous
  have heq : ρQ = Representation.trivial ℚ_[p] Gal(PadicAlgCl p/E) Q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact haction g v
  have hperiods : HodgeTate.zeroWeightSpan
      (ι := realPrimePowerLocalPeriodAction p 0) ρQ = ⊤ := by
    rw [heq]
    exact zeroWeightSpan_trivialRepresentation p (realPrimePowerLocalPeriodAction p 0)
  obtain ⟨hcomparison, hweights⟩ :=
    (HodgeTate.zeroWeightSpan_eq_top_iff_comparison_bijective_and_weights_zero p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      ρQ hinj).mp hperiods
  exact ⟨⟨S, finrank_primePlusPeriodQuotient_of_rank p hp ξ S hperiod,
    hcomparison, hweights⟩, rfl⟩

/-- A stable quotient of the actual selected Tate representation, with
rational rank `(p - 1) / 2` and trivial Galois action, is ordinary at every RM
label. The rank-one deduction uses the degree of the completed RM field;
fixed pure tensors supply all weight-zero periods. [RaynaudRigid, §1,
Theorem 1 and §3(a)--(b)] motivates these hypotheses for split toric reduction,
but the geometric uniformization and RM-stable kernel are separate inputs. -/
theorem nonempty_primePlusOrdinaryQuotient_of_trivialPeriodAction
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hperiod : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        (p - 1) / 2)
    (htrivial : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule),
      (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule g v = v)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let E := RealPrimePowerCompletion p 0
  let V := primePlusDecompositionRepresentation p hp ξ
  obtain ⟨W, _⟩ := exists_primePlusBaseOrdinaryQuotient_of_trivialPeriodAction
    p hp ξ S hperiod htrivial
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p 0 m hm V) :=
    primePlusConjugateRationalModule p hp ξ m hm
  let : IsScalarTower ℚ_[p] E
      (Rep.localCoefficientConjugate p 0 m hm V) :=
    primePlusConjugateScalarTower p hp ξ m hm
  exact (HodgeTate.nonempty_weightZeroQuotient_localCoefficientConjugate_iff p
    (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
    0 m hm V).mp ⟨W⟩

/-- The chosen weight-zero quotient at every RM label retains the trivial
Raynaud period action. This transports the *specified* stable kernel through
coefficient conjugation, instead of merely transporting existence. -/
theorem exists_primePlusOrdinaryQuotient_of_trivialPeriodAction_with_fixed
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hperiod : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        (p - 1) / 2)
    (htrivial : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule),
      (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule g v = v)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    ∃ W : PrimePlusOrdinaryQuotient p hp ξ m hm,
      ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
        (v : (primePlusDecompositionScalarConjugate p hp ξ m hm) ⧸
          W.kernel.toSubmodule),
        (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
          W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule g v = v := by
  let E := RealPrimePowerCompletion p 0
  let V := primePlusDecompositionRepresentation p hp ξ
  let σ := realPrimePowerCompletionAutomorphism p 0 m hm
  let : Module ℚ_[p] (Rep.localCoefficientConjugate p 0 m hm V) :=
    primePlusConjugateRationalModule p hp ξ m hm
  let : IsScalarTower ℚ_[p] E (Rep.localCoefficientConjugate p 0 m hm V) :=
    primePlusConjugateScalarTower p hp ξ m hm
  let : Module ℚ_[p] (Rep.scalarConjugate σ.toRingEquiv V) :=
    Module.compHom _ (algebraMap ℚ_[p] E)
  let : IsScalarTower ℚ_[p] E (Rep.scalarConjugate σ.toRingEquiv V) := {
    smul_assoc r a v := by
      change (algebraMap ℚ_[p] E r * a) • v =
        algebraMap ℚ_[p] E r • (a • v)
      exact mul_smul _ _ _ }
  obtain ⟨W₀, hW₀⟩ := exists_primePlusBaseOrdinaryQuotient_of_trivialPeriodAction
    p hp ξ S hperiod htrivial
  have hdim₀ : Module.finrank E (V ⧸ S.toSubmodule) = 1 := by
    rw [← hW₀]
    exact W₀.finrank_eq_one
  have hcomp₀ : Function.Bijective (HodgeTate.comparison p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      ((V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) := by
    rw [← hW₀]
    exact W₀.comparison_bijective
  have hweights₀ (q : ℤ) (hq : q ≠ 0) :
      HodgeTate.weightSpace p (realPrimePowerLocalPeriodAction p 0)
        ((V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ := by
    rw [← hW₀]
    exact W₀.weights_zero q hq
  let T := Rep.scalarConjugateSubrepresentationEquiv σ.toRingEquiv V S
  have hdim : Module.finrank E
      (Rep.scalarConjugate σ.toRingEquiv V ⧸ T.toSubmodule) = 1 :=
    (Rep.finrank_scalarConjugate_quotient σ.toRingEquiv V S).trans hdim₀
  have hcomp : Function.Bijective (HodgeTate.comparison p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (((Rep.scalarConjugate σ.toRingEquiv V).ρ.quotient
        T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p])) :=
    (HodgeTate.comparison_bijective_iff p
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ V S)).mp hcomp₀
  have hweights (q : ℤ) (hq : q ≠ 0) :
      HodgeTate.weightSpace p (realPrimePowerLocalPeriodAction p 0)
        (((Rep.scalarConjugate σ.toRingEquiv V).ρ.quotient
          T.toSubmodule T.apply_mem_toSubmodule).restrictScalars ℚ_[p]) q = ⊥ :=
    (HodgeTate.weightSpace_eq_bot_iff
      (Rep.scalarConjugateQuotientRestrictScalarsEquiv ℚ_[p] σ V S) q).mp
        (hweights₀ q hq)
  let W : HodgeTate.WeightZeroQuotient p
      (realPrimePowerLocalPeriodAction p 0)
      (realPrimePowerLocalPeriodAction_fixes p 0)
      (Rep.scalarConjugate σ.toRingEquiv V).ρ :=
    ⟨T, hdim, hcomp, hweights⟩
  refine ⟨W, ?_⟩
  intro g x
  let e := Rep.scalarConjugateQuotientEquiv σ.toRingEquiv V S
  obtain ⟨v, rfl⟩ := e.surjective x
  change (Rep.scalarConjugate σ.toRingEquiv V).ρ.quotient
    T.toSubmodule T.apply_mem_toSubmodule g (e v) = e v
  calc
    _ = e (V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule g v) :=
      (Rep.scalarConjugateQuotientEquiv_apply_action σ.toRingEquiv V S g v).symm
    _ = e v := congrArg e (htrivial g v)

/-- The valuation pairing of a Raynaud period lattice with the cocharacter
lattice detects its Galois action when it is nondegenerate. In the split toric
case the cocharacter action is trivial, so Galois also fixes the period
lattice. This is the linear-algebra deduction from [RaynaudRigid, §3(a)--(b),
p. 475]; construction of the pairing and its identification with the period
quotient of the selected Jacobian are separate geometric inputs. -/
theorem nonempty_primePlusOrdinaryQuotient_of_splitToricPairing
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hperiod : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) =
        (p - 1) / 2)
    (X : Type*) [AddCommGroup X] [Module ℚ_[p] X]
    (ρX : Representation ℚ_[p]
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) X)
    (hsplit : ∀ g x, ρX g x = x)
    (pairing : ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) →ₗ[ℚ_[p]]
      X →ₗ[ℚ_[p]] ℚ_[p])
    (hnondegenerate : Function.Injective pairing)
    (hequivariant : ∀ g v x,
      pairing ((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule g v) (ρX g x) = pairing v x)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  have htrivial (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) :
      (primePlusDecompositionRepresentation p hp ξ).ρ.quotient
        S.toSubmodule S.apply_mem_toSubmodule g v = v := by
    apply hnondegenerate
    apply LinearMap.ext
    intro x
    simpa only [hsplit g x] using hequivariant g v x
  exact nonempty_primePlusOrdinaryQuotient_of_trivialPeriodAction p hp ξ S
    hperiod htrivial m hm

/-- A Galois-equivariant identification of the selected Jacobian's period
quotient with the homology of the split two-component graph produces the
ordinary quotient at every coefficient label. This applies the rank and
trivial-action criterion; the supplied equivariant graph identification
remains a separate geometric input. -/
theorem nonempty_primePlusOrdinaryQuotient_of_splitGraph
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hgraph : (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]).Equiv
      (Representation.trivial ℚ_[p]
        Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)
        (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let E := RealPrimePowerCompletion p 0
  let V := primePlusDecompositionRepresentation p hp ξ
  let Q := V ⧸ S.toSubmodule
  let ρQ := (V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]
  have htrivial (g : Gal(PadicAlgCl p/E)) (v : Q) : ρQ g v = v := by
    apply hgraph.injective
    change hgraph ((ρQ g) v) = hgraph v
    have hi := hgraph.toIntertwiningMap.isIntertwining ρQ
      (Representation.trivial ℚ_[p] Gal(PadicAlgCl p/E)
        (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology) g v
    change hgraph ((ρQ g) v) =
      (Representation.trivial ℚ_[p] Gal(PadicAlgCl p/E)
        (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology) g (hgraph v) at hi
    simpa [Representation.trivial] using hi
  have hperiod : Module.finrank ℚ_[p] Q = (p - 1) / 2 := by
    rw [hgraph.toLinearEquiv.finrank_eq,
      (Graph.twoComponentHomologyEquiv ℚ_[p] ((p - 1) / 2)).finrank_eq]
    exact Module.finrank_fin_fun ℚ_[p]
  exact nonempty_primePlusOrdinaryQuotient_of_trivialPeriodAction p hp ξ S
    hperiod htrivial m hm

/-- If residue Galois fixes each node and its two branches, the graph action
on actual first homology is trivial. Thus an equivariant Picard comparison for
the selected Jacobian supplies the split-graph ordinary quotient at every RM
label. The Picard comparison itself remains a separate geometric input;
Applicability of [SGA7I, Exposé IX, §8.2 and §12.3] at the residue prime,
and compatibility with regularization at a node `xy = π^n`, remain separate
obligations; a prime-to-residue Tate sequence does not supply this input. -/
theorem nonempty_primePlusOrdinaryQuotient_of_fixedGraphNodes
    (α : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      Equiv.Perm (Fin (((p - 1) / 2) + 1)))
    (hα : ∀ g i, α g i = i)
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (hgraph : (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]).Equiv
      (Graph.twoComponentHomologyRepresentation ℚ_[p] ((p - 1) / 2) α))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  have htrivial := Graph.twoComponentHomologyRepresentation_eq_trivial
    ℚ_[p] ((p - 1) / 2) α hα
  rw [htrivial] at hgraph
  exact nonempty_primePlusOrdinaryQuotient_of_splitGraph p hp ξ S hgraph m hm

/-- A surjective Picard period-to-graph map of the expected rational rank is
an equivariant equivalence. This isolates the finite-dimensional step in the
same-Jacobian ordinary argument: the geometric surjection, its compatibility
with the actual Galois action, and the period rank must be supplied for the
selected pointed plus Jacobian. The graph dimension is computed from its
`d + 1` nodes; [TripathiGoswamiRevised, proof of Proposition
`prime-deep-DO`]. -/
theorem nonempty_primePlusOrdinaryQuotient_of_surjectiveGraphMap
    (α : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      Equiv.Perm (Fin (((p - 1) / 2) + 1)))
    (hα : ∀ g i, α g i = i)
    (S : Subrepresentation (primePlusDecompositionRepresentation p hp ξ).ρ)
    (f : (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]).IntertwiningMap
        (Graph.twoComponentHomologyRepresentation ℚ_[p] ((p - 1) / 2) α))
    (hsurj : Function.Surjective f)
    (hrank : Module.finrank ℚ_[p]
      ((primePlusDecompositionRepresentation p hp ξ) ⧸ S.toSubmodule) = (p - 1) / 2)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) := by
  let E := RealPrimePowerCompletion p 0
  let V := primePlusDecompositionRepresentation p hp ξ
  let Q := V ⧸ S.toSubmodule
  let H := (Graph.twoComponentComplex ℚ_[p] ((p - 1) / 2)).homology
  let : Module.Finite E V :=
    Module.finite_of_finrank_eq_succ (by
      simpa only [Nat.reduceAdd] using finrank_primePlusDecompositionRepresentation p hp ξ)
  let : Module.Finite ℚ_[p] E := inferInstance
  let : Module.Finite ℚ_[p] V := Module.Finite.trans E V
  let : Module.Finite ℚ_[p] Q := Module.Finite.quotient ℚ_[p] S.toSubmodule
  have hgraphRank : Module.finrank ℚ_[p] H = (p - 1) / 2 := by
    rw [(Graph.twoComponentHomologyEquiv ℚ_[p] ((p - 1) / 2)).finrank_eq]
    exact Module.finrank_fin_fun ℚ_[p]
  have hfin : Module.finrank ℚ_[p] Q = Module.finrank ℚ_[p] H :=
    hrank.trans hgraphRank.symm
  have hinj : Function.Injective f := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hfin).mpr
    exact hsurj
  let e : (((primePlusDecompositionRepresentation p hp ξ).ρ.quotient
      S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p]).Equiv
        (Graph.twoComponentHomologyRepresentation ℚ_[p] ((p - 1) / 2) α) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩)
      (by intro g; exact f.isIntertwining' g)
  exact nonempty_primePlusOrdinaryQuotient_of_fixedGraphNodes p hp ξ α hα S e m hm

/-- Once the selected Jacobian has the ordinary quotient at label one,
coefficient conjugation gives it at every coprime RM label. -/
theorem nonempty_primePlusOrdinaryQuotient_iff (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Nonempty (PrimePlusOrdinaryQuotient p hp ξ m hm) ↔
      Nonempty (PrimePlusOrdinaryQuotient p hp ξ 1
        (Nat.coprime_one_left _)) := by
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p 0 m hm
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateRationalModule p hp ξ m hm
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (Rep.localCoefficientConjugate p 0 m hm
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateScalarTower p hp ξ m hm
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p 0 1 (Nat.coprime_one_left _)
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateRationalModule p hp ξ 1 (Nat.coprime_one_left _)
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p 0)
      (Rep.localCoefficientConjugate p 0 1 (Nat.coprime_one_left _)
        (primePlusDecompositionRepresentation p hp ξ)) :=
    primePlusConjugateScalarTower p hp ξ 1 (Nat.coprime_one_left _)
  exact HodgeTate.nonempty_weightZeroQuotient_localCoefficientConjugate_independent p
    (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
    0 m hm (primePlusDecompositionRepresentation p hp ξ)

/-- The selected plus Jacobian's labelled local Tate module carries its
completed-coefficient module topology. -/
@[instance_reducible] def primePlusDecompositionConjugateTopology (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    TopologicalSpace (primePlusDecompositionScalarConjugate p hp ξ m hm) :=
  moduleTopology (RealPrimePowerCompletion p 0) _

attribute [local instance] primePlusDecompositionConjugateTopology

theorem primePlusDecompositionConjugateModuleTopology (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    IsModuleTopology (RealPrimePowerCompletion p 0)
      (primePlusDecompositionScalarConjugate p hp ξ m hm) := ⟨rfl⟩

attribute [local instance] primePlusDecompositionConjugateModuleTopology

/-- The genuine Tate action on the selected plus Jacobian remains continuous
after local restriction and conjugation of its coefficient label. -/
theorem continuous_primePlusDecompositionScalarConjugate (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) :
    Continuous fun y : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) ×
        primePlusDecompositionScalarConjugate p hp ξ m hm =>
      (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ y.1 y.2 := by
  unfold primePlusDecompositionScalarConjugate Rep.localCoefficientConjugate
    primePlusDecompositionRepresentation
  apply Rep.continuous_scalarConjugate_comp
    (realPrimePowerCompletionAutomorphism p 0 m hm).toRingEquiv
    (primePlusLocalTateRepresentation p hp ξ) (primePlusLocalGaloisRestriction p)
    (continuous_primePlusLocalGaloisRestriction p)
  unfold primePlusLocalTateRepresentation
  have h := GroupScheme.continuous_localConjugateTateRep
    (realCyclotomicField p) (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) p 0
    (primePlusPrimePowerRealMultiplication p hp) m hm
  with_reducible simpa only [GroupScheme.localConjugateTateRepTopology] using h

/-- Every orbit of the selected plus Jacobian's labelled Tate action is continuous. -/
theorem continuous_primePlusDecompositionScalarConjugate_apply (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1)))
    (v : primePlusDecompositionScalarConjugate p hp ξ m hm) :
    Continuous (fun g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) =>
      (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g v) := by
  have h := continuous_primePlusDecompositionScalarConjugate p hp ξ m hm
  have hf : Continuous (fun g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) => (g, v)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using h.comp hf

/-- A weight-zero quotient of the same selected plus Jacobian yields the
continuous triangular local form used in the Skinner--Wiles checklist. The
existence of this quotient is the separate Raynaud--Picard obligation. -/
theorem PrimePlusOrdinaryQuotient.exists_continuous_characters_upperTriangular
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    ∃ (b : Module.Basis (Fin 2) (RealPrimePowerCompletion p 0)
        (primePlusDecompositionScalarConjugate p hp ξ m hm))
      (χ₁ χ₂ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
        (RealPrimePowerCompletion p 0)ˣ)
      (a : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) → RealPrimePowerCompletion p 0),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ W.kernel ∧
      Nonempty (((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).Equiv
          (Representation.ofCharacter χ₂)) ∧
      (∀ τ, ∀ q : ℤ, q ≠ 0 → HodgeTate.labelledWeightSpace p
        (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
        (Representation.ofCharacter χ₂) q τ = ⊥) ∧
      HodgeTate.zeroWeightSpan (ι := realPrimePowerLocalPeriodAction p 0)
        ((Representation.ofCharacter χ₂).restrictScalars ℚ_[p]) = ⊤ ∧
      ∀ g, LinearMap.toMatrix b b
        ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) =
        !![(χ₁ g : RealPrimePowerCompletion p 0), a g; 0,
          (χ₂ g : RealPrimePowerCompletion p 0)] := by
  let := Valued.toNontriviallyNormedField (RealPrimePowerCompletion p 0)
    (WithZero (Multiplicative ℤ))
  let : Module.Finite (RealPrimePowerCompletion p 0)
      (primePlusDecompositionScalarConjugate p hp ξ m hm) :=
    Module.finite_of_finrank_eq_succ (by
      simpa only [Nat.reduceAdd] using
        (finrank_primePlusDecompositionScalarConjugate p hp ξ m hm))
  unfold PrimePlusOrdinaryQuotient at W
  with_reducible
    exact HodgeTate.WeightZeroQuotient.exists_continuous_characters_upperTriangular p
      (K := RealPrimePowerCompletion p 0)
      (E := RealPrimePowerCompletion p 0)
      (G := Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (V := primePlusDecompositionScalarConjugate p hp ξ m hm)
      (realPrimePowerLocalPeriodAction p 0) (realPrimePowerLocalPeriodAction_fixes p 0)
      (ρ := (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ) W
      (finrank_primePlusDecompositionScalarConjugate p hp ξ m hm)
      (continuous_primePlusDecompositionScalarConjugate_apply p hp ξ m hm)

/-- On the selected plus Jacobian, a supplied weight-zero quotient gives the
finite-inertia condition on its actual lower diagonal character. The fixed
periods come from the quotient, while finiteness is the rank-one input of
[Caruso2019, Theorem 2.2.1]. -/
theorem PrimePlusOrdinaryQuotient.exists_characters_finiteInertia
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    ∃ (b : Module.Basis (Fin 2) (RealPrimePowerCompletion p 0)
        (primePlusDecompositionScalarConjugate p hp ξ m hm))
      (χ₁ χ₂ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
        (RealPrimePowerCompletion p 0)ˣ)
      (a : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) → RealPrimePowerCompletion p 0),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ W.kernel ∧
      Nonempty (((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).Equiv
          (Representation.ofCharacter χ₂)) ∧
      (Set.range (χ₂.comp
        (PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)).subtype)).Finite ∧
      (∀ g, LinearMap.toMatrix b b
        ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) =
          !![(χ₁ g : RealPrimePowerCompletion p 0), a g; 0,
            (χ₂ g : RealPrimePowerCompletion p 0)]) := by
  obtain ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, _, hperiods, hmatrix⟩ :=
    W.exists_continuous_characters_upperTriangular p hp ξ m hm
  let := Valued.toNontriviallyNormedField (RealPrimePowerCompletion p 0)
    (WithZero (Multiplicative ℤ))
  have hfinite := HodgeTate.finite_inertia_of_character_zeroWeightSpan p
    (RealPrimePowerCompletion p 0) (RealPrimePowerCompletion p 0) χ₂ hχ₂ hperiods
  exact ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, hfinite, hmatrix⟩

/-- The same selected fibre also supplies an integral lattice for the quotient
character, with continuous Teichmüller normalization, pro-`p` image and finite
inertia. This lattice is for the quotient character; identifying it with the
global Skinner--Wiles residual lattice remains a separate comparison. -/
theorem PrimePlusOrdinaryQuotient.exists_normalized_characters
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    ∃ (b : Module.Basis (Fin 2) (RealPrimePowerCompletion p 0)
        (primePlusDecompositionScalarConjugate p hp ξ m hm))
      (χ₁ χ₂ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
        (RealPrimePowerCompletion p 0)ˣ)
      (a : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) → RealPrimePowerCompletion p 0),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ W.kernel ∧
      Nonempty (((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).Equiv
          (Representation.ofCharacter χ₂)) ∧
      (∀ g, LinearMap.toMatrix b b
        ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) =
          !![(χ₁ g : RealPrimePowerCompletion p 0), a g; 0,
            (χ₂ g : RealPrimePowerCompletion p 0)]) ∧
      ∃ S : Subrepresentation ((Representation.ofCharacter χ₂).restrictScalars
          𝒪[RealPrimePowerCompletion p 0]),
        ∃ hS : Submodule.IsLattice (RealPrimePowerCompletion p 0) S.toSubmodule,
        letI := hS
        Continuous (normalizedCharacterOfLattice (RealPrimePowerCompletion p 0) p χ₂ S) ∧
        CompactSpace (normalizedCharacterOfLattice (RealPrimePowerCompletion p 0) p χ₂ S).range ∧
        TotallyDisconnectedSpace
          (normalizedCharacterOfLattice (RealPrimePowerCompletion p 0) p χ₂ S).range ∧
        (∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H]
          (f : (normalizedCharacterOfLattice (RealPrimePowerCompletion p 0) p χ₂ S).range →* H),
          Continuous f → IsPGroup p f.range) ∧
        (Set.range ((normalizedCharacterOfLattice (RealPrimePowerCompletion p 0) p χ₂ S).comp
          (PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)).subtype)).Finite := by
  obtain ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, hfinite, hmatrix⟩ :=
    W.exists_characters_finiteInertia p hp ξ m hm
  refine ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, hmatrix, ?_⟩
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  exact exists_lattice_normalized_character (RealPrimePowerCompletion p 0) p χ₂ hχ₂
    (PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) hfinite

/-- Integral normalized ordinary data of the selected pointed plus Jacobian.
The lattice belongs to the local quotient character of this Jacobian. A
comparison with a global residual lattice is separate arithmetic data. -/
structure PrimePlusNormalizedOrdinaryData (m : ℕ)
    (hm : m.Coprime (p ^ (0 + 1))) where
  basis : Module.Basis (Fin 2) (RealPrimePowerCompletion p 0)
    (primePlusDecompositionScalarConjugate p hp ξ m hm)
  upperCharacter : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
    (RealPrimePowerCompletion p 0)ˣ
  lowerCharacter : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
    (RealPrimePowerCompletion p 0)ˣ
  upperRight : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →
    RealPrimePowerCompletion p 0
  upper_continuous : Continuous upperCharacter
  lower_continuous : Continuous lowerCharacter
  lattice : Subrepresentation ((Representation.ofCharacter lowerCharacter).restrictScalars
    𝒪[RealPrimePowerCompletion p 0])
  lattice_isLattice : Submodule.IsLattice (RealPrimePowerCompletion p 0)
    lattice.toSubmodule
  upperTriangular : ∀ g,
    LinearMap.toMatrix basis basis
      ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) =
        !![(upperCharacter g : RealPrimePowerCompletion p 0), upperRight g;
          0, (lowerCharacter g : RealPrimePowerCompletion p 0)]
  finite_normalized_inertia :
    letI := lattice_isLattice
    (Set.range ((normalizedCharacterOfLattice
      (RealPrimePowerCompletion p 0) p lowerCharacter lattice).comp
        (PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)).subtype)).Finite
  /-- The particular weight-zero quotient from which this basis was chosen. -/
  sourceQuotient : PrimePlusOrdinaryQuotient p hp ξ m hm
  /-- The upper basis vector belongs to the kernel of that quotient. -/
  basis_zero_mem_sourceKernel : basis 0 ∈ sourceQuotient.kernel
  /-- The lower diagonal character is the action on that same quotient. -/
  quotientCharacterEquiv :
    (((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
      sourceQuotient.kernel.toSubmodule
      sourceQuotient.kernel.apply_mem_toSubmodule)).Equiv
        (Representation.ofCharacter lowerCharacter)

/-- Construct normalized local data while retaining the particular quotient
and its equivariant lower-character realization. -/
theorem PrimePlusOrdinaryQuotient.exists_normalizedDataWithSource
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    ∃ d : PrimePlusNormalizedOrdinaryData p hp ξ m hm,
      d.sourceQuotient = W := by
  obtain ⟨b, χ₁, χ₂, a, hχ₁, hχ₂, hb, he, hmat, S, hS,
    _, _, _, _, hfinite⟩ := W.exists_normalized_characters p hp ξ m hm
  exact ⟨⟨b, χ₁, χ₂, a, hχ₁, hχ₂, S, hS, hmat, hfinite,
    W, hb, Classical.choice he⟩, rfl⟩

/-- One normalized basis tied to a specified weight-zero quotient. -/
noncomputable def PrimePlusOrdinaryQuotient.normalizedData
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    PrimePlusNormalizedOrdinaryData p hp ξ m hm :=
  Classical.choose (W.exists_normalizedDataWithSource p hp ξ m hm)

/-- The normalized data remembers exactly the quotient used to build it. -/
theorem PrimePlusOrdinaryQuotient.normalizedData_sourceQuotient
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    (W.normalizedData p hp ξ m hm).sourceQuotient = W := by
  exact Classical.choose_spec (W.exists_normalizedDataWithSource p hp ξ m hm)

/-- A weight-zero quotient on the selected plus Jacobian yields its local
normalized data; finite inertia uses [Caruso2019, Theorem 2.2.1]. -/
theorem PrimePlusOrdinaryQuotient.exists_normalizedOrdinaryData
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (W : PrimePlusOrdinaryQuotient p hp ξ m hm) :
    Nonempty (PrimePlusNormalizedOrdinaryData p hp ξ m hm) :=
  ⟨W.normalizedData p hp ξ m hm⟩

/-- If the chosen source quotient has trivial local Galois action, then its
lower diagonal character is exactly one. The source quotient equivalence is
stored in the normalized data, so this assertion does not apply to an
arbitrary unrelated weight-zero quotient. -/
theorem PrimePlusNormalizedOrdinaryData.lowerCharacter_eq_one_of_sourceQuotient_fixed
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (hfixed : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionScalarConjugate p hp ξ m hm) ⧸
        d.sourceQuotient.kernel.toSubmodule),
      (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        d.sourceQuotient.kernel.toSubmodule
        d.sourceQuotient.kernel.apply_mem_toSubmodule g v = v) :
    d.lowerCharacter = 1 := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change (d.lowerCharacter g : RealPrimePowerCompletion p 0) = 1
  have h := LinearMap.congr_fun
    (d.quotientCharacterEquiv.toIntertwiningMap.isIntertwining' g)
      (d.quotientCharacterEquiv.symm (1 : RealPrimePowerCompletion p 0))
  change d.quotientCharacterEquiv
      ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        d.sourceQuotient.kernel.toSubmodule
        d.sourceQuotient.kernel.apply_mem_toSubmodule g
          (d.quotientCharacterEquiv.symm (1 : RealPrimePowerCompletion p 0))) =
    (Representation.ofCharacter d.lowerCharacter) g
      (d.quotientCharacterEquiv
        (d.quotientCharacterEquiv.symm (1 : RealPrimePowerCompletion p 0))) at h
  rw [hfixed g] at h
  simpa only [Representation.ofCharacter_apply,
    d.quotientCharacterEquiv.apply_symm_apply, mul_one] using h.symm

/-- The lower character in a normalized basis equals the action of its
specified source quotient. This applies to the finite quadratic twist at
the complementary cusp without identifying it with the trivial character. -/
theorem PrimePlusNormalizedOrdinaryData.lowerCharacter_eq_of_sourceQuotient_character
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (χ : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ)
    (hact : ∀ (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (v : (primePlusDecompositionScalarConjugate p hp ξ m hm) ⧸
        d.sourceQuotient.kernel.toSubmodule),
      (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        d.sourceQuotient.kernel.toSubmodule
        d.sourceQuotient.kernel.apply_mem_toSubmodule g v =
          (χ g : RealPrimePowerCompletion p 0) • v) :
    d.lowerCharacter = χ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have h := LinearMap.congr_fun
    (d.quotientCharacterEquiv.toIntertwiningMap.isIntertwining' g)
      (d.quotientCharacterEquiv.symm (1 : RealPrimePowerCompletion p 0))
  change d.quotientCharacterEquiv
      ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.quotient
        d.sourceQuotient.kernel.toSubmodule
        d.sourceQuotient.kernel.apply_mem_toSubmodule g
          (d.quotientCharacterEquiv.symm (1 : RealPrimePowerCompletion p 0))) =
    (Representation.ofCharacter d.lowerCharacter) g
      (d.quotientCharacterEquiv
        (d.quotientCharacterEquiv.symm (1 : RealPrimePowerCompletion p 0))) at h
  rw [hact g, map_smul] at h
  simpa only [Representation.ofCharacter_apply,
    d.quotientCharacterEquiv.apply_symm_apply, smul_eq_mul, mul_one] using h.symm

/-- A full integral lattice in the trivial chosen quotient character has
trivial determinant character before reduction. -/
theorem PrimePlusNormalizedOrdinaryData.integralLowerCharacter_eq_one
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (hlower : d.lowerCharacter = 1) :
    Representation.determinantCharacter d.lattice.toRepresentation = 1 := by
  let : Submodule.IsLattice (RealPrimePowerCompletion p 0)
      d.lattice.toSubmodule := d.lattice_isLattice
  apply MonoidHom.ext
  intro g
  apply Units.map_injective
    (IsFractionRing.injective 𝒪[RealPrimePowerCompletion p 0]
      (RealPrimePowerCompletion p 0))
  have hmap := congrArg
    (fun f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ => f g)
    (Representation.map_determinantCharacter_characterLattice
      d.lowerCharacter d.lattice)
  have hchar : d.lowerCharacter g = 1 :=
    congrArg (fun f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ => f g) hlower
  simpa using hmap.trans hchar

/-- Reducing the chosen integral lattice preserves the trivial lower
character. -/
theorem PrimePlusNormalizedOrdinaryData.reducedLowerCharacter_eq_one
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (hlower : d.lowerCharacter = 1) :
    (Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
      𝒪[RealPrimePowerCompletion p 0] →*
        𝒪[RealPrimePowerCompletion p 0] ⧸ 𝓂[RealPrimePowerCompletion p 0])).comp
      (Representation.determinantCharacter d.lattice.toRepresentation) = 1 := by
  rw [d.integralLowerCharacter_eq_one p hp ξ hlower]
  exact MonoidHom.comp_one _

/-- In the triangular basis of a split-period quotient, the upper character
is the determinant of the same labelled Tate action. -/
theorem PrimePlusNormalizedOrdinaryData.upperCharacter_eq_det_of_lowerOne
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (hlower : d.lowerCharacter = 1)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    (d.upperCharacter g : RealPrimePowerCompletion p 0) =
      LinearMap.det ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) := by
  have h := congrArg Matrix.det (d.upperTriangular g)
  rw [LinearMap.det_toMatrix d.basis] at h
  have hchar : (d.lowerCharacter g : RealPrimePowerCompletion p 0) = 1 := by
    simpa using congrArg
      (fun f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
        (RealPrimePowerCompletion p 0)ˣ => (f g : RealPrimePowerCompletion p 0)) hlower
  simpa [Matrix.det_fin_two, hchar] using h.symm

/-- The determinant of the actual labelled Tate action is the product of the
two diagonal characters in its chosen ordinary basis. -/
theorem PrimePlusNormalizedOrdinaryData.upper_mul_lower_eq_det
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    (d.upperCharacter g : RealPrimePowerCompletion p 0) *
      (d.lowerCharacter g : RealPrimePowerCompletion p 0) =
        LinearMap.det ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) := by
  have h := congrArg Matrix.det (d.upperTriangular g)
  rw [LinearMap.det_toMatrix d.basis] at h
  simpa [Matrix.det_fin_two] using h.symm

/-- Coordinates of the actual selected plus-Jacobian local representation in
the ordinary basis. -/
@[expose] def PrimePlusNormalizedOrdinaryData.coordinateRepresentation
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm) :
    Representation (RealPrimePowerCompletion p 0)
      (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
      (Fin 2 → RealPrimePowerCompletion p 0) :=
  d.basis.equivFun.conjRingEquiv.toMonoidHom.comp
    (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ

/-- Coordinates in the chosen ordinary basis give an equivalence of the
actual labelled Tate action with its triangular matrix representation. -/
def PrimePlusNormalizedOrdinaryData.coordinateEquiv
    {m : ℕ} {hm : m.Coprime (p ^ (0 + 1))}
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm) :
    (primePlusDecompositionScalarConjugate p hp ξ m hm).ρ.Equiv
      (d.coordinateRepresentation p hp ξ) := by
  refine Representation.Equiv.mk d.basis.equivFun ?_
  intro g
  apply LinearMap.ext
  intro v
  change d.basis.equivFun
      ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g v) =
    d.basis.equivFun
      ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g
        (d.basis.equivFun.symm (d.basis.equivFun v)))
  rw [d.basis.equivFun.symm_apply_apply]

end HilbertModularity.Hypergeometric
