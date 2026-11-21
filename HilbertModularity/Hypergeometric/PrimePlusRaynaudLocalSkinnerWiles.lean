/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalOrdinaryRow
public import HilbertModularity.Hypergeometric.PrimePlusDeepCuspChecklist

/-! # The native label-one Skinner–Wiles local condition

The actual selected plus Jacobian supplies both residual characters, the
Raynaud ordinary basis, and the operator comparison. A standard local/global
decomposition equivalence supplies its continuous map and inertia relation.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms

attribute [local instance] realFieldAlgebra realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

local instance primePlusRaynaudChecklistCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸
      𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- Any maximal ideal of the real cyclotomic integers containing the
conductor prime is the unique prime used in the local model. -/
theorem realPrimeAboveConductor_eq_of_maximal_mem
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal]
    (hpP : (p : 𝓞 (realCyclotomicField p)) ∈ P) :
    P = (realPrimeAboveConductor p).asIdeal := by
  let a := realPrimeGenerator p
  have hpow : a ^ ((p - 1) / 2) ∈
      (Ideal.span {(p : 𝓞 (realCyclotomicField p))} :
        Ideal (𝓞 (realCyclotomicField p))) := by
    rw [← span_realPrimeGenerator_pow p (by omega), Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hp_le : Ideal.span {(p : 𝓞 (realCyclotomicField p))} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hpP
  have hPpow : a ^ ((p - 1) / 2) ∈ P := hp_le hpow
  have ha : a ∈ P := (inferInstance : P.IsPrime).mem_of_pow_mem _ hPpow
  have hle : Ideal.span {a} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact ha
  have hmax : (Ideal.span {a}).IsMaximal :=
    realPrimeGenerator_isMaximal p (by omega)
  have he : Ideal.span {a} = P := hmax.eq_of_le (inferInstance : P.IsMaximal).ne_top hle
  exact he.symm.trans (span_realPrimeGenerator p (by omega))

/-- All local comparison fields for the selected numerator-cusp basis and
selected native residual datum. The coefficient map identity retains the
same RM label. -/
noncomputable def primePlusRaynaudCubicNumeratorLocalComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal]
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hcont : Continuous φ)
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (hI : ∀ g : primeDecompositionGroup Q,
      (g : AbsoluteGalois (realCyclotomicField p)) ∈
        Q.inertia (AbsoluteGalois (realCyclotomicField p)) →
      φ g ∈ PadicAlgCl.inertia p (RealPrimePowerCompletion p 0)) :
    PrimePlusSkinnerWilesLocalComparison p hp
      (darmonRationalParameter p ξ₀) 1 (Nat.coprime_one_left _)
      (primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
        hξ hA hB hAB hdeep 1 (Nat.coprime_one_left _))
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
      (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ) Q where
  decompositionMap := φ
  continuous_decompositionMap := hcont
  localEquiv := primePlusRaynaudLabelOneLocalEquiv p hp
    (darmonRationalParameter p ξ₀) β C hmap
    (primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
      hξ hA hB hAB hdeep 1 (Nat.coprime_one_left _)) σ
  representation_intertwines := by
    intro g v
    exact primePlusRaynaudLabelOneLocalEquiv_intertwines p hp
      (darmonRationalParameter p ξ₀) β C hmap
      (primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
        hξ hA hB hAB hdeep 1 (Nat.coprime_one_left _))
      Q σ φ hφ g v
  upper_residual_eq := by
    intro g
    exact primePlusRaynaudCubicNumerator_upperResidual_eq p hp ξ₀
      hξ hA hB hAB hdeep β κ C 1 (Nat.coprime_one_left _)
      Q σ φ hφ g
  lower_residual_eq := by
    intro g
    exact primePlusRaynaudCubicNumerator_lowerResidual_eq p hp ξ₀
      hξ hA hB hAB hdeep β κ C 1 (Nat.coprime_one_left _) Q φ g
  inertia_map := hI

/-- [TripathiGoswami, Proposition `prime-deep-DO` and
Proposition `SW-checklist`] At a rational numerator cusp of depth at least
three, the actual selected plus-Jacobian Tate action satisfies the local
Skinner–Wiles ordinary condition at every prime above `p`. The native
coefficient comparison is kept explicit and fixes the RM label. -/
theorem primePlusRaynaudCubicNumerator_skinnerWilesOrdinaryAt
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal]
    (hpP : (p : 𝓞 (realCyclotomicField p)) ∈ P)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P] :
    Nonempty (SkinnerWilesOrdinaryAt p
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
      (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ) Q) := by
  have hP : P = (realPrimeAboveConductor p).asIdeal :=
    realPrimeAboveConductor_eq_of_maximal_mem p hp P hpP
  have : Q.LiesOver (realPrimeAboveConductor p).asIdeal := by
    rw [← hP]
    infer_instance
  obtain ⟨σ, δ, hcont, hconj, hI⟩ := exists_primePlusDecompositionEquiv p hp Q
  let d := primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
    hξ hA hB hAB hdeep 1 (Nat.coprime_one_left _)
  let L := primePlusRaynaudCubicNumeratorLocalComparison p hp ξ₀
    hξ hA hB hAB hdeep β κ C hmap Q σ δ.toMonoidHom hcont hconj
      (fun g hg => (hI g).mp hg)
  exact ⟨L.ordinaryAt p hp (darmonRationalParameter p ξ₀)
    1 (Nat.coprime_one_left _) d
    (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
    (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ) Q⟩


end HilbertModularity.Hypergeometric
