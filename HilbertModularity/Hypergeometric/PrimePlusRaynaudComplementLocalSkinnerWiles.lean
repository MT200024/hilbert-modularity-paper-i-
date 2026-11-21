/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementResidualOrdering
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalOrdinaryRow
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalSkinnerWiles

/-! # The selected complementary-cusp Skinner–Wiles local condition

The actual selected plus-Jacobian quotient at the complementary deep cusp has
the Darmon–Mestre quadratic character. Swapping the selected residual
semisimplification order makes it the lower character in the chosen basis.
The upper residual character follows from the determinant on that same Tate
action. The conjugate decomposition map remains explicit at every prime.
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

local instance primePlusComplementChecklistCharP (p : ℕ) [Fact p.Prime] :
    CharP (𝒪[RealPrimePowerCompletion p 0] ⧸
      𝓂[RealPrimePowerCompletion p 0]) p :=
  inferInstanceAs (CharP 𝓀[RealPrimePowerCompletion p 0] p)

/-- At a rational complementary deep cusp, the actual selected global Tate
action agrees with the fixed quadratic Raynaud basis and the swapped native
residual datum. The native comparison keeps the same RM coefficient label. -/
noncomputable def primePlusRaynaudCubicDifferenceLocalComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
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
      (primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
        hξ hB hAB hdeep)
      (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
      (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).swap Q where
  decompositionMap := φ
  continuous_decompositionMap := hcont
  localEquiv := primePlusRaynaudLabelOneLocalEquiv p hp
    (darmonRationalParameter p ξ₀) β C hmap
    (primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
      hξ hB hAB hdeep) σ
  representation_intertwines := by
    intro g v
    exact primePlusRaynaudLabelOneLocalEquiv_intertwines p hp
      (darmonRationalParameter p ξ₀) β C hmap
      (primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
        hξ hB hAB hdeep) Q σ φ hφ g v
  upper_residual_eq := by
    intro g
    exact primePlusRaynaudCubicDifference_upperResidual_eq p hp ξ₀
      hξ hB hAB hdeep β κ C Q σ φ hφ g
  lower_residual_eq := by
    intro g
    exact primePlusRaynaudCubicDifference_lowerResidual_eq p hp ξ₀
      hξ hB hAB hdeep β κ C Q σ φ hφ g
  inertia_map := hI

/-- [TripathiGoswamiRevised, Proposition `prime-deep-DO` and
Proposition `SW-checklist`] At the rational complementary cusp of depth at
least three, the actual selected plus-Jacobian Tate action satisfies the
local Skinner–Wiles ordinary condition with the swapped residual ordering at
every prime above `p`. The named Raynaud, Darmon–Mestre and decomposition
literature inputs remain visible in its dependencies. -/
theorem primePlusRaynaudCubicDifference_skinnerWilesOrdinaryAt
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
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
      (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).swap Q) := by
  have hP : P = (realPrimeAboveConductor p).asIdeal :=
    realPrimeAboveConductor_eq_of_maximal_mem p hp P hpP
  have : Q.LiesOver (realPrimeAboveConductor p).asIdeal := by
    rw [← hP]
    infer_instance
  obtain ⟨σ, δ, hcont, hconj, hI⟩ := exists_primePlusDecompositionEquiv p hp Q
  let d := primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
    hξ hB hAB hdeep
  let L := primePlusRaynaudCubicDifferenceLocalComparison p hp ξ₀
    hξ hB hAB hdeep β κ C hmap Q σ δ.toMonoidHom hcont hconj
      (fun g hg => (hI g).mp hg)
  exact ⟨L.ordinaryAt p hp (darmonRationalParameter p ξ₀)
    1 (Nat.coprime_one_left _) d
    (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
    (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).swap Q⟩

end HilbertModularity.Hypergeometric
