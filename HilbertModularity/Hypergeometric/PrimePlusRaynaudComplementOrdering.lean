/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalSkinnerWiles
public import HilbertModularity.Geometry.GroupScheme.PrimePlusComplementDeepCusp

/-! # Residual ordering at the complementary deep cusp

The Darmon–Mestre isogeny transports the split period quotient through the
actual quadratic cyclotomic twist. Its lower residual character is therefore
the quadratic character; the selected global residual datum must be ordered
with that character second at this cusp.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.HilbertModularForms

/-- Exchange the two residual semisimplification characters while keeping
the same actual integral action, trace and determinant. -/
def SkinnerWilesResidualData.swap
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) : SkinnerWilesResidualData ρ where
  integralAction := D.integralAction
  integral_spec := D.integral_spec
  chi₁ := D.chi₂
  chi₂ := D.chi₁
  residual_trace g := by
    rw [D.residual_trace]
    exact add_comm _ _
  residual_det g := by
    rw [D.residual_det]
    exact mul_comm _ _

@[simp] theorem SkinnerWilesResidualData.swap_chi₁
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) : D.swap.chi₁ = D.chi₂ := (rfl)

@[simp] theorem SkinnerWilesResidualData.swap_chi₂
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) : D.swap.chi₂ = D.chi₁ := (rfl)

/-- Swapping the residual ordering inverts its ratio, so the kernel and
ratio field are unchanged. -/
theorem SkinnerWilesResidualData.residualRatio_swap
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) (g : AbsoluteGalois F) :
    residualRatio D.swap g = (residualRatio D g)⁻¹ := by
  rw [residualRatio_apply, residualRatio_apply]
  change D.chi₂ g * (D.chi₁ g)⁻¹ =
    (D.chi₁ g * (D.chi₂ g)⁻¹)⁻¹
  group

/-- The swapped datum cuts out the same residual ratio field. -/
theorem SkinnerWilesResidualData.residualRatio_swap_eq_one_iff
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    {ρ : Representation E (AbsoluteGalois F) (Fin 2 → E)}
    (D : SkinnerWilesResidualData ρ) (g : AbsoluteGalois F) :
    residualRatio D.swap g = 1 ↔ residualRatio D g = 1 := by
  rw [D.residualRatio_swap g]
  exact inv_eq_one

end HilbertModularity.HilbertModularForms

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

local instance complementResidualGalCompact (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- The determinant of any full chosen quotient lattice is the canonical
integral lift of its actual lower field character. -/
theorem PrimePlusNormalizedOrdinaryData.integralLowerCharacter_eq_integerCharacter
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm) :
    Representation.determinantCharacter d.lattice.toRepresentation =
      IsNonarchimedeanLocalField.integerCharacter
        (RealPrimePowerCompletion p 0)
        d.lowerCharacter d.lower_continuous := by
  let : Submodule.IsLattice (RealPrimePowerCompletion p 0)
      d.lattice.toSubmodule := d.lattice_isLattice
  apply MonoidHom.ext
  intro g
  apply Units.map_injective
    (IsFractionRing.injective 𝒪[RealPrimePowerCompletion p 0]
      (RealPrimePowerCompletion p 0))
  have h₁ := congrArg
    (fun f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ => f g)
    (Representation.map_determinantCharacter_characterLattice
      d.lowerCharacter d.lattice)
  have h₂ := congrArg
    (fun f : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ => f g)
    (IsNonarchimedeanLocalField.map_integerCharacter
      (RealPrimePowerCompletion p 0) d.lowerCharacter d.lower_continuous)
  exact h₁.trans h₂.symm

/-- The reduction of the actual quadratic twist is the selected global
canonical-prime cyclotomic character at the chosen local Galois element.
This remains true for any residue-field equivalence `κ`, because the values
are exactly `±1`. -/
theorem primePlusComplementQuadraticCharacter_reduced_eq_cyclotomic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
      𝒪[RealPrimePowerCompletion p 0] →*
        𝒪[RealPrimePowerCompletion p 0] ⧸
          𝓂[RealPrimePowerCompletion p 0])
        (IsNonarchimedeanLocalField.integerCharacter
          (RealPrimePowerCompletion p 0)
          (primePlusComplementQuadraticCharacter p hp)
          (primePlusComplementQuadraticCharacter_continuous p hp) g) =
      Units.map κ.toMonoidHom
        (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)
          (primePlusLocalGaloisRestriction p g)) := by
  let F := RealPrimePowerCompletion p 0
  let ε := realPrimeResidualCyclotomicCharacter
    (realCyclotomicField p) p (by omega)
  let χ := primePlusComplementQuadraticCharacter p hp
  let u := IsNonarchimedeanLocalField.integerCharacter F χ
    (primePlusComplementQuadraticCharacter_continuous p hp)
  have hsign : primePlusLocalResidualCyclotomicCharacter p hp g =
      Units.map (realPrimeResidueEquiv p (by omega)).toMonoidHom
        (ε (primePlusLocalGaloisRestriction p g)) := by
    apply Units.ext
    have h₁ := primePlusLocalResidualCyclotomicCharacter_eq_reduction p hp g
    have h₂ := realPrimeResidualCyclotomicCharacter_residue
      (realCyclotomicField p) p (by omega)
      (primePlusLocalGaloisRestriction p g)
    exact (congrArg Units.val h₁).trans h₂.symm
  have hval : ((u g : 𝒪[F]) : F) = (χ g : F) := rfl
  rcases realPrimeResidualCharacter_eq_one_or_neg_one p (by omega)
    (primePlusLocalGaloisRestriction p g) with hε | hε
  · have hlocal : primePlusLocalResidualCyclotomicCharacter p hp g = 1 := by
      rw [hsign, hε]
      simp
    have hχ : χ g = 1 :=
      primePlusComplementQuadraticCharacter_of_residual_one p hp g hlocal
    have hu : (u g : 𝒪[F]) = 1 := by
      apply IsFractionRing.injective 𝒪[F] F
      change ((u g : 𝒪[F]) : F) = (1 : F)
      simpa [hχ] using hval
    apply Units.ext
    change Ideal.Quotient.mk (𝓂[F]) (u g : 𝒪[F]) =
      κ (ε (primePlusLocalGaloisRestriction p g) :
        𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    rw [hu, hε]
    simp
  · have hlocal : primePlusLocalResidualCyclotomicCharacter p hp g = -1 := by
      rw [hsign, hε]
      simp
    have hχ : χ g = -1 :=
      primePlusComplementQuadraticCharacter_of_residual_neg_one p hp g hlocal
    have hu : (u g : 𝒪[F]) = -1 := by
      apply IsFractionRing.injective 𝒪[F] F
      change ((u g : 𝒪[F]) : F) = (-1 : F)
      simpa [hχ] using hval
    apply Units.ext
    change Ideal.Quotient.mk (𝓂[F]) (u g : 𝒪[F]) =
      κ (ε (primePlusLocalGaloisRestriction p g) :
        𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    rw [hu, hε]
    simp

/-- The swapped selected datum places the trivial character first and the
canonical-prime cyclotomic character second. It uses the same integral Tate
action, fixed-vector trace and determinant as the native datum. -/
theorem PrimePlusNativeTateComparison.complementResidualCharacters
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β) :
    (C.selectedResidualData p hp ξ β κ).swap.chi₁ = 1 ∧
      (C.selectedResidualData p hp ξ β κ).swap.chi₂ =
        (Units.map κ.toMonoidHom).comp
          (realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega)) := by
  let D := C.selectedResidualData p hp ξ β κ
  have h₂ : D.chi₂ = 1 := C.selectedResidualData_chi₂_eq_one p hp ξ β κ
  have hratio := C.selectedResidualRatio p hp ξ β κ
  constructor
  · simpa only [D, SkinnerWilesResidualData.swap_chi₁] using h₂
  · rw [SkinnerWilesResidualData.swap_chi₂]
    apply MonoidHom.ext
    intro g
    have hg := congrArg (fun f : AbsoluteGalois (realCyclotomicField p) →*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0])ˣ => f g) hratio
    change residualRatio D g = _ at hg
    rw [residualRatio_apply] at hg
    have h₂g : D.chi₂ g = 1 := congrArg (fun f : AbsoluteGalois
      (realCyclotomicField p) →*
        (𝒪[RealPrimePowerCompletion p 0] ⧸
          𝓂[RealPrimePowerCompletion p 0])ˣ => f g) h₂
    simpa only [h₂g, inv_one, mul_one] using hg

/-- A complementary-cusp ordinary basis whose lower character is the
actual Darmon–Mestre quadratic twist matches the second character of the
swapped selected native residual datum at every conjugate decomposition
prime. -/
theorem PrimePlusNativeTateComparison.complementLowerResidual_eq_of_quadraticLower
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (hlower : d.lowerCharacter = primePlusComplementQuadraticCharacter p hp)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) :
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
    (C.selectedResidualData p hp ξ β κ).swap.chi₂
      (g : AbsoluteGalois (realCyclotomicField p)) := by
  let F := RealPrimePowerCompletion p 0
  let χ := primePlusComplementQuadraticCharacter p hp
  let ε := realPrimeResidualCyclotomicCharacter
    (realCyclotomicField p) p (by omega)
  let D := C.selectedResidualData p hp ξ β κ
  have hD := (C.complementResidualCharacters p hp ξ β κ).2
  have hInt := d.integralLowerCharacter_eq_integerCharacter p hp ξ m hm
  have hIntChar : IsNonarchimedeanLocalField.integerCharacter F
      d.lowerCharacter d.lower_continuous =
      IsNonarchimedeanLocalField.integerCharacter F χ
        (primePlusComplementQuadraticCharacter_continuous p hp) := by
    apply MonoidHom.ext
    intro t
    apply Units.map_injective (IsFractionRing.injective 𝒪[F] F)
    have h₁ := congrArg (fun f : Gal(PadicAlgCl p/F) →* Fˣ => f t)
      (IsNonarchimedeanLocalField.map_integerCharacter F
        d.lowerCharacter d.lower_continuous)
    have h₂ := congrArg (fun f : Gal(PadicAlgCl p/F) →* Fˣ => f t)
      (IsNonarchimedeanLocalField.map_integerCharacter F χ
        (primePlusComplementQuadraticCharacter_continuous p hp))
    have hχt : d.lowerCharacter t = χ t :=
      congrArg (fun f : Gal(PadicAlgCl p/F) →* Fˣ => f t) hlower
    exact h₁.trans (hχt.trans h₂.symm)
  have hεconj : ε (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) =
      ε (g : AbsoluteGalois (realCyclotomicField p)) := by
    simp [map_mul, mul_assoc]
  calc
    _ = Units.map (Ideal.Quotient.mk 𝓂[F] : 𝒪[F] →* 𝒪[F] ⧸ 𝓂[F])
        (IsNonarchimedeanLocalField.integerCharacter F
          d.lowerCharacter d.lower_continuous (φ g)) := by
      simpa only [MonoidHom.comp_apply] using congrArg
        (fun f : Gal(PadicAlgCl p/F) →* 𝒪[F]ˣ =>
          Units.map (Ideal.Quotient.mk 𝓂[F] : 𝒪[F] →* 𝒪[F] ⧸ 𝓂[F])
            (f (φ g))) hInt
    _ = Units.map (Ideal.Quotient.mk 𝓂[F] : 𝒪[F] →* 𝒪[F] ⧸ 𝓂[F])
        (IsNonarchimedeanLocalField.integerCharacter F χ
          (primePlusComplementQuadraticCharacter_continuous p hp) (φ g)) := by
      exact congrArg
        (fun f : Gal(PadicAlgCl p/F) →* 𝒪[F]ˣ =>
          Units.map (Ideal.Quotient.mk 𝓂[F] : 𝒪[F] →* 𝒪[F] ⧸ 𝓂[F])
            (f (φ g))) hIntChar
    _ = Units.map κ.toMonoidHom
        (ε (primePlusLocalGaloisRestriction p (φ g))) :=
      primePlusComplementQuadraticCharacter_reduced_eq_cyclotomic p hp κ (φ g)
    _ = Units.map κ.toMonoidHom
        (ε (g : AbsoluteGalois (realCyclotomicField p))) := by
      rw [hφ g, hεconj]
    _ = D.swap.chi₂ (g : AbsoluteGalois (realCyclotomicField p)) :=
      (congrArg (fun f : AbsoluteGalois (realCyclotomicField p) →*
        (𝒪[F] ⧸ 𝓂[F])ˣ => f (g : AbsoluteGalois (realCyclotomicField p))) hD).symm

end HilbertModularity.Hypergeometric

end
